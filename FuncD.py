# %%
import argparse
import csv
import operator
from os import write
import sys
from time import time
import uuid
from difflib import SequenceMatcher
from enum import Enum
from itertools import combinations
from timeit import default_timer as timer
from typing import Hashable

from pyspark import SparkFiles
from pyspark.rdd import RDD
from pyspark.sql import SparkSession, DataFrame
from pyspark.sql.functions import udf, isnull
from pyspark.sql.types import (DecimalType, IntegerType, StringType,
                               StructField, StructType, TimestampType)

parser = argparse.ArgumentParser(description='Discover functional dependencies in the GHTorrent dataset.')
parser.add_argument('data_path', nargs='?', default='data/subset_users.csv', help='Path to CSV data file.')
parser.add_argument('-s', '--soft_threshold', type=float, default=0.9, help='Probability must be least this large to be a soft FD.')
parser.add_argument('-d', '--delta_threshold', type=float, default=0.05, help='Difference must be at most this large to be a delta FD.')
parser.add_argument('-t', '--sample_threshold', type=float, default=0.3, help='Decide which FDs will be dropped after sampling.')
parser.add_argument('-z', '--sample_size', type=float, default=0.03, help='Percentage of the dataset which is going to be included in the sample.')
parser.add_argument('--approx', action='store_true', help='Whether to use an approximate algorithm for string comparisons. Uses an exact algortihm by default.')
parser.add_argument('--out', '-o', default='results.csv', help='Path to results output file. Defaults to results.csv.')
args = parser.parse_args()

IGNORED_LHS_ATTRS = {
  'id',
  'login',
  'created_at',
  'long',
  'lat'
}

sampling = True

# Type aliases to give types some semantic meaning
DataValue = Hashable # must be hashable because it is used as dict key
AttrName = str

class Classification(Enum):
  NO_HARD_SOFT_FD = 'No Hard/Soft FD'
  HARD = 'Hard'
  SOFT = 'Soft'

  def __str__(self):
    return str(self.value)

class FunctionalDependency:
  def __init__(self, lhs: 'tuple[AttrName, ...]', rhs: AttrName):
    self.lhs = lhs
    self.rhs = rhs
    self.probability = 0.0
    self.classification: 'Classification | None' = None
    self.delta = False
    self.id = uuid.uuid4().hex

  def __str__(self):
    return f'({",".join(self.lhs)}) -> {self.rhs}'


def difference(a, b, value_range) -> float:
  """
  The difference between two non-string values, relative to the full range of
  possible values. Returns 0.0 if values are equal, and returns 1.0 if values
  are completely different.
  """
  return abs(a - b) / (value_range[1] - value_range[0])

def stringDifference(a, b):
  s = SequenceMatcher(a=a, b=b, autojunk=False)
  if args.approx:
    return 1 - s.real_quick_ratio()
  else:
    return 1 - s.ratio()

def attrs_to_tuple(fds: 'list[FunctionalDependency]'):
  """
  Maps every user's lhs and rhs attributes to a tuple ((lhs, rhs), 1).
  """
  def anon(user):
    tuples = []
    for fd in fds:
      lhs_values = tuple(user[attr] for attr in fd.lhs)
      rhs_value = user[fd.rhs]
      tuples.append(((fd.id, lhs_values, rhs_value), 1))
    return tuples
  return anon


def tuple_to_dict(tup: 'tuple[tuple[str, tuple[DataValue, ...], DataValue], int]'):
  (fd_id, lhs_values, rhs_value), count = tup
  return ((fd_id, lhs_values), {rhs_value: count})


def counts_to_prob(values: 'tuple[tuple[str, tuple[DataValue, ...]], dict[DataValue, int]]'):
  """
  Given the RHS values and their counts for each set of LHS values, computes the
  probability that two records with the same LHS have the same RHS.
  """
  (fd_id, _), rhs_value_counts = values
  rhs_counts = rhs_value_counts.values() # confusing: gets values from dict, which are the counts in this case

  total = sum(rhs_counts)

  # Avoid divisions by zero
  if total == 1:
    return {
      'fd_id': fd_id,
      'prob': 1.0,
      'total': total
    }

  prob = 0.0
  for count in rhs_counts:
    prob += (count / total) * ((count - 1) / (total - 1))

  return {
    'fd_id': fd_id,
    'prob': prob,
    'total': total
  }


def map_to_boolean_by_difference(fds: 'list[FunctionalDependency]'):
  fds_by_id = {fd.id: fd for fd in fds}

  def anon(values: 'tuple[tuple[str, tuple[DataValue, ...]], dict[DataValue, int]]'):
    (fd_id, _), rhs_value_counts = values
    rhs_values = rhs_value_counts.keys()
    fd = fds_by_id[fd_id]

    is_delta = True
    if fd.rhs in string_attrs:
      # This is a bottleneck in terms of complexity: if the type is str then we cannot just find min and max in one loop
      for a, b in combinations(rhs_values, 2):
        if stringDifference(a, b) > args.delta_threshold:
          is_delta = False
          break
    else:
      # For these types, we only need to compare the min and max because the difference
      # function is 'transitive', i.e. d(a, b) + d(b, c) = d(a, c)
      mini = min(rhs_values)  # type: ignore
      maxi = max(rhs_values)  # type: ignore
      is_delta = difference(mini, maxi, value_ranges[fd.rhs]) <= args.delta_threshold

    return (fd_id, is_delta)

  return anon


def common_part(rdd: RDD, fds: 'list[FunctionalDependency]'):
  # Count RHS values by LHS value 
  rdd = rdd.flatMap(attrs_to_tuple(fds)) # 1 in the report
  rdd = rdd.reduceByKey(operator.add) # 2 in the report
  rdd = rdd.map(tuple_to_dict) # 3 in the report
 
  # Merge dictionaries assuming keys are unique 
  # (they are unique because of the `reduceByKey` from before) 
  rdd = rdd.reduceByKey(lambda d1, d2: {**d1, **d2}) # 4 in the report
  return rdd


def hard_soft_part(rdd: RDD):
  rdd = rdd.map(counts_to_prob) # 5 in the report

  # Compute weighted average of probabilites
  # 6 in the report
  rdd = rdd.map(lambda d: (d['fd_id'], {
    'weighted_prob': d['prob'] * d['total'],
    'total': d['total']
  }))
  # 7 in the report
  rdd = rdd.reduceByKey(lambda d1, d2: {
    'weighted_prob': d1['weighted_prob'] + d2['weighted_prob'],
    'total': d1['total'] + d2['total']
  })
  rdd = rdd.map(lambda d: {
    d[0]: d[1]['weighted_prob'] / d[1]['total']
  })
  if rdd.isEmpty():
    return {}
  else:
    return rdd.reduce(lambda d1, d2: {**d1, **d2})


def delta_part(rdd: RDD, fds: 'list[FunctionalDependency]'):
  rdd = rdd.filter(lambda x: x[0][0] in [f.id for f in fds])
  rdd = rdd.map(map_to_boolean_by_difference(fds)) # 5 in the report
  rdd = rdd.reduceByKey(operator.and_) # 6 in the report
  rdd = rdd.map(lambda x: {
    x[0]: x[1]
  })
  if rdd.isEmpty():
    return {}
  else:
    return rdd.reduce(lambda d1, d2: {**d1, **d2})


def generate_deps(attributes: 'list[AttrName]', n: int):
  """
  Generates A -> B dependencies, where A has n attributes and B one attribute.
  """
  lhs_attrs = set(attributes) - IGNORED_LHS_ATTRS
  rhs_attrs = set(attributes)

  lhs_combos = combinations(lhs_attrs, n)

  deps: list[FunctionalDependency] = []

  for lhs_attrs in lhs_combos:
    for rhs_attr in rhs_attrs:
      if rhs_attr not in lhs_attrs:
        deps.append(FunctionalDependency(lhs_attrs, rhs_attr))

  return deps


def purge_non_minimal_deps(candidate_deps: 'list[FunctionalDependency]', fd: FunctionalDependency):
  """
  Given a list of candidate dependencies, purge all non-minimal dependencies
  regarding given fd.
  """
  if fd.classification != Classification.HARD and fd.classification != Classification.SOFT:
    # If fd is not a hard or soft dependency, then we cannot proceed.
    return candidate_deps, []

  minimal_deps = []
  purged_deps = []

  for cfd in candidate_deps:
    is_minimal = not (set(fd.lhs).issubset(set(cfd.lhs)) and fd.rhs == cfd.rhs)
    if is_minimal:
      minimal_deps.append(cfd)
    else:
      purged_deps.append(cfd)

  return minimal_deps, purged_deps


# %% Create Spark session
spark = SparkSession.builder.appName("FuncD").getOrCreate()

t = timer()

# Add to Spark the third party modules we need.
spark.sparkContext.addFile("iso3166.py")
sys.path.insert(0, SparkFiles.getRootDirectory()) # type: ignore

from iso3166 import countries

# %% Read the data from CSV

# This reflects the SQL schema of the `users` table provided at:
# https://github.com/gousiosg/github-mirror/blob/3d5f4b2ffa5d510455e58b1209c31f4d1b211306/sql/schema.sql
schema = StructType([
  StructField("id", IntegerType()),
  StructField("login", StringType()),
  StructField("company", StringType()),
  StructField("created_at", TimestampType()),
  StructField("type", StringType()),
  StructField("fake", IntegerType()),
  StructField("deleted", IntegerType()),
  StructField("long", DecimalType(11, 8)), # numbers define precision
  StructField("lat", DecimalType(10, 8)), # numbers define precision
  StructField("country_code", StringType()),
  StructField("state", StringType()),
  StructField("city", StringType()),
  StructField("location", StringType()),
])
print(f'Reading data from {args.data_path}')

users = spark.read.csv(args.data_path, schema, nullValue='\\N')

# %% Preprocessing
print("Preprocessing")

# Remove fake users
users = users.filter(users.fake == 0)
users = users.drop('fake')

@udf
def get_country_name(code: str):
  if code is None:
    return None
  try:
    return countries.get(code).name # type: ignore
  except:
    return None

# Add column "country" with the country name based on the country code.
users = users.withColumn('country', get_country_name(users.country_code))  # type: ignore

# Remove users that have null value for lat/long
# ~ means not
users = users.filter(~isnull('lat'))
users = users.filter(~isnull('long'))

# For string attributes, replace null values with the empty string
string_attrs = {attr for attr, dtype in users.dtypes if dtype == 'string'}
users = users.fillna('', subset=list(string_attrs))

# %% Compute attribute value ranges
print("Computing attribute value ranges")
value_ranges = {}
for attr in set(users.columns) - string_attrs:
  minimum = users.agg({attr: 'min'}).collect()[0][0]
  maximum = users.agg({attr: 'max'}).collect()[0][0]
  value_ranges[attr] = (minimum, maximum)

def chunks(lst, n=None):
  """
  Yield successive n-sized chunks from a list. The last chunk may be smaller.
  """
  if n is None:
    yield lst
  else:
    for i in range(0, len(lst), n):
      yield lst[i:i+n]

# %% Check FDs
discovered_deps = []
CHUNKS_SIZE = None


def discover_dependencies(users: DataFrame, common_candidates: 'list | None', sampling: bool):
  
  for n in range(1, 4):
      print(f'Generating FDs with {n} LHS elements...')
      candidates = generate_deps(users.columns, n)
      delta_candidates: 'list[FunctionalDependency]' = []
      shared_candidates: 'list[FunctionalDependency]' = []

      print(f'Purging non-minimal FDs...')
      for fd in discovered_deps:
        candidates, purged = purge_non_minimal_deps(candidates, fd)

      # If we are not in sampling mode then we have to use the shared candidates produced
      # by the intersection of the sampling candidate sets
      print(f'Sampling mode? --> {sampling}')
      if (not sampling) and (common_candidates):
          for cand in candidates:
            for sample_cand in common_candidates:
              if (cand.lhs == sample_cand[0]):
                if (cand.rhs == sample_cand[1]):
                  shared_candidates.append(cand)
          candidates = shared_candidates


      candidates_by_id = {fd.id: fd for fd in candidates}
      print(f'Final list of lhs = {n} candidates checked: {len(candidates)}')
      # if n == 3 : spark.stop()
      print(f'Calculating probabilities...')
      for chunk in chunks(candidates, CHUNKS_SIZE):
        
        common_result = common_part(users.rdd, chunk)
        ps = hard_soft_part(common_result)

        for id, p in ps.items():
          fd = candidates_by_id[id]

          classification = Classification.NO_HARD_SOFT_FD
          if p == 1:
            classification = Classification.HARD
            fd.delta = True
          else:
            if p > args.soft_threshold:
              classification = Classification.SOFT
            delta_candidates.append(fd)
          #Again if sampling, then discard the candidates with a probability that is 50% or lower
          if (sampling):
            if (p > args.sample_threshold):
              fd.probability = p
              fd.classification = classification
              discovered_deps.append(fd)
          else:
              fd.probability = p
              fd.classification = classification
              discovered_deps.append(fd)

        delta_result = {}
        if len(delta_candidates) > 0:
          # print('Checking delta FDs...')
          delta_result = delta_part(common_result, delta_candidates)

        for id, result in delta_result.items():
          fd = candidates_by_id[id]
          # print(f'Checked delta FD {fd}: {result}')
          fd.delta = result 

def write_results(discovered_deps):

  print(f'Checked {len(discovered_deps)} FDs')
  print(f'Writing result to {args.out}')
  with open(args.out, mode='w') as file:
    results = [[fd.lhs, fd.rhs, fd.probability, fd.classification, fd.delta] for fd in discovered_deps]
    wr = csv.writer(file, quoting=csv.QUOTE_ALL)
    wr.writerow(['Left-hand Side', 'Right-hand side', 'Probability', 'Classification', 'Delta'])
    wr.writerows(results)

sampling_candidates_deps = []

for x in range(1,4):
  discovered_deps = []
  sample = users.sample(False, args.sample_size)
  discover_dependencies(sample, None, True)
  deps = [[fd.lhs, fd.rhs] for fd in discovered_deps]
  sampling_candidates_deps.append(deps)

sample1, sample2, sample3 = sampling_candidates_deps[0], sampling_candidates_deps[1], sampling_candidates_deps[2]

common_candidates = [x for x in (sample1 or sample2 or sample3) if x in (sample1 and sample2 and sample3)]
print("Common Candidates between the samples: ", len(common_candidates))


discovered_deps = []
discover_dependencies(users, common_candidates, False)
write_results(discovered_deps)
t1 = timer() - t
print(f'Elapsed time for sampling and discovering: {t1:.2f} sec')

# %%
spark.stop()
