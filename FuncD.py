# %%
import csv
import datetime
import sys
from enum import Enum
from itertools import chain, combinations
from operator import add
from typing import Hashable

from pyspark import SparkFiles
from pyspark.rdd import RDD
from pyspark.sql import SparkSession
from pyspark.sql.functions import udf
from pyspark.sql.types import (DecimalType, IntegerType, StringType,
                               StructField, StructType, TimestampType)
from strsimpy.damerau import Damerau
from timeit import default_timer as timer

damerau = Damerau() # distance

SOFT_THRESHOLD = 0.9

DELTA_NUM = 1000 # random
DELTA_DATE = 86400*365 # seconds in 24 hours * 365days
DELTA_STR = 10.0 # random

# USERS_DATA_PATH = "data/users.csv"
USERS_DATA_PATH = "data/subset_users.csv"
TEST_DATA_PATH = "data/test_data.csv"

IGNORED_ATTRIBUTES = {
  'id',
  'login',
  'created_at',
  'deleted',
  'fake',
  'type',
  'long',
  'lat'
}

# Type aliases to give types some semantic meaning
DataValue = Hashable # must be hashable because it is used as dict key
AttrName = str

class Classification(Enum):
  NO_FD = 'No Hard/Soft FD'
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

  def __str__(self):
    return f'({",".join(self.lhs)}) -> {self.rhs}'


def isDifferenceMoreThanDelta(a, b) -> 'bool':
  """
  Returns True if the absolute difference between two values is more than delta, False otherwise
  Different metrics are used depending on the types of values (see implementation).
  """
  if type(a) is not type(b):
    raise TypeError(f'Arguments to be compared must be of the same type. Got types: {type(a)} and {type(b)}.')
  if type(a) is int or type(a) is float:
    return abs(a - b) > DELTA_NUM
  if type(a) is datetime.datetime:
    return abs((a - b).total_seconds()) > DELTA_DATE
  if type(a) is str:
    return damerau.distance(a, b) > DELTA_STR
  else:
    raise NotImplementedError(f'Comparison of arguments of type {type(a)} not implemented.')


def attrs_to_tuple(lhs_attrs: 'tuple[AttrName, ...]', rhs_attr: AttrName):
  """
  Maps every user's lhs and rhs attributes to a tuple ((lhs, rhs), 1).
  """
  def anon(user):
    lhs_values = tuple(str(user[attr]) for attr in lhs_attrs)
    rhs_value = str(user[rhs_attr])
    return ((lhs_values, rhs_value), 1)
  return anon


def tuple_to_dict(tup: 'tuple[tuple[tuple[DataValue, ...], DataValue], int]'):
  (lhs_values, rhs_value), count = tup
  return (lhs_values, {rhs_value: count})


def counts_to_prob(values: 'tuple[DataValue, dict[DataValue, int]]'):
  """
  Given the RHS values and their counts for each set of LHS values, computes the
  probability that two records with the same LHS have the same RHS.
  """
  _, rhs_value_counts = values
  rhs_counts = rhs_value_counts.values() # confusing: gets values from dict, which are the counts in this case

  total = sum(rhs_counts)

  # Avoid divisions by zero
  if total == 1:
    return {
      'prob': 1.0,
      'total': total
    }

  prob = 0.0
  for count in rhs_counts:
    prob += (count / total) * ((count - 1) / (total - 1))

  return {
    'prob': prob,
    'total': total
  }


def map_to_boolean_by_distance(values: 'tuple[DataValue, dict[DataValue, int]]'):
  _, rhs_value_counts = values
  rhs_values = rhs_value_counts.keys()
  
  if {type(value) for value in rhs_values} <= {int, float, datetime.datetime}:
    # For these types, we only need to compare the min and max because the difference
    # function is 'transitive', i.e. d(a, b) + d(b, c) = d(a, c)
    return not isDifferenceMoreThanDelta(min(rhs_values), max(rhs_values))  # type: ignore
  else:
    # This is a bottleneck in terms of complexity: if the type is str then we cannot just find min and max in one loop
    for pair in combinations(rhs_values, 2):
      if isDifferenceMoreThanDelta(*pair):
        return False

  return True

def common_part(fd: FunctionalDependency):
  # Count RHS values by LHS value 
  rdd = users.rdd.map(attrs_to_tuple(fd.lhs, fd.rhs)) # 1 in the report
  rdd = rdd.reduceByKey(add) # 2 in the report
  rdd = rdd.map(tuple_to_dict) # 3 in the report
 
  # Merge dictionaries assuming keys are unique 
  # (they are unique because of the `reduceByKey` from before) 
  rdd = rdd.reduceByKey(lambda d1, d2: {**d1, **d2}) # 4 in the report
  return rdd

def hard_soft_part(rdd: RDD):
  rdd = rdd.map(counts_to_prob) # 5 in the report

  # Compute weighted average of probabilites
  # 6 in the report
  rdd = rdd.map(lambda d: {
    'weighted_prob': d['prob'] * d['total'],
    'total': d['total']
  })
  # 7 in the report
  d = rdd.reduce(lambda d1, d2: {
    'weighted_prob': d1['weighted_prob'] + d2['weighted_prob'],
    'total': d1['total'] + d2['total']
  })
  # 8 in the report
  return d['weighted_prob'] / d['total']


def delta_part(rdd: RDD):
  rdd = rdd.map(map_to_boolean_by_distance) # 5 in the report
  rdd = rdd.reduce(lambda x1, x2: x1 and x2) # 6 in the report
  return rdd

def generate_deps(attributes: 'list[AttrName]'):
  """
  Generates A -> B dependencies, where A has up to 3 attributes and B one attribute.
  """
  attrs = set(attributes) - IGNORED_ATTRIBUTES
  lhs_combos = chain(
    combinations(attrs, 1),
    combinations(attrs, 2),
    combinations(attrs, 3)
  )

  deps: list[FunctionalDependency] = []
  for lhs_attrs in lhs_combos:
    for rhs_attr in attrs:
      if rhs_attr not in lhs_attrs:
        deps.append(FunctionalDependency(lhs_attrs, rhs_attr))

  return deps


def purge_non_minimal_deps(candidate_deps: 'list[FunctionalDependency]', fd: 'FunctionalDependency'):
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
users = spark.read.csv(USERS_DATA_PATH, schema, nullValue='\\N')

# %% Preprocessing

# Remove fake users
users = users.filter(users.fake == 0)

@udf
def get_country_name(code: str):
  if code is None:
    return None
  try:
    return countries.get(code).name # type: ignore
  except:
    return None

# Add column "country" with the country name based on the country code.
users = users.withColumn('country', get_country_name(users.country_code))

# %% Check FDs
candidate_deps = generate_deps(users.columns)
discovered_deps = []
isDelta = False
count = 0

while len(candidate_deps) > 0:
  count += 1
  fd = candidate_deps.pop(0)
  print("="*100,f'\n{count}\nChecking FD {fd}')

  both = common_part(fd)
  p = hard_soft_part(both)

  classification = Classification.NO_FD
  if p == 1:
    classification = Classification.HARD
    isDelta = True
  else:
    if p > SOFT_THRESHOLD:
      classification = Classification.SOFT
    isDelta = delta_part(both)

  print(f'Probability = {p}, {classification}')

  fd.probability = p
  fd.classification = classification
  fd.delta = isDelta
  discovered_deps.append(fd)

  # We purge as we go because candidate_deps is sorted from the smallest to the
  # largest candidate FDs. Thus, the first time we see a soft or hard FD it is
  # already minimal.
  candidate_deps, purged = purge_non_minimal_deps(candidate_deps, fd)
  if len(purged) > 0:
    print('\tPurged FDs:')
    for fd in purged:
      print(f'\t\t{fd}')

  print("Delta-FD is found") if isDelta else print("No Delta-FD")

# %% Write results
file_name = f"results for {SOFT_THRESHOLD}, {DELTA_NUM}, {DELTA_DATE}, {DELTA_STR}.csv"
with open(file_name, mode='w') as file:
  results = [[fd.lhs, fd.rhs, fd.probability, fd.classification, fd.delta] for fd in discovered_deps]
  wr = csv.writer(file, quoting=csv.QUOTE_ALL)
  wr.writerow(['Left-hand Side', 'Right-hand side', 'Probability', 'Classification', 'Delta'])
  wr.writerows(results)

t1 = timer() - t
print("Elapsed time: {:.2f}".format(t1), "sec")

# %%
spark.stop()
