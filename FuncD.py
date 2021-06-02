# %%
import csv
import sys
import uuid
from enum import Enum
from itertools import chain, combinations
from operator import add
from typing import Hashable

from pyspark import SparkFiles
from pyspark.sql import SparkSession
from pyspark.sql.functions import udf
from pyspark.sql.types import (DecimalType, IntegerType, StringType,
                               StructField, StructType, TimestampType)

SOFT_THRESHOLD = 0.9
# USERS_DATA_PATH = "data/users.csv"
USERS_DATA_PATH = "data/subset_users.csv"
TEST_DATA_PATH = "data/test_data.csv"

IGNORED_ATTRIBUTES = {
  'fake',
}

IGNORED_ATTRIBUTES_LHS = {
  'id',
  'login',
  'created_at',
  'long',
  'lat',
}

# Type aliases to give types some semantic meaning
DataValue = Hashable # must be hashable because it is used as dict key
AttrName = str

class Classification(Enum):
  NO_FD = 'No FD'
  HARD = 'Hard'
  SOFT = 'Soft'

  def __str__(self):
    return str(self.value)

class FunctionalDependency:
  def __init__(self, lhs: 'tuple[AttrName, ...]', rhs: AttrName):
    self.lhs = lhs
    self.rhs = rhs
    self.probability = 0.0
    self.classification = None
    self.id = uuid.uuid4().hex

  def __str__(self):
    return f'({",".join(self.lhs)}) -> {self.rhs}'


def attrs_to_tuple(fds: 'list[FunctionalDependency]'):
  """
  Maps every user's lhs and rhs attributes to a tuple ((lhs, rhs), 1).
  """
  def anon(user):
    tuples = []
    for fd in fds:
      lhs_values = tuple(str(user[attr]) for attr in fd.lhs)
      rhs_value = str(user[fd.rhs])
      tuples.append(((fd.id, lhs_values, rhs_value), 1))
    return tuples
  return anon


def tuple_to_dict(tup: 'tuple[str, tuple[tuple[DataValue, ...], DataValue], int]'):
  (fd_id, lhs_values, rhs_value), count = tup
  return ((fd_id, lhs_values), {rhs_value: count})


def counts_to_prob(values: 'tuple[DataValue, dict[DataValue, int]]'):
  """
  Given the RHS values and their counts for each set of LHS values, computes the
  probability that two records with the same LHS have the same RHS.
  """
  (fd_id, lhs_values), rhs_value_counts = values
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


def dependency_prob(fds: 'list[FunctionalDependency]'):
  """
  Computes the probability that two records with the same values for the LHS
  attributes have the same RHS value.
  """
  # Count RHS values by LHS value
  rdd = users.rdd.flatMap(attrs_to_tuple(fds))
  rdd = rdd.reduceByKey(add)
  rdd = rdd.map(tuple_to_dict)

  # Merge dictionaries assuming keys are unique
  # (they are unique because of the `reduceByKey` from before)
  rdd = rdd.reduceByKey(lambda d1, d2: {**d1, **d2})

  rdd = rdd.map(counts_to_prob)

  # Compute weighted average of probabilites
  rdd = rdd.map(lambda d: (d['fd_id'], {
    'weighted_prob': d['prob'] * d['total'],
    'total': d['total']
  }))

  rdd = rdd.reduceByKey(lambda d1, d2: {
    'weighted_prob': d1['weighted_prob'] + d2['weighted_prob'],
    'total': d1['total'] + d2['total']
  })

  rdd = rdd.map(lambda d: {
    d[0]: d[1]['weighted_prob'] / d[1]['total']
  })

  return rdd.reduce(lambda d1, d2: {**d1, **d2})


def generate_deps(attributes: 'list[AttrName]', n: 'int'):
  """
  Generates A -> B dependencies, where A has n attributes and B one attribute.
  """
  attrs = set(attributes) - IGNORED_ATTRIBUTES
  lhs_combos = combinations(attrs - IGNORED_ATTRIBUTES_LHS, n)

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

# Add to Spark the third party modules we need.
spark.sparkContext.addFile("iso3166.py")
sys.path.insert(0,SparkFiles.getRootDirectory())

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

# Yield successive n-sized chunks from a list.
def chunks(lst, n):
  for i in range(0, len(lst), n):
      yield lst[i:i + n]

# %% Check FDs
discovered_deps = []
chunks_size = -1

# From 1 to 3 LHS elements.
for n in range(1, 4):
  print(f'Generating FDs with {n} LHS elements...')
  candidates = generate_deps(users.columns, n)

  # We purge as we go because candidate_deps is sorted from the smallest to the
  # largest candidate FDs. Thus, the first time we see a soft or hard FD it is
  # already minimal.
  print(f'Purging non-minimal FDs...')
  for fd in discovered_deps:
    candidates, purged = purge_non_minimal_deps(candidates, fd)
    for fd in purged: print(f'\t{fd} purged')
  
  # It will be useful to access candidates by ID.
  candidates_by_id = {}
  for fd in candidates:
    candidates_by_id[fd.id] = fd

  # If we don't a chunk size, set it to the current length of candidates.
  if chunks_size == -1:
    chunks_size = len(candidates)

  print(f'Calculating probabilities...')
  for chunk in chunks(candidates, chunks_size):
    ps = dependency_prob(chunk)

    for id, p in ps.items():
      fd = candidates_by_id[id]

      classification = Classification.NO_FD
      if p == 1:
        classification = Classification.HARD
      elif p > SOFT_THRESHOLD:
        classification = Classification.SOFT

      print(f'\t{fd}: {p}, {classification}')

      fd.probability = p
      fd.classification = classification
      discovered_deps.append(fd)

# %% Write results
with open('brute_force_results.csv', mode='w') as file:
  results = [[fd.lhs, fd.rhs, fd.probability, fd.classification] for fd in discovered_deps]
  wr = csv.writer(file, quoting=csv.QUOTE_ALL)
  wr.writerow(['Left-hand Side', 'Right-hand side', 'Probability', 'Classification'])
  wr.writerows(results)

# %%
spark.stop()
