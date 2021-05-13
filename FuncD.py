# %%
import csv
from itertools import chain, combinations
from operator import add
from typing import Any

from iso3166 import countries
from pyspark.sql import SparkSession
from pyspark.sql.functions import udf
from pyspark.sql.types import (DecimalType, IntegerType, StringType,
                               StructField, StructType, TimestampType)

SOFT_THRESHOLD = 0.9
# USERS_DATA_PATH = "data/users.csv"
USERS_DATA_PATH = "data/subset_users.csv"
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

class FunctionalDependency:
  def __init__(self, lhs: 'tuple[str, ...]', rhs: str):
    self.lhs = lhs
    self.rhs = rhs

  def __str__(self):
    return f'({",".join(self.lhs)}) -> {self.rhs}'


def attrs_to_tuple(lhs_attrs: 'tuple[str, ...]', rhs_attr: str):
  """
  Maps every user's lhs and rhs attributes to a tuple ((lhs, rhs), 1).
  """
  def anon(user):
    lhs_values = tuple(str(user[attr]) for attr in lhs_attrs)
    rhs_value = str(user[rhs_attr])
    return ((lhs_values, rhs_value), 1)
  return anon


def tuple_to_dict(tup: 'tuple[tuple[tuple[Any, ...], Any], int]'):
  (lhs_values, rhs_value), count = tup
  return (lhs_values, {rhs_value: count})


def counts_to_prob(values: 'tuple[Any, dict[str, int]]'):
  """
  Given the RHS values and their counts for each set of LHS values, computes the
  probability that two records with the same LHS have the same RHS.
  """
  lhs_values, rhs_value_counts = values
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


def dependency_prob(fd: FunctionalDependency):
  """
  Computes the probablity that two records with the same values for the LHS
  attributes have the same RHS value.
  """
  # Count RHS values by LHS value
  rdd = users.rdd.map(attrs_to_tuple(fd.lhs, fd.rhs))
  rdd = rdd.reduceByKey(add)
  rdd = rdd.map(tuple_to_dict)

  # Merge dictonaries assuming keys are unique
  # (they are unique because of the `reduceByKey` from before)
  rdd = rdd.reduceByKey(lambda d1, d2: {**d1, **d2})

  rdd = rdd.map(counts_to_prob)

  # Compute weighted average of probabilites
  rdd = rdd.map(lambda d: {
    'weighted_probs': d['prob'] * d['total'],
    'total': d['total']
  })
  d = rdd.reduce(lambda d1, d2: {
    'weighted_probs': d1['weighted_probs'] + d2['weighted_probs'],
    'total': d1['total'] + d2['total']
  })
  return d['weighted_probs'] / d['total']


def generate_deps(attributes: 'list[str]'):
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


# %% Create Spark session
spark = SparkSession.builder.appName("FuncD").getOrCreate()

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
results = []
for fd in candidate_deps:
  print(f'Checking FD {fd}')

  p = dependency_prob(fd)

  classification = 'No FD'
  if p == 1:
    classification = 'Hard'
  elif p > SOFT_THRESHOLD:
    classification = 'Soft'

  print(f'Probability = {p}, {classification}')
  results.append([fd.lhs, fd.rhs, p, classification])

# %% Write results
with open('brute_force_results.csv', mode='w') as file:
  wr = csv.writer(file, quoting=csv.QUOTE_ALL)
  wr.writerow(['Left-hand Side', 'Right-hand side', 'Probability', 'Classification'])
  wr.writerows(results)

# %%
spark.stop()
