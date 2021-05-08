# %%
import csv
from itertools import combinations
from os import replace

from pyspark.sql import SparkSession
from pyspark.sql.functions import udf
from pyspark.sql.types import DecimalType, IntegerType, StringType, StructField, StructType, TimestampType
from iso3166 import countries

# %%
USERS_DATA_PATH = "data/users.csv"
USERS_DATA_SUBSET_PATH = "data/subset_users.csv"

# %%
spark = SparkSession.builder.appName("FuncD").getOrCreate()

# %%
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
users = spark.read.csv(USERS_DATA_SUBSET_PATH, schema, nullValue='\\N')

# %% Preprocessing

# 1. Remove fake users
users = users.filter(users.fake == 0)

# 2. Impute column "country" with the country name based on the country_code.
country_imputer = udf(lambda code: countries.get(code).name if code != None else code, StringType())
users = users.withColumn('country', country_imputer(users.country_code))

# %% Configuration.
ignored_fields = (
  'id',
  'login',
  'created_at',
  'deleted',
  'fake',
  'type',
  'long',
  'lat'
)

soft_threshold = 0.9

# %% Mapping and reducing functions.

# map_cols_to_tuple maps every user's lhs and rhs columns
# to a tuple (lhs, { rhs: 1 }).
def map_cols_to_tuple(lhs_cols, rhs_cols):
  def anon(user):
    lhs_values = tuple(str(user[col]) for col in lhs_cols)
    rhs_values = tuple(str(user[col]) for col in rhs_cols)
    return (lhs_values, {rhs_values: 1})
  return anon

# merge_columns merges dictionary b into a, where a and b
# are of type { col_name: count, ... }, summing the counts
# for the same keys.
def merge_columns(a, b):
  for rhs_values in a.keys():
    if rhs_values not in b:
      b[rhs_values] = 0
    b[rhs_values] += a[rhs_values]

  return b

# get_majority_sum gets the sum for all elements with the same
# left hand side and the count of elements with the majority
# right hand value for that left hand side.
def get_majority_sum(values):
  rhs_values_frequencies = values[1]
  rhs_frequencies = rhs_values_frequencies.values()

  total = sum(rhs_frequencies)
  prob = 0

  if total == 1:
    # Avoid divisions by zero.
    return {
      'probabilities': [(1.0, 1)],
      'total': total
    }

  for freq in rhs_frequencies:
    prob += (freq / total) * ((freq - 1) / (total - 1))

  return {
    'probabilities': [(prob, total)],
    'total': total
  }

# reduce_counts reduces all counts by summing all majority values
# and all total values.
def reduce_counts(a, b):
  return {
    'probabilities': [*a['probabilities'], *b['probabilities']],
    'total': a['total'] + b['total']
  }

def calculate_probability(reduction):
  total = reduction['total']
  probs = reduction['probabilities']

  # Hard FDs: the sum of all probabilities is the same as
  # the number of different elements because they're all 1.
  # We do this to avoid floating point imprecisions.
  if sum([p[0] for p in probs]) == len(probs):
    return 1.0

  weighted_prob = 0
  for (p, freq) in probs:
    weighted_prob += p * (freq/total)

  return weighted_prob

# dependency_ratio returns a ratio majority / total, where majority
# is the number of rows that have the most common right hand side value
# for all left side values. The total is basically the total number of rows.
#
# NOTE: we probably don't need to calculate total as it is the total number
# of rows.
def dependency_ratio(lhs_cols, rhs_cols):
  dt = users.rdd.map(map_cols_to_tuple(lhs_cols, rhs_cols))
  dt = dt.reduceByKey(merge_columns)
  dt = dt.map(get_majority_sum)
  re = dt.reduce(reduce_counts)
  prob = calculate_probability(re)
  return prob

# Generates A -> B rules, where A has up to 3 columns and B one from the
# columns.
def generate_combos(columns):
  lhs_combos = [
    *list(combinations(columns, 1)),
    *list(combinations(columns, 2)),
    *list(combinations(columns, 3)),
  ]

  combos = []

  for lhs_cols in lhs_combos:
    for col in columns:
      if col not in lhs_cols:
        combos.append((lhs_cols, (col,)))

  return combos

# Filter by ignored_fields.
def filter_ignored(relation):
  for field in ignored_fields:
    if field in relation[0] or field in relation[1]:
      return False
  return True

to_check = generate_combos(users.columns)
to_check = filter(filter_ignored, to_check)
to_check = list(to_check)

results = []

for (lhs_cols, rhs_cols) in to_check:
  print(f'Checking FS: {lhs_cols} -> {rhs_cols}')
  v = dependency_ratio(lhs_cols, rhs_cols)

  classification = 'No FD'
  if v == 1:
    classification = 'Hard'
  elif v > soft_threshold:
    classification = 'Soft'

  print(f'Probability = {v}, {classification}')
  results.append([lhs_cols, rhs_cols, v, classification])

with open('brute_force_results.csv', mode='w') as file:
  wr = csv.writer(file, quoting=csv.QUOTE_ALL)
  wr.writerow(['Left-hand Side', 'Right-hand side', 'Probability', 'Classification'])
  wr.writerows(results)

spark.stop()
