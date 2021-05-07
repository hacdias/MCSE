# %%
from os import replace
from pyspark.sql import SparkSession
from pyspark.sql.functions import udf
from pyspark.sql.types import DecimalType, IntegerType, StringType, StructField, StructType, TimestampType
from ISO3166 import *

    
# %%
USERS_DATA_PATH = "data/users.csv"
USERS_DATA_PATH_SUBSET = "data/subset_users.csv"

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
    StructField("country", StringType()), # ADDED country field
    StructField("state", StringType()),
    StructField("city", StringType()),
    StructField("location", StringType()),
])
users = spark.read.csv(USERS_DATA_PATH_SUBSET, schema, nullValue='\\N')


users = users.filter(users.fake==0) # FIlter out fake users
print(users.count())

# Use country code Dict to add a column with the full country name 
country_imputer = udf(lambda code: ISO3166.get(code.upper()) if code != None else code, StringType()) 
updated_users = users.withColumn('country',country_imputer(users.country_code))

print(updated_users.tail(10))



spark.stop()
