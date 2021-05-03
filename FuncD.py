# %%
from pyspark.sql import SparkSession
from pyspark.sql.types import DecimalType, IntegerType, StringType, StructField, StructType, TimestampType

# %%
USERS_DATA_PATH = "data/users.csv"

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
users = spark.read.csv(USERS_DATA_PATH, schema, nullValue='\\N')

# %% Print the first row
print(users.head(1))

# %% Use the RDD interpretation of the DataFrame (slow)
nimo = users.rdd.filter(lambda user: user.login == 'nimobeeren').collect()
print(nimo)

# %% Use the DataFrame directly (faster)
nimo = users.filter(users.login == 'nimobeeren').collect()
print(nimo)

# %%
spark.stop()
