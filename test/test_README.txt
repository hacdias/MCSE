# README for Testing #

Currently the test data has the following structure for the relevant attributes
=====================================================================================
total # of rows = 10.000
company = 1 unique value
country_code = 2 distinct values (245-9755)
state = 1 unique value
location = 10.000 distinct values
=====================================================================================

##EXPECTED DEPENDENCIES## (Only some of them)

HARD 
Positive Test Case: company -> state    

SOFT
Positive Test Case: state-> country_code
Negative Test Case: company -> city 

DELTA
Positive Test Case: company -> city
no: ??


