### This script exports an EBD text file to a CSV-like format (without column
### headers). These CSV files are much faster to load than the original EBD format,
### because they contain only a subset of the available columns.
###
### It should not be run on the full 300GB dataset, but instead on a
### smaller subset which can be created with the filter.r script.

library(auk)
library(lubridate)
library(tidyverse)

# define paths
f_ebd <- "../../app/public/data/ebird/ebd_barswa_1950_2020.txt"
f_export <- "../../app/public/data/ebird/ebd_barswa_1950_2020.csv"

# read the ebd file (can take a while, don't run on full 300GB dataset)
print("Reading EBD file")
ebd <- read_ebd(f_ebd)

print("Transforming data")
ebd_export <- ebd %>%
    transmute(
        # get number of days since 1970-01-01 (can be negative)
        date = as.integer(observation_date),
        lat = latitude,
        lon = longitude,
        # set unknown observation counts to 1
        count = as.integer(
            if_else(
                observation_count == "X" | is.na(observation_count),
                "1",
                observation_count
            )
        )
    ) %>%
    # filter out observations outside europe/africa
    filter(-30 < lon & lon < 60) %>%
    # sort by ascending date
    arrange(date)

# print info before exporting
glimpse(ebd_export)

# write to file
print("Writing CSV file")
write.table(ebd_export, f_export, sep=",", row.names = FALSE, col.names = FALSE)

print("Done!")
