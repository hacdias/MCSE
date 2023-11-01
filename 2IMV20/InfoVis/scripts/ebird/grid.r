### This script generates a geographical grid containing the relative
### frequency of observed birds for each month. The output is written to a
### JSON file.
###
### The input is a CSV file which can be created with the export.r script.

library(jsonlite)
library(lubridate)
library(tidyverse)

# define paths
f_input <- "../../app/public/data/ebird/ebd_barswa_1950_2020.csv"
f_output <- "../../app/public/data/ebird/ebd_grid_barswa_1980_2019.json"

# read input CSV
print("Reading CSV file")
ebd_input <- read.csv(f_input, header = FALSE, col.names = c("date", "lat", "lon", "count"))

# clean and filter the data
ebd <- ebd_input %>%
    # convert numbers to dates
    mutate(date = as_date(date)) %>%
    # filter out very large observations
    filter(count < 1000) %>%
    # filter out observations before 1980
    filter(year(date) >= 1980)

print("Generating grid")

# compute monthly count totals needed to compute monthly frequency
month_summary <- ebd %>%
    mutate(
        month = floor_date(date, unit="month"),
    ) %>%
    select(month, count) %>%
    group_by(month) %>%
    summarize(month_count = sum(count), .groups="drop")

# generate grid of monthly frequencies
size <- 4 # size of each cell in degrees
grid <- ebd %>%
    mutate(
        month = floor_date(date, unit="month"),
        lat_round = floor(lat / size) * size,
        lon_round = floor(lon / size) * size
    ) %>%
    # sum counts for all rows with the same month, lat and lon
    group_by(month, lat_round, lon_round) %>%
    summarize(cell_count = sum(count), .groups="drop") %>%
    # compute monthly frequency for each cell
    inner_join(month_summary, by="month") %>%
    mutate(
        # compute cell count relative to monthly count total
        frequency = cell_count / month_count
    ) %>%
    # scale frequency to [0,1] for each month
    group_by(month) %>%
    mutate(frequency = frequency / max(frequency)) %>%
    ungroup()

# convert grid to JSON
print("Writing JSON file")
all_list <- list()
years <- 1980:2019
months <- 1:12
for (y in years) {
    year_list <- list()
    for (m in months) {
        month_list <- list()
        month_df <- grid %>%
            filter(year(month) == y & month(month) == m) %>%
            select(lat_round, lon_round, frequency)
        
        if (nrow(month_df) > 0) {
            # convert dataframe to list of (equal-length) vectors
            month_list <- split(month_df, seq(nrow(month_df))) %>% lapply(unlist)
            names(month_list) <- NULL
        }
        
        year_list[[m]] <- month_list
    }
    
    # use the year as the key to create a JSON object
    # lists without names form a JSON array
    all_list[[paste(y)]] <- year_list
}

write(toJSON(all_list), file=f_output)

print("Done!")
