library(jsonlite)
library(lubridate)
library(tidyverse)

# define paths
f_input <- "../../app/public/data/ebird/ebd_barswa_1950_2020.csv"
f_output <- "../../app/public/data/ebird/ebd_latitudes_barswa_1980_2019.json"

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

print("Generating data")
ebd_mean_lat <- ebd %>%
    group_by(year = year(date), month = month(date)) %>%
    summarize(mean_lat = weighted.mean(lat, count), .groups="drop")

print("Writing JSON file")
all_list <- list()
years <- 1980:2019
months <- 1:12
for (y in years) {
    year_vector <- c()
    for (m in months) {
        month_df <- ebd_mean_lat %>% filter(year == y & month == m)
        
        value <- month_df$mean_lat[1]
        year_vector <- append(year_vector, value)  
    }
    
    # use the year as the key to create a JSON object
    # lists without names and vectors form a JSON array
    all_list[[paste(y)]] <- year_vector
}

write(toJSON(all_list, na="null"), f=f_output)
