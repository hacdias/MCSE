#!/bin/bash

START_YEAR=1958
END_YEAR=2019
DIST=../../data/raw/terraclimate

rm -rf $DIST
mkdir -p $DIST
cd $DIST

for i in `seq $START_YEAR $END_YEAR`; do
	wget -nc -c -nd https://climate.northwestknowledge.net/TERRACLIMATE-DATA/TerraClimate_tmax_$i.nc 
	# wget -nc -c -nd https://climate.northwestknowledge.net/TERRACLIMATE-DATA/TerraClimate_tmin_$i.nc 
done
