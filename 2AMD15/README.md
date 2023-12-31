# 📦 2AMD15 Big Data Management

_Group #5_

## 📦 Installation

1. Download [the dataset](https://ghtorrent.org/downloads.html) and place the `users.csv` file in a subdirectory named `data` (create it if it does not exist).

2. Install dependencies with pip:

```bash
pip install -r requirements.txt
```

Tested on Python 3.6.8.

## ⚙️ Usage

```
usage: FuncD.py [-h] [-s SOFT_THRESHOLD] [-d DELTA_THRESHOLD]
                [-t SAMPLE_THRESHOLD] [-z SAMPLE_SIZE] [--approx] [--out OUT]
                [data_path]

Discover functional dependencies in the GHTorrent dataset.

positional arguments:
  data_path             Path to CSV data file. Defaults to
                        data/subset_users.csv.

optional arguments:
  -h, --help            show this help message and exit
  -s SOFT_THRESHOLD, --soft_threshold SOFT_THRESHOLD
                        Probability must be least this large to be a soft FD.
  -d DELTA_THRESHOLD, --delta_threshold DELTA_THRESHOLD
                        Difference must be at most this large to be a delta
                        FD.
  -t SAMPLE_THRESHOLD, --sample_threshold SAMPLE_THRESHOLD
                        Decide which FDs will be dropped after sampling.
  -z SAMPLE_SIZE, --sample_size SAMPLE_SIZE
                        Percentage of the dataset which is going to be
                        included in the sample.
  --approx              Whether to use an approximate algorithm for string
                        comparisons. Uses an exact algortihm by default.
  --out OUT, -o OUT     Path to results output file. Defaults to results.csv.
```
