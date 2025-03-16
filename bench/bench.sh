#!/usr/bin/env bash
# set -x #echo on
# 
# time coqc STLC.v -R ../_build/default/theories Rocqet -I ../_build/default/src &> output1.txt
# 
# time coqc STLC_bool_sum_fix_prod_iso.v -R ../_build/default/theories Rocqet -I ../_build/default/src &> output1.txt

# Create a CSV file with headers
echo "filename,real_time_seconds" > benchmark_results.csv

# Process each .v file in the current directory
for file in *.v; do
  # Skip if no .v files exist
  [ -e "$file" ] || continue
  
  echo "Processing $file..."
  
  # Create a temporary file to capture the time output
  time_output=$(mktemp)
  
  # Run the command and capture the time output
  (time coqc "$file" -R ../_build/default/theories Rocqet -I ../_build/default/src &> "output_${file%.v}.txt") 2> "$time_output"
  
  # Extract the real time in seconds
  real_time=$(grep "real" "$time_output" | awk '{print $2}')
  
  # Convert time format (e.g., 0m1.234s) to seconds
  minutes=$(echo $real_time | cut -d'm' -f1)
  seconds=$(echo $real_time | cut -d'm' -f2 | cut -d's' -f1)
  total_seconds=$(echo "$minutes * 60 + $seconds" | bc)
  
  # Append to the CSV
  echo "$file,$total_seconds" >> benchmark_results.csv
  
  # Clean up temporary file
  rm "$time_output"
done
