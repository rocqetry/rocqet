#!/usr/bin/env bash

# Usage: ./extract-module.sh input_file.ml module_name [output_file.ml]

if [ $# -lt 2 ]; then
    echo "Usage: $0 <input_file> <module_name> [output_file]"
    echo "Example: $0 source.ml Cshmgen extracted_module.ml"
    exit 1
fi

INPUT_FILE=$1
MODULE_NAME=$2
OUTPUT_FILE=$3

# Check if input file exists
if [ ! -f "$INPUT_FILE" ]; then
    echo "Error: Input file '$INPUT_FILE' not found."
    exit 1
fi

# Extract the module using awk
# The pattern starts with "module <MODULE_NAME> =" and continues until we find "end" at the appropriate nesting level
awk -v module="$MODULE_NAME" '
BEGIN { 
    found = 0; 
    level = 0; 
    in_module = 0;
}

$0 ~ "^[[:space:]]*module[[:space:]]+" module "[[:space:]]*=" { 
    found = 1;
    in_module = 1;
    level = 0;
    print;
    next;
}

found == 1 {
    # Count struct to increase nesting level
    if ($0 ~ /struct/) level++; 
    
    # Count end to decrease nesting level
    if ($0 ~ /end/) level--; 
    
    print;
    
    # If we reached the end of the module, stop
    if (level == 0 && in_module && $0 ~ /end/) { 
        exit; 
    }
}
' "$INPUT_FILE" > "${OUTPUT_FILE:-/dev/stdout}"

# If output file was specified, confirm extraction
if [ -n "$OUTPUT_FILE" ]; then
    echo "Module '$MODULE_NAME' extracted to $OUTPUT_FILE"
else
    echo "Module '$MODULE_NAME' extracted to stdout"
fi
