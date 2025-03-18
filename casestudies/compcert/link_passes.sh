#!/usr/bin/env bash

# Check if the correct number of arguments is provided
if [ $# -ne 2 ]; then
    echo "Usage: $0 <source_directory> <destination_directory>"
    exit 1
fi

SOURCE_DIR="$1"
DEST_DIR="$2"

# Check if source directory exists
if [ ! -d "$SOURCE_DIR" ]; then
    echo "Error: Source directory '$SOURCE_DIR' does not exist."
    exit 1
fi

# Check if destination directory exists
if [ ! -d "$DEST_DIR" ]; then
    echo "Error: Destination directory '$DEST_DIR' does not exist."
    exit 1
fi

# Copy all files from source to destination, overwriting if they exist
echo "Copying files from '$SOURCE_DIR' to '$DEST_DIR'..."
cp -f "$SOURCE_DIR"/* "$DEST_DIR" 2>/dev/null

# Check if the copy operation was successful
if [ $? -eq 0 ]; then
    echo "All passes linked successfully."
else
    echo "Warning: Some files may not have been linked. This could be due to:"
    echo "  - No files in the source directory"
    echo "  - Permission issues"
    echo "  - Special files that cannot be copied with cp"
fi
