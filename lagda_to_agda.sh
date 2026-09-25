#!/bin/bash

for lagda_file in "$@"; do
    agda_file="${lagda_file%.lagda}.agda"
    
    awk '
    /\\begin\{code\}/ { in_code = 1; next }
    /\\end\{code\}/ { in_code = 0; next }
    in_code { print }
    ' "$lagda_file" > "$agda_file"
    
    echo "Converted: $lagda_file -> $agda_file"
done
