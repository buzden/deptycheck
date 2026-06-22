#!/usr/bin/env bash

set -e

# Find .editorconfig section header that mentions *.sh
header=$(grep -F '*.sh' .editorconfig)

# Get comma-separated patterns
patterns=${header#\[\{}
patterns=${patterns%\}\]}

# Build `-name p1 -o -name p2 ...`
args=$(python3 -c "import sys; print(' -o '.join(f'-name {p}' for p in sys.argv[1].split(',')))" "$patterns")

# Run shellcheck on matching files
# shellcheck disable=SC2086  # word splitting intended to split string into separate find args
find . -type f \( $args \) -exec shellcheck --shell=sh -S warning {} +
