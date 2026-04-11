#!/usr/bin/env bash
# Install all requirements from requirements files
cd requirements || exit 1
find ./ -type f -name "*.txt" -exec pip install -r "{}" \;