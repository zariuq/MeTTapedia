#!/bin/bash
# CPU-friendly build wrapper
# Always limits to 4 jobs maximum

export LAKE_JOBS=4

if [ -z "$1" ]; then
    echo "Usage: ./build.sh <target>"
    echo "Example: ./build.sh FourColor.Geometry.DualForest"
    exit 1
fi

echo "Building $1 with LAKE_JOBS=$LAKE_JOBS (CPU-friendly)..."
lake build "$@"
