#!/usr/bin/env bash
set -e
echo Running all scripts in this directory...
mkdir -p ./logs
for scriptfile in *.hs *.lhs; do
    echo $scriptfile
    timeout --preserve-status 1m\
        cabal run -v0 -O0 $scriptfile >./logs/${scriptfile}.stdout
done
