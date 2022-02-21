#!/usr/bin/env bash

set -e

# with Data.List.unzip
cabal run unzip-list --enable-profiling -O2 -- +RTS -hy\
      && hp2ps -c unzip-list

# with "Functor unzip"
cabal run unzip-fmap --enable-profiling -O2 -- +RTS -hy\
      && hp2ps -c unzip-fmap
