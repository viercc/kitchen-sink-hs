#!/usr/bin/env bash

set -e

GHC='ghc-8.6'
INSTALL="cabal install -w $GHC"

$GHC --version

mkdir -p ./bin/int-0
$INSTALL -O0 --installdir=./bin/int-0

mkdir -p ./bin/int-1
$INSTALL -O1 --installdir=./bin/int-1

mkdir -p ./bin/int-2
$INSTALL -O2 --installdir=./bin/int-2

mkdir -p ./bin/int-1-prof
$INSTALL -O1 --enable-profiling --installdir=./bin/int-1-prof

mkdir -p ./bin/integer-0
$INSTALL -O0 -fuse-integer --installdir=./bin/integer-0

mkdir -p ./bin/integer-1
$INSTALL -O1 -fuse-integer --installdir=./bin/integer-1

mkdir -p ./bin/integer-2
$INSTALL -O2 -fuse-integer --installdir=./bin/integer-2
