#!/usr/bin/env bash

set -e

# N=$(ghc -e '42 ^ 10 :: Integer')
N=17080198121677824

for pp in $(find -L bin -executable -type f | sort); do
    printf '%-28s' $pp
    /bin/time --format='    (real=%E mem=%M)' $pp $N +RTS -T
done
