module Test where

import MasterMind
import V4

ans  :: V4 Int
ans = V4 1 1 2 3

qs@[q1, q2, q3, q4] = [V4 2 2 3 4, V4 3 3 2 2, V4 1 2 3 4, V4 1 4 1 5]

rs@[r1, r2, r3, r4] = map (response ans) qs

hints@[h1, h2, h3, h4] = zipWith responseToHint qs rs
