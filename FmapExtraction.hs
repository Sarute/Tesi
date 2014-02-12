module FmapExtraction where

import Prelude

type M a = ([]) (a)

ret :: a1 -> M a1
ret = return

bind :: (M a1) -> (a1 -> M a2) -> M a2
bind = (>>=)

miofmap :: (a1 -> a2) -> (M a1) -> M a2
miofmap = map

axiom1Left :: (M a1) -> (a1 -> a2) -> M a2
axiom1Left xs f =
  miofmap f xs

axiom1Right :: (M a1) -> (a1 -> a2) -> M a2
axiom1Right xs f =
  bind xs (\a -> ret (f a))

