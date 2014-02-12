module MaybeHaskell2 where

import Prelude
import Data.Maybe

type M a = Maybe a

ret :: a1 -> Maybe a1
ret a =
  Just a

bind :: (M a1) -> (a1 -> M a2) -> M a2
bind l f =
  case l of {
   Nothing -> Nothing;
   Just a -> f a}

