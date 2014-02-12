module ProvaMaybe where

import Prelude
import Data.Maybe

type M a = Maybe a

ret :: a1 -> M a1
ret = Just

bind :: (M a1) -> (a1 -> M a2) -> M a2
bind = (>>=)

nothing :: M a1
nothing = Nothing

