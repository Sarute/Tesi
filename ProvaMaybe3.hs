module ProvaMaybe2 where

import Prelude
import Data.Maybe

type M a = Maybe a

ret :: a1 -> M a1
ret = Just

bind :: (M a1) -> (a1 -> M a2) -> M a2
bind l f =
  case l of {
   Nothing -> Nothing;
   Just a -> f a}


nothing :: M a1
nothing = Nothing

type M0 a = M a

ret0 :: a1 -> M0 a1
ret0 x =
  ret x

bind0 :: (M0 a1) -> (a1 -> M0 a2) -> M0 a2
bind0 x x0 =
  bind x x0

nothing0 :: M0 a1
nothing0 =
  nothing

strictMaybe1 :: (a1 -> M0 a2) -> M0 a2
strictMaybe1 z =
  bind0 nothing0 z

strictMaybe2 :: (a1 -> M0 a2) -> M0 a2
strictMaybe2 z =
  Nothing

