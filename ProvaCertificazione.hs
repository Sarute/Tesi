module ProvaCertificazione where

import Prelude

type M val = State St a

ret :: a1 -> M a1
ret = return

bind :: (M a1) -> (a1 -> M a2) -> M a2
bind = (>>=)

type Val = Int

certificazione_ret :: (M Val) -> M Val
certificazione_ret x =
  bind x (\y -> ret y)

certificazione_ret2 :: (M Val) -> M Val
certificazione_ret2 x =
  x

