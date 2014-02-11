module ProvaCertificazione1 where

import Prelude
import Control.Monad.Trans.State

type Loc = String

type Val = Int

type St = ([]) ((,) String Int)

type M a = State St a


ret :: a1 -> M a1
ret = return


bind :: (M a1) -> (a1 -> M a2) -> M a2
bind = (>>=)


certificazione_ret :: (M Val) -> M Val
certificazione_ret x =
  bind x (\y -> ret y)

certificazione_ret2 :: (M Val) -> M Val
certificazione_ret2 x =
  x

