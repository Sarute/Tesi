module ProvaCertificazione where

import qualified Prelude

certificazione_ret :: (M Val) -> M Val
certificazione_ret x =
  bind x (\y -> ret y)

certificazione_ret2 :: (M Val) -> M Val
certificazione_ret2 x =
  x

