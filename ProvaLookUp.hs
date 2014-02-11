module EstrazioneHaskellTesi where

import Prelude
import Control.Monad.Trans.State

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
type M a = State St a

ret :: a1 -> M a1
ret = return

bind :: (M a1) -> (a1 -> M a2) -> M a2
bind = (>>=)

type Loc = String

type Val = Int

type St = ([]) ((,) String Int)
emptyStore = []



lookUp :: Loc -> M Val
lookUp x =
  bind get (\m ->
    (lookUpList' x m ->
    case m of {
     [] -> ret 0;
     (:) p tl ->
      case p of {
       (,) y v ->
        case x == y of {
         True -> ret v;
         False -> lookUpList' x tl}}}))


update :: Loc -> Val -> M ()
update =
  Prelude.error "AXIOM TO BE REALIZED"

swap_program :: Loc -> Loc -> (M ())
swap_program l1 l2 =
  bind (lookUp l1) (\x ->
    bind (lookUp l2) (\y -> bind (update l1 y) (\x0 -> update l2 x)))

run :: St -> St
run initMem =  let (x, a) = runState( do lookUp "var";) initMem in a

main =  print $ run emptyStore


