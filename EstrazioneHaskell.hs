module EstrazioneHaskellTesi where

import Prelude
import Control.Monad.Trans.State

data Unit =
   Tt

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

lookUpList' :: Loc -> St-> Maybe Int
lookUpList' x m =
  case m of {
   [] -> Nothing;
   (:) p tl ->
    case p of {
     (,) y v ->
      case x == y of {
       True -> Just v;
       False -> lookUpList' x tl}}}

lookUp :: Loc-> M Int
lookUp x =
  bind get (\m ->
    case lookUpList' x m of {
     Just a -> ret a;
     Nothing -> ret 0})

update' :: String -> Int -> St-> St
update' x a mem =
  case mem of {
   [] -> (:) ((,) x a) [];
   (:) p tl ->
    case p of {
     (,) y v ->
      case y == x of {
       True -> (:) ((,) x a) tl;
       False -> (:) ((,) y v) (update' x a tl)}}}

update :: String -> Int -> M ()
update x a =
  bind get (\s -> put (update' x a s))

swap_program :: Loc -> Loc -> M ()
swap_program l1 l2 =
  bind (lookUp l1) (\x ->
    bind (lookUp l2) (\y -> bind (update l1 y) (\x0 -> update l2 x)))


run :: St -> St
run initMem =  let (x, a) = runState( do update "myVar1" 1; update "myVar2" 7;update "myVar3" 4; swap_program "myVar1" "myVar2") initMem in a

main =  print $ run emptyStore

