module EstrazioneHaskellTesi where

import Prelude
import Control.Monad.Trans.State

type Memory = ([]) ((,) String Int)
emptyMemory = [] 

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
type M a = State st a

bind :: (M a1) -> (a1 -> M a2) -> M a2
bind = (>>=)
beq_str :: String -> String -> Bool
beq_str sa sb =
  case sa of {
   [] ->
    case sb of {
     [] -> True;
     (:) b sb' -> False};
   (:) a sa' ->
    case sb of {
     [] -> False;
     (:) b sb' ->
      case (==) a b of {
       True -> beq_str sa' sb';
       False -> False}}}

lookUpList' :: String -> M Int
lookUpList' x m =
  case m of {
   [] -> Nothing;
   (:) p tl ->
    case p of {
     (,) y v ->
      case beq_str x y of {
       True -> Just v;
       False -> lookUpList' x tl}}}

lookUp :: String -> M Int
lookUp x =
  bind get (\m ->
    case lookUpList' x m of {
     Just a -> ret a;
     Nothing -> ret 0})

update' :: String -> Int -> M ()
update' x a mem =
  case mem of {
   [] -> (:) ((,) x a) [];
   (:) p tl ->
    case p of {
     (,) y v ->
      case beq_str y x of {
       True -> (:) ((,) x a) tl;
       False -> (:) ((,) y v) (update' x a tl)}}}

update :: String -> Int -> M ()
update x a =
  bind get (\s -> put (update' x a s))

swap_program :: String -> String -> (M ())
swap_program l1 l2 =
  bind (lookUp l1) (\x ->
    bind (lookUp l2) (\y -> bind (update l1 y) (\x0 -> update l2 x)))


run :: Memory -> Memory
run initMem =  let (x, a) = runState( do update "myVar1" 1; update "myVar2" 7;update "myVar3" 4; swap_program "myVar1" "myVar2") initMem in a

main =  print $ run emptyMemory
