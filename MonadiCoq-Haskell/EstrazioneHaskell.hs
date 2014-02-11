module EstrazioneHaskell where

import qualified Prelude

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
type Memory = ([]) ((,) String Int)

type State' a = State Memory a

type M a = State' a

ret :: a1 -> M a1
ret = return

bind :: (M a1) -> (a1 -> M a2) -> M a2
bind = (>>=)

getM :: (Memory -> a1) -> M a1
getM f =
  bind get (\m -> ret (f m))

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

lookUpList' :: String -> Memory -> Maybe Int
lookUpList' x m =
  case m of {
   [] -> Nothing;
   (:) p tl ->
    case p of {
     (,) y v ->
      case beq_str x y of {
       True -> Just v;
       False -> lookUpList' x tl}}}

lookUp :: String -> State' Int
lookUp x =
  bind get (\m ->
    case lookUpList' x m of {
     Just a -> ret a;
     Nothing -> ret 0})

update' :: String -> Int -> Memory -> Memory
update' x a mem =
  case mem of {
   [] -> (:) ((,) x a) [];
   (:) p tl ->
    case p of {
     (,) y v ->
      case beq_str y x of {
       True -> (:) ((,) x a) tl;
       False -> (:) ((,) y v) (update' x a tl)}}}

update :: String -> Int -> State' ()
update x a =
  bind get (\s -> put (update' x a s))

swap_program :: String -> String -> (State' ())
swap_program l1 l2 =
  bind (lookUp l1) (\x ->
    bind (lookUp l2) (\y -> bind (update l1 y) (\x0 -> update l2 x)))

