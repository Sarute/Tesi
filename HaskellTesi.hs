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
lookUp loc = do 		
		mem <- get		
		case varLookUpList' loc mem of
			Just s -> return s
			Nothing -> return 0
			where
				varLookUpList' :: String -> St -> Maybe Val
				varLookUpList' name [] = Nothing
				varLookUpList' name ((n,v):xs) = if name == n then Just v else varLookUpList' name xs

update :: Loc -> Val -> M ()
update str val = do
			mem <- get
			put( varUpdate' str val mem)
	where
		varUpdate' :: Loc -> Int -> St -> St
		varUpdate' name nval [] = [(name,nval)]
		varUpdate' name nval ((n,v):xs) = if name == n 
										  then (n,nval):xs 
										  else (n,v):(varUpdate' name nval xs)

swap_program :: Loc -> Loc -> (M ())
swap_program l1 l2 =
  bind (lookUp l1) (\x ->
    bind (lookUp l2) (\y -> bind (update l1 y) (\x0 -> update l2 x)))


run :: St -> St
run initMem =  let (x, a) = runState( do update "myVar1" 1; update "myVar2" 7;update "myVar3" 4; swap_program "myVar1" "myVar2") initMem in a

main =  print $ run emptyStore

