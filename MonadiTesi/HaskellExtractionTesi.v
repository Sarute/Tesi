Require Import String List Coq.Strings.String Coq.Lists.List.
Add LoadPath "/Users/Saretta/Desktop/CMTI/Tesi/MonadiTesi".
Require Import StoreMonadTesi.


Extraction Language Haskell.


Extract Constant MemoryState.loc => "String".
Extract Constant MemoryState.val => "Int".
Extract Constant MemoryState.st => "([]) ((,) String Int)".


Extract Constant MemoryState.M "a"=> "State St a".
Extract Constant MemoryState.ret => "return".
Extract Constant MemoryState.bind => "(>>=)".
Extract Inductive unit => "()" [ "()" ].


Extract Constant MemoryState.lookUp => 
"lookUp loc = do 		
		mem <- get		
		case varLookUpList' loc mem of
			Just s -> return s
			Nothing -> return 0
			where
				varLookUpList' :: String -> St -> Maybe Val
				varLookUpList' name [] = Nothing
				varLookUpList' name ((n,v):xs) = if name == n then Just v else varLookUpList' name xs".

Extract Constant MemoryState.update =>
"update str val = do
			mem <- get
			put( varUpdate' str val mem)
	where
		varUpdate' :: Loc -> Int -> St -> St
		varUpdate' name nval [] = [(name,nval)]
		varUpdate' name nval ((n,v):xs) = if name == n 
										  then (n,nval):xs 
										  else (n,v):(varUpdate' name nval xs)".





