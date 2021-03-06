Add LoadPath "/Users/Saretta/Desktop/CMTI/Tesi/MonadiTesi".
Require Import MaybeMonad.
Require Import MaybeMonadTesi.

Extraction Language Haskell.

Extract Constant  MaybeMonadInterface.M "a"=> "Maybe a".
Extract Constant MaybeMonadInterface.ret => "Just".
Extract Constant MaybeMonadInterface.bind "l f"=>" bind l f =
  case l of {
	Just a -> f a;
	Nothing -> Nothing}".
Extract Constant MaybeMonadInterface.Nothing => "Nothing".


Extraction "ProvaMaybe2" ProvaMaybe.