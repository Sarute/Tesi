Add LoadPath "/Users/Saretta/Desktop/CMTI/Tesi/MonadiTesi".
Require Import MaybeMonad.


Extraction Language Haskell.

Extract Constant  MaybeMonadInterface.M "a"=> "Maybe a".
Extract Constant MaybeMonadInterface.ret => "Just".
Extract Constant MaybeMonadInterface.bind =>"(>>=)".
Extract Constant MaybeMonadInterface.Nothing => "Nothing".


Extraction "ProvaMaybe" MaybeMonadInterface.