Add LoadPath "/Users/Saretta/Desktop/CMTI/Tesi/MonadiTesi".
Require Import FmapInterface.

Extraction Language Haskell.

Extract Constant FmapMonadInterface.M "a"=>  "([]) (a)".
Extract Constant FmapMonadInterface.ret => "return".
Extract Constant FmapMonadInterface.bind => "(>>=)".
Extract Constant FmapMonadInterface.fmap => "map".


Extraction "FmapExtraction" FmapMonadInterface.


