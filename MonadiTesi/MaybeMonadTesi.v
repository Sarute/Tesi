Add LoadPath "/Users/Saretta/Desktop/CMTI/Tesi/MonadiTesi".

Module ProvaMaybe.

Require Export MaybeMonad.
Require Export MonadInterfaceTesi.

Include Type MaybeMonadInterface.
Set Implicit Arguments.

Definition StrictMaybe1 {A B}  (z: A -> M B) := Nothing A>>= z .
Definition StrictMaybe2 {A B} (z : A -> M B):= Nothing B.


End ProvaMaybe.

