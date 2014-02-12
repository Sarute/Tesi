Add LoadPath "/Users/Saretta/Desktop/CMTI/Tesi/MonadiTesi".
Require Import MonadInterfaceTesi.



Module MaybeMonadInterface <: MONAD_INTERFACE.
 Set Implicit Arguments.


Include MONAD_INTERFACE.

Parameter Nothing : forall (A: Type), M A.

Axiom Strictness : forall (A B : Type), forall (f : A -> M B),
(Nothing A) >>= f = (Nothing B).




End MaybeMonadInterface.


