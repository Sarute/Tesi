Add LoadPath "/Users/Saretta/Desktop/CMTI/Tesi/MonadiTesi".
Require Import MonadInterfaceTesi.



Module  FmapMonadInterface <: MONAD_INTERFACE.
 Set Implicit Arguments.

Include MONAD_INTERFACE.

Parameter fmap : forall (A B: Type), (A -> B) -> M A -> M B.

Axiom fmapAxiom : forall {A B} (xs : M A)(f : A ->  B),
fmap f xs = xs >>= (fun a => ret (f a)).

Definition Axiom1Left {A B} (xs : M A)(f : A ->  B) := fmap f xs.
Definition Axiom1Right {A B} (xs : M A)(f : A -> B) := xs >>= (fun a => ret (f a)).


End FmapMonadInterface.

