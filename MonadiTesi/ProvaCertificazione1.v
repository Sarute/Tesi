Require Import String List Coq.Strings.String Coq.Lists.List.
Add LoadPath "/Users/Saretta/Desktop/CMTI/Tesi/MonadiTesi".

Require Import StoreMonadInterfaceTesi.


Module Certificazione : StateMonadInterface.

Include Type StateMonadInterface.

Theorem Ceritificazione_retCompleta : forall (x : M val),
x >>= (fun y => ret y) = x.
Proof.
intros.
apply right_neutral.
Defined.

Definition Certificazione_ret (x : M val) := x >>= (fun y => ret y).
Definition Certificazione_ret2 (x : M val) := x.



End Certificazione.