Require Import String.
Require Import List.
Require Import Coq.Strings.String.
Require Import Ascii.

Add LoadPath "/Users/Saretta/Desktop/CMTI/Tesi/MonadiTesi".
Require Import StoreMonadInterfaceTesi.


Module MemoryState : StateMonadInterface.

Include Type StateMonadInterface.



Lemma swap_program : forall (l1 l2 : loc), l1 <> l2 -> 
{c : M unit | ((c >>= (fun _ => lookUp l2)) = (lookUp l1) >>= fun x => c >>= (fun _ => ret x)) /\
 ((c >>= (fun _ => lookUp l1)) = (lookUp l2) >>= fun x => c >>= (fun _ => ret x)) /\ 
  forall (l : loc), (l <> l1 /\ l <> l2) ->((c >>= fun _ => lookUp(l))) = ((lookUp(l) >>= fun x => c >>= fun _ => ret x ))
}.
Proof.
intros.

exists ((lookUp l1)>>= (fun x => lookUp l2 >>= (fun y => (update l1 y) >>= (fun _ => update l2 x)))).
split.

replace (lookUp l1 >>=
(fun x : val =>
 lookUp l1 >>=
 (fun x0 : val =>
  lookUp l2 >>=
  (fun y : val => update l1 y >>= (fun _ : unit => update l2 x0))) >>=
 (fun _ : unit => ret x))) 
with (lookUp l1 >>=
(fun x : val =>
 lookUp l1 >>=
 (fun x0 : val =>
  lookUp l2 >>=
  (fun y : val => update l1 y >>= (fun _ : unit => update l2 x0)
  >>= (fun _ : unit => ret x))))).

rewrite lookUp_idempotence.
rewrite <-associativity.

f_equal.
apply functional_extensionality.
intros.
rewrite<- associativity.
f_equal.

apply functional_extensionality; intros.
rewrite<- associativity.
rewrite <-associativity.
rewrite <- lookUp_after_update.
rewrite right_neutral.
reflexivity.

f_equal.
apply functional_extensionality; intros.
rewrite<- associativity.
f_equal.
apply functional_extensionality; intros.
rewrite <- associativity.
reflexivity.

split.


rewrite <- associativity.

replace (lookUp l2 >>=
(fun x : val =>
 lookUp l1 >>=
 (fun x0 : val =>
  lookUp l2 >>=
  (fun y : val => update l1 y >>= (fun _ : unit => update l2 x0))) >>=
 (fun _ : unit => ret x)))
with (lookUp l2 >>=
(fun x : val =>
 (lookUp l1 >>=
 (fun x0 : val =>
  (lookUp l2 >>=
  (fun y : val => update l1 y >>= (fun _ : unit => update l2 x0))) >>=
 (fun _ : unit => ret x))))).


rewrite lookUp_commutativity.
f_equal.


apply functional_extensionality.
intros.

 replace (fun v : val =>
 lookUp l2 >>= (fun y : val => update l1 y >>= (fun _ : unit => update l2 x)) >>=
 (fun _ : unit => ret v))
with (fun v : val =>
 lookUp l2 >>= ((fun y : val => update l1 y >>= (fun _ : unit => update l2 x) >>=
 (fun _ : unit => ret v)))).
rewrite lookUp_idempotence.

rewrite <-associativity.
replace ((fun x0 : val =>
 update l1 x0 >>= (fun _ : unit => update l2 x) >>=
 (fun _ : unit => lookUp l1)) )
with ((fun x0 : val =>
 update l1 x0 >>= (fun _ : unit => update l2 x) >>= (fun _ : unit => ret x0))).
reflexivity.


apply functional_extensionality. intros.
rewrite <-associativity.
rewrite update_commutativity.
rewrite <-lookUp_after_update.
rewrite right_neutral.
rewrite update_commutativity.
rewrite associativity.
reflexivity.
auto.
auto.


apply functional_extensionality.
intros.
rewrite associativity.
reflexivity.

auto.
f_equal.
apply functional_extensionality.
intros.
rewrite associativity.
reflexivity.
intros.

replace (lookUp l >>=
(fun x : val =>
 lookUp l1 >>=
 (fun x0 : val =>
  lookUp l2 >>=
  (fun y : val => update l1 y >>= (fun _ : unit => update l2 x0))) >>=
 (fun _ : unit => ret x)))
with (lookUp l >>=
(fun x : val =>
 (lookUp l1 >>=
 (fun x0 : val =>
 ( lookUp l2 >>=
  (fun y : val => update l1 y >>= (fun _ : unit => update l2 x0)) >>=
 (fun _ : unit => ret x)))))).
rewrite lookUp_commutativity.
rewrite<- associativity.
f_equal.

apply functional_extensionality.
intros.

replace (lookUp l >>=
(fun v : val =>
 lookUp l2 >>= (fun y : val => update l1 y >>= (fun _ : unit => update l2 x)) >>=
 (fun _ : unit => ret v)))
with (lookUp l >>=
(fun v : val =>
 (lookUp l2 >>= (fun y : val => update l1 y >>= (fun _ : unit => (update l2 x>>=
 (fun _ : unit => ret v))))))).
rewrite lookUp_commutativity.

rewrite <- associativity.
f_equal.

apply functional_extensionality.
intros.
rewrite<- update_lookUp_commutativity.
rewrite <-associativity.

f_equal.

apply functional_extensionality. intros.
rewrite <- update_lookUp_commutativity.
f_equal.

rewrite right_neutral.
reflexivity.

auto.
decompose [and] H0;auto.
auto.
decompose [and] H0; auto.
decompose [and] H0; auto.

rewrite associativity.
f_equal.
apply functional_extensionality.
intros.
rewrite<- associativity.
rewrite associativity.
reflexivity.

decompose [and] H0; auto.


f_equal.
apply functional_extensionality.
intros.
rewrite associativity.
reflexivity.
Defined.

End MemoryState.





