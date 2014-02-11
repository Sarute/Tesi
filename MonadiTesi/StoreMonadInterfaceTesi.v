Add LoadPath "/Users/Saretta/Desktop/CMTI/Tesi/MonadiTesi".
Require Import MonadInterfaceTesi.

Module Type StateMonadInterface <: MONAD_INTERFACE.
 Set Implicit Arguments.

Include MONAD_INTERFACE.


Parameter loc : Set.
Parameter val: Set.
Parameter st :Set.
Parameter lookUp: forall (A: loc), M val. 
Parameter update: forall (A: loc) (a :val), M unit.



Axiom functional_extensionality_dep : forall {A} {B : A -> Type},
  forall (f g : forall x : A, B x),
  (forall x, f x = g x) -> f = g.

Lemma functional_extensionality {A B} (f g : A -> B) :
  (forall x, f x = g x) -> f = g.
Proof.
 intros.
 apply functional_extensionality_dep.
 apply H.
Qed.

Tactic Notation "extensionality" ident(x) :=
  match goal with
    [ |- ?X = ?Y ] =>
    (apply (@functional_extensionality _ _ X Y) ||
     apply (@functional_extensionality_dep _ _ X Y)) ; intro x
  end.

Axiom lookUp_idempotence: 
forall (l : loc ) (f : val-> val-> M val), 
(lookUp l) >>= (fun x =>(lookUp l)>>= (fun y => (f x y))) = lookUp l >>= (fun x => (f x x)).

Axiom update_idempotence:
forall (v v' : val) (l : loc) (x : unit -> M val),
(update l v) >>= (fun _ => (update l v') >>= x) = (update l v') >>= x.

Axiom lookUp_after_update :
forall (v : val) (l : loc) (f : val -> M val),
(update l v) >>= (fun _ => (lookUp l >>= f)) = (update l v) >>= (fun _ => f v).

Axiom lookUp_commutativity :
forall (l1 l2: loc) (f: val -> val -> M val), 
l1 <> l2 ->
(lookUp l1 >>= (fun v => lookUp l2 >>= (fun v' => f v v'))) = ((lookUp l2) >>= (fun v' => (lookUp l1 >>= (fun v => f v v')))). 

Axiom update_commutativity :
forall (v v' : val) (l1 l2 : loc) (x : unit -> M val),
l1 <> l2 ->
(update l1 v) >>= (fun _ => (update l2 v') >>= x) = (update l2 v') >>= (fun _ => (update l1 v) >>= x).


Axiom update_lookUp_commutativity:
forall (l1 l2: loc) (v v' : val) (f :val-> M val),
l1<>l2 ->
(update l1 v) >>= (fun _ => (lookUp l2) >>= (fun v' => f v')) = (lookUp l2) >>= (fun v' => (update l1 v) >>= (fun _ => f v')).

End StateMonadInterface.
