Add LoadPath "/Users/Saretta/Desktop/CMTI/Tesi/MonadiCoq-Haskell".
Require Import MonadInterface.

Module Type StateType.
 Parameter st : Set.
End StateType.


Module StateMonad(St : StateType) <: MONAD.
 Set Implicit Arguments.
Import St.


Definition State' (a : Type) : Type := st -> (a * st).

Definition M := State'.

Definition ret (A : Type) : (A -> M A) := fun x st=> (x, st).
Definition bind (A B : Type) (c1 : M A) (c2 : A -> M B) : M B := 
fun st => let (x, st') := c1 st in c2 x st'.
 
Infix ">>=" := bind (at level 20, left associativity) : monad_scope.
Open Scope monad_scope.


Lemma equal_f : forall {A B : Type} {f g : A -> B},
 f = g -> forall x, f x = g x.
Proof.
intros.
rewrite H.
reflexivity.
Qed.

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




Lemma left_neutral : forall (A B : Type) (f : A -> M B) (a : A), 
   (ret a) >>= f = f a.
  Proof.
   intros.
   unfold ret.
   unfold bind.
   reflexivity.
  Defined.


  Lemma right_neutral : forall (A : Type) (m : M A), 
    m >>= (fun a : A => ret a) = m.
  Proof.
intros.
unfold bind.
unfold ret.
extensionality st'.
induction m.
reflexivity.
  Defined.

 
Lemma associativity : forall (A B C : Type) (m : M A) (k : A -> M B)(h : B -> M C),
   m >>= (fun x : A => k x >>= h) = (m >>= k) >>= h.
  Proof.
    intros.
    unfold bind, ret.
    extensionality st'.
    induction m.
    reflexivity.
 Defined.

Definition putM (m : st) : M unit :=
    fun previous_s =>
      ret tt m.

Definition get : M st :=
  fun m => ret m m.
 
Definition getM (A: Set) (f: st -> A):  M A :=
 bind get (fun m => ret (f m)).


End StateMonad.









