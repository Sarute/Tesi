Module Type MONAD.
Set Implicit Arguments.

Parameter M : forall (A: Type), Type.
Parameter ret : forall (A:Type), A -> (M A).
Parameter bind : forall (A B : Type), M A -> (A -> M B) -> M B.

Infix ">>=" := bind (at level 20, left associativity): monad_scope.
Open Scope monad_scope.

Axiom left_neutral : forall (A B :Type)(f:A -> M B)(a : A),
  (ret a) >>= f = f a.

Axiom right_neutral : forall (A : Type) (m : M A),
 m >>= ( fun a : A => ret a ) = m.

Axiom associativity : forall (A B C : Type) (m : M A) (k: A -> M B) (h: B -> M C),
 m >>= (fun x : A => k x >>= h) = (m >>= k) >>= h.

End MONAD.