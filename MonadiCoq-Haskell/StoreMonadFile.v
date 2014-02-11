
Require Import String.
Require Import List.
Require Import Coq.Strings.String.
Require Import Ascii.



Add LoadPath "/Users/Saretta/Desktop/CMTI/Tesi/MonadiCoq-Haskell".
Require Import StateMonadFile.
Require Import StoreFile.

Module MemoryState := StateMonad Store.


Import MemoryState.
Import Store.

Fixpoint beq_str (sa sb : String.string) {struct sb}: bool := 
   match sa, sb with
 | EmptyString, EmptyString  => true
 | EmptyString, String b sb' => false
 | String a sa', EmptyString => false
 | String a sa', String b sb'=> match (ascii_dec a b) with 
                                | left _ => beq_str sa' sb'
                                | right _ => false
                                end
 end.

Theorem beq_str_refl : forall i,
  true = beq_str i i.
Proof.
  induction 0; simpl; try (rewrite <- IHi; case (ascii_dec a a));
  try reflexivity; intro C; elimtype False; apply C; reflexivity.
Qed.

Axiom beq_str_diff : forall i j, i <> j ->  beq_str i j = false.

Fixpoint lookUpList' (x : string) (m : st) : option val  :=
	match m with
	| nil => None  
	| (y, v) :: tl => if beq_str x y 
				then Some v
				else lookUpList' x tl
				end.




Definition lookUp (x :string) : (State' val )  :=
	bind get (fun m =>  
        match lookUpList' x m with
	| None => ret 0
	| Some a => ret a
	end) .



Fixpoint update' (x : string) (a : val) (mem : st) : st :=
match mem with
| nil => (x, a):: nil
| (y,v) :: tl => if beq_str  y x
                    then (x, a):: tl
                    else (y,v) :: (update' x a tl)
                    end.


Definition update (x: string) (a: val) : State' unit:=
(get >>= fun s => (putM (update' x a s))).





Axiom lookUp_update:forall (l : string ) (x : State' val), 
(lookUp l) >>= (fun v =>(update l v ) >>= (fun _ => x)) = x.

Axiom lookUp_idempotence: 
forall (l : string ) (f : val -> val -> State' val), 
(lookUp l) >>= (fun x =>(lookUp l)>>= (fun y => (f x y))) = lookUp l >>= (fun x => (f x x)).

Axiom update_idempotence:
forall (v v' : val) (l : string) (x : unit -> State' val),
(update l v) >>= (fun _ => (update l v') >>= x) = (update l v') >>= x.

Axiom lookUp_after_update :
forall (v : val) (l : string) (f : val -> State' val),
(update l v) >>= (fun _ => (lookUp l >>= f)) = (update l v) >>= (fun _ => f v).

Axiom lookUp_commutativity :
forall (l1 l2: string) (f: val -> val -> State' val), 
l1 <> l2 ->
(lookUp l1 >>= (fun v => lookUp l2 >>= (fun v' => f v v'))) = ((lookUp l2) >>= (fun v' => (lookUp l1 >>= (fun v => f v v')))). 

Axiom update_commutativity :
forall (v v' : val) (l1 l2 : string) (x : unit -> State' val),
l1 <> l2 ->
(update l1 v) >>= (fun _ => (update l2 v') >>= x) = (update l2 v') >>= (fun _ => (update l1 v) >>= x).


Axiom update_lookUp_commutativity:
forall (l1 l2: string) (v v' : val) (f : val -> State' val),
l1<>l2 ->
(update l1 v) >>= (fun _ => (lookUp l2) >>= (fun v' => f v')) = (lookUp l2) >>= (fun v' => (update l1 v) >>= (fun _ => f v')).





Lemma first_program : forall (l1 l2: string), 
{ x : State' val | forall (s: st), let (v', s) := x s in v' = 0}.
Proof.
intros.
exists (ret 0).
simpl.
reflexivity.
Defined.


Lemma frist_program1_5 : forall (l1 l2: string), 
{ x : State' val | x = lookUp l1 }.
intros.
exists (lookUp l1).
reflexivity.
Defined.


Lemma first_program3 : forall (l1 l2 : string),
{c : State' unit | bind c (fun _ => lookUp l2) = (lookUp l1 >>= (fun x => c >>= (fun _ => ret x)))}.
Proof.
intros.
exists ((lookUp l1)>>= (update l2)).


replace (lookUp l1 >>=(fun x : val => lookUp l1 >>= update l2 >>= (fun _ : unit => ret x))) with
            (lookUp l1 >>= (fun x : val => lookUp l1 >>= (fun v => (update l2 v) >>=   (fun _ : unit => ret x)))).
rewrite lookUp_idempotence.
rewrite <- associativity.

replace (fun x : val => update l2 x >>= (fun _ : unit => ret x))
  with  (fun x : val => update l2 x >>= (fun _ : unit => lookUp l2)).
reflexivity. 
apply functional_extensionality.
intros.
rewrite <- lookUp_after_update.
rewrite right_neutral.
reflexivity.

replace (fun x : val => lookUp l1 >>= update l2 >>= (fun _ : unit => ret x))
  with  (fun x : val => lookUp l1 >>= (fun y => update l2 y >>= (fun _ : unit => ret x))).
rewrite lookUp_idempotence.
reflexivity.
apply functional_extensionality.
intros.
rewrite associativity.
reflexivity.
Defined.



Lemma swap_program : forall (l1 l2 : string), l1 <> l2 -> 
{c : State' unit | ((c >>= (fun _ => lookUp l2)) = (lookUp l1) >>= fun x => c >>= (fun _ => ret x)) /\
 ((c >>= (fun _ => lookUp l1)) = (lookUp l2) >>= fun x => c >>= (fun _ => ret x)) /\ 
  forall (l : string), (l <> l1 /\ l <> l2) ->((c >>= fun _ => lookUp(l))) = ((lookUp(l) >>= fun x => c >>= fun _ => ret x ))
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

replace ((fun x : val =>
 lookUp l2 >>= (fun y : val => update l1 y >>= (fun _ : unit => update l2 x)) >>=
 (fun _ : unit => lookUp l2)))
with ((fun x : val =>
 lookUp l2 >>=
 (fun y : val =>
  update l1 y >>= (fun _ : unit => update l2 x)>>= (fun _ : unit => ret x)))).
reflexivity.
replace ((fun x : val =>
 lookUp l2 >>=(fun y : val =>
  update l1 y >>= (fun _ : unit => update l2 x) >>= (fun _ : unit => ret x))))
with  ((fun x : val =>
 lookUp l2 >>=(fun y : val =>
  update l1 y >>= (fun _: unit => ((update l2 x) >>= (fun _ : unit => ret x)))))).

apply functional_extensionality.
intros.
rewrite<- lookUp_after_update.
rewrite right_neutral.
rewrite <-associativity.
reflexivity.

reflexivity.
f_equal.


apply functional_extensionality.
intros.
rewrite <-associativity.
f_equal.

apply functional_extensionality.
intros.
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




































































 







