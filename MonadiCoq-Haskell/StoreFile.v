
Require Import String.
Require Import List.


Require Import Coq.Strings.String.
Require Import Ascii.

Add LoadPath "/Users/Saretta/Desktop/CMTI/Tesi/MonadiCoq-Haskell".
Require Import StateMonadFile.


Module Store <: StateType.


Definition val := nat.
Definition memory := list (string * val).

Definition st := memory.



End Store.





