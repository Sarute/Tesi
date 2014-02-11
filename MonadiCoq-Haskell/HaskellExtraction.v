Require Import String List Coq.Strings.String Coq.Lists.List.
Add LoadPath "/Users/Saretta/Desktop/CMTI/Tesi/MonadiCoq-Haskell".
Require Import StoreMonadFile.

Extraction Language Haskell.

Require Import Ascii String.
Extract Inductive list => "([])" [ "[]" "(:)" ].
Extract Inlined Constant tl => "(tail)".
Extract Inlined Constant app => "(++)".
Extract Inductive option => "Maybe" [ "Just" "Nothing" ].
Extract Inductive string => "String" [ "[]" "(:)" ].
Extract Inductive prod => "(,)" [ "(,)" ].
Extract Inductive bool => "Bool" [ "True" "False" ].
Extract Inductive sumbool => "Bool" [ "True" "False" ].
Extract Inductive unit => "()" [ "()" ].
Extract Inlined Constant string_dec => "(==)".
Extract Inlined Constant ascii_dec => "(==)".
Extract Inductive ascii => "Char" [ "you_forgot_to_patch_coq" ] "you_forgot_to_patch_coq".

Extract Inductive sumbool => "Bool" [ "True" "False" ].
Extract Inductive nat => "Int" ["0" "succ"]
  "(\fO fS n -> if n==0 then fO () else fS (n-1))".
Extract Inductive unit => "()" [ "()" ].

Extract Inlined Constant StoreFile.Store.val => "Int".
Check StoreFile.Store.st.
Check MemoryState.State'.


Check MemoryState.State'.

Extract Inlined Constant StoreFile.Store.st => "Memory".
Check MemoryState.ret.
Check MemoryState.M.
Extract Constant MemoryState.State' "a"=> "State Memory a".
Extract Constant MemoryState.ret => "return".
Extract Constant MemoryState.bind => "(>>=)".
Extract Inlined Constant MemoryState.putM => "put".
Extract Inlined Constant MemoryState.get => "get".

Extraction "EstrazioneHaskell" lookUp update swap_program.

