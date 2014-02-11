Require Import String List Coq.Strings.String Coq.Lists.List.
Add LoadPath "/Users/Saretta/Desktop/CMTI/Tesi/MonadiTesi".
Require Import ProvaCertificazione1.


Extraction Language Haskell.


Extract Constant Certificazione.loc => "String".
Extract Constant Certificazione.val => "Int".
Extract Constant Certificazione.st => "([]) ((,) String Int)".


Extract Constant Certificazione.M "a"=> "State St a".
Extract Constant Certificazione.ret => "return".
Extract Constant Certificazione.bind => "(>>=)".
Extract Inductive unit => "()" [ "()" ].

Extraction "ExtractionCert" Certificazione.