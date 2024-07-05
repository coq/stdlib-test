(* Check both removal of coercions with target Funclass and mixing
   string and numeral scopes *)

Require Import String.
Open Scope string_scope.
Inductive PAIR := P (s:string) (n:nat).
Coercion P : string >-> Funclass.
Check ("1" 0).
