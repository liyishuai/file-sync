From FileSync Require Export
     File.
From ExtLib Require Export
     List
     RelDec.
From Ceres Require Export
     Ceres.

Variant F :=
  Fls    (p: path)
| Fread  (p: path)
| Fwrite (p: path) (c: content)
| Fmkdir (p: path)
| Frm    (p: path).

Variant A :=
  Als   (l: list name)
| Aread (c: content)
| Ayes
| Ano.

Variant R := R1 | R2.

Variant Q :=
  QFile (r: R) (f: F)
| QSync.

Definition S : Type := node * node * node.

Instance RelDec_A : RelDec (@eq A) :=
  { rel_dec a b :=
      match a, b with
      | Als   x, Als   y
      | Aread x, Aread y => x ?[ eq ] y
      | Ayes   , Ayes
      | Ano    , Ano     => true
      | _      , _       => false
      end
  }.

Open Scope sexp_scope.

Instance Serialize__A: Serialize A :=
  fun a => match a with
         | Als   l => to_sexp l
         | Aread c => to_sexp c
         | Ayes    => Atom "yes"
         | Ano     => Atom "no"
         end.

Instance Serialize__F: Serialize F :=
  fun f => match f with
         | Fls    p   => [Atom "ls"   ; to_sexp p]
         | Fread  p   => [Atom "read" ; to_sexp p]
         | Fwrite p c => [Atom "write"; to_sexp p; to_sexp c]
         | Fmkdir p   => [Atom "mkdir"; to_sexp p]
         | Frm    p   => [Atom "rm"   ; to_sexp p]
         end.

Instance Serialize__R: Serialize R :=
  fun r => Atom (if r is R1 then "R1" else "R2").

Instance Serialize__Q: Serialize Q :=
  fun q => if q is QFile r f then [to_sexp r; to_sexp f]
         else Atom "Sync".

Close Scope sexp_scope.
