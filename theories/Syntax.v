From JSON Require Import
     Encode
     Decode
     Operator.
From FileSync Require Export
     File.
From ExtLib Require Export
     List
     Sets
     ListSet
     RelDec.
From Ceres Require Export
     Ceres.
Import
  JNotations.

Variant F :=
  Fls    (p: path)
| Fread  (p: path)
| Fwrite (p: path) (c: content)
| Fmkdir (p: path)
| Frm    (p: path).

Variant A :=
  Als   (l: list name)
| Aread (c: content)
| Aret  (z: Z)
| Ayes
| Ano.

Variant R := R1 | R2.

Variant Q :=
  QFile (r: R) (f: F)
| QSync.

Definition S : Type := node * node * node.
Definition initS: S := (emptyDir, emptyDir, emptyDir).

Global Instance RelDec_Z: RelDec (@eq Z) :=
  { rel_dec := Z.eqb }.

#[export]
Instance RelDec_A : RelDec (@eq A) :=
  { rel_dec a b :=
      match a, b with
      | Als x, Als y => subset x y &&& subset y x
      | Aret x, Aret y
      | Aread x, Aread y => x ?[ eq ] y
      | Ayes   , Ayes
      | Ano    , Ano     => true
      | _      , _       => false
      end%Z
  }.

Open Scope sexp_scope.

#[export]
Instance Serialize__A: Serialize A :=
  fun a => match a with
         | Als   l => to_sexp l
         | Aread c => to_sexp c
         | Aret  z => Atom z
         | Ayes    => Atom "yes"
         | Ano     => Atom "no"
         end.

#[export]
Instance Serialize__F: Serialize F :=
  fun f => match f with
         | Fls    p   => [Atom "ls"   ; to_sexp p]
         | Fread  p   => [Atom "read" ; to_sexp p]
         | Fwrite p c => [Atom "write"; to_sexp p; to_sexp c]
         | Fmkdir p   => [Atom "mkdir"; to_sexp p]
         | Frm    p   => [Atom "rm"   ; to_sexp p]
         end.

#[export]
Instance Serialize__R: Serialize R :=
  fun r => Atom (if r is R1 then 1 else 2)%Z.

#[export]
Instance Serialize__Q: Serialize Q :=
  fun q => if q is QFile r f then [to_sexp r; to_sexp f]
         else Atom "Sync".

Close Scope sexp_scope.

#[export]
Instance JDecode__A: JDecode A :=
  fun j =>
    (b <- JDecode__bool j;; inr (if b : bool then Ayes else Ano))
      <|> Aret  <$> JDecode__Z      j
      <|> Aread <$> JDecode__string j
      <|> Als   <$> decode__list    j.

Close Scope list_scope.

#[export]
Instance JDecode__R: JDecode R :=
  fun j =>
    r <- JDecode__nat j;;
    match r with
    | 1 => inr R1
    | 2 => inr R2
    | _ => inl $ "Invalid replica: " ++ to_string r
    end.

#[export]
Instance JDecode__path: JDecode path :=
  @decode__list string _.

#[export]
Instance JDecode__Q: JDecode Q :=
  fun j =>
    (r <- dpath "target" j;;
     m <- dpath "method" j;;
     p <- dpath "path"   j;;
     f <- (match m with
           | "rm"    => inr $ Frm p
           | "ls"    => inr $ Fls p
           | "read"  => inr $ Fread p
           | "mkdir" => inr $ Fmkdir p
           | "write" => Fwrite p <$> dpath "content" j
           | _ => inl $ "Invalid method: " ++ m
           end);;
    inr (QFile r f))%string
    <|> (str <- JDecode__string j;;
         if str is "sync" then inr QSync
         else inl $ "Invalid query: " ++ str).

#[export]
Instance JEncode__F: JEncode F :=
  fun f =>
    match f with
    | Fls    p   => jobj "method" "ls"    + jobj "path" p
    | Frm    p   => jobj "method" "rm"    + jobj "path" p
    | Fread  p   => jobj "method" "read"  + jobj "path" p
    | Fmkdir p   => jobj "method" "mkdir" + jobj "path" p
    | Fwrite p c => jobj "method" "write" + jobj "path" p + jobj "content" c
    end.

#[export]
Instance JEncode__Q: JEncode Q :=
  fun q =>
    match q with
    | QSync => JSON__String "sync"
    | QFile r f =>
      jobj "target" (if r is R1 then 1 else 2) + JEncode__F f
    end.
