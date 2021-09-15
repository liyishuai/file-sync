From Coq Require Export
     Basics
     Bool
     List
     String.
From ExtLib Require Export
     Extras
     FMapAList
     Functor
     ListMonad
     Maps
     Monad
     OptionMonad
     String.
Export
  FunNotation
  FunctorNotation
  MonadNotation
  IfNotations
  ListNotations.
Open Scope monad_scope.
Open Scope lazy_bool_scope.
Open Scope program_scope.

Definition name    := string.
Definition content := string.

Inductive node :=
  File      : content         -> node
| Directory : alist name node -> node.

Definition path := list name.    

Definition basename : path -> name := flip (@last name) "".
Definition dirname  : path -> path := @removelast name.

Fixpoint cd (p: path) (n: node) : option node :=
  match p, n with
  | f::p, Directory d => lookup f d >>= cd p
  | [], _ => Some n
  | _ , _ => None
  end.

Definition ls (p: path) (n: node) : list name :=
  if cd p n is Some (Directory d)
  then map fst d
  else [].

Definition read (p: path) (n: node) : option content :=
  n <- cd p n;;
  if n is File c
  then Some c
  else None.

Fixpoint override (p: path) (m n: node) : node :=
  match p, n with
  | [], _ => m
  | f::p, Directory d =>
    let n0 := if lookup f d is Some d0 then d0 else Directory [] in
    Directory $ add f (override p m n0) d
  | f::p, File _ => Directory [(f, override p m $ Directory [])]
  end.

(* mkdir -p *)
Fixpoint mkdirp (p: path) (n: node) : option node :=
  match p, n with
  | [f], Directory d =>
    if lookup f d is Some _
    then None                   (* Already exists *)
    else Some $ Directory $ add f (Directory []) d
  | f::p, Directory d =>
    if lookup f d is Some n
    then n' <- mkdirp p n;;
         Some (Directory $ add f n' d)
    else Some $ Directory $ add f (Directory []) d
  | _, _ => None
  end.

Definition mkdir (p: path) (n: node) : option node :=
  if cd (dirname p) n is Some (Directory _)
  then mkdirp p n
  else None.                    (* Parent not found *)   

Definition write (p: path) (c: content) (n: node) : option node :=
  if cd (dirname p) n is Some ((Directory _) as d)
  then if cd [basename p] d is Some (Directory _)
       then None                (* Cannot write to directory *)
       else Some $ override p (File c) n
  else None.                    (* Parent not found *)

(* rm -f *)
Fixpoint rmf (p: path) (n: node) : node :=
  match p, n with
  | [f], Directory d => Directory $ remove f d
  | f::p, Directory d =>
    if lookup f d is Some d0
    then Directory $ add f (rmf p d0) d
    else n
  | _, _ => n
  end.

Definition rm (p: path) (n: node) : option node :=
  if cd p n is Some _
  then Some $ rmf p n
  else None.                    (* Target not found *)

Fixpoint leb_node (n m: node) : bool :=
  match n, m with
  | Directory d, Directory e =>
    forallb
      (fun '(p, n) =>
         if lookup p e is Some m
         then leb_node n m
         else false) d
  | File f, File g => f =? g
  | _, _ => false
  end.

Definition eqb_node (n m: node) : bool :=
  leb_node n m &&& leb_node m n.

Module FileNotations.

Infix "<=?" := leb_node (at level 70, no associativity) : file_scope.
Infix  "=?" := eqb_node (at level 70, no associativity) : file_scope.

End FileNotations.
