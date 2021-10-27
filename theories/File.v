From Coq Require Export
     Basics
     Bool
     List
     PeanoNat
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

Definition emptyDir: node := Directory empty.

Definition mapping := alist name node.

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
    let n0 := if lookup f d is Some d0 then d0 else emptyDir in
    Directory $ add f (override p m n0) d
  | f::p, File _ => Directory [(f, override p m $ emptyDir)]
  end.

(* mkdir -p *)
Fixpoint mkdirp (p: path) (n: node) : option node :=
  match p, n with
  | [f], Directory d =>
    match lookup f d with
    | Some (Directory _) => Some n
    | Some (File _)      => None
    | None => Some $ Directory $ add f emptyDir d
    end
  | f::p, Directory d =>
    if lookup f d is Some n
    then n' <- mkdirp p n;;
         Some (Directory $ add f n' d)
    else Some $ Directory $ add f emptyDir d
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

(* rm -r *)
Definition rm (p: path) (n: node) : option node :=
  if cd (dirname p) n is Some (Directory _)
  then Some $ rmf p n
  else None.                    (* Parent not found *)

Fixpoint size (n: node) : nat :=
  if n is Directory d
  then fold_left plus (map (size ∘ snd) d) 1
  else 1.

Lemma fold_left_plus : forall l n,
    n <= fold_left plus l n.
Proof.
  induction l; intuition.
  simpl.
  apply Nat.le_trans with (n + a); intuition.
Qed.

Lemma fold_left_plus_linear : forall l n m,
    n <= m ->
    fold_left plus l n <= fold_left plus l m.
Proof.
  induction l; intuition.
  simpl.
  apply IHl.
  intuition.
Qed.

Lemma size_subdir (f: name) (n: node) (d: mapping) :
  In (f, n) d ->
  size n < size (Directory d).
Proof.
  intro.
  induction d; intuition.
  unfold In in H.
  fold (In (f, n) d) in H.
  intuition.
  - subst.
    simpl.
    unfold compose.
    simpl.
    apply Nat.lt_le_trans with (S (size n)); intuition.
    apply fold_left_plus.
  - simpl in *.
    eapply Nat.lt_le_trans; eauto.
    apply fold_left_plus_linear.
    intuition.
Qed.

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
