From FileSync Require Export
     Sync
     Syntax.
From ITree Require Export
     Nondeterminism
     ITree.
Import
  Monads.

Definition fstep (f: F) : state node A :=
  fun n =>
    match f with
    | Fls   p => (n, Als (ls p n))
    | Fread p =>
      (n, if read p n is Some c
       then Aread c else Ano)
    | Fwrite p c =>
      if write p c n is Some n'
      then (n', Ayes) else (n, Ano)
    | Fmkdir p =>
      if mkdir p n is Some n'
      then (n', Ayes) else (n, Ano)
    | Frm p =>
      if p is nil then (n, Ano) else
      (rmf p n, Ayes)
      (* if rm p n is Some n' *)
      (* then (n', Ayes) else (n, Ano) *)
    end.

Definition qstep (q: Q) : state S A :=
  fun '(g, r1, r2) =>
    if q is QFile r f
    then if r is R1 then
           let (r1', a) := fstep f r1 in
           (g, r1', r2, a)
         else
           let (r2', a) := fstep f r2 in
           (g, r1, r2', a)
    else (recon g r1 r2, Aret BinInt.Z0).

Local Open Scope list_scope.

Fixpoint power {A} (l: list A) : list (list A) :=
  if l is a::l'
  then let p : list (list A) := power l' in
       p ++ map (cons a) p
  else [[]].

Definition qstept E `(nondetE -< E) (q: Q) : stateT S (itree E) A :=
  fun gab =>
    let '(g, r1, r2) := gab in
    if q is QFile r f
    then if r is R1 then
           let (r1', a) := fstep f r1 in
           ret (g, r1', r2, a)
         else
           let (r2', a) := fstep f r2 in
           ret (g, r1, r2', a)
    else
      let aps := allPaths g r1 r2 in
      ps <- choose1 aps (power aps);;
      if lset_subset (list_eqb _) aps ps
      then ret (recon g r1 r2, Aret BinInt.Z0)
      else r <- choose1 BinInt.Z.one [BinInt.Z.two];;
           ret (reconset ps gab, Aret r).
