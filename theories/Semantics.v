From FileSync Require Export
     Sync
     Syntax.
From ITree Require Export
     Basics.
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
      if rm p n is Some n'
      then (n', Ayes) else (n, Ano)
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
    else (recon g r1 r2, Ayes).
