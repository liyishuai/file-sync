From FileSync Require Export
     File.
Export
  FileNotations.
Open Scope file_scope.
Open Scope list_scope.

Definition dirty (g s: node) (p: path) : bool :=
  match cd p g, cd p s with
  | Some n, Some m => negb $ n =? m
  | None  , None   => false
  | _     , _      => true
  end.

Definition replace (p: path) (s: node) : node -> node :=
  if cd p s is Some n then override p n else rmf p.

Program Fixpoint recon (g a b: node) {measure (size g)} : node * node * node :=
  if a =? g
  then (b, b, b)
  else
    if b =? g
    then (a, a, a)
    else
      if a =? b
      then (a, a, a)
      else
        match a, b with
        | Directory da, Directory db =>
          let dg : mapping := if g is Directory dg then dg else [] in
          let fgab :=
              map
                (fun f : string =>
                   match lookup f dg, lookup f da, lookup f db with
                   | Some g, Some a, Some b =>
                     let '(g', a', b') := recon g a b in
                     (add f g', add f a', add f b')
                   | None, Some a, Some b =>
                     if a =? b
                     then (add f a, id, id)
                     else (id, id, id)
                   | Some g, Some a, None =>
                     if a =? g
                     then (remove f, remove f, id)
                     else (id, id, id)
                   | Some g, None, Some b =>
                     if b =? g
                     then (remove f, id, remove f)
                     else (id, id, id)
                   | None, None, Some b =>
                     (add f b, add f b, id)
                   | None, Some a, None =>
                     (add f a, id, add f a)
                   | _, None, None =>
                     (remove f, id, id)
                   end) (map fst $ dg ++ da ++ db) in
          let '(dg', da', db') :=
              @fold_left (_ * _ * _) (_ * _ * _)
                         (fun '(dg, da, db) '(fg, fa, fb) =>
                           (fg dg, fa da, fb db)) fgab (dg, da, db) in
          (Directory dg', Directory da', Directory db')
        | _, _ => (g, a, b)
        end.
Next Obligation.
  destruct g0; try discriminate.
  rewrite alist_find_alt in Heq_anonymous.
  unfold alist_find' in Heq_anonymous.
  unfold compose in Heq_anonymous.
  destruct (find (fun x : string * node => RelDec.rel_dec f (fst x)) a0) eqn:Hfind;
    try discriminate.
  destruct p.
  inversion Heq_anonymous; subst.
  apply find_some in Hfind.
  intuition.
  eapply size_subdir; eauto.
Defined.
