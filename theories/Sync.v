From ExtLib Require Export
     ListSet.
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

Definition dirtyPaths (g s: node) : list path :=
  List.filter (dirty g s) $ lset_union (list_eqb _) (pathsOf g) (pathsOf s).

Definition allPaths (g a b: node) : list path :=
  lset_union (list_eqb _) (dirtyPaths g a) (dirtyPaths g b).

Definition ssrecon (gab: node * node * node) (p: path) : node * node * node :=
  let '(g, a, b) := gab in
  match cd p g, cd p a, cd p b with
  | Some gp, Some ap, Some bp =>
      if ap =? gp
      then (override p bp g, override p bp a, b)
      else
        if bp =? gp
        then (override p ap g, a, override p ap b)
        else
          if ap =? bp
          then (override p ap g, a, b)
          else gab
  | None, Some ap, Some bp =>
      if ap =? bp
      then (override p ap g, a, b)
      else gab
  | Some gp, Some ap, None =>
      if ap =? gp
      then (rmf p g, rmf p a, b)
      else gab
  | Some gp, None, Some bp =>
      if bp =? gp
      then (rmf p g, a, rmf p b)
      else gab
  | None, None, Some bp =>
      (override p bp g, override p bp a, b)
  | None, Some ap, None =>
      (override p ap g, a, override p ap b)
  | _, None, None =>
      (rmf p g, a, b)
  end.

Definition reconset : list path -> node * node * node -> node * node * node :=
  fold_left ssrecon.

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

Lemma recon_alt (g a b: node) :
  recon g a b = reconset (allPaths g a b) (g, a, b).
Abort.

Definition conflict (g a b: node) (p: path) : bool :=
  let '(_, a', b') := recon g a b in
  match cd p a', cd p b' with
  | Some ap, Some bp => negb $ ap =? bp
  | None, None => false
  | _, _ => true
  end.
