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

(* Program *) Fixpoint recon (g a b: node) (* {measure (size g)} *) : node * node * node :=
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
          let dg := if g is Directory dg then dg else [] in
          let '(dg', da', db') :=
              fold_left
                (fun '(dg, da, db) f =>
                   match lookup f dg, lookup f da, lookup f db with
                   | Some g, Some a, Some b =>
                     let '(g', a', b') := (g, a, b) in
                     (* let '(g', a', b') := recon g a b in *)
                     (add f g' dg, add f a' da, add f b' db)
                   | None, Some a, Some b =>
                     if a =? b
                     then (add f a dg, da, db)
                     else (dg, da, db)
                   | Some g, Some a, None =>
                     if a =? g
                     then (remove f dg, remove f da, db)
                     else (dg, da, db)
                   | Some g, None, Some b =>
                     if b =? g
                     then (remove f dg, da, remove f db)
                     else (dg, da, db)
                   | None, None, Some b =>
                     (add f b dg, add f b da, db)
                   | None, Some a, None =>
                     (add f a dg, da, add f a db)
                   | _, None, None =>
                     (remove f dg, da, db)
                   end) (map fst $ da ++ db) (dg, da, db) in
          (Directory dg', Directory da', Directory db')
        | _, _ => (g, a, b)
        end.
