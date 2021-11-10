From FileSync Require Import
     Syntax.
From AsyncTest Require Import
     Jexp.

Definition traceT := list (labelT * (IR * IR)).

Example tget_strong (l : labelT) (p : jpath) (t : traceT) : IR :=
  odflt (JSON__Object []) $ snd <$> get l t >>= jget p.

Definition tget_weak' (jget : jpath -> IR -> option IR)
           (l : labelT) (p : jpath) (t : traceT) : IR :=
  odflt (last (pick_some $ map (jget p ∘ snd ∘ snd) t) $ JSON__Object []) $
        snd <$> get l t >>= jget p.

Definition tget_weak : labelT -> jpath -> traceT -> IR := tget_weak' jget_weak.

Fixpoint jexp_to_IR' (tget : labelT -> jpath -> traceT -> IR)
         (t : traceT) (e : jexp) : IR :=
  match e with
  | Jexp__Const  j   => j
  | Jexp__Array  l   => JSON__Array  $ map     (jexp_to_IR' tget t) l
  | Jexp__Object m   => JSON__Object $ map_snd (jexp_to_IR' tget t) m
  | Jexp__Ref  l p f => f $ tget l p t
  end.

Example jexp_to_IR_strong : traceT -> jexp -> IR := jexp_to_IR' tget_strong.

Definition jexp_to_IR_weak : traceT -> jexp -> IR := jexp_to_IR' tget_weak.

Definition findpath' (p : jpath) : traceT -> list labelT :=
  fmap fst ∘ filter (fun lj => if jget_weak p (snd $ snd lj) is Some _
                             then true else false).

Definition findpath (p : jpath) (f : IR -> IR) (t : traceT) : list jexp :=
  l <- findpath' p t;; [Jexp__Ref l p f].
