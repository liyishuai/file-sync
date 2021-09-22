From ITree Require Export
     ITree.
Export
  Monads
  ITreeNotations.
Open Scope itree_scope.

Section Server.

Parameters Q A S : Type.

Variant serverE : Type -> Type :=
  Server__Recv : serverE Q
| Server__Send : A -> serverE unit.

Definition serverOf (step: Q -> state S A) : S -> itree serverE void :=
  rec (fun s =>
         q <- trigger Server__Recv;;
         let (s', a) := step q s in
         embed Server__Send a;;
         call s').

End Server.
