From ExtLib Require Export
     Extras
     RelDec.
From Ceres Require Export
     Ceres.
From ITree Require Export
     Exception
     ITree.
From Coq Require Export
     String.
Export
  FunNotation
  Monads
  ITreeNotations.
Open Scope itree_scope.
Open Scope string_scope.

Section Server.

Variables Q A S : Type.

Hypothesis RelDec__A   : RelDec (@eq A).
Hypothesis Serialize__A: Serialize A.
Hypothesis Serialize__Q: Serialize Q.

Variant serverE : Type -> Type :=
  Server__Recv : S -> serverE Q
| Server__Exec : Q -> A -> serverE unit.

Definition serverOf (step: Q -> state S A) : S -> itree serverE void :=
  rec (fun s =>
         q <- embed Server__Recv s;;
         let (s', a) := step q s in
         embed Server__Exec q a;;
         call s').

Variant observeE : Type -> Type :=
  Observe__FromServer : Q -> observeE A
| Observe__FromClient : S -> observeE Q.

Class Is__oE E `{observeE -< E} `{exceptE string -< E}.

Definition observe {E} `{Is__oE E} (m: itree serverE void) : itree E void :=
  interp
    (fun _ e =>
       match e in serverE Y return _ Y with
       | Server__Recv s => embed Observe__FromClient s
       | Server__Exec q a =>
         a' <- embed Observe__FromServer q;;
         if a' ?[ eq ] a
         then Ret tt
         else throw $ "Upon " ++ to_string q ++
                    ", expect " ++ to_string a ++
                    ", but observed " ++ to_string a'
       end) m.

End Server.

Arguments serverOf {_ _ _}.
Arguments observe  {_ _ _ _ _ _ _ _ _ _}.

Notation failureE := (exceptE string).
Notation oE Q A S := (observeE Q A S +' failureE).
Instance oE_Is__oE Q A S : Is__oE Q A S (oE Q A S). Defined.
