From ExtLib Require Export
     Extras
     RelDec.
From Ceres Require Export
     Ceres.
From ITree Require Export
     Exception
     Nondeterminism
     ITree.
From Coq Require Export
     String.
Export
  FunNotation
  Monads
  SumNotations
  ITreeNotations.
Open Scope itree_scope.
Open Scope string_scope.
Open Scope sum_scope.

Section Server.

Variables Q A S : Type.

Hypothesis RelDec__A   : RelDec (@eq A).
Hypothesis Serialize__A: Serialize A.
Hypothesis Serialize__Q: Serialize Q.

Variant serverE : Type -> Type :=
  Server__Recv : S -> serverE Q
| Server__Exec : Q -> A -> serverE unit.

Definition serverOf {E} `{serverE -< E} (step: Q -> state S A) : S -> itree E void :=
  rec (fun s =>
         q <- embed Server__Recv s;;
         let (s', a) := step q s in
         embed Server__Exec q a;;
         call s').

Class Is__sE E `{serverE -< E} `{nondetE -< E}.

Definition serverOfT {E} `{serverE -< E} `{nondetE -< E}
           (stept: forall {F} `{nondetE -< F}, Q -> stateT S (itree F) A)
  : S -> itree E void :=
  rec (fun s =>
         q <- embed Server__Recv s;;
         '(s', a) <- stept q s;;
         embed Server__Exec q a;;
         call s').

Variant observeE : Type -> Type :=
  Observe__FromServer : Q -> observeE A
| Observe__FromClient : S -> observeE Q.

Class Is__oE E `{observeE -< E} `{nondetE -< E} `{exceptE string -< E}.

Definition observe {E} `{Is__oE E} (m: itree (serverE +' nondetE) void) : itree E void :=
  interp
    (fun _ e =>
       match e with
       | (se|) =>
           match se in serverE Y return _ Y with
           | Server__Recv s => embed Observe__FromClient s
           | Server__Exec q a =>
               a' <- embed Observe__FromServer q;;
               if a' ?[ eq ] a
               then Ret tt
               else throw $ "Upon " ++ to_string q ++
                          ", expect " ++ to_string a ++
                          ", but observed " ++ to_string a'
           end
       | (|ne) =>
           match ne in nondetE Y return _ Y with
           | Or => trigger Or
           end
       end) m.

End Server.

Arguments serverOf {_ _ _ _ _}.
Arguments observe  {_ _ _ _ _ _ _ _ _ _ _}.
Arguments serverOfT {_ _ _ _ _ _}.

Notation failureE := (exceptE string).
Notation sE Q A S := (serverE Q A S +' nondetE).
Notation oE Q A S := (observeE Q A S +' nondetE +' failureE).
#[global]
Instance oE_Is__oE Q A S : Is__oE Q A S (oE Q A S). Defined.
#[global]
Instance sE_Is__sE Q A S : Is__sE Q A S (sE Q A S). Defined.
