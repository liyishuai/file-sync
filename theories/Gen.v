From ExtLib Require Export
     Extras
     Applicative
     Functor
     Monad.
From SimpleIO Require Export
     IO_Random
     SimpleIO.
From Ceres Require Export
     CeresSerialize.
From Coq Require Export
     Basics
     ExtrOcamlIntConv
     String
     List.
Export
  FunNotation
  FunctorNotation
  MonadNotation
  ListNotations.
Open Scope monad_scope.
Open Scope string_scope.
Open Scope program_scope.

Definition tee {A} `{Serialize A} (io: IO A) : IO A :=
  a <- io;;
  prerr_endline (to_string a);;
  ret a.

Definition io_choose_ {A} (default : IO A) (l : list A) : IO A :=
  match l with
  | [] => default
  | a :: _ =>
    i <- nat_of_int <$> ORandom.int (int_of_nat (length l));;
    ret (nth i l a)
  end.

Definition io_choose' {A} (l : list A) : IO (nat * A) :=
  match l with
  | [] => failwith "Cannot choose from empty list"
  | a :: _ =>
    i <- nat_of_int <$> ORandom.int (int_of_nat (length l));;
    ret (i, nth i l a)
  end.

Definition io_choose {A} : list A -> IO A :=
  fmap snd ∘ io_choose'.

Definition io_or {A} (x y : IO A) : IO A :=
  b <- ORandom.bool tt;;
  if b : bool then x else y.

Definition gen_string' : IO string :=
  io_choose ["foo"; "bar"].

Fixpoint gen_many {A} (n : nat) (ma : IO A) : IO (list A) :=
  match n with
  | O => ret []
  | S n' => liftA2 cons ma $ io_or (ret []) (gen_many n' ma)
  end.

Definition gen_string : IO string :=
  String.concat "." <$> gen_many 3 gen_string'.
