From SimpleIO Require Import
     IO_Random.
From FileSync Require Import
     Execute.

Definition run_test: io_unit :=
  IO.unsafe_run' (ORandom.self_init tt;; fileTester).

Separate Extraction run_test.
