From QuickChick Require Export
     QuickChick.
From ITree Require Export
     Exception
     ITree.
From SimpleIO Require Export
     SimpleIO.
From AsyncTest Require Export
     Instances.
From FileSync Require Export
     Trace.
Export
  SumNotations.
Open Scope sum_scope.

Variant clientE {gen_state} : Type -> Type :=
  Client__Exec : IR        -> clientE IR
| Client__Gen  : gen_state -> clientE IR.
Arguments clientE: clear implicits.

Module Type AsyncTestSIG.

Parameter gen_state     : Type.
Parameter otherE        : Type -> Type.
Parameter other_handler : otherE ~> IO.
Arguments other_handler {_}.

Notation failureE       := (exceptE string).
Notation tE             := (failureE +' clientE gen_state +' otherE).

Parameter tester_config : Type.
Parameter tester_init   : IO tester_config.
Parameter exec_request  : tester_config -> IR -> IO IR.
Parameter upon_success  : tester_config -> IO unit.
Parameter upon_failure  : tester_config -> IO unit.

Parameter gen_step      : gen_state -> traceT -> IO jexp.

Parameter tester        : itree tE void.

End AsyncTestSIG.

Module AsyncTest (SIG : AsyncTestSIG).
Include SIG.

Notation scriptT := (list (jexp * labelT)).

Definition shrink_execute' (exec : scriptT -> IO (bool * traceT))
           (init : scriptT) : IO (option scriptT) :=
  (* print_endline "===== initial script =====";; *)
  (* print_endline (to_string init);; *)
  IO.fix_io
    (fun shrink_rec ss =>
       match ss with
       | [] => print_endline "<<<<< shrink exhausted >>>>";; ret None
       | sc :: ss' =>
         prerr_endline (to_string (List.length ss'));;
         (* print_endline "<<<<< current script >>>>>>";; *)
         (* print_endline (to_string sc);; *)
         '(b, tr) <- exec sc;;
         if b : bool
         then (* print_endline ("===== accepting trace ===== " ++ (to_string (length ss')))%string;; *)
              (* print_endline (to_string tr);; *)
              shrink_rec ss'
         else print_endline "<<<<< rejecting trace >>>>>";;
              print_endline (to_string tr);;
              (* print_endline "<<<<< shrink ended >>>>>>>>";; *)
              ret (Some sc)
       end) (repeat_list 10 $ shrinkListAux (const []) init).

Definition shrink_execute (first_exec : IO (bool * (scriptT * traceT)))
           (then_exec : scriptT -> IO (bool * traceT)) : IO bool :=
  '(b, (sc, tr)) <- first_exec;;
  if b : bool
  then
    (* print_endline "===== accepting trace =====";; *)
    (* print_endline (to_string tr);; *)
    ret true
  else print_endline "<<<<< rejecting trace >>>>>";;
       print_endline (to_string tr);;
       IO.while_loop (shrink_execute' then_exec) sc;;
       ret false.

Fixpoint execute' {R} (fuel : nat) (config: tester_config)
         (oscript : option scriptT) (acc : scriptT * traceT) (m : itree tE R)
  : IO (bool * (scriptT * traceT)) :=
  let (script0, trace0) := acc in
  match fuel with
  | O => ret (true, acc)
  | S fuel =>
    match observe m with
    | RetF _ => ret (true, acc)
    | TauF m' => execute' fuel config oscript acc m'
    | VisF e k =>
      match e with
      | (Throw err|) =>
        print_endline (String "010" "ERR: " ++ err)%string;;
        ret (false, acc)
      | (|ce|) =>
        match ce in clientE _ Y return (Y -> _) -> _ with
        | Client__Exec q =>
          fun k =>
            match trace0 with
            | [] =>
              print_endline "Should not happen: exec on empty trace";;
              ret (false, acc)
            | t0::l0 =>
              let label: labelT := fst (last l0 t0) in
              a <- exec_request config q;;
              execute' fuel config oscript (script0, trace0++[(label, a)]) (k a)
            end
        | Client__Gen gs =>
          fun k => '(ostep, osc') <-
                 match oscript with
                 | Some [] => ret (None, Some [])
                 | Some (sc :: script') =>
                   ret (Some sc, Some script')
                 | None =>
                   let l : labelT := S $ fold_left max (map snd script0) O in
                   step <- gen_step gs trace0;;
                   ret (Some (step, l), None)
                 end;;
                 match ostep with
                 | Some ((e, l) as step) =>
                   let req : IR := jexp_to_IR_weak trace0 e in
                   execute' fuel config osc' (script0++[step],
                                               trace0++[(l, req)]) (k req)
                 | None =>
                   prerr_endline "Script exhausted";;
                   ret (true, acc)
                 end
        end k
      | (||oe) => other_handler oe >>= execute' fuel config oscript acc ∘ k
      end
    end
  end.

Definition execute {R} (m : itree tE R)
           (oscript : option scriptT) : IO (bool * (scriptT * traceT)) :=
  config <- tester_init;;
  result <- execute' 5000 config oscript ([], []) m;;
  (if fst result : bool then upon_success config else upon_failure config);;
  ret result.

Definition test : IO bool :=
  shrink_execute (execute tester None)
                 (fmap (fun '(b, (_, t)) => (b, t)) ∘ execute tester ∘ Some).

End AsyncTest.
