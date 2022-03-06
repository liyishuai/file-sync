From AsyncTest Require Export
     Operator.
From FileSync Require Export
     AsyncTest
     Gen
     Server
     Semantics.
From SimpleIO Require Export
     IO_Float
     IO_Random
     IO_Sys
     IO_Filename
     IO_Unix
     SimpleIO.
From ITreeIO Require Export
     ITreeIO.
From Coq Require Export
     ExtrOcamlBasic
     ExtrOcamlIntConv.
Import
  ListNotations
  SumNotations
  XNotations
  OSys
  OFilename.
Open Scope sum_scope.

Parameter ols   : ocaml_string -> IO (list ocaml_string).
Parameter orm   : list ocaml_string -> IO bool.
Extract Constant ols =>
  "fun p k -> k (try FileUtil.ls p with 
   _ -> prerr_endline ""ls: error""; [])".
Extract Constant orm =>
  "fun p k -> k (try FileUtil.rm ~recurse:true p; true with
   | FileUtil.RmError str -> prerr_endline str; true
   | _ -> prerr_endline ""rm: error""; true)".

Parameter omkdirp : ocaml_string -> IO bool.
Parameter omkdir  : ocaml_string -> IO bool.
Extract Constant omkdirp =>
          "fun p k -> k (try FileUtil.mkdir ~parent:true p; true with _ -> false)".
Extract Constant omkdir =>
          "fun p k -> k (try Sys.mkdir p 0x755; true with _ -> false)".

(* Definition omkdirp (dir: ocaml_string) : IO bool := *)
(*   i <- command ("mkdir -p " ^ quote dir);; *)
(*   ret (int_eqb i int_zero). *)

(* Definition omkdir (dir: ocaml_string) : IO bool := *)
(*   i <- command ("mkdir " ^ quote dir);; *)
(*   ret (int_eqb i int_zero). *)

Definition flatten: path -> ocaml_string :=
  flip (fold_left concat) "" ∘ map to_ostring.

Definition read_file' (cin: in_channel) : IO content :=
  len <- in_channel_length cin;;
  ostr <- really_input_string cin len;;
  ret (from_ostring ostr).

Definition read_file (p: path) : IO IR :=
  ocin <- catch_any_exc (open_in (flatten p));;
  if ocin is Some cin then
    oc <- catch_any_exc (read_file' cin);;
    close_in_noerr cin;;
    ret (if oc is Some c then JSON__String c else JSON__False)
  else ret JSON__False.

Definition write_file (p: path) (str: content) : IO IR :=
  ooc <- catch_any_exc (open_out (flatten p));;
  if ooc is Some oc
  then ot <- catch_any_exc (output_string oc str);;
       close_out_noerr oc;;
       ret (if ot is Some tt then JSON__True else JSON__False)
  else ret JSON__False.

Arguments Observe__FromServer {_ _ _}.
Arguments Observe__FromClient {_ _ _}.

Variant logE : Type -> Set :=
  Log: string -> logE unit.

Class Is__tE E `{failureE -< E} `{clientE S -< E} `{logE -< E}.
Notation tE := (failureE +' clientE S +' logE).
#[export]
Instance tE_Is__tE: Is__tE tE. Defined.

Definition toClient T (oe: oE _ _ _ T) : itree tE T :=
  match oe with
  | (oe|) =>
    match oe in observeE _ _ _ T return _ T with
    | Observe__FromServer q =>
      j <- embed Client__Exec (JEncode__Q q);;
      match JDecode__A j with
      | inl str =>
        embed Log str;;
        throw ("Cannot parse response IR: " ++ Printer.to_string j)
      | inr a => ret a
      end
    | Observe__FromClient s =>
      j <- embed Client__Gen s;;
      match JDecode__Q j with
      | inl str =>
        embed Log str;;
        throw ("Cannot parse request IR: " ++ Printer.to_string j)
      | inr q => ret q
      end
    end
  | (|Throw str) => throw str
  end.

Parameter sleepf : float -> IO unit.
Extract Constant sleepf => "fun f k -> k (Unix.sleepf f)".

Module FileTypes: AsyncTestSIG.

Definition gen_state := S.
Definition otherE := logE.
Definition other_handler {T} (oe: otherE T) : IO T :=
  let 'Log str := oe in
  prerr_endline str.

Definition tester_config := string.

Infix "^" := ostring_app.

Definition UNISON (config: ocaml_string) : IO int :=
  (* sleepf (OFloat.Unsafe.of_string "1e-3");; *)
  command ("unison " ^ (concat config "A") ^ " " ^ (concat config "B")
          ^ " -batch -confirmbigdel=false " ^
          "-debug files -debug props -debug copy -debug exn -debug remote+ >> "
          ^ (concat config "logs.txt") ^ " 2>> " ^ (concat config "error.txt")).

Definition tester_init: IO tester_config :=
  base <- get_temp_dir_name;;
  timestamp <- OFloat.to_string <$> OUnix.gettimeofday;;
  let dir := concat base (concat "unison" timestamp) in
  omkdirp (concat dir "A");;
  omkdirp (concat dir "B");;
  UNISON dir;;
  ret (from_ostring dir).

Definition upon_success (config: tester_config) : IO unit :=
  orm [to_ostring config];; ret tt.

Definition upon_failure (config: tester_config) : IO unit :=
  print_endline ("DIR: " ++ config).

Open Scope list_scope.

Definition exec_request (config: tester_config) (j: IR) : IO IR :=
  match JDecode__Q j with
  | inl str => failwith str
  | inr QSync =>
    JSON__Number ∘ z_of_int <$> UNISON config
  | inr (QFile r f) =>
    let base: path := if r is R1 then [config; "A"] else [config; "B"] in
    match f with
    | Fls    p   => JEncode__list ∘ map (from_ostring ∘ basename) <$>
                               ols (flatten (base ++ p))
    | Fread  p   => read_file (base ++ p)
    | Fwrite p s => write_file (base ++ p) s
    | Fmkdir p   => JEncode__bool <$> omkdir (flatten (base ++ p))
    | Frm    p   => if p is [] then ret JSON__False else
                     JEncode__bool <$> orm [flatten (base ++ p)]
    end
  end.

Open Scope jexp_scope.

Definition isAls (irA: IR) : bool :=
  if Decode.decode irA is inr (Als _) then true else false.

Definition gen_step (s: gen_state) (t: traceT) : IO jexp :=
  let '(g, a, b) := s in
  target <- io_choose [1; 2];;
  method <- io_choose ["ls"; "read"; "mkdir"; "write"; "rm"];;
  let lsA : list (labelT * IR) := List.filter (isAls ∘ snd) t in
  let pls : list path :=
    '(labelA, irA) <- lsA;;
    '(labelQ, irQ) <- List.filter (Nat.eqb labelA ∘ fst) t;;
    let children : list path :=
      if Decode.decode irA is inr (Als names)
      then map (flip cons nil) names
      else [] in
    if Decode.decode irQ is inr (QFile _ (Fls dir))
    then map (app dir) children
    else []
  in
  p <- io_or (io_choose (pathsOf g ++ pathsOf a ++ pathsOf b ++ pls))
            (gen_many 3 gen_string);;
  c <- gen_string;;
  io_choose [Jexp__Const (JSON__String "sync");
             jobj "target" target +
             jobj "method" method +
             if method is "write"
             then jobj "path" p + jobj "content" c
             else jobj "path" p
    ].

Close Scope jexp_scope.

Definition fileServer   := serverOf qstep initS.
Definition fileObserver := observe fileServer.

Definition tester := interp toClient fileObserver.

End FileTypes.

Module FileTest := AsyncTest FileTypes.

Fixpoint multi_test' (fuel : nat) (test : IO bool) : IO unit :=
  match fuel with
  | O => print_endline "Success"
  | Datatypes.S fuel =>
    b <- test;;
    if b : bool
    then
      print_endline (to_string fuel);;
      multi_test' fuel test
    else print_endline "Failure"
  end.

Definition multi_test : IO bool -> IO unit := multi_test' 5000.

Definition fileTester: IO unit :=
  multi_test FileTest.test.
