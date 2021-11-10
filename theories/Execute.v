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
     SimpleIO.
From ITreeIO Require Export
     ITreeIO.
From Coq Require Export
     ExtrOcamlBasic
     ExtrOcamlIntConv
     ExtrOcamlNativeString.
Import
  ListNotations
  SumNotations
  XNotations
  OSys.
Open Scope sum_scope.

Parameter ols   : string -> IO (list string).
Parameter orm   : list string -> IO bool.
Parameter omkdir: string -> IO bool.
Extract Constant ols =>
  "fun p k -> k (try FileUtil.ls p with 
   _ -> prerr_endline ""ls: error""; [])".
Extract Constant orm =>
  "fun p k -> k (try FileUtil.rm ~recurse:true p; true with
   | FileUtil.RmError str -> prerr_endline str; true
   | _ -> prerr_endline ""rm: error""; true)".
Extract Constant omkdir =>
  "fun p k -> k (try FileUtil.mkdir p; true with
   | FileUtil.MkdirError str -> prerr_endline str; false
   | _ -> prerr_endline ""mkdir: error""; false)".

Extract Inductive string => "string"
[
(* EmptyString *)
"(* If this appears, you're using String internals. Please don't *)
  """"
"
(* String *)
"(* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)
"
]
"(* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))
".
Extract Constant to_ostring => "(fun x -> x)".
Extract Constant from_ostring => "(fun x -> x)".

Parameter obasename: string -> string.
Extract Constant obasename => "Filename.basename".

Definition flatten: path -> string :=
  String.concat "/".

Definition read_file' (p: path) : IO content :=
  cin <- open_in (flatten p);;
  len <- in_channel_length cin;;
  ostr <- really_input_string cin len;;
  close_in_noerr cin;;
  ret (from_ostring ostr).

Definition read_file (p: path) : IO IR :=
  oc <- catch_any_exc (read_file' p);;
  ret (if oc is Some c then JEncode__String c else JSON__False).

Definition write_file (p: path) (str: content) : IO IR :=
  i <- command ("echo -n " ++ str ++ " > " ++ flatten p);;
  ret (if nat_of_int i is O then JSON__True else JSON__False).

Arguments Observe__FromServer {_ _ _}.
Arguments Observe__FromClient {_ _ _}.

Variant logE : Type -> Set :=
  Log: string -> logE unit.

Class Is__tE E `{failureE -< E} `{clientE S -< E} `{logE -< E}.
Notation tE := (failureE +' clientE S +' logE).
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

Definition UNISON: IO int :=
  sleepf (OFloat.Unsafe.of_string "1e-3");;
  command "unison A B -batch -confirmbigdel=false".

Module FileTypes: AsyncTestSIG.

Definition gen_state := S.
Definition otherE := logE.
Definition other_handler {T} (oe: otherE T) : IO T :=
  let 'Log str := oe in
  prerr_endline str.

Open Scope list_scope.

Definition exec_request (j: IR) : IO IR :=
  match JDecode__Q j with
  | inl str => failwith str
  | inr QSync =>
    UNISON;;
    ret JSON__True
  | inr (QFile r f) =>
    let base: path := if r is R1 then ["A"] else ["B"] in
    match f with
    | Fls    p   => JEncode__list ∘ map obasename <$> ols (flatten (base ++ p))
    | Fread  p   => read_file (base ++ p)
    | Fwrite p s => write_file (base ++ p) s
    | Fmkdir p   => JEncode__bool <$> omkdir (flatten (base ++ p))
    | Frm    p   => if p is [] then ret JSON__False else
                     JEncode__bool <$> orm [flatten (base ++ p)]
    end
  end.

Open Scope jexp_scope.

Definition gen_step (s: gen_state) (t: traceT) : IO jexp :=
  let '(g, a, b) := s in
  target <- io_choose [1; 2];;
  method <- io_choose ["ls"; "read"; "mkdir"; "write"; "rm"];;
  (* Todo: choose path from ls response. *)
  p <- io_or (io_choose (pathsOf g ++ pathsOf a ++ pathsOf b))
             (gen_many 3 gen_string);;
  c <- gen_string;;
  io_choose [Jexp__Const JSON__Null;
            (jobj "target" target +
             jobj "method" method +
             jobj "path"    p     +
             jobj "content" c)].

Close Scope jexp_scope.

Definition tester_state := unit.
Definition tester_init: IO tester_state :=
  command "rm -rf A B; mkdir A B";;
  UNISON;;
  ret tt.

Definition fileServer   := serverOf qstep initS.
Definition fileObserver := observe fileServer.

Definition tester (_: tester_state) := interp toClient fileObserver.

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
