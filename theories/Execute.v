From FileSync Require Export
     Gen
     Server
     Semantics.
From SimpleIO Require Export
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
  SumNotations
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
   | FileUtil.RmError str -> prerr_endline str; false
   | _ -> prerr_endline ""rm: error""; false)".
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

Definition read_file (p: path) : IO A :=
  oc <- catch_any_exc (read_file' p);;
  ret (if oc is Some c then Aread c else Ano).

Definition write_file (p: path) (str: content) : IO A :=
  ou <- catch_any_exc (cout <- open_out (flatten p);;
                   output_string cout str;;
                   close_out_noerr cout);;
  ret (if ou is Some tt then Ayes else Ano).

Arguments Observe__FromServer {_ _ _}.
Arguments Observe__FromClient {_ _ _}.

Definition runObserve {T} (oe: observeE Q A S T) : IO T :=
  match oe in observeE _ _ _ T return _ T with
  | Observe__FromServer QSync =>
    command "unison -batch A B";; ret Ayes
  | Observe__FromServer (QFile r f) =>
    let base: path := if r is R1 then ["A"] else ["B"] in
    tee $
    match f with
    | Fls    p   => Als ∘ map obasename <$> ols (flatten (base ++ p))
    | Fread  p   => read_file (base ++ p)
    | Fwrite p s => write_file (base ++ p) s
    | Fmkdir p   => b <- omkdir (flatten (base ++ p));;
                   ret (if b : bool then Ayes else Ano)
    | Frm    p   => b <- orm [flatten (base ++ p)];;
                   ret (if b : bool then Ayes else Ayes )
    end
  | Observe__FromClient s =>
    tee $
    let '(g, a, b) := s in
    r <- io_choose [R1; R2];;
    p <- gen_many 3 gen_string;;
    c <- gen_string;;
    io_choose [QSync;
              QFile r (Fls p);
              QFile r (Fread p);
              QFile r (Fwrite p c);
              QFile r (Fmkdir p);
              QFile r (Frm p)]
  end.

Definition runO T (oe: oE Q A S T) : IO T :=
  match oe with
  | (oe|)        => runObserve oe
  | (|Throw str) => failwith str
  end.

Definition fileServer   := serverOf qstep initS.
Definition fileObserver := observe fileServer.
Definition fileTester   :=
  orm ["A"; "B"];; omkdir "A";; omkdir "B";; command "unison -batch A B";;
  interp_io runO fileObserver.
