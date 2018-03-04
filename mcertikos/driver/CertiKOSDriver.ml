(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Generating the code of CertiKOS *)

open Printf
open Camlcoq
open Clflags
open C
open Builtins

(* Location of the compatibility library *)

let stdlib_path = ref(
  try
    Sys.getenv "COMPCERT_LIBRARY"
  with Not_found ->
    Configuration.stdlib_path)

let command cmd =
  if !option_v then begin
    prerr_string "+ "; prerr_string cmd; prerr_endline ""
  end;
  Sys.command cmd

let quote_options opts =
  String.concat " " (List.rev_map Filename.quote opts)

let safe_remove file =
  try Sys.remove file with Sys_error _ -> ()

(* Printing of error messages *)

let print_error oc msg =
  let print_one_error = function
  | Errors.MSG s -> output_string oc (camlstring_of_coqstring s)
  | Errors.CTX i -> fprintf oc "%s (%ld)" (extern_atom i) (P.to_int32 i)
  | Errors.POS i -> fprintf oc "%ld" (P.to_int32 i)
  in
    List.iter print_one_error msg;
    output_char oc '\n'

(* Determine names for output files.  We use -o option if specified
   and if this is the final destination file (not a dump file).
   Otherwise, we generate a file in the current directory. *)

let output_filename ?(final = false) source_file source_suffix output_suffix =
  match !option_o with
  | Some file when final -> option_o := None; file
  | _ -> 
    Filename.basename (Filename.chop_suffix source_file source_suffix)
    ^ output_suffix

(* A variant of [output_filename] where the default output name is fixed *)

let output_filename_default default_file =
  match !option_o with
  | Some file -> option_o := None; file
  | None -> default_file

(* Generate the assembly file for CertiKOS *)

exception SymbolNotFresh of (AST.ident * string)

let add_symbol (ident, string) =
  assert (not (Hashtbl.mem atom_of_string string));
  assert (not (Hashtbl.mem string_of_atom ident));
  next_atom := max !next_atom (P.succ ident);
  Hashtbl.add atom_of_string string ident;
  Hashtbl.add string_of_atom ident string

let add_symbols () = List.iter add_symbol (List.map (fun (i, s) -> (i, Camlcoq.camlstring_of_coqstring s)) Symbols.symbols)

let compile_certikos ofile =
  add_symbols ();
  match CertiKOSImpl.extract_module CertiKOS.certikos with
    | Errors.Error msg ->
      print_error stderr msg;
      exit 2
    | Errors.OK p ->
      let oc = open_out ofile in
      PrintLAsm.print_program oc p;
      close_out oc

(* From asm to object file *)

let assemble ifile ofile =
  let cmd =
    sprintf "%s -o %s %s %s"
      Configuration.asm ofile (quote_options !assembler_options) ifile in
  let retcode = command cmd in
  if retcode <> 0 then begin
    safe_remove ofile;
    eprintf "Error during assembling.\n";
    exit 2
  end

let process_certikos () =
  let sourcename = "certikos.c" in
  if !option_S then begin
    compile_certikos
                        (output_filename ~final:true sourcename ".c" ".s");
    ""
  end else begin
    let asmname =
      if !option_dasm
      then output_filename sourcename ".cm" ".s"
      else Filename.temp_file "compcert" ".s" in
    compile_certikos asmname;
    let objname = output_filename ~final: !option_c sourcename ".c" ".o" in
    assemble asmname objname;
    if not !option_dasm then safe_remove asmname;
    objname
  end

(* Linking *)

let linker exe_name files =
  let cmd =
    sprintf "%s -o %s %s %s"
      Configuration.linker
      (Filename.quote exe_name)
      (quote_options files)
      (if Configuration.has_runtime_lib
       then sprintf "-L%s -lcompcert" !stdlib_path
       else "") in
  if command cmd <> 0 then exit 2

(* Record actions to be performed after parsing the command line *)

let actions : ((string -> string) * string) list ref = ref []

let push_action fn arg =
  actions := (fn, arg) :: !actions

let push_linker_arg arg =
  push_action (fun s -> s) arg

let perform_actions () =
  let rec perform = function
  | [] -> []
  | (fn, arg) :: rem -> let res = fn arg in res :: perform rem
  in perform (List.rev !actions)

(* Command-line parsing *)

let explode_comma_option s =
  match Str.split (Str.regexp ",") s with
  | [] -> assert false
  | hd :: tl -> tl

type action =
  | Set of bool ref
  | Unset of bool ref
  | Self of (string -> unit)
  | String of (string -> unit)
  | Integer of (int -> unit)

let rec find_action s = function
  | [] -> None
  | (re, act) :: rem ->
      if Str.string_match re s 0 then Some act else find_action s rem

let parse_cmdline spec usage =
  let acts = List.map (fun (pat, act) -> (Str.regexp pat, act)) spec in
  let rec parse i =
    if i < Array.length Sys.argv then begin
      let s = Sys.argv.(i) in
      match find_action s acts with
      | None ->
          if s <> "-help" && s <> "--help" 
          then eprintf "Unknown argument `%s'\n" s
          else printf "%s" usage;
          exit 2
      | Some(Set r) ->
          r := true; parse (i+1)
      | Some(Unset r) ->
          r := false; parse (i+1)
      | Some(Self fn) ->
          fn s; parse (i+1)
      | Some(String fn) ->
          if i + 1 < Array.length Sys.argv then begin
            fn Sys.argv.(i+1); parse (i+2)
          end else begin
            eprintf "Option `%s' expects an argument\n" s; exit 2
          end
      | Some(Integer fn) ->
          if i + 1 < Array.length Sys.argv then begin
            let n =
              try
                int_of_string Sys.argv.(i+1)
              with Failure _ ->
                eprintf "Argument to option `%s' must be an integer\n" s;
                exit 2
            in
            fn n; parse (i+2)
          end else begin
            eprintf "Option `%s' expects an argument\n" s; exit 2
          end
    end
  in parse 1

let usage_string =
"CertiKOS code generator, using
The CompCert C verified compiler, version " ^ Configuration.version ^ "
Usage: certikos [options]
Processing options:
  -c             Compile to object file only (no linking), result in <file>.o
  -E             Preprocess only, send result to standard output
  -S             Compile to assembler only, save result in <file>.s
  -o <file>      Generate output in <file>
Preprocessing options:
  -I<dir>        Add <dir> to search path for #include files
  -D<symb>=<val> Define preprocessor symbol
  -U<symb>       Undefine preprocessor symbol
  -Wp,<opt>      Pass option <opt> to the preprocessor
Language support options (use -fno-<opt> to turn off -f<opt>) :
  -fbitfields    Emulate bit fields in structs [off]
  -flongdouble   Treat 'long double' as 'double' [off]
  -fstruct-return  Emulate returning structs and unions by value [off]
  -fvararg-calls Emulate calls to variable-argument functions [on]
  -fpacked-structs  Emulate packed structs [off]
  -finline-asm   Support inline 'asm' statements [off]
  -fall          Activate all language support options above
  -fnone         Turn off all language support options above
Code generation options: (use -fno-<opt> to turn off -f<opt>) :
  -fsse          (IA32) Use SSE2 instructions for some integer operations [on]
  -fsmall-data <n>  Set maximal size <n> for allocation in small data area
  -fsmall-const <n>  Set maximal size <n> for allocation in small constant area
  -ffloat-const-prop <n>  Control constant propagation of floats
                   (<n>=0: none, <n>=1: limited, <n>=2: full; default is full)
  -falign-functions <n>  Set alignment (in bytes) of function entry points
  -falign-branch-targets <n>  Set alignment (in bytes) of branch targets
  -falign-cond-branches <n>  Set alignment (in bytes) of conditional branches
  -Wa,<opt>      Pass option <opt> to the assembler
Tracing options:
  -dparse        Save C file after parsing and elaboration in <file>.parse.c
  -dc            Save generated Compcert C in <file>.compcert.c
  -dclight       Save generated Clight in <file>.light.c
  -dcminor       Save generated Cminor in <file>.cm
  -drtl          Save unoptimized generated RTL in <file>.rtl
  -dtailcall     Save RTL after tail call optimization in <file>.tailcall.rtl
  -dinlining     Save RTL after inlining optimization in <file>.inlining.rtl
  -dconstprop    Save RTL after constant propagation in <file>.constprop.rtl
  -dcse          Save RTL after CSE optimization in <file>.cse.rtl
  -dalloc        Save LTL after register allocation in <file>.alloc.ltl
  -dmach         Save generated Mach code in <file>.mach
  -dasm          Save generated assembly in <file>.s
Linking options:
  -l<lib>        Link library <lib>
  -L<dir>        Add <dir> to search path for libraries
  -Wl,<opt>      Pass option <opt> to the linker
General options:
  -stdlib <dir>  Set the path of the Compcert run-time library [MacOS X only]
  -v             Print external commands before invoking them
"

let language_support_options = [
  option_fbitfields; option_flongdouble;
  option_fstruct_return; option_fvararg_calls; option_fpacked_structs;
  option_finline_asm
]

let cmdline_actions =
  let f_opt name ref =
    ["-f" ^ name ^ "$", Set ref; "-fno-" ^ name ^ "$", Unset ref] in
  [
  "-I$", String(fun s -> prepro_options := s :: "-I" :: !prepro_options);
  "-D$", String(fun s -> prepro_options := s :: "-D" :: !prepro_options);
  "-U$", String(fun s -> prepro_options := s :: "-U" :: !prepro_options);
  "-[IDU].", Self(fun s -> prepro_options := s :: !prepro_options);
  "-[lL].", Self(fun s -> push_linker_arg s);
  "-o$", String(fun s -> option_o := Some s);
  "-E$", Set option_E;
  "-S$", Set option_S;
  "-c$", Set option_c;
  "-v$", Set option_v;
  "-g$", Self (fun s -> option_g := true; push_linker_arg s);
  "-stdlib$", String(fun s -> stdlib_path := s);
  "-dparse$", Set option_dparse;
  "-dc$", Set option_dcmedium;
  "-dclight$", Set option_dclight;
  "-dcminor", Set option_dcminor;
  "-drtl$", Set option_drtl;
  "-dltl$", Set option_dltl;
  "-dalloctrace$", Set option_dalloctrace;
  "-dmach$", Set option_dmach;
  "-dasm$", Set option_dasm;
  "-sdump$", Set option_sdump;
  ".*\\.[oa]$", Self (fun s ->
      push_linker_arg s);
  "-Wp,", Self (fun s ->
      prepro_options := List.rev_append (explode_comma_option s) !prepro_options);
  "-Wa,", Self (fun s ->
      assembler_options := s :: !assembler_options);
  "-Wl,", Self (fun s ->
      push_linker_arg s);
  "-Os$", Set option_Osize;
  "-O$", Unset option_Osize;
  "-timings$", Set option_timings;
  "-fsmall-data$", Integer(fun n -> option_small_data := n);
  "-fsmall-const$", Integer(fun n -> option_small_const := n);
  "-ffloat-const-prop$", Integer(fun n -> option_ffloatconstprop := n);
  "-falign-functions$", Integer(fun n -> option_falignfunctions := Some n);
  "-falign-branch-targets", Integer(fun n -> option_falignbranchtargets := n);
  "-falign-cond-branches", Integer(fun n -> option_faligncondbranchs := n);
  "-fall$", Self (fun _ ->
              List.iter (fun r -> r := true) language_support_options);
  "-fnone$", Self (fun _ ->
              List.iter (fun r -> r := false) language_support_options);
  ]
  @ f_opt "tailcalls" option_ftailcalls
  @ f_opt "longdouble" option_flongdouble
  @ f_opt "struct-return" option_fstruct_return
  @ f_opt "bitfields" option_fbitfields
  @ f_opt "vararg-calls" option_fvararg_calls
  @ f_opt "unprototyped" option_funprototyped
  @ f_opt "packed-structs" option_fpacked_structs
  @ f_opt "inline-asm" option_finline_asm
  @ f_opt "fpu" option_ffpu
  @ f_opt "sse" option_ffpu (* backward compatibility *)

(** ** The builtin environment *)

let builtins_generic = {
  typedefs = [
    (* keeps GCC-specific headers happy, harmless for others *)
    "__builtin_va_list", C.TPtr(C.TVoid [], [])
  ];
  functions = [
    (* Floating-point absolute value *)
    "__builtin_fabs",
      (TFloat(FDouble, []), [TFloat(FDouble, [])], false);
    (* Block copy *)
    "__builtin_memcpy_aligned",
         (TVoid [],
           [TPtr(TVoid [], []); 
            TPtr(TVoid [AConst], []); 
            TInt(Cutil.size_t_ikind, []);
            TInt(Cutil.size_t_ikind, [])],
          false);
    (* Annotations *)
    "__builtin_annot",
        (TVoid [],
          [TPtr(TInt(IChar, [AConst]), [])],
          true);
    "__builtin_annot_intval",
        (TInt(IInt, []),
          [TPtr(TInt(IChar, [AConst]), []); TInt(IInt, [])],
          false)
  ]
}

(* Add processor-dependent builtins *)

let builtins =
  { typedefs = builtins_generic.typedefs @ CBuiltins.builtins.typedefs;
    functions = builtins_generic.functions @ CBuiltins.builtins.functions }

let _ =
  Gc.set { (Gc.get()) with Gc.minor_heap_size = 524288 };
  Machine.config :=
    begin match Configuration.arch with
(*
    | "powerpc" -> Machine.ppc_32_bigendian
    | "arm"     -> Machine.arm_littleendian
*)
    | "ia32"    -> Machine.x86_32
    | _         -> assert false
    end;
  Builtins.set builtins;
  (*
  CPragmas.initialize();
  *)
  parse_cmdline cmdline_actions usage_string;
  let objfile = process_certikos () in
  linker_options := objfile :: !linker_options;
  if !linker_options <> [] 
  && not (!option_c || !option_S || !option_E)
  then begin
    linker (output_filename_default "a.out") !linker_options
  end
