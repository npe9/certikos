open Printf
open Datatypes
open Camlcoq
open Sections
open AST
open Memdata
open LAsm
open PrintAsm
open GlobIdent

let print_instruction oc = function
  | Coq_asm_instruction i -> PrintAsm.print_instruction oc i

(** BEGIN LAsm pseudo-instructions *)

  | Pmov_rm_RA (a) ->
      fprintf oc "	movl	%a, %%eax\n" addressing a;
        fprintf oc "	movl	%%eax, (%%esp)\n"
  | Pmov_ra_RA (id) ->
      if target = MacOS then begin
        let id = extern_atom id in
        indirect_symbols := StringSet.add id !indirect_symbols;
        fprintf oc "	movl	$L%a$non_lazy_ptr, 0(%%esp)\n" raw_symbol id
      end else
        fprintf oc "	movl	$%a, 0(%%esp)\n" symbol id

  | Ppopl_RA (rd) ->
      fprintf oc "	popl	%a\n" ireg rd
  | Ppushl_RA (rd) ->
      fprintf oc "	pushl	%a\n" ireg rd
  | PELFLOAD ->
      fprintf oc "	jmp    __elf_load\n"
  | Pmov_rm_nop (rd, a) ->
      fprintf oc ""
  | Pmov_rm_nop_RA (a) -> 
      fprintf oc ""
  | Ptss_switch ->
      fprintf oc "	call    tss_switch\n" 
  | Prdmsr ->
      fprintf oc "\trdmsr\n"
  | Pwrmsr ->
      fprintf oc "\twrmsr\n"
  | Prcr0 rd ->
      fprintf oc "\tmovl\t%%cr0, %a\n" ireg rd
  | Prcr3 rd ->
      fprintf oc "\tmovl\t%%cr3, %a\n" ireg rd
  | Prcr4 rd ->
      fprintf oc "\tmovl\t%%cr4, %a\n" ireg rd
  | Pvmptrld id ->
      if target = MacOS then begin
        let id = extern_atom id in
        indirect_symbols := StringSet.add id !indirect_symbols;
        fprintf oc "\tvmptrld\tL%a$non_lazy_ptr\n" raw_symbol id
      end else
        fprintf oc "\tvmptrld\t%a\n" symbol id
  | Pvmread (id, rd, rs) ->
      fprintf oc "\tvmread\t%a, %a\n" ireg rd ireg rs
  | Pvmwrite (id, rd, rs) ->
      fprintf oc "\tvmwrite\t%a, %a\n" ireg rd ireg rs
  | Pinvept (rd, a) ->
      fprintf oc "\tinvept\t%a, %a\n" addressing a ireg rd
  | Pvmx_load_guest ->
      fprintf oc "\tjmp __vmx_load_guest\n"
  | Pvmx_store_guest ->
      fprintf oc "\tjmp __vmx_store_guest\n"

(** END LAsm pseudo-instructions *)

let print_function oc name fn =
  Hashtbl.clear current_function_labels;
  float_literals := [];
  jumptables := [];
  current_function_sig := fn.fn_sig;
  let (text, lit, jmptbl) =
    match C2C.atom_sections name with
    | [t;l;j] -> (t, l, j)
    |    _    -> (Section_text, Section_literal, Section_jumptable) in
  section oc text;
  let alignment =
    match !Clflags.option_falignfunctions with Some n -> n | None -> 16 in
  print_align oc alignment;
  if not (C2C.atom_is_static name) then
    fprintf oc "	.globl %a\n" symbol name;
  fprintf oc "%a:\n" symbol name;
  print_location oc (C2C.atom_location name);
  cfi_startproc oc;
  List.iter (print_instruction oc) fn.fn_code;
  cfi_endproc oc;
  if target = ELF then begin
    fprintf oc "	.type	%a, @function\n" symbol name;
    fprintf oc "	.size	%a, . - %a\n" symbol name symbol name
  end;
  if !float_literals <> [] then begin
    section oc lit;
    print_align oc 8;
    List.iter (print_literal oc) !float_literals;
    float_literals := []
  end;
  if !jumptables <> [] then begin
    section oc jmptbl;
    print_align oc 4;
    List.iter (print_jumptable oc) !jumptables;
    jumptables := []
  end

let atom_alignof a =
  (* Hard-coded page-aligned glabol variables *)
  if a = coq_PTPool_LOC || a = coq_IDPMap_LOC || a = coq_EPT_LOC ||
     a = coq_VMCS_LOC then Some 4096
  else None

let init_size init =
  match init with
  | Init_space sz -> Z.to_int sz
  | Init_int32 n -> 4 (* Need an assert n == 0 *)
  | _ -> assert false

let print_var oc name v =
  match v.gvar_init with
  | [] -> ()
  | _  ->
      let sec =
        match C2C.atom_sections name with
        | [s] -> s
        |  _  -> Section_data true
      and align =
        match atom_alignof name with
        | Some a -> a
        | None -> 8 in (* 8-alignment is a safe default *)
      let name_sec =
        name_of_section sec in
      if name_sec = ".data" then begin
        fprintf oc "	%s\n" name_sec;
        let sz =
          string_of_int (List.fold_left (fun x y -> x + init_size y) 0 v.gvar_init) in
        if C2C.atom_is_static name then
          fprintf oc "	.local	%a\n" symbol name;
        fprintf oc "	.comm	%a, %s, %d\n"
          symbol name
          sz
          align;
        if target = ELF then begin
          fprintf oc "	.type	%a, @object\n" symbol name;
        end
      end else if name_sec <> "COMM" then begin
        fprintf oc "	%s\n" name_sec;
        print_align oc align;
        if not (C2C.atom_is_static name) then
          fprintf oc "	.globl	%a\n" symbol name;
        fprintf oc "%a:\n" symbol name;
        print_init_data oc name v.gvar_init;
        if target = ELF then begin
          fprintf oc "	.type	%a, @object\n" symbol name;
          fprintf oc "	.size	%a, . - %a\n" symbol name symbol name
        end
      end else begin
        let sz =
          match v.gvar_init with [Init_space sz] -> sz | _ -> assert false in
        if C2C.atom_is_static name then
          fprintf oc "	.local	%a\n" symbol name;
        fprintf oc "	.comm	%a, %s, %d\n"
          symbol name
          (Z.to_string sz)
          align
      end

let print_globdef oc (name, gdef) =
  match gdef with
  | Some (Gfun(Internal code)) -> print_function oc name code
  | Some (Gfun(External ef)) -> ()
  | Some (Gvar v) -> print_var oc name v
  | None -> ()

let print_program oc p =
  PrintAnnot.print_version_and_options oc comment;
  need_masks := false;
  indirect_symbols := StringSet.empty;
  Hashtbl.clear filename_num;
  List.iter (print_globdef oc) p.prog_defs;
  if !need_masks then begin
    section oc Section_const;  (* not Section_literal because not 8-bytes *)
    print_align oc 16;
    fprintf oc "%a:	.quad   0x8000000000000000, 0\n"
               raw_symbol "__negd_mask";
    fprintf oc "%a:	.quad   0x7FFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF\n"
               raw_symbol "__absd_mask"
  end;
  if target = MacOS then begin
    fprintf oc "	.section __IMPORT,__pointers,non_lazy_symbol_pointers\n";
    StringSet.iter
      (fun s ->
        fprintf oc "L%a$non_lazy_ptr:\n" raw_symbol s;
        fprintf oc "	.indirect_symbol %a\n" raw_symbol s;
        fprintf oc "	.long	0\n")
      !indirect_symbols
  end
