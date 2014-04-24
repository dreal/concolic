open Cil
open Batteries
open IO
open Smt2_cmd
open Basic
open Int64
open Vcmap

type expr =
  | E of Basic.exp
  | F of Basic.formula

let is_exp e =
  match e with
  | E _ -> true
  | _ -> false

let extract_exp e =
  match e with
  | E e1 -> e1
  | _ -> failwith "error"

let is_formula e =
  not (is_exp e)

let extract_formula e =
  match e with
  | F f -> f
  | _ -> failwith "error"

let is_gfun e =
  match e with
  | GFun _ -> true
  | _ -> false

let all f bs =
  List.length (List.filter f bs) != 0

let any f bs =
  not (all f bs)

let gensym : unit -> string =
  let i = ref zero in
  fun () ->
  begin
    i := add !i one;
    string_of_int (Int64.to_int !i)
  end

class removeUnnecessaryCodeVisitor =
  object(self)
    inherit nopCilVisitor as super
    method vstmt stmt  =
      match stmt.skind with
     | Instr ins ->
        DoChildren
     | Block b ->
        DoChildren
     | If _ ->
        DoChildren
     | Return _
     | Goto _
     | Break _
     | Continue _
     | Switch _
     | Loop _
     | TryFinally _
     | TryExcept _
     | ComputedGoto _ ->
        ChangeTo Cil.invalidStmt
  end

let debug = ref false

let rec translation file_name=
  let cil_file = Frontc.parse file_name () in
  visitCilFile (new removeUnnecessaryCodeVisitor) cil_file;
  begin
    match !debug with
    | true ->
      dumpFile defaultCilPrinter Pervasives.stdout "codegen" cil_file;
    | _ -> ();
  end;
  let globals = List.filter is_gfun cil_file.globals in
  let exprs = List.flatten (List.map translate_function globals) in
  match (all is_formula exprs) with
  | true ->
    Basic.make_and (List.map extract_formula exprs)
  | false -> failwith "not all are formula"

and translate_function f : expr list =
  match f with
  | GFun (fd, _) -> translate_blocks [fd.sbody]
  | _ -> failwith "should be function"

and translate_blocks blocks : expr list =
  let translate_block block =
    translate_stmts block.bstmts
  in
  List.flatten (List.map translate_block blocks)

and translate_stmts stmts : expr list =
  let translate_stmt stmt =
    translate_stmtkinds [stmt.skind]
  in
  List.flatten (List.map translate_stmt stmts)

and translate_stmtkinds skinds : expr list =
  let translate_stmtkind sk =
    match sk with
    | Instr ins ->
      translate_instrs ins
    | Return _ -> failwith "not now return"
    | Goto _ -> failwith "not now goto"
    | Break _ -> failwith "not now break"
    | Continue _ -> failwith "not now continue"
    | If (be, e1, e2, _)->
      let be' = translate_exps [be] in
      let e1' = translate_blocks [e1] in
      let e2' = translate_blocks [e2] in
      begin
      match (all is_formula be'), (all is_formula (e1' @ e2')) with
      | true, true ->
         let F be = List.hd be' in
         let es1 = List.map extract_formula e1' in
         let es2 = List.map extract_formula e2' in
         [F (
             Basic.make_and
               [ Basic.make_or [be; Basic.make_and es1]; Basic.make_or [Basic.Not be; Basic.make_and es2]]
           )]
      | _ -> failwith "should all be formula"
      end
    | Switch _ -> failwith "not now switch"
    | Loop _ -> failwith "not now loop"
    | Block b ->
       translate_blocks [b]
    | TryFinally _ -> failwith "not now try"
    | TryExcept _ -> failwith "not now try"
    | ComputedGoto _ -> failwith "not now comput goto"
  in
  List.flatten (List.map translate_stmtkind skinds)

and translate_exps exps : expr list =
  let translate_exp (e : Cil.exp) =
    match e with
    | Const c -> E (translate_const c)
    | Lval lval ->
       E (translate_lval lval)
    | SizeOf _ -> failwith "not now sizeof"
    | SizeOfE _ -> failwith "not now sizeof"
    | SizeOfStr _ -> failwith "not now sizeof"
    | AlignOf _ -> failwith "not now align"
    | AlignOfE _ -> failwith "not now align"
    | AddrOfLabel _ -> failwith "not now align"
    | UnOp (uop, e, _) ->
      begin
        let e' = List.hd (translate_exps [e]) in
        match uop with
        | Neg ->
          begin
            match e' with
            | E e'' -> E (Basic.Neg e'')
            | _ -> failwith "should be an expression"
          end
        | BNot -> failwith "todo"
        | LNot ->
          begin
            match e' with
            | E e'' -> failwith "should be a formula"
            | F e'' -> F (Basic.Not e'')
          end
      end
    | BinOp (bop, e1, e2, _) ->
        begin
          let e1' = List.hd (translate_exps [e1]) in
          let e2' = List.hd (translate_exps [e2]) in
          match bop with
          | PlusA ->
             begin
              match all is_exp [e1'; e2'] with
              | true ->
                let E e1' = e1' in
                let E e2' = e2' in
                E (Basic.Add [e1'; e2'])
              | false -> failwith "not all expression"
            end
          | PlusPI  -> failwith "not now plus"
          | IndexPI -> failwith "not now index"
          | MinusA ->
            begin
              match all is_exp [e1'; e2'] with
              | true ->
                let E e1' = e1' in
                let E e2' = e2' in
                E (Basic.Sub [e1'; e2'])
              | false -> failwith "not all expression"
            end
          | MinusPI -> failwith "not now minus"
          | MinusPP -> failwith "not now minus"
          | Mult ->
            begin
              match all is_exp [e1'; e2'] with
              | true ->
                let E e1' = e1' in
                let E e2' = e2' in
                E (Basic.Mul [e1'; e2'])
              | false -> failwith "not all expression"
            end
          | Div ->
            begin
              match all is_exp [e1'; e2'] with
              | true ->
                let E e1' = e1' in
                let E e2' = e2' in
                E (Basic.Div (e1', e2'))
              | false -> failwith "not all expression"
            end
          | Mod -> failwith "not now mod"
          | Shiftlt -> failwith "not now shift"
          | Shiftrt -> failwith "not now shift"
          | Lt ->
            begin
              match all is_exp [e1'; e2'] with
              | true ->
                let E f1 = e1' in
                let E f2 = e2' in
                F (Basic.Lt (f1, f2))
              | _ -> failwith "not all formula"
            end
          | Gt ->
            begin
              match all is_exp [e1'; e2'] with
              | true ->
                let E f1 = e1' in
                let E f2 = e2' in
                F (Basic.Gt (f1, f2))
              | _ -> failwith "not all formula"
            end
          | Le ->
            begin
              match all is_exp [e1'; e2'] with
              | true ->
                let E f1 = e1' in
                let E f2 = e2' in
                F (Basic.Le (f1, f2))
              | _ -> failwith "not all formula"
            end
          | Ge ->
            begin
              match all is_exp [e1'; e2'] with
              | true ->
                let E f1 = e1' in
                let E f2 = e2' in
                F (Basic.Ge (f1, f2))
              | _ -> failwith "not all formula"
            end
          | Eq ->
            begin
              match all is_exp [e1'; e2'] with
              | true ->
                let E f1 = e1' in
                let E f2 = e2' in
                F (Basic.Eq (f1, f2))
              | _ -> failwith "not all formula"
            end
          | Ne ->
            begin
              match all is_exp [e1'; e2'] with
              | true ->
                let E f1 = e1' in
                let E f2 = e2' in
                F (Basic.Eq (f1, f2))
              | _ -> failwith "not all formula"
            end
          | BAnd -> failwith ""
          | BXor -> failwith ""
          | BOr -> failwith ""
          | LAnd ->
            begin
              match all is_formula [e1'; e2'] with
              | true ->
                let F f1 = e1' in
                let F f2 = e2' in
                F (Basic.And [f1; f2])
              | _ -> failwith "not all formula"
            end
          | LOr ->
            begin
              match all is_formula [e1'; e2'] with
              | true ->
                let F f1 = e1' in
                let F f2 = e2' in
                F (Basic.Or [f1; f2])
              | _ -> failwith "not all formula"
            end
        end
    | CastE (_, e) ->
      begin
        let e = translate_exps [e] in
        match all is_exp e with
        | true ->
          List.hd e
        | false -> failwith "not a expression for caste"
      end
    | AddrOf _ -> failwith "not now addrOf"
    | StartOf _ -> failwith "not now startOf"
    | Question _ -> failwith "not now question"
  in
  List.map translate_exp exps


and translate_instrs ins : expr list =
  let translate_inst ins =
    match ins with
    | Set (lval, e, _) ->
      let lval = translate_lval lval in
      let e' = List.hd (translate_exps [e]) in
      begin
        match e' with
        | E e' -> F (Basic.Eq (lval, e'))
        | _ -> failwith "should be an expression"
      end
    | Call _ -> failwith "not now call"
    | Asm _ -> failwith "not now asm"
  in
  List.map translate_inst ins

and translate_lval l : Basic.exp =
  let (lhost, _) = l in
  match lhost with
  | Var vi -> Basic.Var (vi.vname)
  | _ -> failwith "not now (translate_lval)"

and translate_const (c : Cil.constant) =
  match c with
  | CInt64 (i, _, _) ->
    Basic.Num (to_float i)
  | CStr _ -> failwith "not now string"
  | CWStr _ -> failwith "not now CWStr"
  | CChr _ -> failwith "not now char"
  | CReal (f, _, _) -> Basic.Num f
  | CEnum _ -> failwith "not now enum"

let spec = []
let usage = "Usage: cil2smt.native [<options>] <.c>\n<options> are: "

let run () =
  let src = ref "" in
  let _ = Arg.parse spec
      (fun x -> if Sys.file_exists x then src := x
        else raise (Arg.Bad (x^": No such file"))) usage in
  let f = translation !src in
  let vars = Set.to_list (collect_vars_in_formula f) in
  let var_decls = List.map (fun v -> DeclareFun v) vars in
  let logic_cmd = SetLogic QF_NRA in
  let out = IO.stdout in
  Smt2.print out
    (List.flatten
       [[logic_cmd];
        var_decls;
        [Assert f;
         CheckSAT;
         Exit]])

let _ = run ()
