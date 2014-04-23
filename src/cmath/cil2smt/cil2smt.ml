open Cil
open Batteries
open IO
open Smt2_cmd
open Basic

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
  let i = ref 0 in
  fun () ->
  begin
    i := !i + 1;
    string_of_int !i
  end

class removeUnnecessaryCodeVisitor =
  object(self)
    inherit nopCilVisitor as super
    method vstmt stmt  =
      match stmt.skind with
     | Instr ins ->
        DoChildren
     | Return _ ->
        ChangeTo Cil.invalidStmt
     | Goto _ ->
        ChangeTo Cil.invalidStmt
     | Break _ ->
        ChangeTo Cil.invalidStmt
     | Continue _ ->
        ChangeTo Cil.invalidStmt
     | If _ ->
        DoChildren
     | Switch _ ->
        ChangeTo Cil.invalidStmt
     | Loop _ ->
        ChangeTo Cil.invalidStmt
     | Block b ->
        DoChildren
     | TryFinally _ ->
        ChangeTo Cil.invalidStmt
     | TryExcept _ ->
        ChangeTo Cil.invalidStmt
     | ComputedGoto _ ->
        ChangeTo Cil.invalidStmt
  end

class ssaTransformVisitor =
  object(self)
    inherit nopCilVisitor as super
    method vinst ins  =
      match ins with
      | Cil.Set ((host, l), e, l') ->
         begin
           match host with
           | Var vi ->
              vi.vname <- vi.vname ^ (gensym ());
              ChangeTo [Cil.Set ((Var vi, l), e, l')]
           | _ -> DoChildren
         end
      | _ -> DoChildren
  end

let rec translation file_name=
  let cil_file = Frontc.parse file_name () in
  visitCilFile (new removeUnnecessaryCodeVisitor) cil_file;
  visitCilFile (new ssaTransformVisitor) cil_file;
  Simplify.splitStructs := true;
  Simplify.simpleMem := true;
  Simplify.onlyVariableBasics := false;
  List.iter Simplify.doGlobal cil_file.globals;
  dumpFile defaultCilPrinter Pervasives.stdout "codegen" cil_file;
  let globals = List.filter is_gfun cil_file.globals in
  let exprs = List.flatten (List.map translate_function globals) in
  match (all is_formula exprs) with
  | true ->
     Basic.print_formula IO.stdout (Basic.make_and (List.map extract_formula exprs))
  | false -> Printf.printf "not all are formula"


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
               [ Basic.make_and [be; Basic.make_and es1]; Basic.make_and [Basic.Not be; Basic.make_and es2]]
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
    | CastE _ -> failwith "not now"
    | AddrOf _ -> failwith "not now"
    | StartOf _ -> failwith "not now"
    | Question _ -> failwith "not now"
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
    | Call _ -> failwith "todo"
    | Asm _ -> failwith "not now"
  in
  List.map translate_inst ins

and translate_lval l : Basic.exp =
  let (lhost, _) = l in
  match lhost with
  | Var vi -> Basic.Var (vi.vname)
  | _ -> failwith "not now"

and translate_const (c : Cil.constant) =
  match c with
  | CInt64 (i, _, _) -> failwith "not now int 64"
  | CStr _ -> failwith "a string"
  | CWStr _ -> failwith "not now"
  | CChr _ -> failwith "a char"
  | CReal (f, _, _) -> Basic.Num f
  | CEnum _ -> failwith "an enum"


let _ =
  translation "./sin.c"
