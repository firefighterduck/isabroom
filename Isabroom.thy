theory Isabroom
  imports Model
begin

typedecl binop
typedecl unop
datatype condition = Eq | Neq | Leq | Le | Geq | Gr
type_synonym 'a func = "string \<times> nat \<times> 'a option"

datatype 'a command =
  AssignConst var val 
| AssignVar var var
| Load var var
| Store var var
| Malloc var
| Free var
| BinOp binop var var
| UnOp unop var
| PtrPlus var var
| PtrSub var var
| Memcpy (dest: var) (source: var) (number: var)
| Assume condition var var
| Assert condition var var
| Call "'a func" "var list"

subsection \<open>CFG\<close>

typedecl CFG_node
axiomatization entry :: CFG_node and exit :: CFG_node

type_synonym 'a edge = "CFG_node \<times> 'a command \<times> CFG_node"
type_synonym 'a cfg = "'a func \<times> 'a edge set"

inductive semantics :: "pre_config \<Rightarrow> 'a command \<Rightarrow> pre_config option \<Rightarrow> bool" where
  "fits k x \<Longrightarrow> semantics (S,B,M) (AssignConst x k) (Some (Stack ((lookup s)(x:=k)),B,M))"
| "size x = size y \<Longrightarrow> semantics (S,B,M) (AssignVar x y) (Some (Stack ((lookup s)(x:=lookup s y)),B,M))"
| "base B (loc64_ops.from_val (lookup s y)) = 0 \<or> 
  (loc64_ops.from_val (lookup s y)) + (sizev x) > ende B (loc64_ops.from_val (lookup s y)) \<Longrightarrow>
   semantics (S,B,M) (Load x y) None"
| "\<not>(base B (loc64_ops.from_val (lookup s y)) = 0 \<or> 
  (loc64_ops.from_val (lookup s y)) + (sizev x) > ende B (loc64_ops.from_val (lookup s y))) \<Longrightarrow>
  
  semantics (Stack ((lookup s)(x:=
end