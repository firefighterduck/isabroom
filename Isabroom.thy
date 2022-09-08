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
| Malloc var var
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

abbreviation can_allocate_from :: "blocks \<Rightarrow> loc \<Rightarrow> blockname \<Rightarrow> val \<Rightarrow> bool" where
  "can_allocate_from B l n z \<equiv>
    0<l \<and> \<comment> \<open>The location is not at null.\<close>
    l < l + (loc64_ops.from_val z) \<and> \<comment> \<open>The allocated block does not wrap around.\<close>
    \<comment> \<open>It doesn't overlap with any other block.\<close>
    (\<forall>b\<in>set (raw_blocks B). \<not>(overlaps_with (n,l,l + (loc64_ops.from_val z)) b)) \<and>
    (\<forall>b\<in>set (raw_blocks B). (case b of (n',_,_) \<Rightarrow> n'\<noteq>n)) \<comment> \<open>The name is new and unique\<close>"

inductive semantics :: "pre_config \<Rightarrow> 'a command \<Rightarrow> pre_config option \<Rightarrow> bool" where
  "fits k x \<Longrightarrow> semantics (S,B,M) (AssignConst x k) (Some (Stack ((lookup S)(x:=k)),B,M))"
| "size x = size y \<Longrightarrow> semantics (S,B,M) (AssignVar x y) (Some (Stack ((lookup S)(x:=lookup S y)),B,M))"
| LoadFail: 
  "\<comment> \<open>y does not point into any block, i.e. is an invalid location\<close>
  base B (loc64_ops.from_val (lookup S y)) = 0 \<or>
  \<comment> \<open>This load would read past the end of the block.\<close>
  ((loc64_ops.from_val (lookup S y)) + (sizev x) > ende B (loc64_ops.from_val (lookup S y)) \<or> 
  \<comment> \<open>This would read past the maximum location and wrap around.\<close>
  (loc64_ops.from_val (lookup S y)) + (sizev x) \<le> (loc64_ops.from_val (lookup S y))) \<Longrightarrow>
     semantics (S,B,M) (Load x y) None"
| LoadSuccess: "\<lbrakk>\<not>(base B (loc64_ops.from_val (lookup S y)) = 0 \<or> 
  ((loc64_ops.from_val (lookup S y)) + (sizev x) > ende B (loc64_ops.from_val (lookup S y)) \<or>
  (loc64_ops.from_val (lookup S y)) + (sizev x) \<le> (loc64_ops.from_val (lookup S y))));
  \<comment> \<open>The addressed memory cells are actually allocated.\<close>
  access M (loc64_ops.from_val (lookup S y)) (size x) = Some v\<rbrakk> \<Longrightarrow> 
    semantics (S,B,M) (Load x y) (Some (Stack ((lookup S)(x:=v)), B, M))"
| StoreFail:
  "\<comment> \<open>x does not point into any block, i.e. is an invalid location\<close>
  base B (loc64_ops.from_val (lookup S x)) = 0 \<or>
  \<comment> \<open>This store woudl write past the end of the block.\<close>
  ((loc64_ops.from_val (lookup S x)) + (sizev y) > ende B (loc64_ops.from_val (lookup S x)) \<or> 
  \<comment> \<open>This would write past the maximum location and wrap around.\<close>
  (loc64_ops.from_val (lookup S x)) + (sizev y) \<le> (loc64_ops.from_val (lookup S x))) \<Longrightarrow>
    semantics (S,B,M) (Store x y) None"
| StoreSuccess: "\<not>(base B (loc64_ops.from_val (lookup S x)) = 0 \<or> 
  ((loc64_ops.from_val (lookup S x)) + (sizev y) > ende B (loc64_ops.from_val (lookup S x)) \<or>
  (loc64_ops.from_val (lookup S x)) + (sizev y) \<le> (loc64_ops.from_val (lookup S x)))) \<Longrightarrow> 
    semantics (S,B,M) (Store x y) (Some (S, B, update_memory M (loc64_ops.from_val (lookup S x)) (lookup S y)))"
| MallocError: "
  \<comment> \<open>If we would allocate 0 bytes or x can't hold a pointer.\<close>
  (\<forall>v\<in>set (lookup S z). v = 0) \<or> (size x \<noteq> loc_N_B) \<Longrightarrow> 
  semantics (S,_,_) (Malloc x z) None"
| MallocSuccessNull: "\<lbrakk>\<exists>v\<in>set (lookup S z). v \<noteq> 0; size x = loc_N_B\<rbrakk> \<Longrightarrow>
  semantics (S,B,M) (Malloc x z) (Some (Stack ((lookup S)(x:=null x)),B,M))"
| MallocSuccess: "\<lbrakk>\<exists>v\<in>set (lookup S z). v \<noteq> 0; size x = loc_N_B;
  \<comment> \<open>l and n are new, k is arbitrary\<close>
  can_allocate_from B l n (lookup S z); length k = length (lookup S z)\<rbrakk> \<Longrightarrow>
  semantics (S,B,M) (Malloc x z) 
    (Some (Stack ((lookup S)(x:=loc64_ops.to_val l)), 
    Blocks ((n,l,l+(loc64_ops.from_val (lookup S z)))#raw_blocks B),
    update_memory M l k))"

end