theory Isabroom
  imports Model
begin

typedecl binop
axiomatization apply_binop :: "binop \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val"
typedecl unop
axiomatization apply_unop :: "unop \<Rightarrow> val \<Rightarrow> val"
datatype condition = Eq | Neq | Leq | Le | Geq | Gr

fun eval_cond_aux :: "val \<Rightarrow> val \<Rightarrow> (byte \<Rightarrow> byte \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> bool" where
  "eval_cond_aux [] [] _ b = b"
| "eval_cond_aux [] _ _ _ = undefined"
| "eval_cond_aux _ [] _ _ = undefined"
| "eval_cond_aux (v1#xs) (v2#ys) c b = (if v1=v2 then eval_cond_aux xs ys c b
    else c v1 v2)"

fun eval_cond :: "condition \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" where
  "eval_cond Eq v1 v2 = (v1=v2)"
| "eval_cond Neq v1 v2 = (v1\<noteq>v2)"
| "eval_cond Leq v1 v2 = eval_cond_aux v1 v2 (\<le>) True"
| "eval_cond Le v1 v2 = eval_cond_aux v1 v2 (<) False"
| "eval_cond Geq v1 v2 = eval_cond_aux v1 v2 (\<ge>) True"
| "eval_cond Gr v1 v2 = eval_cond_aux v1 v2 (>) False"

type_synonym 'a func = "string \<times> var list \<times> 'a option"

datatype 'a command =
  AssignConst var val 
| AssignVar var var
| Load var var
| Store var var
| Malloc var var
| Free var
| BinOp binop var var var
| UnOp unop var var
| PtrPlus var var var
| PtrSub var var var
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

context fixes cfg_lookup :: "string \<Rightarrow> pre_config \<Rightarrow> pre_config \<Rightarrow> bool" begin
inductive semantics :: "pre_config \<Rightarrow> 'a command \<Rightarrow> pre_config option \<Rightarrow> bool"
  where
  "fits k x \<Longrightarrow> semantics (S,B,M) (AssignConst x k) (Some (update_stack S x k,B,M))"
| "size x = size y \<Longrightarrow> semantics (S,B,M) (AssignVar x y) (Some (update_stack S x (lookup S y),B,M))"
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
    semantics (S,B,M) (Load x y) (Some (update_stack S x v, B, M))"
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
  semantics (S,B,M) (Malloc x z) (Some (update_stack S x (null x),B,M))"
| MallocSuccess: "\<lbrakk>\<exists>v\<in>set (lookup S z). v \<noteq> 0; size x = loc_N_B;
  \<comment> \<open>l and n are new, k is arbitrary\<close>
  can_allocate_from B l n (lookup S z); length k = length (lookup S z)\<rbrakk> \<Longrightarrow>
  semantics (S,B,M) (Malloc x z) 
    (Some (update_stack S  x (loc64_ops.to_val l), 
    Blocks ((n,l,l+(loc64_ops.from_val (lookup S z)))#raw_blocks B),
    update_memory M l k))"
| FreeError: "loc64_ops.from_val (lookup S x) \<noteq> base B (loc64_ops.from_val (lookup S x))
  \<Longrightarrow> semantics (S,B,_) (Free x) None"
| FreeSuccess: "\<lbrakk>loc64_ops.from_val (lookup S x) = y; y = base B y\<rbrakk>
  \<Longrightarrow> semantics (S,B,M) (Free x) (Some (S,free_block B y, free_memory M y (ende B y)))"
| "semantics (S,B,M) (BinOp b x y z) 
  (Some (update_stack S x (apply_binop b (lookup S y) (lookup S z)),B,M))"
| "semantics (S,B,M) (UnOp u x y) 
  (Some (update_stack S x (apply_unop u (lookup S y)),B,M))"
| PtrPlusError: "\<lbrakk>y'=loc64_ops.from_val (lookup S y); z'=loc64_ops.from_val (lookup S z);
  (\<forall>v\<in>set (lookup S y). v = 0) \<or> (y' + z' < base B y') \<or> (y' + z' > ende B y')\<rbrakk>
  \<Longrightarrow> semantics (S,B,M) (PtrPlus _ y z) None"
| PtrPlusSuccess: "\<lbrakk>y'=loc64_ops.from_val (lookup S y); z'=loc64_ops.from_val (lookup S z);
  \<exists>v\<in>set (lookup S y). v \<noteq> 0; y' + z' \<ge> base B y'; y' + z' \<le> ende B y'\<rbrakk>
  \<Longrightarrow> semantics (S,B,M) (PtrPlus x y z) (Some (update_stack S x (loc64_ops.to_val (y'+z')),B,M))"
| PtrSubError: "\<lbrakk>y'=loc64_ops.from_val (lookup S y); z'=loc64_ops.from_val (lookup S z);
  (\<forall>v\<in>set (lookup S y). v = 0) \<or> (from_block y' B \<noteq> from_block z' B)\<rbrakk>
  \<Longrightarrow> semantics (S,B,M) (PtrSub _ y z) None"
| PtrSubSuccess: "\<lbrakk>y'=loc64_ops.from_val (lookup S y); z'=loc64_ops.from_val (lookup S z);
  \<exists>v\<in>set (lookup S y). v \<noteq> 0; from_block y' B = from_block z' B\<rbrakk>
  \<Longrightarrow> semantics (S,B,M) (PtrSub x y z) (Some (update_stack S x (loc64_ops.to_val (y'-z')),B,M))"
| MemcpyError: "\<lbrakk>y'=loc64_ops.from_val (lookup S y); z'=loc64_ops.from_val (lookup S z);
  x'=loc64_ops.from_val (lookup S x);
  \<comment> \<open>x or y do not point into any block, i.e. is an invalid location\<close>
  from_block x' B = None \<or> from_block y' B = None \<or>
  \<comment> \<open>The size is too big, i.e. we would read/write out of bounds\<close>
  x'+z' > ende B x' \<or> y'+z' > ende B y' \<or>
  \<comment> \<open>The two memory portions (pointer+size) overlap\<close>
  intv (x'+z') (bounds (raw_blocks B) y') \<or> intv (y'+z') (bounds (raw_blocks B) x')\<rbrakk> 
  \<Longrightarrow> semantics (S,B,M) (Memcpy x y z) None"
| MemcpySuccess: "\<lbrakk>y'=loc64_ops.from_val (lookup S y); z'=loc64_ops.from_val (lookup S z);
  from_block x' B \<noteq> None; from_block y' B \<noteq> None; x'+z' \<le> ende B x'; y'+z' \<le> ende B y';
  \<not>(intv (x'+z') (bounds (raw_blocks B) y')); \<not>(intv (y'+z') (bounds (raw_blocks B) x'));
  access M y' (unat z') = Some v\<rbrakk>
  \<Longrightarrow> semantics (S,B,M) (Memcpy x y z) (Some (S,B,update_memory M x' v))"
| "eval_cond c (lookup S x) (lookup S y) \<Longrightarrow> semantics (S,B,M) (Assume c x y) (Some (S,B,M))"
| AssertError: "\<not> eval_cond c (lookup S x) (lookup S y) \<Longrightarrow> semantics (S,B,M) (Assert c x y) None"
| AssertSuccess: "eval_cond c (lookup S x) (lookup S y) \<Longrightarrow> semantics (S,B,M) (Assert c x y) (Some (S,B,M))"
| "\<lbrakk>distinct args; length args = length params; list_all2 (\<lambda>a p. size a = size p) args params;
  cfg_lookup f (Stack (bind_args_to_params (lookup S) params args),B,M) (S',B',M')\<rbrakk>
  \<Longrightarrow> semantics (S,B,M) (Call (f,params,_) args) 
    (Some (Stack (bind_args_to_params (lookup S') args params),B',M'))"

abbreviation cfg_step :: "'a edge \<Rightarrow> pre_config \<Rightarrow> pre_config \<Rightarrow> bool" where
  "cfg_step e pre post \<equiv> semantics pre (fst (snd e)) (Some post)"

abbreviation cfg_step_find :: "'a edge set \<Rightarrow> CFG_node \<Rightarrow> CFG_node  \<Rightarrow> pre_config \<Rightarrow> pre_config \<Rightarrow> bool" where
  "cfg_step_find es from to pre post \<equiv> \<exists>cmd. (from,cmd,to) \<in> es \<and> semantics pre cmd (Some post)"

inductive cfg_reachable :: "'a edge set \<Rightarrow> CFG_node \<Rightarrow> CFG_node \<Rightarrow> pre_config \<Rightarrow> pre_config \<Rightarrow> bool" where
  SingleStep: "cfg_step_find es from to pre post \<Longrightarrow> cfg_reachable es from to pre post"
| MultiStep: "\<lbrakk>cfg_step_find es from to' pre interm; cfg_reachable es to' to interm post\<rbrakk>
  \<Longrightarrow> cfg_reachable es from to pre post"

abbreviation cfg_semantics :: "'a cfg \<Rightarrow> pre_config \<Rightarrow> pre_config \<Rightarrow> bool" where
  "cfg_semantics cfg pre post \<equiv> cfg_reachable (snd cfg) entry exit pre post"
end

fun find_fun :: "(string \<rightharpoonup> 'a cfg) \<Rightarrow> string \<Rightarrow> pre_config \<Rightarrow> pre_config \<Rightarrow> bool" where
  "find_fun funs f pre post = 
    (case (funs f) of Some cfg \<Rightarrow> cfg_semantics (find_fun funs) cfg pre post
    | None \<Rightarrow> False)"

definition program_semantics :: "(string \<rightharpoonup> 'a cfg) \<Rightarrow> 'a cfg \<Rightarrow> pre_config \<Rightarrow> pre_config \<Rightarrow> bool" where
  "program_semantics funs cfg pre post = 
  cfg_semantics 
    (\<lambda>name pre post. case (funs name) of Some cfg \<Rightarrow> cfg_semantics cfg pre post | None \<Rightarrow> False)
  cfg pre post"

end