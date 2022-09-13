theory Semantics
imports Model
begin
typedecl binop
axiomatization apply_binop :: "binop \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val"
  and plus :: binop
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

text \<open>Given a control flow graph as a map from function names to their body graphs, 
  relate the semantics of the program. The program implicitly starts at ''main''.\<close>
context fixes funs :: "string \<Rightarrow> 'a cfg option" begin
inductive semantics :: "pre_config \<Rightarrow> 'a command \<Rightarrow> pre_config option \<Rightarrow> bool"
  and fun_semantics :: "string \<Rightarrow> pre_config \<Rightarrow> pre_config \<Rightarrow> bool"
  and cfg_reachable :: "'a edge set \<Rightarrow> CFG_node \<Rightarrow> CFG_node \<Rightarrow> pre_config \<Rightarrow> pre_config \<Rightarrow> bool" where
  SingleStep: "\<lbrakk>\<exists>cmd. (from,cmd,to) \<in> es; semantics pre cmd (Some post)\<rbrakk> \<Longrightarrow> cfg_reachable es from to pre post"
| MultiStep: "\<lbrakk>\<exists>cmd. (from,cmd,to') \<in> es; semantics pre cmd (Some interm); 
  cfg_reachable es to' to interm post\<rbrakk> \<Longrightarrow> cfg_reachable es from to pre post"
| "\<lbrakk>(funs f) = Some cfg; cfg_reachable (snd cfg) entry exit pre post\<rbrakk> \<Longrightarrow> fun_semantics f pre post"
|  "fits k x \<Longrightarrow> semantics (S,B,M) (AssignConst x k) (Some (update_stack S x k,B,M))"
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
  fun_semantics f (Stack (bind_args_to_params (lookup S) params args),B,M) (S',B',M')\<rbrakk>
  \<Longrightarrow> semantics (S,B,M) (Call (f,params,_) args) 
    (Some (Stack (bind_args_to_params (lookup S') args params),B',M'))"
end

abbreviation program_semantics :: "(string \<Rightarrow> 'a cfg option) \<Rightarrow> pre_config \<Rightarrow> bool" where
  "program_semantics program post \<equiv> fun_semantics program ''main'' initial post"

lift_definition program_semantics_config :: "(string \<Rightarrow> 'a cfg option) \<Rightarrow> config \<Rightarrow> bool" is
  "program_semantics" .

abbreviation all_blocks_alloc :: "block list \<Rightarrow> memory \<Rightarrow> bool" where
  "all_blocks_alloc B M \<equiv> list_all (\<lambda>(n,l,u). \<forall>x. intv x (l,u) \<longrightarrow> M x \<noteq> None) B"

lift_definition blocks_alloc :: "blocks \<Rightarrow> memory \<Rightarrow> bool" is all_blocks_alloc .

abbreviation config_blocks_alloc :: "pre_config \<Rightarrow> bool" where
  "config_blocks_alloc \<equiv> \<lambda>(_,B,M). blocks_alloc B M"

lemma assumes "config_blocks_alloc pre"
  shows "(semantics pr pre cmd (Some post) \<longrightarrow> config_blocks_alloc post) \<and>
    (fun_semantics pr f pre post \<longrightarrow> config_blocks_alloc post) \<and>
    (cfg_reachable pr es from to pre post \<longrightarrow> config_blocks_alloc post)"
proof (induction rule: semantics_fun_semantics_cfg_reachable.induct)
  case (SingleStep "from" to es pre cmd post)
  then show ?case sorry
next
  case (MultiStep "from" to' es pre cmd interm to post)
  then show ?case sorry
next
  case (LoadFail B S y x M)
  then show ?case sorry
next
  case (LoadSuccess B S y x M v)
  then show ?case sorry
next
  case (StoreFail B S x y M)
  then show ?case sorry
next
  case (StoreSuccess B S x y M)
  then show ?case sorry
next
  case (MallocError S z x uu uv)
  then show ?case sorry
next
  case (MallocSuccessNull S z x B M)
  then show ?case sorry
next
  case (MallocSuccess S z x B l n k M)
  then show ?case sorry
next
  case (FreeError S x B uw)
  then show ?case sorry
next
  case (FreeSuccess S x y B M)
  then show ?case sorry
next
  case (PtrPlusError y' S y z' z B M ux)
  then show ?case sorry
next
  case (PtrPlusSuccess y' S y z' z B M x)
  then show ?case sorry
next
  case (PtrSubError y' S y z' z B M uy)
  then show ?case sorry
next
  case (PtrSubSuccess y' S y z' z B M x)
  then show ?case sorry
next
  case (MemcpyError y' S y z' z x' x B M)
  then show ?case sorry
next
  case (MemcpySuccess y' S y z' z x' B M v x)
  then show ?case sorry
next
  case (AssertError c S x y B M)
  then show ?case sorry
next
  case (AssertSuccess c S x y B M)
  then show ?case sorry
qed oops

lemma assumes "config_def pre"
  shows "(semantics pr pre cmd (Some post) \<longrightarrow> config_def post) \<and>
    (fun_semantics pr f pre post \<longrightarrow> config_def post) \<and>
    (cfg_reachable pr es from to pre post \<longrightarrow> config_def post)"
proof (induction rule: semantics_fun_semantics_cfg_reachable.induct)
  case (SingleStep "from" to es pre cmd post')
  then show ?case sorry
next
  case (MultiStep "from" to' es pre cmd interm to post)
  then show ?case sorry
next
  case (LoadFail B S y x M)
  then show ?case sorry
next
  case (LoadSuccess B S y x M v)
  then show ?case sorry
next
  case (StoreFail B S x y M)
  then show ?case sorry
next
  case (StoreSuccess B S x y M)
  then show ?case sorry
next
  case (MallocError S z x uu uv)
  then show ?case sorry
next
  case (MallocSuccessNull S z x B M)
  then show ?case sorry
next
  case (MallocSuccess S z x B l n k M)
  then show ?case sorry
next
  case (FreeError S x B uw)
  then show ?case sorry
next
  case (FreeSuccess S x y B M)
  then show ?case sorry
next
  case (PtrPlusError y' S y z' z B M ux)
  then show ?case sorry
next
  case (PtrPlusSuccess y' S y z' z B M x)
  then show ?case sorry
next
  case (PtrSubError y' S y z' z B M uy)
  then show ?case sorry
next
  case (PtrSubSuccess y' S y z' z B M x)
  then show ?case sorry
next
  case (MemcpyError y' S y z' z x' x B M)
  then show ?case sorry
next
  case (MemcpySuccess y' S y z' z x' B M v x)
  then show ?case sorry
next
  case (AssertError c S x y B M)
  then show ?case sorry
next
  case (AssertSuccess c S x y B M)
  then show ?case sorry
qed oops

end