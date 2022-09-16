theory Contracts
imports SeparationLogic
begin

fun strip_prenex :: "form \<Rightarrow> (var set \<times> form)" where
  "strip_prenex (Exists x f) = (let (vs,f') = strip_prenex f in (insert x vs,f'))"
| "strip_prenex f = ({},f)"

fun strip_prenexl :: "form \<Rightarrow> (var list \<times> form)" where
  "strip_prenexl (Exists x f) = (let (vs,f') = strip_prenexl f in (x#vs,f'))"
| "strip_prenexl f = ([],f)"

lemma strip_set_list: "\<lbrakk>strip_prenex f = (vset,f'); strip_prenexl f = (vlist, f'')\<rbrakk>
  \<Longrightarrow> vset = set vlist \<and> f'=f''"
proof (induction f arbitrary: vset f' vlist f'')
  case (Exists x1 f)
  obtain vs2 f2 where step2: "strip_prenex f = (vs2,f2)" by fastforce
  obtain vs3 f3 where step3: "strip_prenexl f = (vs3,f3)" by fastforce
  have "strip_prenex (Exists x1 f) = (let (vs2,f2) = strip_prenex f in (insert x1 vs2,f2))" by simp
  with step2 Exists(2) have first: "vset = insert x1 vs2" "f' = f2" by auto
  have "strip_prenexl (Exists x1 f) = (let (vs2,f2) = strip_prenexl f in (x1#vs2,f2))" by simp
  with step3 Exists(3) have "vlist = x1#vs3" "f'' = f3" by auto
  with Exists(1)[OF step2 step3] first show ?case by auto
qed (auto)

fun add_prenex :: "var list \<Rightarrow> form \<Rightarrow> form" where
  "add_prenex [] f = f"
| "add_prenex (v#vs) f = Exists v (add_prenex vs f)"

lemma strip_add_prenexl: 
  "\<lbrakk>strip_prenexl (add_prenex vs f) = (vs',f'); strip_prenexl f = (vs'', f'')\<rbrakk>
  \<Longrightarrow> vs'=vs@vs'' \<and> f'=f''"
proof (induction vs arbitrary: f vs' f' vs'' f'')
  case Nil
  then show ?case by auto
next
  case (Cons a vs)
  obtain vs2 f2 where IHaux: "strip_prenexl (add_prenex vs f) = (vs2,f2)" by fastforce
  have "add_prenex (a#vs) f = (Exists a (add_prenex vs f))" by simp
  then have "strip_prenexl (add_prenex (a#vs) f) = 
    (let (vs2,f2) = strip_prenexl (add_prenex vs f) in (a#vs2,f2))" by simp
  with IHaux Cons(2) have "vs' = a#vs2" "f'=f2" by auto
  with Cons(1)[OF IHaux Cons(3)] have "vs' = a#vs@vs''" "f'=f''" by simp_all
  then show ?case by simp
qed

lemma strip_add_prenex: 
  "\<lbrakk>strip_prenex (add_prenex vs f) = (vs',f'); strip_prenex f = (vs'', f'')\<rbrakk>
  \<Longrightarrow> vs'=set vs\<union>vs'' \<and> f'=f''"
  using strip_add_prenexl strip_set_list by (metis set_append surj_pair)

fun simplify_emp_sepconj :: "form \<Rightarrow> form" where
  "simplify_emp_sepconj (f1 \<^emph> f2) = 
  (case simplify_emp_sepconj f1 of Emp \<Rightarrow> simplify_emp_sepconj f2 
  | f1' \<Rightarrow> (case simplify_emp_sepconj f2 of Emp \<Rightarrow> f1' 
  | f2' \<Rightarrow> f1' \<^emph> f2'))"
| "simplify_emp_sepconj (Disj f1 f2) = Disj (simplify_emp_sepconj f1) (simplify_emp_sepconj f2)"
| "simplify_emp_sepconj (Exists v f) = Exists v (simplify_emp_sepconj f)"
| "simplify_emp_sepconj P = P"

lemma simplification_sound: "separation_logic.form_semantics \<Lambda> d\<Lambda> (S,B,M) (simplify_emp_sepconj P) =
  separation_logic.form_semantics \<Lambda> d\<Lambda> (S,B,M) P" (is "?sem (S,B,M) (_ P) = ?sem (S,B,M) P")
proof
assume "?sem (S, B, M) (simplify_emp_sepconj P)"
then show "?sem (S, B, M) P" proof (induction P arbitrary: S B M)
  case (SepConj P1 P2)
  then show ?case proof (cases "simplify_emp_sepconj P1=Emp")
    case True
    then have "?sem (S,B,Map.empty) (simplify_emp_sepconj P1)" 
      by (auto simp: separation_logic.form_semantics.simps)
    with SepConj have "?sem (S,B,Map.empty) P1" by simp
    moreover from True SepConj have "?sem (S,B,M) P2" by simp
    ultimately show ?thesis by (auto simp: separation_logic.form_semantics.simps) fastforce
  next
    case False
    then have P1: "simplify_emp_sepconj P1 \<noteq> Emp" .
    then show ?thesis proof (cases "simplify_emp_sepconj P2=Emp")
      case True
      then have "?sem (S,B,Map.empty) (simplify_emp_sepconj P2)" 
        by (auto simp: separation_logic.form_semantics.simps)
      with SepConj have P2: "?sem (S,B,Map.empty) P2" by simp
      from True P1 have "simplify_emp_sepconj (P1 \<^emph> P2) = simplify_emp_sepconj P1"
        by (auto split: form.splits)
      with SepConj have "?sem (S,B,M) P1" by simp
      with P2 show ?thesis by (auto simp: separation_logic.form_semantics.simps) fastforce
    next
      case False
      with P1 have "simplify_emp_sepconj (P1 \<^emph> P2) = ((simplify_emp_sepconj P1) 
        \<^emph> (simplify_emp_sepconj P2))" by (auto split: form.splits)
      from SepConj(3)[unfolded this] obtain M1 M2 where M: "dom M1 \<inter> dom M2 = {}" "M = M1 ++ M2" 
        "?sem (S,B,M1) (simplify_emp_sepconj P1)" "?sem (S,B,M2) (simplify_emp_sepconj P2)"
        unfolding separation_logic.form_semantics.simps by auto
      with SepConj have "?sem (S,B,M1) P1" "?sem (S,B,M2) P2" by simp_all
      with M show ?thesis by (auto simp: separation_logic.form_semantics.simps)
    qed
  qed    
next
  case (Disj P1 P2)
  then have "?sem (S,B,M) ((simplify_emp_sepconj P1) \<or>\<^sub>s (simplify_emp_sepconj P2))"
    by simp
  then have "(?sem (S,B,M) (simplify_emp_sepconj P1) \<or> ?sem (S,B,M) (simplify_emp_sepconj P2))" 
    unfolding separation_logic.form_semantics.simps(5) .
  with Disj(1,2) show ?case unfolding separation_logic.form_semantics.simps(5) by auto
next
  case (Exists x1 P)
  then have "?sem (S, B, M) (Exists x1 (simplify_emp_sepconj P))" by simp
  then have "\<exists>v. ?sem (update_stack S x1 v,B,M) (simplify_emp_sepconj P)"
    unfolding separation_logic.form_semantics.simps(9) .
  with Exists(1) show ?case unfolding separation_logic.form_semantics.simps(9) by auto
qed (simp_all)
next
assume "?sem (S, B, M) P"
then show "?sem (S, B, M) (simplify_emp_sepconj P)" proof (induction P arbitrary: S B M)
  case (SepConj P1 P2)
  then obtain M1 M2 where M: "dom M1 \<inter> dom M2 = {}" "M = M1 ++ M2" "?sem (S,B,M1) P1" "?sem (S,B,M2) P2"
    by (auto simp: separation_logic.form_semantics.simps)
  then show ?case proof (cases "simplify_emp_sepconj P1=Emp")
    case True
    with SepConj(1)[OF M(3)] have "M1 = Map.empty" by (auto simp: separation_logic.form_semantics.simps)
    with M(2) have "M=M2" by simp
    with M(4) SepConj(2) have "?sem (S,B,M) (simplify_emp_sepconj P2)" by simp
    with True show ?thesis by simp
  next
    case False
    then have P1: "simplify_emp_sepconj P1 \<noteq> Emp" .
    then show ?thesis proof (cases "simplify_emp_sepconj P2=Emp")
      case True
      with SepConj(2)[OF M(4)] have "M2 = Map.empty" by (auto simp: separation_logic.form_semantics.simps)
      with M(2) have "M=M1" by simp
      with M(3) SepConj(1) have "?sem (S,B,M) (simplify_emp_sepconj P1)" by simp
      moreover from P1 True have "simplify_emp_sepconj (P1 \<^emph> P2) = simplify_emp_sepconj P1" 
        by (auto split: form.splits)
      ultimately show ?thesis by simp
    next
      case False
      from M SepConj have "?sem (S,B,M1) (simplify_emp_sepconj P1)" "?sem (S,B,M2) (simplify_emp_sepconj P2)"
        by auto
      moreover from False P1 have "simplify_emp_sepconj (P1 \<^emph> P2) = ((simplify_emp_sepconj P1) 
        \<^emph> (simplify_emp_sepconj P2))" by (auto split: form.splits)
      ultimately show ?thesis using M(1,2) by (auto simp: separation_logic.form_semantics.simps)
    qed
  qed
next
  case (Disj P1 P2)
  then show ?case by (auto simp: separation_logic.form_semantics.simps(5))
next
  case (Exists x1 P)
  then show ?case by (auto simp: separation_logic.form_semantics.simps(9))
qed (simp_all)
qed

context separation_logic begin
abbreviation star_disj :: "form list \<Rightarrow> form" where
  "star_disj Q \<equiv> fold (\<or>\<^sub>s) Q FalseF" 
end

text \<open>The paper distinguishes program variables and logical variables.
  For the formalization, it suffices to know the arguments to a function 
  to get the program variables, as the function can't use any other variables.
  Therefore, we do not use different types for these two kinds of variables but just different sets.
  We also use meta-variables wherever possible.\<close>
 
type_synonym pre_contract = "(form\<times>(form list)) list"

typedef contract = "{(cs, (f,args))::pre_contract\<times>func | cs args f.
  \<forall>(P,Q)\<in>set cs. quantifree_symb_heap P \<and> \<comment> \<open>P is a quantifier-free symbolic heap\<close>
  \<comment> \<open>Q is a disjunction of single formulas of the form \<open>\<exists>UQ. Qf \<^emph> Qeq\<close>\<close>
  list_all (\<lambda>q. case strip_prenex q of (UQ, Qf \<^emph> Qeq) \<Rightarrow>
    \<comment> \<open>The prenex variables are the logical ones in Qf and Qeq, that are not also in P.\<close>
    UQ = (free_vars Qf \<union> free_vars Qeq) - set args - free_vars P \<and>
    \<comment> \<open>Qf is a quantifier-free symbolic heap with only logical variables\<close>
    quantifree_symb_heap Qf \<and> free_vars Qf \<inter> set args = {} \<and>
    \<comment> \<open>Qeq is of the form \<open>x1=e1 \<^emph> ... \<^emph> xn=en \<^emph> Emp\<close> for arguments xi and some expressions e 
      that only contain logical variables.\<close>
    (\<exists>eqs. Qeq = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq x e)) (zip args eqs) Emp)
    \<and> list_all (\<lambda>e. free_vars e \<inter> set args = {}) eqs)
    | _ \<Rightarrow> False) Q \<and> Q \<noteq> []}" morphisms raw_contract Contract
  by (smt (z3) empty_iff mem_Collect_eq set_empty2)

setup_lifting type_definition_contract

lift_definition conjunctive :: "contract \<Rightarrow> bool" is
  "\<lambda>(cs, (f,args)). \<forall>(P,Qs) \<in> set cs. length Qs = 1" .

context program_logic
begin
lift_definition sound :: "contract \<Rightarrow> bool" is
  "\<lambda>(cs, (f,args)). \<forall>(P,Qs) \<in> set cs. \<forall>c c' F.
    (((c \<turnstile> (P\<^emph>F)) \<and> fun_semantics fs f c c' \<and> symbolic_heap F \<and> free_vars F \<inter> set args = {}) 
    \<longrightarrow> (c' \<turnstile> ((star_disj Qs) \<^emph> F)))" .
end

abbreviation single_stmt_cfg :: "func \<Rightarrow> command \<Rightarrow> cfg" where
  "single_stmt_cfg f cmd \<equiv> (f, {(entry,cmd,exit)})"

abbreviation single_fun_prog :: "func \<Rightarrow> command \<Rightarrow> prog" where
  "single_fun_prog f cmd \<equiv> (case f of (n,args) \<Rightarrow> [n\<mapsto>single_stmt_cfg f cmd])"

locale standard_prog = fixes x y z X Y Z u :: var 
  assumes var_sep: "{x,y,z,u} \<inter> {X,Y,Z} = {}" and diff_var: "x\<noteq>y\<and>y\<noteq>z\<and>x\<noteq>z\<and>x\<noteq>u\<and>y\<noteq>u\<and>z\<noteq>u"
begin

definition assign :: prog where "assign \<equiv> single_fun_prog (''assign'',[x,y]) (AssignVar x y)"
definition assign_contract :: pre_contract where 
  "assign_contract \<equiv> [(f_eq y Y,[Emp \<^emph> (f_eq x Y)\<^emph>(f_eq y Y)])]"
lift_definition assign_c :: contract is "(assign_contract, (''assign'',[x,y]))"
proof (auto simp: assign_contract_def)
  define eqs where "eqs = [VarE Y,VarE Y]"
  then have "(f_eq x Y \<^emph> f_eq y Y) = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq x e)) (zip [x, y] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e \<and> y \<notin> free_vars e) eqs"
    using var_sep eqs_def by auto
  then show "\<exists>eqs. (f_eq x Y \<^emph> f_eq y Y) = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq x e)) (zip [x, y] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e \<and> y \<notin> free_vars e) eqs" by auto
qed

definition const :: "val \<Rightarrow> prog" where "const k \<equiv> single_fun_prog (''const'',[x]) (AssignConst x k)"
definition const_contract :: "val \<Rightarrow> pre_contract" where 
  "const_contract k \<equiv> [(Emp,[Emp \<^emph> (f_eq x k)])]"
lift_definition const_c :: "val \<Rightarrow> contract" is "\<lambda>k. (const_contract k, (''const'',[x]))"
proof (auto simp: const_contract_def)
  fix k :: val
  define eqs where "eqs = [ConstE k]"
  then have "(f_eq x (ConstE k)) = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq x e)) (zip [x] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e) eqs"
    using var_sep eqs_def by auto
  then show "\<exists>eqs. (f_eq x (ConstE k)) = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq x e)) (zip [x] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e) eqs" by auto
qed

definition load :: prog where "load \<equiv> single_fun_prog (''load'',[x,y]) (Load x y)"
definition load_contract :: pre_contract where 
  "load_contract \<equiv> [((f_eq y Y)\<^emph>(Y\<mapsto>\<^sub>sz),[(Y\<mapsto>\<^sub>sz) \<^emph> (f_eq x z)\<^emph>(f_eq y Y)])]"
lift_definition load_c :: contract is "(load_contract, (''load'',[x,y]))"
  using var_sep[simplified]
proof (auto simp: load_contract_def diff_var)
  define eqs where "eqs = [VarE z, Y]"
  then have "(f_eq x z \<^emph> f_eq y Y) = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq x e)) (zip [x,y] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e \<and> y \<notin> free_vars e) eqs"
    using eqs_def var_sep diff_var by auto
  then show "\<exists>eqs. (f_eq x z \<^emph> f_eq y Y) = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq x e)) (zip [x,y] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e \<and> y \<notin> free_vars e) eqs" by auto
qed

definition store :: prog where "store \<equiv> single_fun_prog (''store'',[x,y]) (Store x y)"
definition store_contract :: pre_contract where 
  "store_contract \<equiv> [((f_eq x X)\<^emph>(f_eq y Y)\<^emph>(X\<mapsto>\<^sub>sz),[(X\<mapsto>\<^sub>sY) \<^emph> (f_eq x X)\<^emph>(f_eq y Y)])]"
lift_definition store_c :: contract is "(store_contract, (''store'',[x,y]))"
  using var_sep[simplified]
proof (auto simp: store_contract_def)
  define eqs where "eqs = [VarE X, Y]"
  then have "(f_eq x X \<^emph> f_eq y Y) = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq x e)) (zip [x,y] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e \<and> y \<notin> free_vars e) eqs"
    using eqs_def var_sep diff_var by auto
  then show "\<exists>eqs. (f_eq x X \<^emph> f_eq y Y) = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq x e)) (zip [x,y] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e \<and> y \<notin> free_vars e) eqs" by auto
qed

definition malloc :: prog where "malloc \<equiv> single_fun_prog (''malloc'',[x,y]) (Malloc x y)"
definition malloc_contract :: pre_contract where 
  "malloc_contract \<equiv> [((f_eq y Y),
    [Emp \<^emph> (f_eq x (null x))\<^emph>(f_eq y Y),
    Exists u (((u\<mapsto>\<top>[Y])\<^emph>(f_eq (Base u) u)\<^emph>(f_eq (Ende u) (e_add u Y))) \<^emph> (f_eq x u)\<^emph>(f_eq y Y))])]"
lift_definition malloc_c :: contract is "(malloc_contract, (''malloc'',[x,y]))"
  using var_sep[simplified] diff_var
proof (auto simp: malloc_contract_def)
  define eqs where "eqs = [ConstE (null x), Y]"
  then have "(f_eq x (null x) \<^emph> f_eq y Y) = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq (VarE x) e)) (zip [x,y] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e \<and> y \<notin> free_vars e) eqs"
    using eqs_def var_sep diff_var by auto
  then show "\<exists>eqs. (f_eq x (null x) \<^emph> f_eq y Y) = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq (VarE x) e)) (zip [x,y] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e \<and> y \<notin> free_vars e) eqs" by auto
next
  define eqs where "eqs = [VarE u, Y]"
  then have "(f_eq x u \<^emph> f_eq y Y) = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq (VarE x) e)) (zip [x,y] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e \<and> y \<notin> free_vars e) eqs"
    using eqs_def var_sep diff_var by auto
  then show "\<exists>eqs. (f_eq x u \<^emph> f_eq y Y) = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq (VarE x) e)) (zip [x,y] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e \<and> y \<notin> free_vars e) eqs" by auto
qed

definition free :: prog where "free \<equiv> single_fun_prog (''free'',[x]) (Free x)"
definition free_contract :: pre_contract where 
  "free_contract \<equiv> [
  ((f_eq x X)\<^emph>(f_eq X null_loc), [(f_eq X null_loc) \<^emph> (f_eq x X)]),
  ((f_eq x X)\<^emph>(X\<mapsto>\<top>[y])\<^emph>(f_eq (Base X) X)\<^emph>(f_eq (Ende X) (e_add X y)),[Emp \<^emph> (f_eq x X)])]"
lift_definition free_c :: contract is "(free_contract, (''free'',[x]))"
  using var_sep[simplified]
proof (auto simp: free_contract_def)
  define eqs where "eqs = [VarE X]"
  then have "f_eq x X = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq x e)) (zip [x] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e) eqs"
    using eqs_def var_sep diff_var by auto
  then show "\<exists>eqs. f_eq x X = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq x e)) (zip [x] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e) eqs" by auto
  then show "\<exists>eqs. f_eq x X = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq x e)) (zip [x] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e) eqs" by auto
qed

definition assign_binop :: "binop \<Rightarrow> prog" where "assign_binop op \<equiv> 
  single_fun_prog (''assign_binop'',[x,y,z]) (BinOp op x y z)"
definition binop_contract :: "binop \<Rightarrow> pre_contract" where 
  "binop_contract op \<equiv> [((f_eq y Y)\<^emph>(f_eq z Z),[Emp \<^emph> (f_eq x (BinOpE op Y Z))\<^emph>(f_eq y Y)\<^emph>(f_eq z Z)])]"
lift_definition binop_c :: "binop \<Rightarrow> contract" is "\<lambda>op. (binop_contract op, (''assign_binop'',[x,y,z]))"
proof (auto simp: binop_contract_def)
  fix op :: binop
  define eqs where "eqs = [BinOpE op Y Z,Y,Z]"
  then have "f_eq x (BinOpE op Y Z)\<^emph>f_eq y Y\<^emph>f_eq z Z = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq x e)) (zip [x,y,z] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e \<and> y \<notin> free_vars e \<and> z \<notin> free_vars e) eqs"
    using eqs_def var_sep diff_var by auto
  then show "\<exists>eqs. f_eq x (BinOpE op Y Z)\<^emph>f_eq y Y\<^emph>f_eq z Z = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq x e)) (zip [x,y,z] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e \<and> y \<notin> free_vars e \<and> z \<notin> free_vars e) eqs" by auto
qed

definition assign_unop ::  "unop \<Rightarrow> prog" where "assign_unop op \<equiv> 
  single_fun_prog (''assign_unop'',[x,y]) (UnOp op x y)"
definition unop_contract :: "unop \<Rightarrow> pre_contract" where 
  "unop_contract op \<equiv> [((f_eq y Y),[Emp \<^emph> (f_eq x (UnOpE op Y))\<^emph>(f_eq y Y)])]"
lift_definition unop_c :: "unop \<Rightarrow> contract" is "\<lambda>op. (unop_contract op, (''assign_unop'',[x,y]))"
proof (auto simp: unop_contract_def)
  fix op :: unop
  define eqs where "eqs = [UnOpE op Y,Y]"
  then have "f_eq x (UnOpE op Y)\<^emph>f_eq y Y = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq x e)) (zip [x,y] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e \<and> y \<notin> free_vars e) eqs"
    using eqs_def var_sep diff_var by auto
  then show "\<exists>eqs. f_eq x (UnOpE op Y)\<^emph>f_eq y Y = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq x e)) (zip [x,y] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e \<and> y \<notin> free_vars e) eqs" by auto
qed

definition ptrplus :: prog where "ptrplus \<equiv> single_fun_prog (''ptrplus'',[x,y,z]) (PtrPlus x y z)"
abbreviation "ptrplus\<phi> \<equiv> (Atom Neq (Base Y) null_loc)\<^emph>(f_eq (Base Y) (Base (e_add Y Z)))\<^emph>
  (f_eq (Ende Y) (Ende (e_add Y Z)))"
abbreviation "ptrplus\<phi>2 \<equiv> (Atom Neq (Base Y) null_loc)\<^emph>(f_eq (e_add Y Z) (Ende Y))"
definition ptrplus_contract :: pre_contract where 
  "ptrplus_contract \<equiv> [
  ((f_eq y Y)\<^emph>(f_eq z Z)\<^emph>ptrplus\<phi>,[ptrplus\<phi> \<^emph> (f_eq x (e_add Y Z))\<^emph>(f_eq y Y)\<^emph>(f_eq z Z)]),
  ((f_eq y Y)\<^emph>(f_eq z Z)\<^emph>ptrplus\<phi>2,[ptrplus\<phi>2 \<^emph> (f_eq x (e_add Y Z))\<^emph>(f_eq y Y)\<^emph>(f_eq z Z)])]"
lift_definition ptrplus_c :: contract is "(ptrplus_contract, (''ptrplus'',[x,y,z]))"
  using var_sep[simplified] diff_var
proof (auto simp: ptrplus_contract_def)
  fix op :: unop
  define eqs where "eqs = [e_add Y Z,Y,Z]"
  then have "f_eq x (e_add Y Z)\<^emph>f_eq y Y\<^emph>f_eq z Z = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq x e)) (zip [x,y,z] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e \<and> y \<notin> free_vars e \<and> z \<notin> free_vars e) eqs"
    using eqs_def var_sep diff_var by auto
  then show "\<exists>eqs. f_eq x (e_add Y Z)\<^emph>f_eq y Y\<^emph>f_eq z Z = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq x e)) (zip [x,y,z] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e \<and> y \<notin> free_vars e \<and> z \<notin> free_vars e) eqs" by auto
  then show "\<exists>eqs. f_eq x (e_add Y Z)\<^emph>f_eq y Y\<^emph>f_eq z Z = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq x e)) (zip [x,y,z] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e \<and> y \<notin> free_vars e \<and> z \<notin> free_vars e) eqs" by auto
qed

definition ptrsub :: prog where "ptrsub \<equiv> single_fun_prog (''ptrsub'',[x,y,z]) (PtrSub x y z)"
definition ptrsub_contract :: pre_contract where 
  "ptrsub_contract \<equiv> [((f_eq y Y)\<^emph>(f_eq z Z)\<^emph>(Atom Neq (Base Y) null_loc)\<^emph>(Atom Leq (Base Y) Z)\<^emph>(Atom Leq Z (Ende Y)),
  [Emp \<^emph> (f_eq x (BinOpE minus Y Z)\<^emph>(f_eq y Y)\<^emph>(f_eq z Z))])]"
lift_definition ptrsubs_c :: contract is "(ptrsub_contract, (''ptrsub'',[x,y,z]))"
proof (auto simp: ptrsub_contract_def)
  fix op :: unop
  define eqs where "eqs = [BinOpE Semantics.minus Y Z,Y,Z]"
  then have "f_eq x (BinOpE Semantics.minus Y Z)\<^emph>f_eq y Y\<^emph>f_eq z Z = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq x e)) (zip [x,y,z] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e \<and> y \<notin> free_vars e \<and> z \<notin> free_vars e) eqs"
    using eqs_def var_sep diff_var by auto
  then show "\<exists>eqs. f_eq x (BinOpE Semantics.minus Y Z)\<^emph>f_eq y Y\<^emph>f_eq z Z = simplify_emp_sepconj (foldr (\<lambda>(x, e). (\<^emph>) (f_eq x e)) (zip [x,y,z] eqs) Emp) 
    \<and> list_all (\<lambda>e. x \<notin> free_vars e \<and> y \<notin> free_vars e \<and> z \<notin> free_vars e) eqs" by auto
qed

definition memcpy :: prog where "memcpy \<equiv> single_fun_prog (''memcpy'',[x,y,z]) (Memcpy x y z)"

text \<open>The contracts for assume and assert don't follow the scheme, as the atomic conditions can't be 
  part of either Qf (it can't talk about program variables) or Qeq (it already contains all equalities.\<close>
definition assume_f :: "condition \<Rightarrow> prog" where "assume_f c \<equiv> single_fun_prog (''assume'',[y,z]) (Assume c y z)"
definition assume_contract :: "condition \<Rightarrow> pre_contract" where 
  "assume_contract c \<equiv> [((f_eq y Y)\<^emph>(f_eq z Z),[Atom c y z \<^emph> (f_eq y Y)\<^emph>(f_eq z Z)])]"
lift_definition assume_c :: "condition \<Rightarrow> contract" is "\<lambda>c. (assume_contract c, (''assume'',[y,z]))"
  oops

definition assert_f :: "condition \<Rightarrow> prog" where "assert_f c \<equiv> single_fun_prog (''assert'',[x,y]) (Assert c x y)"
definition assert_contract :: "condition \<Rightarrow> pre_contract" where 
  "assert_contract c \<equiv> [(Atom c y z\<^emph>(f_eq y Y)\<^emph>(f_eq z Z),[Atom c y z \<^emph> (f_eq y Y)\<^emph>(f_eq z Z)])]"
lift_definition assert_c :: "condition \<Rightarrow> contract" is "\<lambda>c. (assert_contract c, (''assert'',[y,z]))"
  oops

definition standard_prog :: prog where "standard_prog \<equiv> assign++load++store++malloc++free
  ++ptrplus++ptrsub++memcpy"
end
end