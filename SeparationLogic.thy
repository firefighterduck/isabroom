theory SeparationLogic
imports Semantics
begin

datatype expr =
  ConstE val
| VarE var
| Base expr
| Ende expr
| UnOpE unop expr
| BinOpE binop expr expr

abbreviation e_add :: "expr \<Rightarrow> expr \<Rightarrow> expr" where
  "e_add e1 e2 \<equiv> BinOpE plus e1 e2"

declare [[coercion VarE, coercion ConstE, coercion_enabled = true]]

fun e_size :: "expr \<Rightarrow> nat" where
  "e_size (ConstE k) = length k"
| "e_size (VarE v) = size v"
| "e_size (Base _) = loc_N_B"
| "e_size (Ende _) = loc_N_B"
| "e_size (UnOpE _ e) = e_size e"
| "e_size (BinOpE _ e _) = e_size e"

fun expr_semantics :: "stack \<Rightarrow> blocks \<Rightarrow> expr \<Rightarrow> val" where
  "expr_semantics S B (ConstE k) = k"
| "expr_semantics S B (VarE x) = lookup S x"
| "expr_semantics S B (Base e) = loc64_ops.to_val (base B (loc64_ops.from_val (expr_semantics S B e)))"
| "expr_semantics S B (Ende e)= loc64_ops.to_val (ende B (loc64_ops.from_val (expr_semantics S B e)))"
| "expr_semantics S B (UnOpE op e) = apply_unop op (expr_semantics S B e)"
| "expr_semantics S B (BinOpE op e1 e2) = apply_binop op (expr_semantics S B e1) (expr_semantics S B e2)"

datatype form =
  PointsTo expr expr (infix "\<mapsto>\<^sub>s" 60)
| PointsToK expr byte expr ("_\<mapsto>\<^sub>_[_]")
| PointsToTop expr expr ("_\<mapsto>\<top>[_]")
| SepConj form form (infixr "\<^emph>" 50)
| Disj form form (infixl "\<or>\<^sub>s" 55)
| LinkedList expr expr
| DoublyLinkedList expr expr expr expr
| Emp
| TrueF
| Atom condition expr expr
| Exists var form

abbreviation f_eq :: "expr \<Rightarrow> expr \<Rightarrow> form" where
  "f_eq e1 e2 \<equiv> Atom Eq e1 e2"

fun symbolic_heap :: "form \<Rightarrow> bool" where
  "symbolic_heap (SepConj f1 f2) = (symbolic_heap f1 \<and> symbolic_heap f2)"
| "symbolic_heap (Disj _ _) = False"
| "symbolic_heap (Exists _ f) = symbolic_heap f"
| "symbolic_heap _ = True"

fun quantifier_free :: "form \<Rightarrow> bool" where
  "quantifier_free (SepConj f1 f2) = (quantifier_free f1 \<and> quantifier_free f2)"
| "quantifier_free (Disj f1 f2) = (quantifier_free f1 \<and> quantifier_free f2)"
| "quantifier_free (Exists _ f) = False"
| "quantifier_free _ = True"

fun pure :: "form \<Rightarrow> bool" where
  "pure (SepConj f1 f2) = (pure f1 \<and> pure f2)"
| "pure (Atom _ _ _) = True"
| "pure _ = False"

class frees =
  fixes free_vars :: "'a \<Rightarrow> var set"

instantiation expr :: frees begin
fun free_vars_expr :: "expr \<Rightarrow> var set" where
  "free_vars_expr (ConstE _) = {}"
| "free_vars_expr (VarE v) = {v}"
| "free_vars_expr (Base e) = free_vars_expr e"
| "free_vars_expr (Ende e) = free_vars_expr e"
| "free_vars_expr (UnOpE _ e) = free_vars_expr e"
| "free_vars_expr (BinOpE _ e1 e2) = free_vars_expr e1 \<union> free_vars_expr e2"
instance .. end

instantiation form :: frees begin
fun free_vars_form :: "form \<Rightarrow> var set" where
 "free_vars_form (PointsTo e1 e2) = free_vars e1 \<union> free_vars e2"
| "free_vars_form (PointsToK e1 _ e2) = free_vars e1 \<union> free_vars e2"
| "free_vars_form (PointsToTop e1 e2) = free_vars e1 \<union> free_vars e2"
| "free_vars_form (SepConj f1 f2) = free_vars_form f1 \<union> free_vars_form f2"
| "free_vars_form (Disj f1 f2) = free_vars_form f1 \<union> free_vars_form f2"
| "free_vars_form (LinkedList e1 e2) = free_vars e1 \<union> free_vars e2"
| "free_vars_form (DoublyLinkedList e1 e2 e3 e4) = free_vars e1 \<union> free_vars e2 \<union> free_vars e3 
  \<union> free_vars e4"
| "free_vars_form Emp = {}"
| "free_vars_form TrueF = {}"
| "free_vars_form (Atom _ e1 e2) = free_vars e1 \<union> free_vars e2"
| "free_vars_form (Exists v f) = free_vars_form f - {v}"
instance .. end

fun rename_vars_expr :: "expr \<Rightarrow> var set \<Rightarrow> (var\<Rightarrow>var) \<Rightarrow> (expr\<times>(var\<Rightarrow>var))" where
  "rename_vars_expr (ConstE val) _ vs = (ConstE val, vs)"
| "rename_vars_expr (VarE var) in_use vs = 
  (if vs var \<in> in_use then (let fresh_v = fresh in_use in (VarE fresh_v, vs(var:=fresh_v))) 
  else (VarE (vs var), vs))"
| "rename_vars_expr (Base expr) in_use vs = (let (e',vs') = rename_vars_expr expr in_use vs in
  (Base e', vs'))"
| "rename_vars_expr (Ende expr) in_use vs = (let (e',vs') = rename_vars_expr expr in_use vs in
  (Ende e', vs'))"
| "rename_vars_expr (UnOpE op expr) in_use vs = (let (e',vs') = rename_vars_expr expr in_use vs in
  (UnOpE op e', vs'))"
| "rename_vars_expr (BinOpE op e1 e2) in_use vs = 
  (let (e1',vs1) = rename_vars_expr e1 in_use vs in
  (let (e2',vs2) = rename_vars_expr e2 in_use vs1 in
  (BinOpE op e1' e2', vs2)))"

fun rename_vars :: "form \<Rightarrow> var set \<Rightarrow> (var\<Rightarrow>var) \<Rightarrow> (form\<times>(var\<Rightarrow>var))" where
  "rename_vars (e1 \<mapsto>\<^sub>s e2) in_use vs =
  (let (e1',vs1) = rename_vars_expr e1 in_use vs in
  (let (e2',vs2) = rename_vars_expr e2 in_use vs1 in
  (e1' \<mapsto>\<^sub>s e2', vs2)))"
| "rename_vars (e1 \<mapsto>\<^sub>b[e2]) in_use vs = 
  (let (e1',vs1) = rename_vars_expr e1 in_use vs in
  (let (e2',vs2) = rename_vars_expr e2 in_use vs1 in
  (e1' \<mapsto>\<^sub>b [e2'], vs2)))"
| "rename_vars (e1 \<mapsto>\<top>[e2]) in_use vs = 
  (let (e1',vs1) = rename_vars_expr e1 in_use vs in
  (let (e2',vs2) = rename_vars_expr e2 in_use vs1 in
  (e1'\<mapsto>\<top>[e2'], vs2)))"
| "rename_vars (f1\<^emph>f2) in_use vs =
  (let (f1',vs1) = rename_vars f1 in_use vs in
  (let (f2',vs2) = rename_vars f2 in_use vs1 in
  (f1' \<^emph> f2', vs2)))"
| "rename_vars (f1\<or>\<^sub>sf2) in_use vs =
  (let (f1',vs1) = rename_vars f1 in_use vs in
  (let (f2',vs2) = rename_vars f2 in_use vs1 in
  (f1' \<or>\<^sub>s f2', vs2)))"
| "rename_vars (LinkedList e1 e2) in_use vs =
  (let (e1',vs1) = rename_vars_expr e1 in_use vs in
  (let (e2',vs2) = rename_vars_expr e2 in_use vs1 in
  (LinkedList e1' e2', vs2)))"
| "rename_vars (DoublyLinkedList e1 e2 e3 e4) in_use vs =
  (let (e1',vs1) = rename_vars_expr e1 in_use vs in
  (let (e2',vs2) = rename_vars_expr e2 in_use vs1 in
  (let (e3',vs3) = rename_vars_expr e3 in_use vs2 in
  (let (e4',vs4) = rename_vars_expr e4 in_use vs3 in
  (DoublyLinkedList e1' e2' e3' e4', vs4)))))"
| "rename_vars Emp _ vs = (Emp,vs)"
| "rename_vars TrueF _ vs = (TrueF,vs)"
| "rename_vars (Atom condition e1 e2) in_use vs =
  (let (e1',vs1) = rename_vars_expr e1 in_use vs in
  (let (e2',vs2) = rename_vars_expr e2 in_use vs1 in
  (Atom condition e1' e2', vs2)))"
| "rename_vars (Exists v f) in_use vs =
  (if vs v \<in> in_use then (let v' = fresh in_use in (let (f',vs') = rename_vars f in_use (vs(v:=v')) in
    (Exists v' f', vs'))) else (let (f',vs') = rename_vars f in_use vs in (Exists (vs' v) f', vs')))"

abbreviation pointsto_sem :: "expr \<Rightarrow> expr \<Rightarrow> pre_config \<Rightarrow> bool" where
  "pointsto_sem e1 e2 c \<equiv> case c of (S,B,M) \<Rightarrow> 
    (dom M = {x. loc64_ops.from_val (expr_semantics S B e1) \<le> x \<and> 
    x < offset (loc64_ops.from_val (expr_semantics S B e1)) (e_size e2)} \<and>
    access M (loc64_ops.from_val (expr_semantics S B e1)) (e_size e2) = Some (expr_semantics S B e2))"

text \<open>We need form to be deeply embedded so that we can talk about symbolic heaps and 
  quantifier free formulae. We also need \<Lambda> to return a form so that we can restrict it 
  to symbolic heaps in prenex form. But because \<Lambda> can potentially make the logic's semantics 
  non-terminating, we can't define them over a completely deeply embedded form with \<Lambda>.\<close>

locale separation_logic =
  fixes \<Lambda> :: "(expr \<Rightarrow> expr \<Rightarrow> form) \<times> (expr \<Rightarrow> expr \<Rightarrow> pre_config \<Rightarrow> bool)"
    and d\<Lambda> :: "(expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> form) \<times> (expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> pre_config \<Rightarrow> bool)"
begin

inductive list_semantics :: "pre_config \<Rightarrow> form \<Rightarrow> bool" where
  \<comment> \<open>Either the list is empty...\<close>
  "\<lbrakk>M = Map.empty; eval_cond Eq (expr_semantics S B e1) (expr_semantics S B e2)\<rbrakk>
  \<Longrightarrow> list_semantics (S,B,M) (LinkedList e1 e2)"
  \<comment> \<open>... or we can take one segment and get its semantics from \<Lambda>.\<close>
| "\<lbrakk>eval_cond Neq (expr_semantics S B e1) (expr_semantics S B e2); 
    \<comment> \<open>For this get new variable and location denoting the second element and split of a heap for \<Lambda>\<close>
    u \<notin> free_vars e1 \<union> free_vars e2; dom M1 \<inter> dom M2 = {}; M = M1 ++ M2; 
    snd \<Lambda> e1 (VarE u) (update_stack S u (loc64_ops.to_val l),B,M1);
    list_semantics (update_stack S u (loc64_ops.to_val l),B,M2) (LinkedList (VarE u) e2)\<rbrakk>
   \<Longrightarrow> list_semantics (S,B,M) (LinkedList e1 e2)"
  \<comment> \<open>And the same for doubly-linked lists.\<close>
| "\<lbrakk>M = Map.empty; eval_cond Eq (expr_semantics S B e1) (expr_semantics S B e1');
    eval_cond Eq (expr_semantics S B e2) (expr_semantics S B e2')\<rbrakk>
  \<Longrightarrow> list_semantics (S,B,M) (DoublyLinkedList e1 e2 e1' e2')"
| "\<lbrakk>eval_cond Neq (expr_semantics S B e1) (expr_semantics S B e1');
    eval_cond Neq (expr_semantics S B e2) (expr_semantics S B e2');
    u \<notin> free_vars e1 \<union> free_vars e2; om M1 \<inter> dom M2 = {}; M = M1 ++ M2;
    snd d\<Lambda> e1 (VarE u) e2 (update_stack S u (loc64_ops.to_val l),B,M1);
    list_semantics (update_stack S u (loc64_ops.to_val l),B,M2) (DoublyLinkedList (VarE u) e1 e1' e2')\<rbrakk>
  \<Longrightarrow> list_semantics (S,B,M) (DoublyLinkedList e1 e2 e1' e2')"

fun form_semantics :: "pre_config \<Rightarrow> form \<Rightarrow> bool" (infix "\<turnstile>" 80)
  where
  "(S,B,M) \<turnstile> (e1 \<mapsto>\<^sub>s e2) = pointsto_sem e1 e2 (S,B,M)"
| "(S,B,M) \<turnstile> (e1 \<mapsto>\<^sub>k[e2]) = (dom M = {x. loc64_ops.from_val (expr_semantics S B e1) \<le> x \<and> 
    x < offset (loc64_ops.from_val (expr_semantics S B e1)) (e_size e2)} \<and> ran M = {k})"
| "(S,B,M) \<turnstile> (e1 \<mapsto>\<top>[e2]) = (dom M = {x. loc64_ops.from_val (expr_semantics S B e1) \<le> x \<and> 
    x < offset (loc64_ops.from_val (expr_semantics S B e1)) (e_size e2)})"
| "(S,B,M) \<turnstile> (\<phi>1\<^emph>\<phi>2) = (\<exists>M1 M2. dom M1 \<inter> dom M2 = {} \<and> M = M1 ++ M2 \<and> (S,B,M1)\<turnstile>\<phi>1 \<and> (S,B,M2)\<turnstile>\<phi>2)"
| "(S,B,M) \<turnstile>  (\<phi>1 \<or>\<^sub>s \<phi>2) = ((S,B,M) \<turnstile> \<phi>1 \<or> (S,B,M) \<turnstile> \<phi>2)"
| "(S,B,M) \<turnstile> Emp = (M = Map.empty)"
| "(S,B,M) \<turnstile> TrueF = True"
| "(S,B,M) \<turnstile> (Atom cond e1 e2) = (M = Map.empty \<and> eval_cond cond (expr_semantics S B e1) (expr_semantics S B e2))"
| "(S,B,M) \<turnstile> (Exists x f) = (\<exists>v. (update_stack S x v,B,M) \<turnstile> f)"
| "c \<turnstile> l = list_semantics c l"
end

locale sound_separation_logic = separation_logic \<Lambda> d\<Lambda> for \<Lambda> d\<Lambda>
  + assumes sound_lambda: "\<forall>c e1 e2. c \<turnstile> (fst \<Lambda> e1 e2) \<longleftrightarrow> snd \<Lambda> e1 e2 c"
    and sound_dlambda: "\<forall>c e1 e2 e3. c \<turnstile> (fst d\<Lambda> e1 e2 e3) \<longleftrightarrow> snd d\<Lambda> e1 e2 e3 c"

locale program_logic = sound_separation_logic 
  + fixes fs :: prog
  assumes "\<forall>n \<in> dom fs. \<forall>cfg. fs n = Some cfg \<longrightarrow> fst (fst cfg) = n"

interpretation standard_sl: 
  sound_separation_logic "((\<lambda>x y. x \<mapsto>\<^sub>s y), pointsto_sem)"
    "((\<lambda>x y z. (x\<mapsto>\<^sub>sz) \<^emph> ((BinOpE plus x (ConstE [8]))\<mapsto>\<^sub>sy)), 
      (\<lambda>x y z (S,B,M). \<exists>M1 M2. dom M1 \<inter> dom M2 = {} \<and> M = M1 ++ M2 \<and>
      pointsto_sem x z (S,B,M1) \<and> pointsto_sem (BinOpE plus x (ConstE [8])) y (S,B,M2)))"
  by standard (auto simp: separation_logic.form_semantics.simps(1,4))

context sound_separation_logic begin
definition satisfiable :: "form \<Rightarrow> bool" where
  "satisfiable P \<equiv> \<exists>S B M. (S,B,M) \<turnstile> P"

definition entails :: "form \<Rightarrow> form \<Rightarrow> bool" where
  "entails P Q \<equiv> \<forall>S B M. (S,B,M) \<turnstile> P \<longrightarrow> (S,B,M) \<turnstile> Q"
end

context separation_logic begin
definition FalseF :: form where
  "FalseF \<equiv> Atom Neq (ConstE []) (ConstE [])"

lemma false_is_false: "\<nexists>S B M. (S,B,M) \<turnstile> FalseF"
  by (auto simp: FalseF_def)

lemma false_conj_unit: "((S,B,M) \<turnstile> (P \<or>\<^sub>s FalseF)) = (S,B,M) \<turnstile> P" 
  using false_is_false by (auto)
end
end