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

datatype form =
  PointsTo expr expr (infix "\<mapsto>\<^sub>s" 60)
| PointsToK expr byte expr ("_\<mapsto>\<^sub>_[_]")
| PointsToTop expr expr ("_\<mapsto>\<top>[_]")
| SepConj form form (infixl "\<^emph>" 50)
| Disj form form (infixl "\<or>\<^sub>s" 55)
| LinkedList "expr \<Rightarrow> expr \<Rightarrow> form" expr expr
| DoublyLinkedList "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> form" expr expr expr expr
| Emp
| TrueF
| Atom condition expr expr
| Exists var form

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
| "free_vars_form (LinkedList _ e1 e2) = free_vars e1 \<union> free_vars e2"
| "free_vars_form (DoublyLinkedList _ e1 e2 e3 e4) = free_vars e1 \<union> free_vars e2 \<union> free_vars e3 
  \<union> free_vars e4"
| "free_vars_form Emp = {}"
| "free_vars_form TrueF = {}"
| "free_vars_form (Atom _ e1 e2) = free_vars e1 \<union> free_vars e2"
| "free_vars_form (Exists v f) = free_vars_form f - {v}"
instance .. end

fun e_size :: "expr \<Rightarrow> nat" where
  "e_size (ConstE k) = length k"
| "e_size (VarE v) = size v"
| "e_size (Base _) = loc_N_B"
| "e_size (Ende _) = loc_N_B"
| "e_size (UnOpE _ e) = e_size e"
| "e_size (BinOpE _ e _) = e_size e"

fun is_symbolic_heap :: "form \<Rightarrow> bool" where
  "is_symbolic_heap (SepConj f1 f2) = (is_symbolic_heap f1 \<and> is_symbolic_heap f2)"
| "is_symbolic_heap (Disj _ _) = False"
| "is_symbolic_heap (Exists _ f) = is_symbolic_heap f"
| "is_symbolic_heap _ = True"

fun quantifier_free :: "form \<Rightarrow> bool" where
  "quantifier_free (SepConj f1 f2) = (quantifier_free f1 \<and> quantifier_free f2)"
| "quantifier_free (Disj f1 f2) = (quantifier_free f1 \<and> quantifier_free f2)"
| "quantifier_free (Exists _ f) = False"
| "quantifier_free _ = True"

fun pure :: "form \<Rightarrow> bool" where
  "pure (SepConj f1 f2) = (pure f1 \<and> pure f2)"
| "pure (Atom _ _ _) = True"
| "pure _ = False"

fun expr_semantics :: "stack \<Rightarrow> blocks \<Rightarrow> expr \<Rightarrow> val" where
  "expr_semantics S B (ConstE k) = k"
| "expr_semantics S B (VarE x) = lookup S x"
| "expr_semantics S B (Base e) = loc64_ops.to_val (base B (loc64_ops.from_val (expr_semantics S B e)))"
| "expr_semantics S B (Ende e)= loc64_ops.to_val (ende B (loc64_ops.from_val (expr_semantics S B e)))"
| "expr_semantics S B (UnOpE op e) = apply_unop op (expr_semantics S B e)"
| "expr_semantics S B (BinOpE op e1 e2) = apply_binop op (expr_semantics S B e1) (expr_semantics S B e2)"

fun form_semantics :: "pre_config \<Rightarrow> form \<Rightarrow> bool" (infix "\<turnstile>" 80)
  where
  "(S,B,M) \<turnstile> (e1 \<mapsto>\<^sub>s e2) = (dom M = {x. loc64_ops.from_val (expr_semantics S B e1) \<le> x \<and> 
    x < offset (loc64_ops.from_val (expr_semantics S B e1)) (e_size e2)} \<and>
    access M (loc64_ops.from_val (expr_semantics S B e1)) (e_size e2) = Some (expr_semantics S B e2))"
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
| "(S,B,M) \<turnstile> (LinkedList \<Lambda> e1 e2) = ((S,B,M) \<turnstile> (Atom Eq e1 e2) \<or>
   ((S,B,M) \<turnstile> ((Atom Neq e1 e2) \<^emph> TrueF) \<and> 
    (\<exists>l u. u \<notin> free_vars e1 \<union> free_vars e2 \<and> 
    (update_stack S u (loc64_ops.to_val l),B,M) \<turnstile> ((\<Lambda> e1 (VarE u)) \<^emph> (LinkedList \<Lambda> (VarE u) e2)))))"
end