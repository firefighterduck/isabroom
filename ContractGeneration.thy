theory ContractGeneration
imports Contracts
begin

fun map_of_eqs :: "form \<Rightarrow> (var \<rightharpoonup> expr)" where
  "map_of_eqs ((f_eq (VarE v) e)\<^emph>f) = (map_of_eqs f)(v\<mapsto>e)"
| "map_of_eqs _ = Map.empty"

fun update_var_eq_after :: "form \<Rightarrow> (expr\<rightharpoonup>expr) \<Rightarrow> form" where
  "update_var_eq_after (f_eq x y) arg_to_new_expr = 
    (case arg_to_new_expr x of Some a \<Rightarrow> f_eq x a | None \<Rightarrow> f_eq x y)"
| "update_var_eq_after ((f_eq x y)\<^emph>rest) arg_to_new_expr = 
    ((case arg_to_new_expr x of Some a \<Rightarrow> f_eq x a | None \<Rightarrow> f_eq x y)
    \<^emph>(update_var_eq_after rest arg_to_new_expr))"
| "update_var_eq_after f _ = f"

definition (in sound_separation_logic) bap :: "var set \<Rightarrow> var set \<Rightarrow> form \<Rightarrow> form \<Rightarrow> form \<Rightarrow> form \<Rightarrow> form \<Rightarrow> bool" where
  "bap args Uq Qfree Qeq C M F \<equiv> entails (Qfree\<^emph>M) (add_prenex (sorted_list_of_set ((free_vars C \<union> free_vars F)
    -(free_vars Qfree \<union> free_vars Qeq \<union> free_vars M))) (C\<^emph>F))
  \<and> quantifree_symb_heap M \<and> quantifree_symb_heap F
  \<and> free_vars M \<subseteq> UNIV - args - Uq \<and> free_vars F \<inter> args = {}"

locale generation_ctxt = program_logic +
  fixes bap_solver :: "var set \<Rightarrow> var set \<Rightarrow> form \<Rightarrow> form \<Rightarrow> form \<Rightarrow> (form\<times>form)" and pvars :: "var list"
  assumes bap_solution: "\<forall>Uq Qf Qeq C M F. bap_solver (set pvars) Uq Qf Qeq C = (M,F) 
    \<longleftrightarrow> bap (set pvars) Uq Qf Qeq C M F"
begin

text \<open>This is what's called biabduct(P,Q,g(a1,...,an),C,D) but with slightly different argument order.\<close>
definition biabduction_step :: "(contract\<times>(var list)) \<Rightarrow> (form\<times>form) \<Rightarrow> (form\<times>form) option" where
  "biabduction_step func_call PQ = (case PQ of (P,Q) \<Rightarrow>
    (case func_call of (contr, call_args) \<Rightarrow>
    (case raw_contract contr of ([(C,[D])],f) \<Rightarrow>
    (case strip_prenex Q of (Uq, Qf\<^emph>Qeq) \<Rightarrow> 
    \<comment> \<open>Rename logical variables\<close>
    (let (C1,vs) = rename_vars C (free_vars P - (set pvars)) VarE in
    (let (D',_) = rename_vars D (free_vars P - (set (pvars))) vs in
    (case strip_prenex D' of (_, Df\<^emph>Deq) \<Rightarrow> 
    \<comment> \<open>Substitute the arguments for the parameters\<close>
    (let (C2,_) = rename_vars_option C1 {} ((map_of_eqs Qeq) \<circ>\<^sub>m (map_of (zip (snd f) call_args))) in
    \<comment> \<open>Do biabduction and construct the next intermediate contract\<close>
    (let (M,F) = bap_solver (set pvars) Uq Qf Qeq C2 in
    (let P_after = M \<^emph> P in
    (let Qf' = F \<^emph> Df in
    (let Qeq' = update_var_eq_after Qeq ((map_of_eqs Deq) \<circ>\<^sub>m (map_of (zip (map VarE call_args) (snd f)))) in
    (let Uq_after = (free_vars Qf' \<union> free_vars Qeq') - (set pvars) - free_vars P_after in
    (let Q_after = add_prenex (sorted_list_of_set Uq_after) (Qf'\<^emph>Qeq') in
    Some (P_after,Q_after))))))))
  | _ \<Rightarrow> None))) | _ \<Rightarrow> None) | _ \<Rightarrow> None)))"
end

text \<open>As in 6.3.1 we assume a function body as a sequence of calls to functions for which we already 
  have the (conjunctive) contracts.\<close>
locale sequential = generation_ctxt +
  fixes func_body :: "(contract\<times>(var list)) list"
  assumes non_empty: "func_body \<noteq> []" and conj: "list_all (conjunctive \<circ> fst) func_body"
  and simple: "list_all (\<lambda>c. (\<exists>c'. fst (raw_contract (fst c)) = [c'])) func_body"
  and well_formed: "list_all (\<lambda>c. set (snd c) \<subseteq> set (pvars) \<and> distinct (snd c)) func_body"
begin
fun symbolic_execution :: "(contract\<times>(var list)) list \<Rightarrow> (form\<times>form) \<Rightarrow> (form\<times>form) option" where
  "symbolic_execution [] (P,Q) = Some (P,Q)"
| "symbolic_execution (func_call#rest) (P,Q) = (case biabduction_step func_call (P,Q) 
    of Some (P_after,Q_after) \<Rightarrow> symbolic_execution rest (P_after,Q_after) | _ \<Rightarrow> None)"

fun build_initial :: "var list \<Rightarrow> var set \<Rightarrow> form" where
  "build_initial [] _ = Emp"
| "build_initial (x#vs) used = (let X = fresh used in (f_eq x X)\<^emph>(build_initial vs (insert X used)))"

definition initialP :: form where
  "initialP \<equiv> simplify_emp_sepconj (build_initial pvars (set pvars))"

text \<open>This is Theorem 3, but I won't prove it yet. This would be way to much work for now.\<close>
lemma "symbolic_execution func_body (initialP, initialP) = Some (P,Q) \<Longrightarrow>
  sound (Contract ([(P,[Q])], (f,pvars)))"
  sorry
end

type_synonym symb_map = "CFG_node \<Rightarrow> (form\<times>form) list"
axiomatization P_init Q_init :: form

abbreviation add_prenex_wo_pvars :: "var set \<Rightarrow> form \<Rightarrow> form" where
  "add_prenex_wo_pvars pvars P \<equiv> add_prenex (sorted_list_of_set (free_vars P - pvars)) P"

definition (in sound_separation_logic) covers :: "var set \<Rightarrow> form \<Rightarrow> form \<Rightarrow> form \<Rightarrow> form \<Rightarrow> bool" where
  "covers pvars P Q P' Q' \<equiv> 
    entails (add_prenex_wo_pvars pvars P) (add_prenex_wo_pvars pvars P') \<and>
    entails (add_prenex_wo_pvars pvars Q') (add_prenex_wo_pvars pvars Q)"

locale loops_allowed = generation_ctxt +
  fixes func_body :: "(CFG_node \<times> string \<times> var list \<times> CFG_node) set" and contracts :: "string \<Rightarrow> contract"
  and cut_points :: "CFG_node set" and widening :: "form \<Rightarrow> form"
  assumes sound_contracts: "\<forall>f. sound (contracts f)"
begin

definition init_symb :: symb_map where "init_symb \<equiv> (\<lambda>_. [])(entry := [(P_init,Q_init)])"

text \<open>Given a worklist of nodes and the symb_maps, relate them to the next worklist and the updated
  symb maps.\<close>
inductive symbolic_execution :: "CFG_node set \<Rightarrow> symb_map \<Rightarrow> CFG_node set \<Rightarrow> symb_map \<Rightarrow> bool" where
  "\<lbrakk>v\<in>worklist; sm v = (P,Q)#sm_v; \<forall>f f_args v'. (v,f,f_args,v') \<in> func_body \<longrightarrow> 
    insert v' (ws-{v}) \<subseteq> worklist_after \<and>
    (\<forall>(C,Ds) \<in> set (fst (raw_contract (contracts f))). 
    (\<forall>D\<in>set Ds.
    (\<forall>P_after Q_after. Some (P_after,Q_after) = 
      biabduction_step (Contract ([(C,[D])],snd (raw_contract (contracts f))), f_args) (P,Q) \<longrightarrow>
    (v'\<notin>cut_points \<longrightarrow> (sm_after v = sm_v \<and> sm_after v' = (sm v')@[(P_after,Q_after)])) \<and>
    (v\<in>cut_points \<and> (\<exists>P' Q'. ((P',Q')\<in> set (sm v') \<and> covers (set pvars) P_after Q_after P' Q') 
      \<longrightarrow> (sm_after v = sm_v \<and> sm_after v' = sm v')) \<and> 
    (\<nexists>P' Q'. ((P',Q')\<in> set (sm v') \<and> covers (set pvars) P_after Q_after P' Q') 
      \<longrightarrow> (sm_after v = sm_v \<and> sm_after v' = sm v'@[(widening P_after, widening Q_after)]))))))\<rbrakk>
    \<Longrightarrow> symbolic_execution worklist sm worklist_after sm_after"
end
end