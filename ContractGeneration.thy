theory ContractGeneration
imports Contracts
begin

fun map_of_eqs :: "form \<Rightarrow> (var \<Rightarrow> expr)" where
  "map_of_eqs (f_eq (VarE v) e) = (VarE)(v:=e)"
| "map_of_eqs ((f_eq (VarE v) e)\<^emph>f) = (map_of_eqs f)(v:=e)"
| "map_of_eqs _ = VarE"

text \<open>As in 6.3.1 we assume a function body as a sequence of calls to functions for which we already 
  have the (conjunctive) contracts.\<close>
locale generation_ctxt = program_logic +
  fixes func_body :: "(contract\<times>(var list)) list" and args :: "var list"
  assumes non_empty: "func_body \<noteq> []" and conj: "list_all (conjunctive \<circ> fst) func_body"
  and simple: "list_all (\<lambda>c. (\<exists>c'. fst (raw_contract (fst c)) = {c'})) func_body"
  and well_formed: "list_all (\<lambda>c. set (snd c) \<subseteq> set (args) \<and> distinct (snd c)) func_body"
begin

fun symbolic_execution :: "contract list \<Rightarrow> (form\<times>form) \<Rightarrow> (form\<times>form) option" where
  "symbolic_execution [] (P,Q) = (P,Q)"
  \<comment> \<open>TODO define actual symbolic execution step\<close>
| "symbolic_execution (func_call#rest) (P,Q) = 
  (let _ = (case raw_contract func_call of (({(C,[D])},f),call_args) \<Rightarrow>
    (case strip_prenex Q of (Uq, Qf\<^emph>Qeq) \<Rightarrow> 
    \<comment> \<open>Rename logical variables\<close>
    (let (C1,vs) = rename_vars C (free_vars P - (set args)) id in
    (let (D',_) = rename_vars D (free_vars P - (set (args))) vs in
    \<comment> \<open>Substitute the arguments for the parameters\<close>
    (let (C2,_) = rename_vars C1 {} (map_of (zip (snd f) call_args)) in
    (let (C3,_) = rename_vars C2 {} (map_of_eqs Qeq) in
    ())))))
  | _ \<Rightarrow> None) in

  symbolic_execution rest (P,Q))"

fun build_initial :: "var list \<Rightarrow> var set \<Rightarrow> form" where
  "build_initial [] _ = Emp"
| "build_initial (x#vs) used = (let X = fresh used in (f_eq x X)\<^emph>(build_initial vs (insert X used)))"

definition initialP :: form where
  "initialP \<equiv> simplify_emp_sepconj (build_initial args (set args))"
end
end