theory Isabroom
  imports "HOL-Library.Word"
begin

type_synonym byte = "8 word"
type_synonym val = "byte list"
type_synonym loc = "64 word"

locale loc_ops =
  fixes N :: "'a::len"
  assumes bytes: "LENGTH('a) mod 8 = 0" begin
definition get_nth_byte :: "'a word \<Rightarrow> nat \<Rightarrow> byte" where
  "get_nth_byte x n = ucast (drop_bit (n*8) (take_bit ((n+1)*8) x))"

fun to_val_aux :: "'a word \<Rightarrow> nat \<Rightarrow> val" where
  "to_val_aux x 0 = [get_nth_byte x 0]"
| "to_val_aux x n = (get_nth_byte x n) # (to_val_aux x (n-1))"

definition to_val :: "'a word \<Rightarrow> val" where
  "to_val x = to_val_aux x (LENGTH('a)-8)"

fun from_val_aux :: "val \<Rightarrow> ('a word \<times> nat)" where
  "from_val_aux [] = (0,0)"
| "from_val_aux (v#vs) = (let (w,n) = from_val_aux vs in 
    (w + ((ucast v)*2^n),Suc n))"

definition from_val :: "val \<Rightarrow> 'a word" where
  "from_val v = fst (from_val_aux v)"

lemma get_nth_byte_zero: 
  "get_nth_byte 0 n = 0" by (simp add: get_nth_byte_def)
end  

interpretation loc64_ops: loc_ops "64::64" by standard simp

typedecl var
axiomatization size :: "var \<Rightarrow> nat" where pos_size: "size v > 0"

typedef stack = "{s::var \<Rightarrow> val. \<forall>v. length (s v) = size v}"
proof -
  define s :: "var \<Rightarrow> val" where "s = (\<lambda>v. replicate (size v) 0)"
  have "\<forall>v. length (s v) = size v" by (simp add: s_def)
  then show ?thesis by auto
qed
setup_lifting type_definition_stack

type_synonym memory = "loc \<rightharpoonup> byte"

type_synonym blockname = nat
type_synonym block = "(blockname\<times>(loc\<times>loc))"

typedef blocks = "{b::block list. 
  (\<forall>n l u. (n,(l,u)) \<in> set b \<longrightarrow> (l<u \<and> l\<noteq>0)) \<and> 
  (\<forall>n1 n2 l1 l2 u1 u2. ((n1,(l1,u1)) \<in> set b \<and> (n2,(l2,u2)) \<in> set b 
    \<and> (l1\<noteq>l2 \<or> u1 \<noteq> u2))
    \<longrightarrow> ((u1\<le>l2 \<or> u2\<le>l1) \<and> n1\<noteq>n2))}" morphisms raw Blocks
proof -
  have "([]::block list) \<in> {b. (\<forall>n l u. (n, l, u) \<in> set b \<longrightarrow> l < u \<and> l \<noteq> 0) \<and>
         (\<forall>n1 n2 l1 l2 u1 u2. (n1, l1, u1) \<in> set b \<and> (n2, l2, u2) \<in> set b \<and> (l1 \<noteq> l2 \<or> u1 \<noteq> u2) 
          \<longrightarrow> ((u1\<le>l2 \<or> u2\<le>l1) \<and> n1\<noteq>n2))}" by simp
  then show ?thesis by blast
qed
setup_lifting type_definition_blocks

fun intv :: "loc \<Rightarrow> (loc\<times>loc) \<Rightarrow> bool" where
  "intv x (l,u) = (l\<le>x \<and> x<u)"

typedef config = "{(s::stack, b::blocks, m::memory) | s b m.
  \<forall>x::loc. m x \<noteq> None \<longrightarrow> (\<exists>n lu. (n,lu) \<in> set (raw b) \<and> intv x lu)}" by auto
setup_lifting type_definition_config

fun bounds :: "block list \<Rightarrow> loc \<Rightarrow> (loc\<times>loc)" where
  "bounds [] l = (0,0)"
| "bounds ((_,lu)#bs) l = (if intv l lu then lu else bounds bs l)"

lemma bounds_neq_zero: "fst (bounds b l) \<noteq> 0 \<Longrightarrow> intv l (bounds b l)"
  by (induction rule: bounds.induct) auto

lift_definition base :: "blocks \<Rightarrow> loc \<Rightarrow> loc" is "\<lambda>B l. fst (bounds B l)" .
lift_definition ende :: "blocks \<Rightarrow> loc \<Rightarrow> loc" is "\<lambda>B l. snd (bounds B l)" .

lemma blocks_axiom1: "base B l = 0 \<or> (base B l \<le> l \<and> l < ende B l)"
proof (auto)  
  assume base_neq_zero: "base B l \<noteq> 0"
  obtain b e where be:"bounds (raw B) l = (b,e)" by force
  from base_neq_zero bounds_neq_zero have "intv l (bounds (raw B) l)" unfolding base.rep_eq by simp
  with be have "intv l (b,e)" by simp
  then show "base B l \<le> l" unfolding base.rep_eq be by simp
next
  assume base_neq_zero: "base B l \<noteq> 0"
  obtain b e where be:"bounds (raw B) l = (b,e)" by force
  from base_neq_zero bounds_neq_zero have "intv l (bounds (raw B) l)" unfolding base.rep_eq by simp
  with be have "intv l (b,e)" by simp
  then show "l < ende B l" unfolding ende.rep_eq be by simp
qed

lemma blocks_axiom2: 
  "(0<base B l \<and> base B l<ende B l' \<and> ende B l'\<le>ende B l) \<or>
   (0<base B l' \<and> base B l'<ende B l \<and> ende B l\<le>ende B l') \<Longrightarrow>
    base B l = base B l' \<and> ende B l = ende B l'"
  apply auto apply transfer'

(*typedef (overloaded) 'a loc = "{v::val. length v = LENGTH('a::len)}"
  morphisms Val Loc by (simp add: Ex_list_of_length)

setup_lifting type_definition_loc

instantiation loc :: (len) zero 
begin
lift_definition zero_loc :: \<open>'a loc\<close> 
  is "replicate LENGTH('a) (0::byte)" by (rule length_replicate)
instance ..
end

instantiation loc :: (len) one 
begin
lift_definition one_loc :: \<open>'a loc\<close>
  is "replicate (LENGTH('a)-1) (0::byte)@[1]" by simp
instance ..
end

instantiation loc :: (len) plus 
begin
lift_definition plus_loc :: \<open>'a loc \<Rightarrow> 'a loc \<Rightarrow> 'a loc\<close>
  is \<open>map2 (+)\<close> by auto
instance ..
end

instantiation loc :: (len) minus 
begin
lift_definition minus_loc :: \<open>'a loc \<Rightarrow> 'a loc \<Rightarrow> 'a loc\<close>
  is \<open>map2 (-)\<close> by auto
instance ..
end*)


end