theory Model
  imports "HOL-Library.Word"
begin

type_synonym byte = "8 word"
type_synonym val = "byte list"
type_synonym loc = "64 word"

abbreviation offset :: "loc \<Rightarrow> nat \<Rightarrow> loc" where
  "offset l n \<equiv> l + (word_of_nat n)"

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

abbreviation sizev :: "var \<Rightarrow> 'a::len word" where
  "sizev v \<equiv> word_of_nat (size v)"

definition fits :: "val \<Rightarrow> var \<Rightarrow> bool" where 
  "fits x v \<equiv> length x = size v"

typedef stack = "{s::var \<Rightarrow> val. \<forall>v. fits (s v) v}" morphisms lookup Stack
proof -
  define s :: "var \<Rightarrow> val" where "s = (\<lambda>v. replicate (size v) 0)"
  have "\<forall>v. length (s v) = size v" by (simp add: s_def)
  then show ?thesis by (auto simp: fits_def)
qed
setup_lifting type_definition_stack

lemma fits_upd: "fits k x \<Longrightarrow> (lookup s)(x:=k) \<in> {s. \<forall>v. fits (s v) v}"
  using lookup by (auto simp: fits_def)

type_synonym memory = "loc \<rightharpoonup> byte"

fun raw_access_rev :: "memory \<Rightarrow> loc \<Rightarrow> nat \<Rightarrow> byte option list" where
  "raw_access_rev m b 0 = [m b]"
| "raw_access_rev m b (Suc n) = m (offset b (Suc n))#(raw_access_rev m b n)"

lemma raw_access_set: "set (raw_access_rev m l n) = {m x | x. \<exists>n'. n' \<le> n \<and> x = offset l n'}"
  apply (induction n)
   apply auto
    apply fastforce
  using le_SucI apply blast
  by (metis (no_types, lifting) le_SucE of_nat_Suc)

definition access :: "memory \<Rightarrow> loc \<Rightarrow> nat \<Rightarrow> val option" where
  "access m l n \<equiv> 
    fold (\<lambda>x l. case x of Some x' \<Rightarrow> (case l of Some l' \<Rightarrow> Some (x'#l') | _ \<Rightarrow> None) | _ \<Rightarrow> None) 
      (rev (raw_access_rev m l n)) (Some [])"

lemma "access m l n \<noteq> None \<longleftrightarrow> (\<forall>x. l\<le>x \<and> x<offset l n \<longrightarrow> m x \<noteq> None)"
proof (unfold access_def, induction "raw_access_rev m l n")
  case Nil
  with raw_access_set[of m l n] show ?case by auto
next
  case (Cons a x)
  then show ?case sorry
qed
  
type_synonym blockname = nat
type_synonym block = "(blockname\<times>(loc\<times>loc))"

typedef blocks = "{b::block list. 
  (\<forall>n l u. (n,(l,u)) \<in> set b \<longrightarrow> (l<u \<and> l\<noteq>0)) \<and> 
  (\<forall>n1 n2 l1 l2 u1 u2. ((n1,(l1,u1)) \<in> set b \<and> (n2,(l2,u2)) \<in> set b 
    \<and> (l1\<noteq>l2 \<or> u1 \<noteq> u2))
    \<longrightarrow> ((u1\<le>l2 \<or> u2\<le>l1) \<and> n1\<noteq>n2))}" morphisms raw_blocks Blocks
proof -
  have "([]::block list) \<in> {b. (\<forall>n l u. (n, l, u) \<in> set b \<longrightarrow> l < u \<and> l \<noteq> 0) \<and>
         (\<forall>n1 n2 l1 l2 u1 u2. (n1, l1, u1) \<in> set b \<and> (n2, l2, u2) \<in> set b \<and> (l1 \<noteq> l2 \<or> u1 \<noteq> u2) 
          \<longrightarrow> ((u1\<le>l2 \<or> u2\<le>l1) \<and> n1\<noteq>n2))}" by simp
  then show ?thesis by blast
qed
setup_lifting type_definition_blocks

fun intv :: "loc \<Rightarrow> (loc\<times>loc) \<Rightarrow> bool" where
  "intv x (l,u) = (l\<le>x \<and> x<u)"

type_synonym pre_config = "stack \<times> blocks \<times> memory"

typedef config = "{(s::stack, b::blocks, m::memory) | s b m.
  \<forall>x::loc. m x \<noteq> None \<longrightarrow> (\<exists>n lu. (n,lu) \<in> set (raw_blocks b) \<and> intv x lu)}" by auto
setup_lifting type_definition_config

lift_definition get_stack :: "config \<Rightarrow> stack" is "\<lambda>c. (case c of (s::stack,_,_) \<Rightarrow> s)" .
lift_definition get_blocks :: "config \<Rightarrow> blocks" is "\<lambda>c. (case c of (_,b::blocks,_) \<Rightarrow> b)" .
lift_definition get_memory :: "config \<Rightarrow> memory" is "\<lambda>c. (case c of (_,_,m::memory) \<Rightarrow> m)" .

fun from_block :: "loc \<Rightarrow> block list \<Rightarrow> block option" where
  "from_block l [] = None"
| "from_block l ((n,lu)#bs) = (if intv l lu then Some (n,lu) else from_block l bs)"

lemma "\<lbrakk>from_block x (raw_blocks (get_blocks c)) = Some (n,l,u); offset x y<u\<rbrakk>
  \<Longrightarrow> access (get_memory c) x y \<noteq> None"
proof
  assume assms: "from_block x (raw_blocks (get_blocks c)) = Some (n, l, u)" "offset x y < u" 
    "access (get_memory c) x y = None"
  show False sorry
qed

fun bounds :: "block list \<Rightarrow> loc \<Rightarrow> (loc\<times>loc)" where
  "bounds [] l = (0,0)"
| "bounds ((_,lu)#bs) l = (if intv l lu then lu else bounds bs l)"

lemma bounds_neq_zero_in: "fst (bounds b l) \<noteq> 0 \<Longrightarrow> \<exists>n. (n,bounds b l) \<in> set b"
  apply (induction rule: bounds.induct) by simp fastforce

lemma bounds_neq_zero: "fst (bounds b l) \<noteq> 0 \<Longrightarrow> intv l (bounds b l)"
  by (induction rule: bounds.induct) auto

lemma sublist_raw_blocks: "b#bs = raw_blocks B \<Longrightarrow> bs \<in> {b. (\<forall>n l u. (n, l, u) \<in> set b \<longrightarrow> l < u \<and> l \<noteq> 0) \<and>
         (\<forall>n1 n2 l1 l2 u1 u2. (n1, l1, u1) \<in> set b \<and> (n2, l2, u2) \<in> set b \<and> (l1 \<noteq> l2 \<or> u1 \<noteq> u2) 
          \<longrightarrow> ((u1\<le>l2 \<or> u2\<le>l1) \<and> n1\<noteq>n2))}" (is "_ \<Longrightarrow> _ \<in> {b. ?block_inv b}")
proof -
  assume "b#bs = raw_blocks B"
  with blocks.raw_blocks have "b#bs \<in> {b. ?block_inv b}" by presburger
  then have "?block_inv (b#bs)" by blast
  moreover have "set bs \<subseteq> set (b#bs)" by (rule set_subset_Cons)
  ultimately have "?block_inv bs" by blast
  then show ?thesis by blast
qed

lemma base_eq_zero: "fst (bounds (raw_blocks B) l) = 0 \<Longrightarrow> snd (bounds (raw_blocks B) l) = 0"
proof (induction "raw_blocks B" l arbitrary: B rule: bounds.induct)
  case (1 l)
  then show ?case by simp
next
  case (2 n lu bs l)
  from Blocks_inverse[OF sublist_raw_blocks[OF this(2)]] have bs: "bs = raw_blocks (Blocks bs)" ..
  show ?case proof (cases "intv l lu")
    case True
    with 2(2)[symmetric] have "bounds (raw_blocks B) l = lu" by auto
    with 2(3) have l0: "fst lu = 0" by simp
    from blocks.raw_blocks 2(2) have "\<forall>n' l u. (n', l, u) \<in> set ((n,lu)#bs) \<longrightarrow> l < u \<and> l \<noteq> 0"
      by simp
    then have "fst lu \<noteq> 0" by (metis list.set_intros(1) prod.collapse)
    with l0 show ?thesis by simp
  next
    case False
    with 2(2)[symmetric] have Bbs: "bounds (raw_blocks B) l = bounds bs l" by simp
    with 2(3) have "fst (bounds bs l) = 0" by simp
    with 2(1)[OF False bs] bs have "snd (bounds bs l) = 0" by simp
    with Bbs show ?thesis by simp
  qed
qed

lift_definition base :: "blocks \<Rightarrow> loc \<Rightarrow> loc" is "\<lambda>B l. fst (bounds B l)" .
lift_definition ende :: "blocks \<Rightarrow> loc \<Rightarrow> loc" is "\<lambda>B l. snd (bounds B l)" .

lemma blocks_axiom1: "base B l = 0 \<or> (base B l \<le> l \<and> l < ende B l)"
proof (auto)  
  assume base_neq_zero: "base B l \<noteq> 0"
  obtain b e where be:"bounds (raw_blocks B) l = (b,e)" by force
  from base_neq_zero bounds_neq_zero have "intv l (bounds (raw_blocks B) l)" unfolding base.rep_eq by simp
  with be have "intv l (b,e)" by simp
  then show "base B l \<le> l" unfolding base.rep_eq be by simp
next
  assume base_neq_zero: "base B l \<noteq> 0"
  obtain b e where be:"bounds (raw_blocks B) l = (b,e)" by force
  from base_neq_zero bounds_neq_zero have "intv l (bounds (raw_blocks B) l)" unfolding base.rep_eq by simp
  with be have "intv l (b,e)" by simp
  then show "l < ende B l" unfolding ende.rep_eq be by simp
qed

lemma blocks_axiom2: 
  "(0<base B l \<and> base B l<ende B l' \<and> ende B l'\<le>ende B l) \<or>
   (0<base B l' \<and> base B l'<ende B l \<and> ende B l\<le>ende B l') \<Longrightarrow>
    base B l = base B l' \<and> ende B l = ende B l'"
proof (auto)
  assume assms: "0<base B l" "base B l<ende B l'" "ende B l'\<le>ende B l"
  from assms base_eq_zero[of B] have bl'0: "base B l' \<noteq> 0" unfolding base.rep_eq ende.rep_eq by auto
  from assms have bl0: "base B l \<noteq> 0" by simp
  {
    assume "base B l \<noteq> base B l'"
    then have "bounds (raw_blocks B) l \<noteq> bounds (raw_blocks B) l'" by (auto simp: base.rep_eq)
    moreover from bounds_neq_zero_in bl0 obtain n where "(n, bounds (raw_blocks B) l) \<in> set (raw_blocks B)" 
      by (auto simp: base.rep_eq)
    moreover from bounds_neq_zero_in bl'0 obtain n' where n': "(n', bounds (raw_blocks B) l') \<in> set (raw_blocks B)" 
      by (auto simp: base.rep_eq)
    ultimately have "(snd (bounds (raw_blocks B) l)\<le>fst (bounds (raw_blocks B) l') \<or> snd (bounds (raw_blocks B) l')\<le>fst (bounds (raw_blocks B) l)) 
      \<and> n\<noteq>n'" using blocks.raw_blocks by (smt (verit, ccfv_threshold) mem_Collect_eq prod.collapse)
    with assms(2) have "snd (bounds (raw_blocks B) l)\<le>fst (bounds (raw_blocks B) l')" by (auto simp:  base.rep_eq ende.rep_eq)
    with assms(3)[unfolded ende.rep_eq] have "snd (bounds (raw_blocks B) l') \<le>  fst (bounds (raw_blocks B) l')" by simp
    with n' blocks.raw_blocks[of B] have False using base.rep_eq bl'0 blocks_axiom1 ende.rep_eq order.trans by fastforce
  }
  then show "base B l = base B l'" by auto
next
  assume assms: "0<base B l" "base B l<ende B l'" "ende B l'\<le>ende B l"
  from assms base_eq_zero[of B] have bl'0: "base B l' \<noteq> 0" unfolding base.rep_eq ende.rep_eq by auto
  from assms have bl0: "base B l \<noteq> 0" by simp
  {
    assume "ende B l \<noteq> ende B l'"
    then have "bounds (raw_blocks B) l \<noteq> bounds (raw_blocks B) l'" by (auto simp: ende.rep_eq)
    moreover from bounds_neq_zero_in bl0 obtain n where "(n, bounds (raw_blocks B) l) \<in> set (raw_blocks B)" 
      by (auto simp: base.rep_eq)
    moreover from bounds_neq_zero_in bl'0 obtain n' where n': "(n', bounds (raw_blocks B) l') \<in> set (raw_blocks B)" 
      by (auto simp: base.rep_eq)
    ultimately have "(snd (bounds (raw_blocks B) l)\<le>fst (bounds (raw_blocks B) l') \<or> snd (bounds (raw_blocks B) l')\<le>fst (bounds (raw_blocks B) l)) 
      \<and> n\<noteq>n'" using blocks.raw_blocks by (smt (verit, ccfv_threshold) mem_Collect_eq prod.collapse)
    with assms(2) have "snd (bounds (raw_blocks B) l)\<le>fst (bounds (raw_blocks B) l')" by (auto simp:  base.rep_eq ende.rep_eq)
    with assms(3)[unfolded ende.rep_eq] have "snd (bounds (raw_blocks B) l') \<le>  fst (bounds (raw_blocks B) l')" by simp
    with n' blocks.raw_blocks[of B] have False using base.rep_eq bl'0 blocks_axiom1 ende.rep_eq order.trans by fastforce
  }
  then show "ende B l = ende B l'" by auto
next
  assume assms: "0 < base B l'" "base B l' < ende B l" "ende B l \<le> ende B l'"
  from assms base_eq_zero[of B] have bl0: "base B l \<noteq> 0" unfolding base.rep_eq ende.rep_eq by auto
  from assms have bl'0: "base B l' \<noteq> 0" by simp
  {
    assume "base B l \<noteq> base B l'"
    then have "bounds (raw_blocks B) l \<noteq> bounds (raw_blocks B) l'" by (auto simp: base.rep_eq)
    moreover from bounds_neq_zero_in bl0 obtain n where n: "(n, bounds (raw_blocks B) l) \<in> set (raw_blocks B)" 
      by (auto simp: base.rep_eq)
    moreover from bounds_neq_zero_in bl'0 obtain n' where "(n', bounds (raw_blocks B) l') \<in> set (raw_blocks B)" 
      by (auto simp: base.rep_eq)
    ultimately have "(snd (bounds (raw_blocks B) l)\<le>fst (bounds (raw_blocks B) l') \<or> snd (bounds (raw_blocks B) l')\<le>fst (bounds (raw_blocks B) l)) 
      \<and> n\<noteq>n'" using blocks.raw_blocks by (smt (verit, ccfv_threshold) mem_Collect_eq prod.collapse)
    with assms(2) have "snd (bounds (raw_blocks B) l')\<le>fst (bounds (raw_blocks B) l)" by (auto simp:  base.rep_eq ende.rep_eq)
    with assms(3)[unfolded ende.rep_eq] have "snd (bounds (raw_blocks B) l) \<le>  fst (bounds (raw_blocks B) l)" by simp
    with n blocks.raw_blocks[of B] have False using base.rep_eq bl0 blocks_axiom1 ende.rep_eq order.trans by fastforce
  }
  then show "base B l = base B l'" by auto
next
   assume assms: "0 < base B l'" "base B l' < ende B l" "ende B l \<le> ende B l'"
  from assms base_eq_zero[of B] have bl0: "base B l \<noteq> 0" unfolding base.rep_eq ende.rep_eq by auto
  from assms have bl'0: "base B l' \<noteq> 0" by simp
  {
    assume "ende B l \<noteq> ende B l'"
    then have "bounds (raw_blocks B) l \<noteq> bounds (raw_blocks B) l'" by (auto simp: ende.rep_eq)
    moreover from bounds_neq_zero_in bl0 obtain n where n: "(n, bounds (raw_blocks B) l) \<in> set (raw_blocks B)" 
      by (auto simp: base.rep_eq)
    moreover from bounds_neq_zero_in bl'0 obtain n' where "(n', bounds (raw_blocks B) l') \<in> set (raw_blocks B)" 
      by (auto simp: base.rep_eq)
    ultimately have "(snd (bounds (raw_blocks B) l)\<le>fst (bounds (raw_blocks B) l') \<or> snd (bounds (raw_blocks B) l')\<le>fst (bounds (raw_blocks B) l)) 
      \<and> n\<noteq>n'" using blocks.raw_blocks by (smt (verit, ccfv_threshold) mem_Collect_eq prod.collapse)
    with assms(2) have "snd (bounds (raw_blocks B) l')\<le>fst (bounds (raw_blocks B) l)" by (auto simp:  base.rep_eq ende.rep_eq)
    with assms(3)[unfolded ende.rep_eq] have "snd (bounds (raw_blocks B) l) \<le>  fst (bounds (raw_blocks B) l)" by simp
    with n blocks.raw_blocks[of B] have False using base.rep_eq bl0 blocks_axiom1 ende.rep_eq order.trans by fastforce
  }
  then show "ende B l = ende B l'" by auto
qed

end