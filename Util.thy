theory Util
  imports 
    Main
    "HOL-Library.FuncSet"
    "HOL-Algebra.Congruence"
begin

lemma dom_eqI1[intro]:
  "(\<And>t. (f t \<noteq> None) = (g t \<noteq> None)) \<Longrightarrow> dom f = dom g"
  unfolding dom_def by auto

lemma dom_eqI2[intro]:
  "(\<And>t. (f t = None) = (g t = None)) \<Longrightarrow> dom f = dom g"
  unfolding dom_def by auto

lemma map_eqI[intro]:
  "dom A = dom B \<Longrightarrow> (\<And>x. x\<in>dom A \<Longrightarrow> A x = B x) \<Longrightarrow> A = B"
  by (simp add: map_le_antisym map_le_def)

lemma map_update_simp[simp]:
  "the ((c(x\<mapsto>u)) x) = u"
  by simp

lemma family_index_eqI[intro]:
  "I=J \<Longrightarrow> {f i|i. i\<in>I} = {f j|j. j\<in>J}"
  by auto

lemma union_fam_eqI[intro]:
  "\<Omega> = \<Omega>' \<Longrightarrow> \<Union>\<Omega> = \<Union>\<Omega>'"
  by auto

lemma func_index_shift:
  "\<And>(f::nat \<Rightarrow> 'a) (n::nat) (m::nat). n\<ge>m \<Longrightarrow> {f i| i. i\<in>{m::nat..n}} = {f (i-1)| i. i\<in>{(m+1)::nat..n+1}}"
proof - 
  fix f n m
  assume \<open>(n::nat)\<ge>m\<close>
  show "{(f::nat \<Rightarrow> 'a) i| i. i\<in>{m::nat..n}} = {f (i-1)| i. i\<in>{m+1..n+1}}"
    by force
qed

lemma list_map_apply:
  "length xs > 0 \<Longrightarrow> i\<in>{0::nat..length xs-1} \<Longrightarrow> (map f xs) ! i = f (xs ! i)"
  using nth_map
  by (metis atLeastAtMost_iff diff_less le_eq_less_or_eq less_imp_diff_less less_numeral_extra(1) linorder_not_le)

lemma dom_map_predicate:
  "dom (\<lambda>x. if P x then Some q else None) = {x. P x}"
  by (simp add: dom_def)

lemma addM_range: "x \<in> {n::nat..m} \<Longrightarrow> x+k \<in> {n+k::nat .. m+k}"
  by auto

lemma app_eqI:"a=b \<Longrightarrow> f a = f b"
  by auto

lemma ge_le_eq_cases:
  fixes i::"nat" and j::"nat"
  shows "(j<i \<Longrightarrow> P) \<Longrightarrow> (j=i \<Longrightarrow> P) \<Longrightarrow> (j>i \<Longrightarrow> P) \<Longrightarrow> P"
  by linarith

lemma le_geq_cases:
  fixes i::"nat" and j::"nat"
  shows "(j<i \<Longrightarrow> P) \<Longrightarrow> (j\<ge>i \<Longrightarrow> P) \<Longrightarrow> P"
  by linarith

lemma nat_induct_one [case_names zero one suc]:
  "P 0 \<Longrightarrow> P 1 \<Longrightarrow> (\<And>(n::nat). n\<ge>1 \<Longrightarrow> P n \<Longrightarrow> P (Suc n)) \<Longrightarrow> (\<And>(n::nat). P n)"
proof (rule nat.induct)
  show "\<And>n. P 0 \<Longrightarrow> P 1 \<Longrightarrow> (\<And>n. 1 \<le> n \<Longrightarrow> P n \<Longrightarrow> P (Suc n)) \<Longrightarrow> P 0"
    by auto
next
  fix n nat assume IH:"\<And>n. 1 \<le> n \<Longrightarrow> P n \<Longrightarrow> P (Suc n)" and \<open>P nat\<close> and \<open>P 1\<close>
  have a1:"nat=1 \<Longrightarrow> P (Suc nat)"
    using IH \<open>P 1\<close> by auto
  have a2:"nat>1 \<Longrightarrow> P (Suc nat)"
    using IH \<open>P nat\<close> by auto
  show "P (Suc nat)"
    using a1 a2 \<open>P 1\<close> \<open>P nat\<close>
    by (metis IH One_nat_def  less_one linorder_not_le)
qed

(*Given a list Ls, a number k, returns the k-th element of Ls *)
definition get_member:: "'a list \<Rightarrow> (nat \<rightharpoonup> _)" (infixl \<open>\<sqdot>\<close> 100) where
  "get_member Ls k = (if k\<in>{1..length Ls} then Some (nth Ls (k-1)) else None)"

lemma get_member_simp_in[simp]:
  "k\<in>{1..length xs} \<Longrightarrow> get_member xs k = Some (nth xs (k-1))"
  unfolding get_member_def by auto

lemma get_member_simp_the_in[simp]:
  "k\<in>{1..length xs} \<Longrightarrow> the (get_member xs k) = nth xs (k-1)"
  unfolding get_member_def by auto

lemma get_member_simp_notin[simp]:
  "k\<notin>{1..length xs} \<Longrightarrow> get_member xs k = None"
  unfolding get_member_def by auto

(*removes the (i+1)-th element of the list.*)
definition remove_at :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remove_at i xs = take i xs @ drop (i+1) xs"

\<comment>\<open>A non-locale implementation of LFP and GFP of functions based on FuncSet\<close>
lemma restrict_apply: "x\<in>A \<Longrightarrow> (\<lambda>x\<in>A. f x) x = f x"
  using restrict_apply' by auto

lemma restrict_eq: "(\<And>x. x\<in>A\<Longrightarrow> f x = g x) \<Longrightarrow> (\<lambda>x\<in>A. f x) = (\<lambda>x\<in>A. g x)"
  using FuncSet.restrict_ext by auto

lemma restrict_eqR: "(\<And>x. x\<in>A\<Longrightarrow> f x = g x) \<Longrightarrow> g\<in>extensional A \<Longrightarrow> (\<lambda>x\<in>A. f x) = g"
  unfolding extensional_def 
  using FuncSet.restrict_ext by auto

lemma fun_eqI: "(\<And>x. f x = g x) \<Longrightarrow> (\<lambda>x. if x=undefined then undefined else f x) = (\<lambda>x. if x=undefined then undefined else g x)"
  using HOL.ext by auto

definition ambient_inter :: "'a set \<Rightarrow> ('a set) set \<Rightarrow> 'a set" where
"ambient_inter U F = {x\<in>U. \<forall>A\<in>F. x\<in>A}"

lemma ambient_inter_compat [simp]: "F1\<subseteq> F2 \<Longrightarrow> ambient_inter U F2 \<subseteq> ambient_inter U F1"
  unfolding ambient_inter_def by auto

lemma ambient_inter_ambient [simp]: "ambient_inter U F \<subseteq> U" unfolding ambient_inter_def by simp

lemma ambient_inter_eq [intro]: "F1=F2 \<Longrightarrow> ambient_inter U F1 = ambient_inter U F2"
  by auto

lemma ambient_inter_emp [simp]: "ambient_inter U {} = U" unfolding ambient_inter_def by auto

lemma ambient_inter_smallest: "\<And>x. x\<in>F \<Longrightarrow> ambient_inter U F \<subseteq> x" unfolding ambient_inter_def by auto

lemma ambient_inter_contain: "(\<And>f. f\<in>\<Omega> \<Longrightarrow> F f\<subseteq> G f) \<Longrightarrow> ambient_inter w {F f|f. f\<in>\<Omega>} \<subseteq> ambient_inter w {G f|f. f\<in>\<Omega>}"
  unfolding ambient_inter_def by auto

definition amb_comp where
  "amb_comp w a = (if a\<subseteq>w then w-a else undefined)"

lemma amb_comp_simps:
  "a\<subseteq>w \<Longrightarrow> amb_comp w a = w-a"
  "\<not>a\<subseteq>w \<Longrightarrow> amb_comp w a = undefined"
  unfolding amb_comp_def by auto

lemma amb_comp_compat [simp]: "a\<subseteq>w \<Longrightarrow> amb_comp w a\<subseteq>w" by (auto simp add:amb_comp_def)

lemma amb_comp_invo [simp]: "a\<subseteq> w \<Longrightarrow> amb_comp w (amb_comp w a) = a" unfolding amb_comp_def by auto

lemma amb_comp_flip : "a\<subseteq> w \<Longrightarrow> b\<subseteq> w \<Longrightarrow> a\<subseteq>b \<Longrightarrow> amb_comp w b \<subseteq> amb_comp w a"
  unfolding amb_comp_def by auto

lemma amb_comp_dm_basic_orand: "a\<subseteq>w \<Longrightarrow> b\<subseteq>w \<Longrightarrow> 
  (amb_comp w (a\<union>b) = amb_comp w a \<inter> amb_comp w b)"
  unfolding amb_comp_def by auto
lemma amb_comp_dm_basic_andor: "a\<subseteq>w \<Longrightarrow> b\<subseteq>w \<Longrightarrow>
 (amb_comp w (a\<inter>b) = amb_comp w a \<union> amb_comp w b)"
  unfolding amb_comp_def by auto
lemma amb_comp_dm_basic:"a\<subseteq>w \<Longrightarrow> b\<subseteq>w \<Longrightarrow>
  ((amb_comp w (a\<union>b) = amb_comp w a \<inter> amb_comp w b) \<and> (amb_comp w (a\<inter>b) = amb_comp w a \<union> amb_comp w b))"
  using amb_comp_dm_basic_andor[of "a""w""b"] amb_comp_dm_basic_orand[of "a""w""b"] by auto 


lemma amb_comp_dm_andor: 
  assumes "\<Omega> \<subseteq> Pow w"
  shows "amb_comp w (ambient_inter w \<Omega>) = \<Union> {amb_comp w s |s. s\<in>\<Omega>}"
proof (cases "\<Omega>={}")
  case True
  then show ?thesis by (simp add:amb_comp_def)
next
  case False
  then show ?thesis using ambient_inter_ambient apply simp
  proof assume nonemp:"\<Omega> \<noteq> {}"
    show "amb_comp w (ambient_inter w \<Omega>) \<subseteq> \<Union> {amb_comp w s |s. s \<in> \<Omega>}"
    proof fix x assume a:"x \<in> amb_comp w (ambient_inter w \<Omega>)"
      have "ambient_inter w \<Omega>\<subseteq> w" using ambient_inter_ambient by auto
      then have "amb_comp w (ambient_inter w \<Omega>) \<subseteq> w" using amb_comp_compat by auto
      then have b:"x\<in> w" using a by blast 
      from a nonemp have "\<exists>s. s\<in>\<Omega> \<and> x\<notin>s" unfolding amb_comp_def ambient_inter_def 
          using ambient_inter_ambient[of "w" "\<Omega>"]
          by fastforce
        then obtain s where c:"s \<in> \<Omega> \<and> x \<notin> s" by auto
        then have "x\<in> amb_comp w s" using b assms unfolding amb_comp_def by auto
        then show "x \<in> \<Union> {amb_comp w s |s. s \<in> \<Omega>}" using c by auto
      qed
    next
      assume nonemp:"\<Omega>\<noteq>{}"
      show "\<Union> {amb_comp w s |s. s \<in> \<Omega>} \<subseteq> amb_comp w (ambient_inter w \<Omega>)"
      proof - from ambient_inter_smallest have a1:"\<And>s. s\<in>\<Omega> \<Longrightarrow> ambient_inter w \<Omega> \<subseteq> s" by auto
        then have "\<And>s. s\<in>\<Omega> \<Longrightarrow> amb_comp w s \<subseteq> amb_comp w (ambient_inter w \<Omega>)"
          using assms ambient_inter_ambient[of "w""\<Omega>"] by (meson Pow_iff amb_comp_flip in_mono)
        then show ?thesis by auto
      qed
  qed
qed


definition eff_fn_union where "eff_fn_union f g A = f A \<union> g A"

definition eff_fn_union_fam :: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) set \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "eff_fn_union_fam w \<Omega> x = (if x\<subseteq>w then \<Union> { \<phi> x | \<phi>. \<phi> \<in> \<Omega>} else undefined)"

definition eff_fn_inter where "eff_fn_inter f g A = f A \<inter> g A"

definition eff_fn_inter_fam :: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) set \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "eff_fn_inter_fam w \<Omega> x = (if x\<subseteq> w then ambient_inter w { \<phi> x | \<phi>. \<phi> \<in> \<Omega>} else undefined)"

definition fun_le :: "('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set) \<Rightarrow> bool" where
"fun_le f g = (\<forall>x. f x \<subseteq> g x)"

lemma fun_le_refl[simp]: "fun_le f f"
  unfolding fun_le_def by auto

lemma fun_le_antisym: "fun_le f g \<Longrightarrow> fun_le g f \<Longrightarrow> f = g"
  unfolding fun_le_def by blast

lemma fun_le_trans: "fun_le f g \<Longrightarrow> fun_le g h \<Longrightarrow> fun_le f h"
  unfolding fun_le_def by auto

definition extension where
  "extension B = {f. \<forall>x. x \<notin> B \<longrightarrow> f x = undefined }"

lemma extensionI[intro]:
  "(\<And>x. x\<notin>B \<Longrightarrow> f x = undefined) \<Longrightarrow> f \<in> extension B"
  unfolding extension_def by auto

lemma extension_elim[elim]:
  "f \<in> extension B \<Longrightarrow> (\<And>x. x\<notin>B \<Longrightarrow> f x = undefined)"
  unfolding extension_def by auto

definition compo :: "'a set \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c)"
  where "compo A g f = (\<lambda>x\<in>A. g (f x))"

lemma compo_simps [simp]:
  "x\<in>A \<Longrightarrow> compo A g f x = g (f x)"
  "x\<notin>A \<Longrightarrow> compo A g f x = undefined"
  unfolding compo_def by auto

lemma extension_union_extension: "f\<in> extension A\<Longrightarrow> g\<in> extension A \<Longrightarrow> (\<lambda>x. f x \<union> g x) \<in> extension A"
  by (simp add:extension_def)

lemma extension_inter_extension: "f\<in> extension A \<Longrightarrow> g\<in> extension A \<Longrightarrow> (\<lambda>x. f x \<inter> g x) \<in> extension A"
  by (simp add:extension_def)

lemma extension_compo_extension: "f\<in> extension A\<Longrightarrow> g \<in> extension A \<Longrightarrow> compo A g f \<in> extension A"
  by (simp add:compo_def extension_def)

definition empty_func :: "'a set \<Rightarrow> 'a set" where
  "empty_func A = {}"

definition extension_fn :: "('a set \<Rightarrow> 'a set) set \<Rightarrow> (('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) set" where
  "extension_fn W = {f. \<forall>x. x\<notin> W \<longrightarrow> f x = empty_func}"

definition carrier_of :: "'a set \<Rightarrow> ('a set\<Rightarrow> 'a set) set" where
  "carrier_of A = (Pow A\<rightarrow>Pow A) \<inter> extension (Pow A)"

lemma carrier_of_elim[elim]:
  "f\<in>carrier_of A \<Longrightarrow> (f\<in>Pow A \<rightarrow> Pow A \<and> f\<in>extension (Pow A))"
  unfolding carrier_of_def by auto

lemma carrier_ofI [intro]:
  "(\<And>s. s\<in>Pow A \<Longrightarrow> f s \<in>Pow A) \<Longrightarrow> (\<And>s. s\<notin> Pow A \<Longrightarrow> f s = undefined) \<Longrightarrow> f\<in>carrier_of A"
  unfolding carrier_of_def extension_def by simp

lemma funcset_compo_funcset: "f\<in> Pow A \<rightarrow> Pow A \<Longrightarrow> g\<in> Pow A \<rightarrow> Pow A \<Longrightarrow> (compo (Pow A) g f) \<in> Pow A \<rightarrow> Pow A"
  by (simp add: Pi_iff compo_def)

lemma carrier_compo_carrier: "f\<in> carrier_of A \<Longrightarrow> g\<in> carrier_of A \<Longrightarrow> (compo (Pow A) g f) \<in> carrier_of A"
  using extension_compo_extension[of "f" "Pow A" "g"] funcset_compo_funcset[of "f" "A" "g"] carrier_of_def[of "A"] by auto 

lemma carrier_union_carrier: "f\<in> carrier_of A \<Longrightarrow> g\<in> carrier_of A \<Longrightarrow> (\<lambda>x. f x \<union> g x) \<in> carrier_of A"
  using extension_union_extension by (auto simp add:carrier_of_def)

lemma carrier_inter_carrier: "f\<in>carrier_of A \<Longrightarrow> g\<in> carrier_of A \<Longrightarrow> (\<lambda>x. f x \<inter> g x) \<in> carrier_of A"
  using extension_inter_extension by (auto simp add:carrier_of_def)

definition mono_of :: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) set" where
  "mono_of A = {f.  \<forall>x y. x\<subseteq>A \<and> y\<subseteq>A \<and> x \<subseteq> y \<longrightarrow> f x \<subseteq> f y}"

lemma mono_ofI [intro]:
  "(\<And>x y. \<lbrakk> x \<subseteq> A ; y \<subseteq> A ; x\<subseteq>y \<rbrakk> \<Longrightarrow> f x \<subseteq> f y) \<Longrightarrow> f\<in>mono_of A"
  unfolding mono_of_def by auto

lemma mono_of_elim [elim]:
  "f\<in>mono_of A \<Longrightarrow> (\<And>x y. \<lbrakk> x \<subseteq> A ; y \<subseteq> A ; x\<subseteq>y \<rbrakk> \<Longrightarrow> f x \<subseteq> f y)"
  unfolding mono_of_def by auto

definition effective_fn_of :: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) set" where
  "effective_fn_of A = carrier_of A \<inter> mono_of A"

lemma effective_fn_of_elim [elim]:
  "f\<in>effective_fn_of A \<Longrightarrow> (f \<in> carrier_of A \<and> f \<in> mono_of A)"
  unfolding effective_fn_of_def by simp

lemma effective_fn_ofI[intro]:
  "f\<in> carrier_of A \<Longrightarrow> f\<in>mono_of A \<Longrightarrow> f\<in>effective_fn_of A"
  unfolding effective_fn_of_def by simp

lemma inter_fixed_set_effective:
  "(\<lambda>A. if A\<subseteq>w then B \<inter> A else undefined) \<in> effective_fn_of w"
  apply rule
   apply (rule carrier_ofI)
    apply auto
  apply rule by auto

lemma union_fixed_set_effective:
  assumes "B\<subseteq> w"
  shows "(\<lambda>A. if A\<subseteq>w then B \<union> A else undefined) \<in> effective_fn_of w"
  apply rule
   apply (rule carrier_ofI)
    using assms apply auto
  apply rule by auto

lemma eff_fn_eq: "f\<in>effective_fn_of w \<Longrightarrow> g\<in>effective_fn_of w \<Longrightarrow> (\<And>s. s\<in>Pow w \<Longrightarrow> f s = g s) \<Longrightarrow> f=g"
proof fix x assume a_f:"f\<in>effective_fn_of w" and a_g:"g\<in>effective_fn_of w" and a_eq:"\<And>s. s\<in>Pow w \<Longrightarrow> f s = g s"
  show "f x = g x"
  proof (cases "x\<in> Pow w")
    case True
    then show ?thesis using a_eq by auto
  next
    case False
    then show ?thesis using a_f a_g by (simp add:effective_fn_of_def carrier_of_def extension_def)
  qed
qed

lemma eff_fn_img_valid:"x\<in>Pow A \<Longrightarrow> f\<in>effective_fn_of A \<Longrightarrow> f x\<in>Pow A"
  unfolding effective_fn_of_def carrier_of_def by auto

lemma eff_fn_img_invalid:"x\<notin>Pow A \<Longrightarrow> f\<in>effective_fn_of A \<Longrightarrow> f x=undefined"
  unfolding effective_fn_of_def carrier_of_def extension_def by auto

lemma eff_fn_img_mono: "x\<in>Pow A \<Longrightarrow> y\<in>Pow A \<Longrightarrow> x\<subseteq>y \<Longrightarrow> f\<in>effective_fn_of A
  \<Longrightarrow> f x \<subseteq> f y"
  unfolding effective_fn_of_def mono_of_def by auto

lemma eff_compo_mono: "f\<in> carrier_of A \<inter> mono_of A \<Longrightarrow> g\<in> carrier_of A \<inter> mono_of A \<Longrightarrow> compo (Pow A) g f \<in> mono_of A"
  apply (simp add: mono_of_def compo_def carrier_of_def)
  by (simp add: Pi_iff)

lemma mono_union_mono: "f\<in> mono_of A \<Longrightarrow> g\<in> mono_of A \<Longrightarrow> (\<lambda>x. f x \<union> g x) \<in> mono_of A"
  apply (simp add:mono_of_def)
  by (simp add: sup.coboundedI1 sup.coboundedI2)

lemma mono_inter_mono: "f\<in> mono_of A \<Longrightarrow> g\<in> mono_of A \<Longrightarrow> (\<lambda>x. f x \<inter> g x) \<in> mono_of A"
  apply (simp add:mono_of_def)
  by (simp add: inf.coboundedI1 inf.coboundedI2)

lemma eff_compo_eff: "f\<in> effective_fn_of A \<Longrightarrow> g\<in>effective_fn_of A \<Longrightarrow> compo (Pow A) g f \<in> effective_fn_of A"
  using eff_compo_mono carrier_compo_carrier apply (auto simp add:effective_fn_of_def)
  by force

lemma eff_compo_assoc: "f\<in>effective_fn_of w \<Longrightarrow> g\<in>effective_fn_of w \<Longrightarrow> h\<in>effective_fn_of w
  \<Longrightarrow> compo (Pow w) h (compo (Pow w) g f) = compo (Pow w) (compo (Pow w) h g) f"
proof (rule eff_fn_eq)
  show "f \<in> effective_fn_of w \<Longrightarrow> g \<in> effective_fn_of w \<Longrightarrow> h \<in> effective_fn_of w \<Longrightarrow> compo (Pow w) h (compo (Pow w) g f) \<in> effective_fn_of w"
    using eff_compo_eff by blast
next
  show "f \<in> effective_fn_of w \<Longrightarrow> g \<in> effective_fn_of w \<Longrightarrow> h \<in> effective_fn_of w \<Longrightarrow> compo (Pow w) (compo (Pow w) h g) f \<in> effective_fn_of w"
    using eff_compo_eff by blast
next
  fix s assume "s \<in> Pow w" and "f\<in>effective_fn_of w" and "g\<in>effective_fn_of w" and "h\<in>effective_fn_of w"
  then show "compo (Pow w) h (compo (Pow w) g f) s = compo (Pow w) (compo (Pow w) h g) f s"
    unfolding compo_def effective_fn_of_def carrier_of_def by auto
qed

lemma eff_union_eff: "f\<in> effective_fn_of A \<Longrightarrow> g\<in>effective_fn_of A \<Longrightarrow> (\<lambda>x. f x \<union> g x) \<in> effective_fn_of A"
  using carrier_union_carrier mono_union_mono by (auto simp add:effective_fn_of_def)

lemma eff_inter_eff: "f\<in> effective_fn_of A \<Longrightarrow> g\<in>effective_fn_of A \<Longrightarrow> (\<lambda>x. f x \<inter> g x) \<in> effective_fn_of A"
  using carrier_inter_carrier mono_inter_mono by (auto simp add:effective_fn_of_def)

lemma fun_le_eff:"f \<in>effective_fn_of A \<Longrightarrow> g\<in>effective_fn_of A \<Longrightarrow> (\<And>x. x\<in>Pow A \<Longrightarrow> f x \<subseteq> g x) \<Longrightarrow> fun_le f g"
proof - assume a_f:"f \<in>effective_fn_of A" and a_g:"g\<in>effective_fn_of A" and cri:"\<And>x. x\<in>Pow A \<Longrightarrow> f x \<subseteq> g x"
  show "fun_le f g" unfolding fun_le_def
  proof fix x show "f x \<subseteq> g x"
    proof (cases "x\<in>Pow A")
      case True
      then show ?thesis using cri by auto
    next
      case False
      then show ?thesis 
      proof - assume "x\<notin> Pow A"
        then have "f x = undefined \<and> g x = undefined" 
          using a_f a_g eff_fn_img_invalid by metis
        then show ?thesis by auto
      qed
    qed
  qed
qed

lemma union_preserve_fun_le':
  "fun_le f1 f2 \<Longrightarrow> fun_le g1 g2 \<Longrightarrow> fun_le (\<lambda>a. f1 a \<union> g1 a) (\<lambda>a. f2 a \<union> g2 a)"
  by (metis (no_types, lifting) fun_le_def sup.mono)

lemma union_preserve_fun_le:
  "fun_le f1 f2 \<Longrightarrow> fun_le g1 g2 \<Longrightarrow> fun_le (eff_fn_union f1 g1) (eff_fn_union f2 g2)"
  using union_preserve_fun_le' unfolding eff_fn_union_def by auto

lemma inter_preserve_fun_le':
  "fun_le f1 f2 \<Longrightarrow> fun_le g1 g2 \<Longrightarrow> fun_le (\<lambda>a. f1 a \<inter> g1 a) (\<lambda>a. f2 a \<inter> g2 a)"
  by (metis (no_types, lifting) fun_le_def inf.mono)

lemma inter_preserve_fun_le:
  "fun_le f1 f2 \<Longrightarrow> fun_le g1 g2 \<Longrightarrow> fun_le (eff_fn_inter f1 g1) (eff_fn_inter f2 g2)"
  using inter_preserve_fun_le' unfolding eff_fn_inter_def by auto

lemma compo_preserve_fun_le: "f1\<in> effective_fn_of A 
\<Longrightarrow> f2\<in> effective_fn_of A \<Longrightarrow> g1\<in> effective_fn_of A \<Longrightarrow> g2 \<in> effective_fn_of A 
\<Longrightarrow> fun_le f1 f2 \<Longrightarrow> fun_le g1 g2 \<Longrightarrow> fun_le (compo (Pow A) g1 f1) (compo (Pow A) g2 f2)"
proof - assume a_f:"fun_le f1 f2" and a_g:"fun_le g1 g2" and b_f1:"f1\<in> effective_fn_of A"
  and b_f2:"f2\<in> effective_fn_of A" and b_g1:"g1\<in> effective_fn_of A" and b_g2:"g2 \<in> effective_fn_of A"
  show "fun_le (compo (Pow A) g1 f1) (compo (Pow A) g2 f2)"
  proof (rule fun_le_eff)
    show "compo (Pow A) g1 f1 \<in> effective_fn_of A"
      using b_f1 b_g1 eff_compo_eff by auto
  next
    show "compo (Pow A) g2 f2 \<in> effective_fn_of A"
      using b_f2 b_g2 eff_compo_eff by auto
  next fix x assume ass:"x\<in>Pow A" then show "compo (Pow A) g1 f1 x \<subseteq> compo (Pow A) g2 f2 x"
    proof - have c1:"f1 x\<subseteq> f2 x" 
        using a_f unfolding fun_le_def by auto
      have c2:"f1 x \<subseteq> A \<and> f2 x \<subseteq> A" 
        using b_f1 b_f2 eff_fn_img_valid ass by auto
      have c3:"g1 (f1 x) \<subseteq> g2 (f1 x)"
        using a_g unfolding fun_le_def by auto
      have "g2 (f1 x) \<subseteq> g2 (f2 x)"
        using b_g2 eff_fn_img_mono[of "f1 x""A" "f2 x" "g2"] c1 c2 by simp
      then show ?thesis using c3 ass unfolding compo_def by simp
    qed
  qed
qed
      

definition op_of where
  "op_of A = (effective_fn_of A) \<rightarrow> (effective_fn_of A)"

definition op_le :: "(('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) \<Rightarrow> (('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) \<Rightarrow> bool" where
  "op_le F G = (\<forall>x. fun_le (F x) (G x))"

definition op_ext where
  "op_ext A = extension (effective_fn_of A)"

definition eff_op_of where
  "eff_op_of A = op_of A \<inter> op_ext A"

lemma op_le_eff: "F\<in>eff_op_of A \<Longrightarrow> G\<in>eff_op_of A \<Longrightarrow> (\<And>x. x\<in>effective_fn_of A \<Longrightarrow> fun_le (F x) (G x)) \<Longrightarrow> op_le F G"
  unfolding op_le_def
proof assume a_F: "F\<in>eff_op_of A" and a_G:"G\<in>eff_op_of A" and ass:"(\<And>x. x \<in> effective_fn_of A \<Longrightarrow> fun_le (F x) (G x))" fix x show "fun_le (F x) (G x)"
  proof (cases "x\<in>effective_fn_of A")
    case True
    then show ?thesis using ass by auto
  next
    case False
    then show ?thesis using a_F a_G unfolding eff_op_of_def op_ext_def extension_def
    by (simp add: fun_le_def)
  qed
qed


definition monotone_op_of ::"'a set \<Rightarrow> ( ('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set) ) set" where
  "monotone_op_of A = (effective_fn_of A \<rightarrow> effective_fn_of A)
  \<inter> {F. \<forall>g1\<in>effective_fn_of A. \<forall>g2\<in> effective_fn_of A. fun_le g1 g2 \<longrightarrow> fun_le (F g1) (F g2)}"

definition Lfp_family :: "'a set \<Rightarrow> (('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) \<Rightarrow> ('a set \<Rightarrow> 'a set) set" where
  "Lfp_family A f = {\<phi>. \<phi>\<in> effective_fn_of A \<and> fun_le (f \<phi>) \<phi>}"

definition Lfp :: "'a set \<Rightarrow> (('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "Lfp w F a = (if a \<subseteq> w then ambient_inter w {\<phi> a | \<phi>. \<phi> \<in> Lfp_family w F} else undefined)"

lemma Lfp_form:
  "Lfp w F = eff_fn_inter_fam w (Lfp_family w F)"
  unfolding Lfp_def eff_fn_inter_fam_def by auto

definition sLfp_family:: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set set" where
  "sLfp_family A F = {B \<in> Pow A. F B \<subseteq> B}"

lemma sLfp_family_in [simp]:
  "sLfp_family w F \<subseteq> Pow w"
  unfolding sLfp_family_def by auto

definition sLfp:: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set" where
  "sLfp w F = ambient_inter w (sLfp_family w F)"

lemma sLfp_in [simp]:
  "sLfp w F \<subseteq> w"
  unfolding sLfp_def by simp

lemma sLfp_fun_le_mono [intro]:
  "fun_le f1 f2 \<Longrightarrow> sLfp w f1 \<subseteq> sLfp w f2"
  unfolding sLfp_def sLfp_family_def fun_le_def
  by (metis (no_types, lifting) Collect_mono ambient_inter_compat dual_order.trans)

definition sGfp_family:: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set set" where
  "sGfp_family w F = {B \<in> Pow w. B \<subseteq> F B}"

lemma sGfp_family_in [simp]:
  "sGfp_family w F \<subseteq> Pow w"
  unfolding sGfp_family_def by auto

definition sGfp:: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set" where
  "sGfp w F = \<Union>(sGfp_family w F)"

lemma sGfp_in [simp]:
  "sGfp w F \<subseteq> w"
  unfolding sGfp_def sGfp_family_def by auto

lemma sGfp_fun_le_mono [intro]:
  "fun_le f1 f2 \<Longrightarrow> sGfp w f1 \<subseteq> sGfp w f2"
  unfolding sGfp_def sGfp_family_def fun_le_def
  by (smt (verit, del_insts) Collect_mono_iff Sup_subset_mono order_trans)

lemma Lfp_family_eqI[intro]: "Lfp_family A F = Lfp_family A (restrict F (effective_fn_of A))"
  unfolding Lfp_family_def by auto

lemma Lfp_restrict_eqI[intro]: "Lfp w F = Lfp w (\<lambda>x\<in>effective_fn_of w. F x)"
  using Lfp_family_eqI[of "w" "F"] unfolding Lfp_def by presburger

lemma Lfp_family_subset_le:"Lfp_family A G \<subseteq> Lfp_family A F \<Longrightarrow> fun_le (Lfp A F) (Lfp A G)"
  unfolding Lfp_def
proof - assume "Lfp_family A G \<subseteq> Lfp_family A F"
  then have "\<And>a. a\<subseteq>A \<Longrightarrow> {\<phi> a |\<phi>. \<phi> \<in> Lfp_family A G} \<subseteq>{\<phi> a |\<phi>. \<phi> \<in> Lfp_family A F}" by auto
  then have "\<And>a. a\<subseteq>A \<Longrightarrow> ambient_inter A {\<phi> a |\<phi>. \<phi> \<in> Lfp_family A F} \<subseteq> ambient_inter A {\<phi> a |\<phi>. \<phi> \<in> Lfp_family A G}" using ambient_inter_compat by auto
  then show "fun_le (\<lambda>a. if a \<subseteq> A then ambient_inter A {\<phi> a |\<phi>. \<phi> \<in> Lfp_family A F} else undefined) (\<lambda>a. if a \<subseteq> A then ambient_inter A {\<phi> a |\<phi>. \<phi> \<in> Lfp_family A G} else undefined)"
    by (simp add: fun_le_def)
qed


lemma op_le_Lfp_family_subset: "op_le F G \<Longrightarrow> Lfp_family w G \<subseteq> Lfp_family w F"
  unfolding op_le_def Lfp_family_def using fun_le_trans by auto

lemma op_le_Lfp__fun_le: "op_le F G \<Longrightarrow> fun_le (Lfp w F) (Lfp w G)"
  using Lfp_family_subset_le[of "w" "G" "F"] op_le_Lfp_family_subset[of "F" "G" "w"] by auto

definition dual_eff_fn:: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "dual_eff_fn w f a = (if a\<subseteq> w then amb_comp w (f (amb_comp w a)) else undefined)"

lemma dual_eff_fn_compat_img: "a\<subseteq>w \<Longrightarrow> dual_eff_fn w f a = amb_comp w (f (amb_comp w a))" unfolding dual_eff_fn_def by simp

lemma ext_dual_ext: "f \<in> extension (Pow w) \<Longrightarrow> dual_eff_fn w f \<in>  extension (Pow w)"
  unfolding extension_def dual_eff_fn_def by auto

lemma mono_dual_mono: "f \<in> mono_of w \<Longrightarrow> f\<in> Pow w \<rightarrow> Pow w \<Longrightarrow> dual_eff_fn w f \<in> mono_of w"
  unfolding dual_eff_fn_def mono_of_def amb_comp_def apply simp
  by (metis Diff_mono Diff_subset Pow_iff funcset_mem order_eq_refl)

lemma funcset_dual_funcset: "f\<in> Pow w \<rightarrow> Pow w \<Longrightarrow> dual_eff_fn w f\<in> Pow w \<rightarrow> Pow w"
  unfolding dual_eff_fn_def amb_comp_def
  by (simp add: Pi_iff)

lemma eff_dual_eff: "f\<in> effective_fn_of w \<Longrightarrow> dual_eff_fn w f \<in> effective_fn_of w"
  using mono_dual_mono[of "f""w"] ext_dual_ext[of "f""w"] funcset_dual_funcset[of "f""w"] 
  unfolding effective_fn_of_def carrier_of_def by auto

lemma dual_eff_fn_invo [simp]: "f\<in> effective_fn_of w \<Longrightarrow> dual_eff_fn w (dual_eff_fn w f) = f"
  unfolding dual_eff_fn_def effective_fn_of_def carrier_of_def extension_def
proof fix a assume a1:"f \<in> (Pow w \<rightarrow> Pow w) \<inter> {f. \<forall>x. x \<notin> Pow w \<longrightarrow> f x = undefined} \<inter> mono_of w"
  show "(if a \<subseteq> w then amb_comp w (if amb_comp w a \<subseteq> w then amb_comp w (f (amb_comp w (amb_comp w a))) else undefined) else undefined) = f a"
    apply simp apply rule
  proof
    assume a2:"a\<subseteq>w"
    show "amb_comp w (amb_comp w (f a)) = f a" using amb_comp_invo a2 a1 Pow_iff by auto
  next
    show "\<not> a \<subseteq> w \<longrightarrow> undefined = f a"
    proof assume a2:"\<not> a\<subseteq> w"
      show "undefined = f a" using a1 Pow_iff a2 by auto
    qed
  qed
qed

definition dual_op where
  "dual_op w F f = dual_eff_fn w (F (dual_eff_fn w f))"

lemma dual_op__op: "F\<in>op_of w \<Longrightarrow> dual_op w F \<in>op_of w"
  unfolding op_of_def dual_op_def using eff_dual_eff by auto

definition op_homo_dual where
  "op_homo_dual w F \<equiv> \<forall>f\<in> effective_fn_of w. F (dual_eff_fn w f) = dual_eff_fn w (F f)"

definition max_of :: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "max_of A x = (if x\<subseteq>A then A else undefined)"

lemma max_of_in_carrier : "max_of A \<in> carrier_of A"
  apply (auto simp add:max_of_def carrier_of_def)
proof 
  fix x assume \<open>x\<notin> Pow A\<close> then show "max_of A x = undefined" 
    by (auto simp add:max_of_def)
qed

lemma max_of_in_funcset : "max_of A \<in> Pow A \<rightarrow> Pow A"
proof -
  from max_of_in_carrier have "max_of A \<in> (Pow A\<rightarrow>Pow A) \<inter> extension (Pow A)" by (simp add:carrier_of_def)
  then show ?thesis by auto
qed

lemma max_of_mono : "max_of A \<in> mono_of A" 
  by (auto simp add:mono_of_def max_of_def)

lemma max_of_effective [simp]: "max_of A \<in> effective_fn_of A"
  using max_of_mono[of "A"] max_of_in_carrier[of "A"] by (simp add:effective_fn_of_def)

lemma effective_op_effective : "f\<in> monotone_op_of A \<Longrightarrow> \<phi>\<in> effective_fn_of A \<Longrightarrow> f \<phi> \<in> effective_fn_of A "
  by (simp add: Pi_iff monotone_op_of_def)

lemma max_of_properties : 
  assumes "A \<noteq> {}"
    and P1: " f\<in> monotone_op_of A "
  shows "max_of A \<in> effective_fn_of A
\<and> (\<forall> xa. f (max_of A) xa \<subseteq> max_of A xa)"
  proof -
    have R1: "max_of A \<in> effective_fn_of A" using max_of_effective by auto
    have R2: "\<forall>xa. f (max_of A) xa \<subseteq> max_of A xa"
      apply (simp add:max_of_def)
    proof 
      fix xa show "(xa \<subseteq> A \<longrightarrow> f (max_of A) xa \<subseteq> A) \<and> (\<not> xa \<subseteq> A \<longrightarrow> f (max_of A) xa \<subseteq> undefined)"
      proof -
        have Q1:"xa \<subseteq> A \<longrightarrow> f (max_of A) xa \<subseteq> A"
        proof -
          have P2: "max_of A \<in> effective_fn_of A" by simp
          then have "f (max_of A) \<in> effective_fn_of A" using assms by (auto simp add:monotone_op_of_def)
          thus ?thesis by (auto simp add:effective_fn_of_def carrier_of_def)
        qed

        have Q2: "(\<not> xa \<subseteq> A \<longrightarrow> f (max_of A) xa = undefined)"
        proof assume a:"\<not> xa \<subseteq> A"
          have "f (max_of A)\<in> effective_fn_of A" using assms effective_op_effective[of "f" "A" "max_of A"] by simp 
          then have "f (max_of A) \<in> extension (Pow A)" by (auto simp add:effective_fn_of_def carrier_of_def)
          then show "f (max_of A) xa = undefined" using a by (simp add:effective_fn_of_def carrier_of_def extension_def)
        qed
        from Q1 Q2 show ?thesis by auto
      qed
    qed
    from R1 R2 show ?thesis by auto
  qed

lemma Lfp_family_nonempty :
  assumes "A \<noteq> {}"
    and P1: " f\<in> monotone_op_of A "
  shows " Lfp_family A f \<noteq> {}"
  apply (simp add:Lfp_family_def carrier_of_def extension_def fun_le_def)
proof
  show "max_of A \<in> effective_fn_of A \<and> (\<forall>x. f (max_of A) x \<subseteq> (max_of A) x)"
    using assms max_of_properties[of "A" "f"] by auto
qed

definition Gfp_family :: "'a set \<Rightarrow> (('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) \<Rightarrow> ('a set \<Rightarrow> 'a set) set" where
"Gfp_family A f = {\<phi>. \<phi>\<in> effective_fn_of A \<and> fun_le \<phi> (f \<phi>)}"

lemma Gfp_family_eqI [intro]: "Gfp_family A F = Gfp_family A (restrict F (effective_fn_of A))"
  unfolding Gfp_family_def by auto


definition Gfp :: "'a set \<Rightarrow> (('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "Gfp w F a = (if a\<subseteq>w then \<Union>{\<phi> a | \<phi>. \<phi>\<in> Gfp_family w F} else undefined)"

lemma Gfp_form:
  "Gfp w F = eff_fn_union_fam w (Gfp_family w F)"
  unfolding Gfp_def eff_fn_union_fam_def by auto

lemma Gfp_restrict_eqI: "Gfp w F = Gfp w (\<lambda>x\<in>effective_fn_of w. F x)"
  using Gfp_family_eqI[of "w" "F"] unfolding Gfp_def by presburger

lemma Gfp_family_subset_le:"Gfp_family A F \<subseteq> Gfp_family A G \<Longrightarrow> fun_le (Gfp A F) (Gfp A G)"
  unfolding Gfp_def
proof - assume "Gfp_family A F \<subseteq> Gfp_family A G"
  then have "\<And>a. a\<subseteq>A \<Longrightarrow> {\<phi> a |\<phi>. \<phi> \<in> Gfp_family A F} \<subseteq>{\<phi> a |\<phi>. \<phi> \<in> Gfp_family A G}" by auto
  then have "\<And>a. a\<subseteq>A \<Longrightarrow> \<Union> {\<phi> a |\<phi>. \<phi> \<in> Gfp_family A F} \<subseteq> \<Union> {\<phi> a |\<phi>. \<phi> \<in> Gfp_family A G}" by (simp add:Sup_subset_mono)
  then show "fun_le (\<lambda>a. if a \<subseteq> A then \<Union> {\<phi> a |\<phi>. \<phi> \<in> Gfp_family A F} else undefined) (\<lambda>a. if a \<subseteq> A then \<Union> {\<phi> a |\<phi>. \<phi> \<in> Gfp_family A G} else undefined)"
    by (simp add: fun_le_def)
qed

lemma op_le_Gfp_family_subset: "op_le F G \<Longrightarrow> Gfp_family w F \<subseteq> Gfp_family w G"
  unfolding op_le_def Gfp_family_def using fun_le_trans by auto

lemma op_le_Gfp__fun_le: "op_le F G \<Longrightarrow> fun_le (Gfp w F) (Gfp w G)"
  using Gfp_family_subset_le[of "w" "F" "G"] op_le_Gfp_family_subset[of "F" "G" "w"] by auto


(* constant effectivity function *)
definition con_eff where
  "con_eff w A a = (if a\<subseteq>w then A else undefined)"

lemma con_eff_eff: "A\<subseteq>w \<Longrightarrow> con_eff w A \<in> effective_fn_of w"
  unfolding con_eff_def effective_fn_of_def carrier_of_def
  extension_def mono_of_def by simp

definition id_eff where
  "id_eff w a = (if a\<subseteq>w then a else undefined)"

lemma id_eff_eff:"id_eff w \<in> effective_fn_of w"
  unfolding id_eff_def effective_fn_of_def carrier_of_def mono_of_def extension_def
    id_eff_def by simp

lemma dual_id_eff__id[simp]: "dual_eff_fn w (id_eff w) = id_eff w"
proof (rule eff_fn_eq)
  show "dual_eff_fn w (id_eff w) \<in> effective_fn_of w" using eff_dual_eff id_eff_eff by auto
  show "id_eff w \<in> effective_fn_of w" using id_eff_eff by auto
  fix x assume "x\<in> Pow w" then show "dual_eff_fn w (id_eff w) x = id_eff w x"
    unfolding dual_eff_fn_def id_eff_def using amb_comp_compat Pow_iff amb_comp_invo by auto
qed

lemma eff_compo_id_r: "f\<in>effective_fn_of w \<Longrightarrow> compo (Pow w) f (id_eff w) = f"
proof (rule eff_fn_eq)
  show "f \<in> effective_fn_of w \<Longrightarrow> compo (Pow w) f (id_eff w) \<in> effective_fn_of w"
    using eff_compo_eff id_eff_eff by auto
next
  show "f \<in> effective_fn_of w \<Longrightarrow> f \<in> effective_fn_of w" by auto
next fix s assume "s\<in>Pow w" and "f\<in>effective_fn_of w" then show "compo (Pow w) f (id_eff w) s = f s"
    unfolding compo_def id_eff_def effective_fn_of_def carrier_of_def
    by auto
qed

lemma eff_compo_id_l: "f\<in>effective_fn_of w \<Longrightarrow> compo (Pow w) (id_eff w) f = f"
proof (rule eff_fn_eq)
  show "f \<in> effective_fn_of w \<Longrightarrow> compo (Pow w) (id_eff w) f  \<in> effective_fn_of w"
    using eff_compo_eff id_eff_eff by auto
next
  show "f \<in> effective_fn_of w \<Longrightarrow> f \<in> effective_fn_of w" by auto
next fix s assume "s\<in>Pow w" and "f\<in>effective_fn_of w" 
    then show "compo (Pow w) (id_eff w) f s = f s"
    unfolding compo_def id_eff_def effective_fn_of_def carrier_of_def
    by auto
qed

definition eff_fn_fam_dual_closed where
  "eff_fn_fam_dual_closed w F \<equiv> \<forall>x\<in>F. (dual_eff_fn w x) \<in> F"

lemma all_eff_fn_dual_closed: "eff_fn_fam_dual_closed w (effective_fn_of w)"
  unfolding eff_fn_fam_dual_closed_def
  using eff_dual_eff by auto

lemma dual_eff_fn_compre:
  "{\<phi>. \<phi>\<in> effective_fn_of w \<and> P \<phi>} = {dual_eff_fn w \<phi>|\<phi>. \<phi>\<in>effective_fn_of w \<and> P (dual_eff_fn w \<phi>)}"
  using eff_dual_eff dual_eff_fn_invo
  by force

lemma fun_fam_img_fam:
  "F=G \<Longrightarrow> {f a|f. f\<in>F} = {f a|f. f\<in>G}" by auto

lemma dual_funle_anti:
  "f\<in> effective_fn_of w \<Longrightarrow> g\<in> effective_fn_of w \<Longrightarrow> fun_le f g \<Longrightarrow> fun_le (dual_eff_fn w g) (dual_eff_fn w f)"
  unfolding fun_le_def dual_eff_fn_def apply simp
proof fix x assume a1:"f \<in> effective_fn_of w"
  and a2:"g \<in> effective_fn_of w" and a3:"\<forall>x. f x \<subseteq> g x"
  show "x \<subseteq> w \<longrightarrow> amb_comp w (g (amb_comp w x)) \<subseteq> amb_comp w (f (amb_comp w x))"
  proof 
    assume a4:"x\<subseteq> w"    
    show "amb_comp w (g (amb_comp w x)) \<subseteq> amb_comp w (f (amb_comp w x))"
    proof -
      from a4 have "(amb_comp w x) \<subseteq> w" using amb_comp_compat by auto
      then have b2:"g (amb_comp w x) \<subseteq> w" using a2 
        unfolding effective_fn_of_def carrier_of_def by auto

      from a4 have "(amb_comp w x) \<subseteq> w" using amb_comp_compat by auto
      then have b1:"f (amb_comp w x) \<subseteq> w" using a1
        unfolding effective_fn_of_def carrier_of_def by auto

      from a3 have "f (amb_comp w x) \<subseteq> g (amb_comp w x)" by auto
      then show ?thesis using amb_comp_flip[of "f (amb_comp w x)""w""g (amb_comp w x)"] b2 b1 by auto
    qed
  qed
qed


lemma dual_Lfp__Gfp_dualop: 
  assumes "F\<in> op_of w"
  shows "dual_eff_fn w (Lfp w F) = Gfp w (dual_op w F)"
  unfolding Lfp_def Lfp_family_def Gfp_def Gfp_family_def dual_op_def dual_eff_fn_def apply rule
proof - fix a
  show "(if a \<subseteq> w then amb_comp w (if amb_comp w a \<subseteq> w then ambient_inter w {\<phi> (amb_comp w a) |\<phi>. \<phi> \<in> {\<phi> \<in> effective_fn_of w. fun_le (F \<phi>) \<phi>}} else undefined) else undefined) =
         (if a \<subseteq> w then \<Union> {\<phi> a |\<phi>. \<phi> \<in> {\<phi> \<in> effective_fn_of w. fun_le \<phi> (\<lambda>a. if a \<subseteq> w then amb_comp w (F (\<lambda>a. if a \<subseteq> w then amb_comp w (\<phi> (amb_comp w a)) else undefined) (amb_comp w a)) else undefined)}} else undefined)"
  proof (cases "a\<subseteq> w")
    case True
    then show ?thesis apply (simp)
    proof -
      assume a1:"a\<subseteq>w"
      show "amb_comp w (ambient_inter w {\<phi> (amb_comp w a) |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le (F \<phi>) \<phi>}) =
    \<Union> {\<phi> a |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le \<phi> (\<lambda>a. if a \<subseteq> w then amb_comp w (F (\<lambda>a. if a \<subseteq> w then amb_comp w (\<phi> (amb_comp w a)) else undefined) (amb_comp w a)) else undefined)}" 
      proof - let ?LHS = "amb_comp w (ambient_inter w {\<phi> (amb_comp w a) |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le (F \<phi>) \<phi>})"
        let ?RHS = "\<Union> {\<phi> a |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le \<phi> (\<lambda>a. if a \<subseteq> w then amb_comp w (F (\<lambda>a. if a \<subseteq> w then amb_comp w (\<phi> (amb_comp w a)) else undefined) (amb_comp w a)) else undefined)}"
        have "{\<phi> (amb_comp w a) |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le (F \<phi>) \<phi>} \<subseteq> Pow w"
          using a1 amb_comp_compat[of "a""w"] effective_fn_of_def[of "w"] carrier_of_def[of "w"] by blast
        then have "?LHS = \<Union> {amb_comp w (\<phi> (amb_comp w a)) |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le (F \<phi>) \<phi>}"
          using amb_comp_dm_andor[of "{\<phi> (amb_comp w a) |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le (F \<phi>) \<phi>}" "w"] by auto
        also have "... = \<Union> {dual_eff_fn w \<phi> a |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le (F \<phi>) \<phi>}"
          using a1 unfolding dual_eff_fn_def by auto
        also have "... = \<Union> {dual_eff_fn w (dual_eff_fn w \<phi>) a |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le (F (dual_eff_fn w \<phi>)) (dual_eff_fn w \<phi>)}"
          by (metis (no_types, opaque_lifting) dual_eff_fn_invo eff_dual_eff)
        also have "... = \<Union> {\<phi> a |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le (F (dual_eff_fn w \<phi>)) (dual_eff_fn w \<phi>)}"
          using dual_eff_fn_invo by fastforce
        finally have a3:"?LHS = \<Union> {\<phi> a |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le (F (dual_eff_fn w \<phi>)) (dual_eff_fn w \<phi>)}" by simp

        have a2:"\<forall>\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le (F (dual_eff_fn w \<phi>)) (dual_eff_fn w \<phi>) 
          \<longleftrightarrow> \<phi> \<in> effective_fn_of w \<and> fun_le \<phi> (dual_eff_fn w (F (dual_eff_fn w \<phi>)))"          
          using assms dual_funle_anti dual_eff_fn_invo unfolding op_of_def
          by (metis (no_types, lifting) Pi_mem eff_dual_eff)

        from a3 a2 have a4:"?LHS = \<Union> {\<phi> a |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le \<phi> (dual_eff_fn w (F (dual_eff_fn w \<phi>))) }" by simp

        from a4 show "?LHS=?RHS" unfolding dual_eff_fn_def by simp
      qed
    qed
  next
    case False
    then show ?thesis by auto
  qed
qed

lemma Lfp_dual_op_invo:
  assumes "F\<in>op_of w"
  shows"Lfp w (dual_op w (dual_op w F)) = Lfp w F"
  unfolding Lfp_def dual_op_def
proof - 
  have "Lfp_family w (\<lambda>f. dual_eff_fn w (dual_eff_fn w (F (dual_eff_fn w (dual_eff_fn w f)))))
  = Lfp_family w (\<lambda>f\<in>effective_fn_of w. dual_eff_fn w (dual_eff_fn w (F (dual_eff_fn w (dual_eff_fn w f)))))"
    using Lfp_family_eqI[of "w""\<lambda>f. dual_eff_fn w (dual_eff_fn w (F (dual_eff_fn w (dual_eff_fn w f))))"] by auto
  also have "... = Lfp_family w (\<lambda>f\<in>effective_fn_of w.(F f))"
    using assms op_of_def dual_eff_fn_invo by (smt (verit, best) Pi_iff restrict_ext)
  finally show "(\<lambda>a. if a \<subseteq> w then ambient_inter w {\<phi> a |\<phi>. \<phi> \<in> Lfp_family w (\<lambda>f. dual_eff_fn w (dual_eff_fn w (F (dual_eff_fn w (dual_eff_fn w f)))))} else undefined) =
    (\<lambda>a. if a \<subseteq> w then ambient_inter w {\<phi> a |\<phi>. \<phi> \<in> Lfp_family w F} else undefined)"
    using Lfp_family_eqI by metis
qed

lemma Gfp_dual_op_invo:
  assumes "F\<in>op_of w"
  shows"Gfp w (dual_op w (dual_op w F)) = Gfp w F"
  unfolding Gfp_def dual_op_def
proof - 
  have "Gfp_family w (\<lambda>f. dual_eff_fn w (dual_eff_fn w (F (dual_eff_fn w (dual_eff_fn w f)))))
  =Gfp_family w (\<lambda>f\<in>effective_fn_of w. dual_eff_fn w (dual_eff_fn w (F (dual_eff_fn w (dual_eff_fn w f)))))"
    using Gfp_family_eqI[of "w""\<lambda>f. dual_eff_fn w (dual_eff_fn w (F (dual_eff_fn w (dual_eff_fn w f))))"] by auto
  also have "... = Gfp_family w (\<lambda>f\<in>effective_fn_of w.(F f))"
    using assms op_of_def dual_eff_fn_invo by (smt (verit, best) Pi_iff restrict_ext)
  finally show "(\<lambda>a. if a \<subseteq> w then \<Union> {\<phi> a |\<phi>. \<phi> \<in> Gfp_family w (\<lambda>f. dual_eff_fn w (dual_eff_fn w (F (dual_eff_fn w (dual_eff_fn w f)))))} else undefined) =
    (\<lambda>a. if a \<subseteq> w then \<Union> {\<phi> a |\<phi>. \<phi> \<in> Gfp_family w F} else undefined)"
    using Gfp_family_eqI by metis
qed
  

lemma Lfp_in_carrier : "Lfp w f \<in> carrier_of w"
proof (auto simp add:carrier_of_def)
  fix x xa
  show "x \<subseteq> w \<Longrightarrow> xa \<in> Lfp w f x \<Longrightarrow> xa \<in> w" unfolding Lfp_def ambient_inter_def by auto

  show "Lfp w f \<in> extension (Pow w)" unfolding Lfp_def Lfp_family_def effective_fn_of_def carrier_of_def
    by (simp add:extension_def ambient_inter_def)
qed

lemma Lfp_eff: "Lfp w f \<in> effective_fn_of w"
  apply (simp add:effective_fn_of_def)
  apply (auto simp add:Lfp_in_carrier)
  unfolding Lfp_def mono_of_def apply auto
proof -
  fix x y z assume a0:"z \<in> ambient_inter w {\<phi> x |\<phi>. \<phi> \<in> Lfp_family w f}" 
    and a1:"x \<subseteq> w"
    and a2:"y \<subseteq> w"
    and a3:"x \<subseteq> y"
  have "\<And>\<phi>. \<phi>\<in> Lfp_family w f \<Longrightarrow> \<phi> x \<subseteq> \<phi> y" using a1 a2 a3 by (auto simp add:Lfp_family_def effective_fn_of_def mono_of_def)
  then show "z \<in> ambient_inter w {\<phi> y |\<phi>. \<phi> \<in> Lfp_family w f}" using a0
  by (smt (verit, ccfv_threshold) ambient_inter_def in_mono mem_Collect_eq)
qed

lemma eff_fn_union_fam_funcset: "\<Omega>\<subseteq> effective_fn_of w \<Longrightarrow> eff_fn_union_fam w \<Omega> \<in> (Pow w \<rightarrow> Pow w)"
  unfolding effective_fn_of_def eff_fn_union_fam_def carrier_of_def
  apply rule by auto

lemma eff_fn_union_fam_extension: "\<Omega>\<subseteq> effective_fn_of w \<Longrightarrow> eff_fn_union_fam w \<Omega> \<in> extension (Pow w)"
  unfolding effective_fn_of_def eff_fn_union_fam_def extension_def carrier_of_def
  by auto

lemma eff_fn_union_fam_mono: "\<Omega>\<subseteq> effective_fn_of w \<Longrightarrow> eff_fn_union_fam w \<Omega> \<in> mono_of w"
  unfolding effective_fn_of_def eff_fn_union_fam_def extension_def carrier_of_def mono_of_def
  apply rule apply rule apply rule apply rule
proof - fix x y assume a1:"x \<subseteq> w \<and> y \<subseteq> w \<and> x \<subseteq> y"
  and ass: "\<Omega> \<subseteq> (Pow w \<rightarrow> Pow w) \<inter> {f. \<forall>x. x \<notin> Pow w \<longrightarrow> f x = undefined} \<inter> {f. \<forall>x y. x \<subseteq> w \<and> y \<subseteq> w \<and> x \<subseteq> y \<longrightarrow> f x \<subseteq> f y}"
  show "(if x \<subseteq> w then \<Union> {\<phi> x |\<phi>. \<phi> \<in> \<Omega>} else undefined) \<subseteq> (if y \<subseteq> w then \<Union> {\<phi> y |\<phi>. \<phi> \<in> \<Omega>} else undefined)"
    using a1 apply simp
    using ass by blast
qed

lemma eff_fn_union_fam_eff: "\<Omega>\<subseteq> effective_fn_of w \<Longrightarrow> eff_fn_union_fam w \<Omega> \<in> effective_fn_of w"
  using eff_fn_union_fam_funcset eff_fn_union_fam_extension eff_fn_union_fam_mono
  unfolding effective_fn_of_def carrier_of_def by (metis Int_iff)

definition eff_lub:: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) set \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "eff_lub w \<Omega> = eff_fn_union_fam w \<Omega>"

lemma eff_lub_eff: "\<Omega>\<subseteq> effective_fn_of w \<Longrightarrow>  eff_lub w \<Omega> \<in>effective_fn_of w"
  unfolding eff_lub_def using eff_fn_union_fam_eff by auto

lemma eff_lub_ub: "\<Omega>\<subseteq>effective_fn_of w \<Longrightarrow> x\<in>\<Omega> \<Longrightarrow> fun_le x (eff_lub w \<Omega>)"
proof - assume a1:"\<Omega>\<subseteq>effective_fn_of w" and a2:"x\<in>\<Omega>"
  show "fun_le x (eff_lub w \<Omega>)"
  proof (rule fun_le_eff)
    show "x \<in> effective_fn_of w"
      using a1 a2 by auto
  next show "eff_lub w \<Omega> \<in> effective_fn_of w"
      unfolding eff_lub_def using eff_fn_union_fam_eff a1 by auto
  next show "\<And>xa. xa \<in> Pow w \<Longrightarrow> x xa \<subseteq> eff_lub w \<Omega> xa"
      unfolding eff_lub_def eff_fn_union_fam_def using a2 by auto
  qed
qed

lemma eff_lub_lub: "A \<subseteq> effective_fn_of w \<Longrightarrow>
           x \<in> effective_fn_of w \<Longrightarrow>
           \<forall>y. y \<in> A \<and> y \<in> effective_fn_of w \<longrightarrow> fun_le y x \<Longrightarrow> fun_le (eff_lub w A) x"
  unfolding eff_lub_def
proof - assume a1:"A \<subseteq> effective_fn_of w" and a2:"x\<in>effective_fn_of w" 
    and a3:"\<forall>y. y \<in> A \<and> y \<in> effective_fn_of w \<longrightarrow> fun_le y x"
  show "fun_le (eff_fn_union_fam w A) x"
  proof (rule fun_le_eff)
    show "eff_fn_union_fam w A \<in> effective_fn_of w" using eff_fn_union_fam_eff a1 by auto
    show "x\<in>effective_fn_of w" using a2 by auto
    show "\<And>z. z\<in>Pow w \<Longrightarrow> eff_fn_union_fam w A z \<subseteq> x z"
    proof - from a3 eff_fn_union_fam_eff a1
      have "\<And>\<phi> z. \<phi>\<in>A \<Longrightarrow> z\<in>Pow w \<Longrightarrow> \<phi> z \<subseteq> x z"
        unfolding fun_le_def by blast
      then show "\<And>z. z\<in>Pow w \<Longrightarrow> eff_fn_union_fam w A z \<subseteq> x z"
        unfolding eff_fn_union_fam_def by auto
    qed
  qed
qed

lemma eff_fn_inter_fam_funcset: "\<Omega>\<subseteq> effective_fn_of w \<Longrightarrow> eff_fn_inter_fam w \<Omega> \<in> (Pow w \<rightarrow> Pow w)"
  by (simp add: eff_fn_inter_fam_def)

lemma eff_fn_inter_fam_extension: "\<Omega>\<subseteq> effective_fn_of w \<Longrightarrow> eff_fn_inter_fam w \<Omega> \<in> extension (Pow w)"
  by (simp add: eff_fn_inter_fam_def extension_def)

lemma eff_fn_inter_fam_mono: "\<Omega>\<subseteq> effective_fn_of w \<Longrightarrow> eff_fn_inter_fam w \<Omega> \<in> mono_of w"
  unfolding effective_fn_of_def eff_fn_union_fam_def extension_def carrier_of_def mono_of_def eff_fn_inter_fam_def
  apply rule apply rule apply rule
proof
  fix x y assume a1:"x \<subseteq> w \<and> y \<subseteq> w \<and> x \<subseteq> y"
  and ass: "\<Omega> \<subseteq> (Pow w \<rightarrow> Pow w) \<inter> {f. \<forall>x. x \<notin> Pow w \<longrightarrow> f x = undefined} \<inter> {f. \<forall>x y. x \<subseteq> w \<and> y \<subseteq> w \<and> x \<subseteq> y \<longrightarrow> f x \<subseteq> f y}"
  show "(if x \<subseteq> w then ambient_inter w {\<phi> x |\<phi>. \<phi> \<in> \<Omega>} else undefined) \<subseteq> (if y \<subseteq> w then ambient_inter w {\<phi> y |\<phi>. \<phi> \<in> \<Omega>} else undefined)"
    apply (simp add:a1)
  proof (rule ambient_inter_contain)
    show "\<And>\<phi>. \<phi> \<in> \<Omega> \<Longrightarrow> \<phi> x \<subseteq> \<phi> y" 
      using ass a1 by blast
  qed
qed

lemma eff_fn_inter_fam_eff: "\<Omega>\<subseteq> effective_fn_of w \<Longrightarrow> eff_fn_inter_fam w \<Omega> \<in> effective_fn_of w"
  using eff_fn_inter_fam_funcset eff_fn_inter_fam_mono eff_fn_inter_fam_extension
  by (metis Int_iff carrier_of_def effective_fn_of_def)

definition eff_glb:: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) set \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "eff_glb w \<Omega> = eff_fn_inter_fam w \<Omega>"

lemma eff_glb_eff: "\<Omega>\<subseteq> effective_fn_of w \<Longrightarrow> eff_glb w \<Omega> \<in> effective_fn_of w"
  unfolding eff_glb_def using eff_fn_inter_fam_eff by auto
  
lemma eff_glb_lb: "\<Omega>\<subseteq>effective_fn_of w \<Longrightarrow> x\<in>\<Omega> \<Longrightarrow> fun_le (eff_glb w \<Omega>) x "
proof - assume a1:"\<Omega>\<subseteq>effective_fn_of w" and a2:"x\<in>\<Omega>"
  show "fun_le (eff_glb w \<Omega>) x"
  proof (rule fun_le_eff)
    show "x \<in> effective_fn_of w"
      using a1 a2 by auto
    show "eff_glb w \<Omega> \<in> effective_fn_of w"
      unfolding eff_glb_def using eff_fn_inter_fam_eff a1 by auto
  next show "\<And>xa. xa \<in> Pow w \<Longrightarrow> eff_glb w \<Omega> xa \<subseteq> x xa"
      unfolding eff_glb_def eff_fn_inter_fam_def ambient_inter_def using a2 by auto
  qed
qed

lemma eff_glb_glb: "A \<subseteq> effective_fn_of w \<Longrightarrow>
           x \<in> effective_fn_of w \<Longrightarrow>
           \<forall>xa. xa \<in> A \<and> xa \<in> effective_fn_of w \<longrightarrow> fun_le x xa \<Longrightarrow> fun_le x (eff_glb w A)"
  unfolding eff_glb_def
proof - assume a1:"A \<subseteq> effective_fn_of w" and a2:"x\<in>effective_fn_of w" 
    and a3:"\<forall>xa. xa \<in> A \<and> xa \<in> effective_fn_of w \<longrightarrow> fun_le x xa"
  show "fun_le x (eff_fn_inter_fam w A)"
  proof (rule fun_le_eff)
    show "eff_fn_inter_fam w A \<in> effective_fn_of w" using eff_fn_inter_fam_eff a1 by auto
    show "x\<in>effective_fn_of w" using a2 by auto
    show "\<And>z. z\<in>Pow w \<Longrightarrow> x z \<subseteq> eff_fn_inter_fam w A z"
    proof - from a3 eff_fn_union_fam_eff a1
      have "\<And>\<phi> z. \<phi>\<in>A \<Longrightarrow> z\<in>Pow w \<Longrightarrow> x z \<subseteq> \<phi> z"
        unfolding fun_le_def by blast
      then show "\<And>z. z\<in>Pow w \<Longrightarrow> x z \<subseteq> eff_fn_inter_fam w A z"
        unfolding eff_fn_inter_fam_def ambient_inter_def apply auto
        using a2 unfolding effective_fn_of_def carrier_of_def by auto
    qed
  qed
qed

lemma eff_fn_union_eff: "f\<in> effective_fn_of w \<Longrightarrow> g\<in> effective_fn_of w \<Longrightarrow> eff_fn_union f g\<in>effective_fn_of w"
  using eff_union_eff unfolding eff_fn_union_def by auto

lemma eff_fn_inter_eff: "f\<in> effective_fn_of w \<Longrightarrow> g\<in> effective_fn_of w \<Longrightarrow> eff_fn_inter f g\<in>effective_fn_of w"
  using eff_inter_eff unfolding eff_fn_inter_def by auto

lemma eff_fn_dm_andor:
  assumes "f\<in>effective_fn_of w" and "g\<in>effective_fn_of w"
  shows "dual_eff_fn w (eff_fn_inter f g) = eff_fn_union (dual_eff_fn w f) (dual_eff_fn w g)
    "
proof (rule eff_fn_eq)
  show "dual_eff_fn w (eff_fn_inter f g) \<in> effective_fn_of w" using eff_fn_inter_eff assms eff_dual_eff by blast
  show "eff_fn_union (dual_eff_fn w f) (dual_eff_fn w g) \<in> effective_fn_of w" using eff_fn_union_eff assms eff_dual_eff by blast
  fix s assume "s\<in> Pow w" then show "dual_eff_fn w (eff_fn_inter f g) s = eff_fn_union (dual_eff_fn w f) (dual_eff_fn w g) s"
    unfolding dual_eff_fn_def eff_fn_inter_def eff_fn_union_def 
    using amb_comp_dm_basic assms amb_comp_compat[of "s""w"] eff_fn_img_valid[of "amb_comp w s""w"] by (metis (full_types) Pow_iff)
qed

lemma eff_fn_dm_orand:
  assumes "f\<in>effective_fn_of w" and "g\<in>effective_fn_of w"
  shows "dual_eff_fn w (eff_fn_union f g) = eff_fn_inter (dual_eff_fn w f) (dual_eff_fn w g)"
proof (rule eff_fn_eq)
  show "dual_eff_fn w (eff_fn_union f g) \<in> effective_fn_of w" using eff_fn_union_eff assms eff_dual_eff by blast
  show "eff_fn_inter (dual_eff_fn w f) (dual_eff_fn w g) \<in> effective_fn_of w" using eff_fn_inter_eff assms eff_dual_eff by blast
  fix s assume "s\<in> Pow w" then show "dual_eff_fn w (eff_fn_union f g) s = eff_fn_inter (dual_eff_fn w f) (dual_eff_fn w g) s"
    unfolding dual_eff_fn_def eff_fn_inter_def eff_fn_union_def 
    using amb_comp_dm_basic assms amb_comp_compat[of "s""w"] eff_fn_img_valid[of "amb_comp w s""w"] by (metis (full_types) Pow_iff)
qed

lemma eff_fn_dm:
  assumes "f\<in>effective_fn_of w" and "g\<in>effective_fn_of w"
  shows "dual_eff_fn w (eff_fn_union f g) = eff_fn_inter (dual_eff_fn w f) (dual_eff_fn w g)
    \<and> dual_eff_fn w (eff_fn_inter f g) = eff_fn_union (dual_eff_fn w f) (dual_eff_fn w g)"
  using eff_fn_dm_andor eff_fn_dm_orand assms by auto

lemma eff_fn_compo_hom:
  assumes "f\<in>effective_fn_of w" and "g\<in>effective_fn_of w"
  shows "dual_eff_fn w (compo (Pow w) f g) = compo (Pow w) (dual_eff_fn w f) (dual_eff_fn w g)"
proof (rule eff_fn_eq)
  show "dual_eff_fn w (compo (Pow w) f g) \<in> effective_fn_of w" using eff_dual_eff eff_compo_eff assms by blast
  show "compo (Pow w) (dual_eff_fn w f) (dual_eff_fn w g) \<in> effective_fn_of w" using assms eff_dual_eff eff_compo_eff by blast
  fix s assume "s\<in>Pow w" then show "dual_eff_fn w (compo (Pow w) f g) s = compo (Pow w) (dual_eff_fn w f) (dual_eff_fn w g) s"
    using Pow_iff amb_comp_compat assms
    unfolding dual_eff_fn_def compo_def by (simp add: Pi_def carrier_of_def effective_fn_of_def)
qed

definition op_union where "op_union F1 F2 f = eff_fn_union (F1 f) (F2 f)"


definition op_inter where "op_inter F1 F2 f = eff_fn_inter (F1 f) (F2 f)"

definition op_compo where "op_compo F2 F1 f = F2 (F1 f)"

lemma monotone_op_union_monotone: "f\<in> monotone_op_of w \<Longrightarrow> g\<in> monotone_op_of w \<Longrightarrow> op_union f g\<in> monotone_op_of w"
  unfolding monotone_op_of_def apply simp
proof
  assume a1:"f \<in> effective_fn_of w \<rightarrow> effective_fn_of w \<and> (\<forall>g1\<in>effective_fn_of w. \<forall>g2\<in>effective_fn_of w. fun_le g1 g2 \<longrightarrow> fun_le (f g1) (f g2))"
  and a2:"g \<in> effective_fn_of w \<rightarrow> effective_fn_of w \<and> (\<forall>g1\<in>effective_fn_of w. \<forall>g2\<in>effective_fn_of w. fun_le g1 g2 \<longrightarrow> fun_le (g g1) (g g2))"
  show "op_union f g \<in> effective_fn_of w \<rightarrow> effective_fn_of w" unfolding op_union_def apply auto
    using a1 a2 eff_fn_union_eff by blast
next
  assume a1:"f \<in> effective_fn_of w \<rightarrow> effective_fn_of w \<and> (\<forall>g1\<in>effective_fn_of w. \<forall>g2\<in>effective_fn_of w. fun_le g1 g2 \<longrightarrow> fun_le (f g1) (f g2))"
  and a2:"g \<in> effective_fn_of w \<rightarrow> effective_fn_of w \<and> (\<forall>g1\<in>effective_fn_of w. \<forall>g2\<in>effective_fn_of w. fun_le g1 g2 \<longrightarrow> fun_le (g g1) (g g2))"
  show "\<forall>g1\<in>effective_fn_of w. \<forall>g2\<in>effective_fn_of w. fun_le g1 g2 \<longrightarrow> fun_le (op_union f g g1) (op_union f g g2)"
    using a1 a2 unfolding op_union_def eff_fn_union_def fun_le_def by blast
qed

lemma monotone_op_inter_monotone: "f\<in> monotone_op_of w \<Longrightarrow> g\<in> monotone_op_of w \<Longrightarrow> op_inter f g\<in> monotone_op_of w"
  unfolding monotone_op_of_def apply simp
proof
  assume a1:"f \<in> effective_fn_of w \<rightarrow> effective_fn_of w \<and> (\<forall>g1\<in>effective_fn_of w. \<forall>g2\<in>effective_fn_of w. fun_le g1 g2 \<longrightarrow> fun_le (f g1) (f g2))"
  and a2:"g \<in> effective_fn_of w \<rightarrow> effective_fn_of w \<and> (\<forall>g1\<in>effective_fn_of w. \<forall>g2\<in>effective_fn_of w. fun_le g1 g2 \<longrightarrow> fun_le (g g1) (g g2))"
  show "op_inter f g \<in> effective_fn_of w \<rightarrow> effective_fn_of w" unfolding op_inter_def apply auto
    using a1 a2 eff_fn_inter_eff by blast
next
  assume a1:"f \<in> effective_fn_of w \<rightarrow> effective_fn_of w \<and> (\<forall>g1\<in>effective_fn_of w. \<forall>g2\<in>effective_fn_of w. fun_le g1 g2 \<longrightarrow> fun_le (f g1) (f g2))"
  and a2:"g \<in> effective_fn_of w \<rightarrow> effective_fn_of w \<and> (\<forall>g1\<in>effective_fn_of w. \<forall>g2\<in>effective_fn_of w. fun_le g1 g2 \<longrightarrow> fun_le (g g1) (g g2))"
  show "\<forall>g1\<in>effective_fn_of w. \<forall>g2\<in>effective_fn_of w. fun_le g1 g2 \<longrightarrow> fun_le (op_inter f g g1) (op_inter f g g2)"
    using a1 a2 unfolding op_inter_def eff_fn_inter_def fun_le_def by blast
qed

lemma monotone_op_compo_monotone: "f\<in> monotone_op_of w \<Longrightarrow> g\<in> monotone_op_of w \<Longrightarrow> op_compo g f\<in> monotone_op_of w"
  unfolding monotone_op_of_def apply simp
proof
  assume a1:"f \<in> effective_fn_of w \<rightarrow> effective_fn_of w \<and> (\<forall>g1\<in>effective_fn_of w. \<forall>g2\<in>effective_fn_of w. fun_le g1 g2 \<longrightarrow> fun_le (f g1) (f g2))"
  and a2:"g \<in> effective_fn_of w \<rightarrow> effective_fn_of w \<and> (\<forall>g1\<in>effective_fn_of w. \<forall>g2\<in>effective_fn_of w. fun_le g1 g2 \<longrightarrow> fun_le (g g1) (g g2))"
  show "op_compo g f \<in> effective_fn_of w \<rightarrow> effective_fn_of w" unfolding op_compo_def apply auto
    using a1 a2 by auto
next
  assume a1:"f \<in> effective_fn_of w \<rightarrow> effective_fn_of w \<and> (\<forall>g1\<in>effective_fn_of w. \<forall>g2\<in>effective_fn_of w. fun_le g1 g2 \<longrightarrow> fun_le (f g1) (f g2))"
  and a2:"g \<in> effective_fn_of w \<rightarrow> effective_fn_of w \<and> (\<forall>g1\<in>effective_fn_of w. \<forall>g2\<in>effective_fn_of w. fun_le g1 g2 \<longrightarrow> fun_le (g g1) (g g2))"
  show "\<forall>g1\<in>effective_fn_of w. \<forall>g2\<in>effective_fn_of w. fun_le g1 g2 \<longrightarrow> fun_le (op_compo g f g1) (op_compo g f g2)"
    using a1 a2 unfolding op_compo_def compo_def fun_le_def
  by blast
qed

lemma Gfp_carrier [simp]:"Gfp w F \<in> carrier_of w"
proof (auto simp add:carrier_of_def)
  fix x xa
  show "x \<subseteq> w \<Longrightarrow> xa \<in> Gfp w F x \<Longrightarrow> xa \<in> w" unfolding Gfp_def Gfp_family_def effective_fn_of_def carrier_of_def by auto
  show "Gfp w F \<in> extension (Pow w)" unfolding Gfp_def Gfp_family_def effective_fn_of_def carrier_of_def
    by (simp add:extension_def)
qed

lemma Gfp_mono [simp]:"Gfp w F \<in> mono_of w"
proof (auto simp add:mono_of_def)
  fix x y xa assume a1:"xa\<in>Gfp w F x" and a2:"x\<subseteq>w" and a3:"y\<subseteq>w" and a4:"x\<subseteq>y"
  have "\<And>\<phi>. \<phi> \<in> Gfp_family w F \<Longrightarrow> \<phi> x \<subseteq> \<phi> y" using a2 a3 a4 by (auto simp add:Gfp_family_def effective_fn_of_def mono_of_def)
  then have a_ineq:"\<Union>{\<phi> x|\<phi>. \<phi>\<in> Gfp_family w F} \<subseteq> \<Union>{\<phi> y |\<phi>. \<phi> \<in> Gfp_family w F}" by auto

  from a2 have b_x:"Gfp w F x = \<Union>{\<phi> x|\<phi>. \<phi>\<in> Gfp_family w F}" unfolding Gfp_def by auto
  from a3 have b_y:"Gfp w F y = \<Union>{\<phi> y|\<phi>. \<phi>\<in> Gfp_family w F}" unfolding Gfp_def by auto
  show "xa\<in>Gfp w F y"
    using b_x b_y a_ineq a1 unfolding Gfp_def by (metis (no_types, lifting) subset_eq)
qed

lemma Gfp_eff:"Gfp w F \<in> effective_fn_of w"
  by (auto simp add:effective_fn_of_def)

lemma dual_Gfp__Lfp_dualop: 
  assumes "F\<in>op_of w"
  shows "dual_eff_fn w (Gfp w F) = Lfp w (dual_op w F)"
proof - 
  have "dual_eff_fn w (Lfp w (dual_op w F)) = Gfp w F"
    using dual_Lfp__Gfp_dualop[of "dual_op w F" "w"] assms Gfp_dual_op_invo dual_op__op by force
  then show ?thesis
    using dual_eff_fn_invo Lfp_eff by metis
qed

subsection \<open>vectors of functions\<close>

definition kprod:: "nat \<Rightarrow> 'a set \<Rightarrow> (nat \<Rightarrow> 'a) set" where
  "kprod k A = ({1..k} \<rightarrow> A) \<inter> extension {1..k}"

lemma kprod_eqI [intro]: "f\<in>kprod k A \<Longrightarrow> g\<in>kprod k A \<Longrightarrow> (\<And>i. i\<in>{1..k} \<Longrightarrow> f i = g i) \<Longrightarrow> f = g"
  apply rule
proof - fix x assume a1:"f \<in> kprod k A" and a2:"g\<in>kprod k A" and a3:"\<And>i. i \<in> {1..k} \<Longrightarrow> f i = g i"
  show "f x = g x"
  proof (cases "x\<in>{1..k}")
    case True
    then show ?thesis using a1 a2 a3 unfolding kprod_def by auto
  next
    case False
    then show ?thesis using a1 a2 a3 unfolding kprod_def extension_def by auto
  qed
qed

lemma fun_le_undefined: "fun_le undefined undefined"
  using fun_le_refl by auto

definition vec_le:: "(nat \<Rightarrow> ('a set \<Rightarrow> 'a set)) \<Rightarrow> (nat \<Rightarrow> ('a set \<Rightarrow> 'a set)) \<Rightarrow> bool" where
  "vec_le f g \<equiv> \<forall>i::nat. fun_le (f i) (g i)"

lemma vec_le_range: "f\<in>kprod n A \<Longrightarrow> g\<in>kprod n A \<Longrightarrow> (\<And>i. i\<in>{1..n} \<Longrightarrow>fun_le (f i) (g i)) \<Longrightarrow> vec_le f g"
  unfolding vec_le_def
  apply rule
proof - fix i assume a1:"f \<in> kprod n A" and a2:"g\<in> kprod n A" and a3:"\<And>i. i \<in> {1..n} \<Longrightarrow> fun_le (f i) (g i)"
  show "fun_le (f i) (g i)"
    apply (cases "i\<in>{1..n}") using a3 apply blast
    using a1 a2 fun_le_undefined unfolding kprod_def extension_def by auto
qed
   

definition vec_nth:: "nat \<Rightarrow> (nat \<Rightarrow> 'a set) \<Rightarrow> 'a set" (infixl \<open>$\<close> 90) where 
  "vec_nth i f = f i"

lemma vec_le_refl: "vec_le f f"
  unfolding vec_le_def by auto

lemma vec_le_trans: "vec_le f g \<Longrightarrow> vec_le g h \<Longrightarrow> vec_le f h"
  unfolding vec_le_def apply auto using fun_le_trans by blast

lemma vec_le_antisym: "vec_le f g \<Longrightarrow> vec_le g f \<Longrightarrow> f = g"
  unfolding vec_le_def using fun_le_antisym by blast

definition vec_lub:: "'a set \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> ('a set \<Rightarrow> 'a set)) set \<Rightarrow> (nat \<Rightarrow> ('a set \<Rightarrow> 'a set))" where
  "vec_lub w k \<Omega> = (\<lambda>i\<in>{1..k}. eff_lub w {f i|f. f\<in>\<Omega>})"

lemma vec_lub_extension: "A \<subseteq> kprod k (effective_fn_of w) \<Longrightarrow> i\<notin>{1..k} \<Longrightarrow> vec_lub w k A i = undefined"
  unfolding vec_lub_def kprod_def eff_lub_def eff_fn_union_fam_def by auto

lemma vec_lub_eff: "A \<subseteq> kprod k (effective_fn_of w) \<Longrightarrow> vec_lub w k A \<in> kprod k (effective_fn_of w)"
  using eff_lub_eff vec_lub_extension unfolding vec_lub_def extension_def kprod_def
  by (smt (verit, ccfv_threshold) FuncSet.restrict_apply Int_Collect PiE mem_Collect_eq restrictI subsetD subsetI)

definition vec_proj:: "nat \<Rightarrow> (nat \<Rightarrow> ('a set \<Rightarrow> 'a set)) set \<Rightarrow> ('a set \<Rightarrow> 'a set) set" where
  "vec_proj i A = {f i| f. f\<in>A}"

lemma vec_proj_eff: "A \<subseteq> kprod k (effective_fn_of w) \<Longrightarrow> i\<in>{1..k} \<Longrightarrow> vec_proj i A \<subseteq> (effective_fn_of w)"
  unfolding kprod_def vec_proj_def by blast

lemma vec_proj_eff_elem: "x \<in> kprod k (effective_fn_of w) \<Longrightarrow> i\<in>{1..k} \<Longrightarrow> x i \<in> (effective_fn_of w)"
  unfolding kprod_def by blast

lemma vec_lub_is_ub: "A \<subseteq> kprod k (effective_fn_of w) \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> kprod k (effective_fn_of w) \<Longrightarrow> vec_le x (vec_lub w k A)"
proof - assume a1:"A \<subseteq> kprod k (effective_fn_of w)" and a2:"x \<in> A" and a3:"x \<in> kprod k (effective_fn_of w)"
  show "vec_le x (vec_lub w k A)"
    using a3
  proof (rule vec_le_range)
    show "vec_lub w k A \<in> kprod k (effective_fn_of w)" 
      using vec_lub_eff a1 by auto
    show "\<And>i. i \<in> {1..k} \<Longrightarrow> fun_le (x i) (vec_lub w k A i)"
      unfolding vec_lub_def
    proof - fix i assume ass:"i\<in>{1..k}" 
      show "fun_le (x i) ((\<lambda>i\<in>{1..k}. eff_lub w {f i |f. f \<in> A}) i)"
      proof - 
        have "{f i| f. f\<in> A} \<subseteq> effective_fn_of w"
          using ass a1 unfolding kprod_def by blast
        then show ?thesis
          using eff_lub_ub[of "{f i |f. f \<in> A}" "w" "x i"] a2 ass by auto
      qed
    qed
  qed
qed

lemma vec_lub_is_lub: 
  "A \<subseteq> kprod k (effective_fn_of w) \<Longrightarrow>
   x \<in> kprod k (effective_fn_of w) \<Longrightarrow> 
   \<forall>y. y \<in> A \<and> y \<in> kprod k (effective_fn_of w) \<longrightarrow> vec_le y x \<Longrightarrow> vec_le (vec_lub w k A) x"
proof - assume a1:"A \<subseteq> kprod k (effective_fn_of w)" and a2:"x \<in> kprod k (effective_fn_of w)" and a3:"\<forall>y. y \<in> A \<and> y \<in> kprod k (effective_fn_of w) \<longrightarrow> vec_le y x"
  show "vec_le (vec_lub w k A) x"
  proof (rule vec_le_range)
    show "vec_lub w k A \<in> kprod k (effective_fn_of w)"
      using vec_lub_eff a1 by auto
    show "x \<in> kprod k (effective_fn_of w)" 
      using a2 by auto
  next
    fix i assume b1:"i \<in> {1..k}" then show "fun_le (vec_lub w k A i) (x i)"
      unfolding vec_lub_def apply simp
    proof - 
      have "{f i |f. f \<in> A} \<subseteq> effective_fn_of w"
        using vec_proj_eff[of "A""k""w""i"] a1 b1 unfolding vec_proj_def by auto
      have "\<forall>y. y \<in> {f i |f. f \<in> A}  \<and> y \<in> effective_fn_of w \<longrightarrow> fun_le y (x i)"
        using a1 a3 vec_le_def by fastforce
      then
      show "fun_le (eff_lub w {f i |f. f \<in> A}) (x i)"
        using eff_lub_lub[of "{f i |f. f \<in> A}" "w" "x i"] vec_proj_eff_elem a2 b1
              \<open>{f i |f. f \<in> A} \<subseteq> effective_fn_of w\<close> by force
    qed
  qed
qed

definition vec_glb:: "'a set \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> ('a set \<Rightarrow> 'a set)) set \<Rightarrow> (nat \<Rightarrow> ('a set \<Rightarrow> 'a set))" where
  "vec_glb w k \<Omega> = (\<lambda>i\<in>{1..k}. eff_glb w {f i|f. f\<in>\<Omega>})"

lemma vec_glb_extension: "A \<subseteq> kprod k (effective_fn_of w) \<Longrightarrow> i\<notin>{1..k} \<Longrightarrow> vec_glb w k A i = undefined"
  unfolding vec_glb_def by auto

lemma vec_glb_eff: "A \<subseteq> kprod k (effective_fn_of w) \<Longrightarrow> vec_glb w k A \<in> kprod k (effective_fn_of w)"
  using eff_glb_eff vec_glb_extension unfolding vec_glb_def extension_def kprod_def
  by (smt (verit, del_insts) FuncSet.restrict_apply Int_Collect PiE mem_Collect_eq restrictI subset_eq)

lemma vec_glb_is_lb: "A \<subseteq> kprod k (effective_fn_of w) \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> kprod k (effective_fn_of w) \<Longrightarrow> vec_le (vec_glb w k A) x"
proof - assume a1:"A \<subseteq> kprod k (effective_fn_of w)" and a2:"x \<in> A" and a3:"x \<in> kprod k (effective_fn_of w)"
  show "vec_le (vec_glb w k A) x"
  proof (rule vec_le_range)
    show "vec_glb w k A \<in> kprod k (effective_fn_of w)" 
      using vec_glb_eff a1 by auto
    show "\<And>i. i \<in> {1..k} \<Longrightarrow> fun_le (vec_glb w k A i) (x i)"
      unfolding vec_glb_def
    proof - fix i assume ass:"i\<in>{1..k}" 
      show "fun_le ((\<lambda>i\<in>{1..k}. eff_glb w {f i |f. f \<in> A}) i) (x i)"
      proof - 
        have "{f i| f. f\<in> A} \<subseteq> effective_fn_of w"
          using ass a1 unfolding kprod_def by blast
        then show ?thesis
          using eff_glb_lb[of "{f i |f. f \<in> A}" "w" "x i"] a2 ass by auto
      qed
    qed
    show "x \<in> kprod k (effective_fn_of w)" using a2 a1 by auto
  qed
qed

lemma vec_glb_is_glb: 
  "A \<subseteq> kprod k (effective_fn_of w) \<Longrightarrow>
   x \<in> kprod k (effective_fn_of w) \<Longrightarrow> 
   \<forall>y. y \<in> A \<and> y \<in> kprod k (effective_fn_of w) \<longrightarrow> vec_le x y \<Longrightarrow> vec_le x (vec_glb w k A)"
proof - assume a1:"A \<subseteq> kprod k (effective_fn_of w)" and a2:"x \<in> kprod k (effective_fn_of w)" and a3:"\<forall>y. y \<in> A \<and> y \<in> kprod k (effective_fn_of w) \<longrightarrow> vec_le x y"
  show "vec_le x (vec_glb w k A)"
  proof (rule vec_le_range)
    show "vec_glb w k A \<in> kprod k (effective_fn_of w)"
      using vec_glb_eff a1 by auto
    show "x \<in> kprod k (effective_fn_of w)" 
      using a2 by auto
  next
    fix i assume b1:"i \<in> {1..k}" then show "fun_le (x i) (vec_glb w k A i)"
      unfolding vec_glb_def apply simp
    proof - 
      have "{f i |f. f \<in> A} \<subseteq> effective_fn_of w"
        using vec_proj_eff[of "A""k""w""i"] a1 b1 unfolding vec_proj_def by auto
      have "\<forall>y. y \<in> {f i |f. f \<in> A}  \<and> y \<in> effective_fn_of w \<longrightarrow> fun_le (x i) y"
        using a1 a3 vec_le_def by fastforce
      then
      show "fun_le (x i) (eff_glb w {f i |f. f \<in> A})"
        using eff_glb_glb[of "{f i |f. f \<in> A}" "w" "x i"] vec_proj_eff_elem a2 b1
              \<open>{f i |f. f \<in> A} \<subseteq> effective_fn_of w\<close> by force
    qed
  qed
qed


section \<open> general nat tree with variable children \<close>

datatype tree = Node "nat" "tree list"

fun height:: "tree \<Rightarrow> nat" where
   "height (Node _ []) = 0"
|  "height (Node _ cs) = 1 + fold max (map height cs) 0"

fun gen_lex_tree:: "nat \<Rightarrow> nat list \<Rightarrow> tree list" where
   "gen_lex_tree 0 _ = []"
|  "gen_lex_tree n store = [Node i (gen_lex_tree (n-1) (filter (\<lambda>x. x\<noteq>i) store)). i \<leftarrow> store]"

definition lex_tree:: "nat \<Rightarrow> tree" where
  "lex_tree n = Node 0 (gen_lex_tree n (upt 1 (n+1)))"

value "lex_tree 3"

lemma list_mem_index':
  assumes "ListMem e ls"
  shows "\<exists>i< length ls. ls ! i = e"
  using in_set_conv_nth[of "e" "ls"] assms unfolding ListMem_iff by simp

lemma list_mem_index:
  assumes "ListMem e ls"
  shows "\<exists>i \<in> {0..length ls-1}. ls ! i = e"
  using list_mem_index'[OF assms] by auto

lemma list_distinct_index:
  assumes "distinct ls"
  shows "i\<in>{0..length ls -1} \<Longrightarrow> j\<in>{0..length ls -1} \<Longrightarrow> ls ! i = ls ! j \<Longrightarrow> i=j"
  using assms
proof (induction ls arbitrary: i j)
  case Nil
  then show ?case
    by auto
next
  case (Cons a t)
  then show ?case
  proof (cases "i=0")
    case True
    then show ?thesis
    proof (cases "j=0")
      case True
      then show ?thesis using \<open>i=0\<close> by auto
    next
      case False
      then show ?thesis 
      proof -
        have b1:"(a # t) ! j = t ! (j-1)" 
          using \<open>j\<noteq>0\<close> by simp
        have b2:"(a # t) ! i = a"
          using \<open>i=0\<close> by simp
        have b3:"a \<notin> set t"
          using \<open>distinct (a#t)\<close> by auto
        from b1 b2 b3 \<open>(a # t) ! i = (a # t) ! j\<close> 
        have False 
          using Cons.prems(2) False by auto
        then show ?thesis by auto
      qed
    qed
  next
    case False
    then show ?thesis
    proof (cases "j=0")
      case True
      then show ?thesis
      proof -
        have b1:"(a # t) ! i = t ! (i-1)" 
          using \<open>i\<noteq>0\<close> by simp
        have b2:"(a # t) ! j = a"
          using \<open>j=0\<close> by simp
        have b3:"a \<notin> set t"
          using \<open>distinct (a#t)\<close> by auto
        from b1 b2 b3 \<open>(a # t) ! i = (a # t) ! j\<close> 
        have False 
          using Cons.prems False by auto
        then show ?thesis by auto
      qed
    next
      case False
      then show ?thesis
      proof -
        have \<open>i - 1 \<in> {0..length t - 1}\<close>
          using \<open>i\<noteq>0\<close> \<open>i \<in> {0..length (a # t) - 1}\<close> by auto
        have \<open>j - 1 \<in> {0..length t - 1}\<close>
          using \<open>j\<noteq>0\<close> \<open>j \<in> {0..length (a # t) - 1}\<close> by auto
        from Cons.IH[of "i-1" "j-1"]
        have "t ! (i - 1) = t ! (j - 1) \<Longrightarrow> distinct t \<Longrightarrow> i - 1 = j - 1"
          using \<open>i - 1 \<in> {0..length t - 1}\<close> \<open>j - 1 \<in> {0..length t - 1}\<close> by auto
        have \<open>t ! (i - 1) = t ! (j - 1)\<close>
          using \<open>(a # t) ! i = (a # t) ! j\<close> \<open>i\<noteq>0\<close> \<open>j\<noteq>0\<close> by auto
        have \<open>distinct t\<close>
          using \<open>distinct (a#t)\<close> by auto
        have "i-1=j-1"
          using \<open>t ! (i - 1) = t ! (j - 1) \<Longrightarrow> distinct t \<Longrightarrow> i - 1 = j - 1\<close> \<open>t ! (i - 1) = t ! (j - 1)\<close> \<open>distinct t\<close>
          by auto
        then show "i=j"
          using \<open>i - 1 \<in> {0..length t - 1}\<close> \<open>j - 1 \<in> {0..length t - 1}\<close> \<open>i\<noteq>0\<close> \<open>j\<noteq>0\<close> by auto
      qed
    qed
  qed
qed
  

lemma list_mem_unique_index:
  assumes "ListMem e ls"
    and "distinct ls"
  shows "\<exists>!i \<in> {0..length ls-1}. (ls ! i = e)"
proof -
  from list_mem_index[OF \<open>ListMem e ls\<close>]
  obtain i where b1:"i \<in> {0..length ls-1} \<and> (ls ! i = e)" by auto
  then have b2:"\<exists>i \<in> {0..length ls - 1}. ls ! i = e" 
    by auto
  have b2:"\<And>j. (j\<in>{0..length ls - 1} \<and> ls ! j = e) \<Longrightarrow> j=i"
    using b1 list_distinct_index[OF \<open>distinct ls\<close>] by auto
  thus ?thesis
    using b1 b2 by auto
qed

definition ls_idx:: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "ls_idx xs a \<equiv> THE i. i\<in>{0..(length xs-1)} \<and> (a=(xs! i))"

lemma idx_ls_mem [intro]:
  "i\<in>{1..length xs} \<Longrightarrow> ListMem (the (xs\<sqdot>i)) xs"
  by (simp add: ListMem_iff get_member_def less_iff_succ_less_eq)

lemma idx_ls_mem2 [intro]:
  "0\<in>{1..length xs-1} \<Longrightarrow> ListMem (xs!(i-1)) xs"
  by simp

lemma ls_idx_prop:
  assumes "ListMem a xs"
      and "distinct xs"
    shows "ls_idx xs a \<in>{0..(length xs-1)} \<and> ((xs! (ls_idx xs a)) = a)"
  unfolding ls_idx_def using list_mem_unique_index[OF \<open>ListMem a xs\<close> \<open>distinct xs\<close>] theI 
  by (metis (mono_tags, lifting))

lemma list_hd_index:
  "length ls >0 \<Longrightarrow> hd ls = ls ! 0"
  using hd_conv_nth by auto

section \<open>Map modifications\<close>

definition ls_to_map:: "nat list \<Rightarrow> 'a list \<Rightarrow> (nat \<rightharpoonup> 'a)" where
  "ls_to_map xs gs x = (if x\<in>set xs then Some (gs ! (ls_idx xs x)) else None)"

lemma ls_to_map_empty_simp[simp]:
  "ls_to_map [] gs = (\<lambda>x. None)"
  unfolding ls_to_map_def by auto

lemma ls_to_map_empty_simp2[simp]:
  "ls_to_map [] gs x = None"
  unfolding ls_to_map_def by auto

lemma ls_to_map_dom [simp]:
  "(dom (ls_to_map xs gs)) = set xs"
  unfolding ls_to_map_def 
  using subset_antisym by fastforce

lemma ls_to_map_notin_simp [simp]:
  "\<not>ListMem x xs \<Longrightarrow> ls_to_map xs gs x = None"
  unfolding ls_to_map_def 
  by (simp add: ListMem_iff)

lemma ls_to_map_dom_size:
  "distinct xs \<Longrightarrow> card (dom (ls_to_map xs gs)) = length xs"
  by (simp add: distinct_card)

lemma ls_to_map_simp [simp]:
  "ListMem x xs \<Longrightarrow> ls_to_map xs gs x = Some (gs ! (ls_idx xs x))"
  unfolding ls_to_map_def using ListMem_iff by force

definition ls_map_to_map:: "nat list \<Rightarrow> (nat \<rightharpoonup> 'a) \<Rightarrow> (nat \<rightharpoonup> 'a)" where
  "ls_map_to_map xs B x = (if x\<in>set xs then B (ls_idx xs x + 1) else None)"

lemma ls_map_to_map_Bot[simp]:
  "ls_map_to_map xs (\<lambda>x. None) = (\<lambda>x. None)"
  by (auto simp add: ls_map_to_map_def)

lemma ls_map_to_map_dom:
  "dom (ls_map_to_map xs B) = (set xs \<inter> {x::nat. ls_idx xs x + 1 \<in>dom B})"
  unfolding ls_map_to_map_def
  by (smt (verit) Collect_cong Int_def dom_def mem_Collect_eq)

(* Map modification function, list version. 
  Precondition: xs has distinct elements; second argument is as long as the first*)
fun subst_map':: "(nat \<Rightarrow> 'a) \<Rightarrow> nat list \<Rightarrow> 'a list \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "subst_map' I [] _ = I"
| "subst_map' I (x # xs) (w # ws) = (subst_map' I xs ws)(x:=w)"
| "subst_map' I _ [] = I"

definition subst_map_by_map:: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<rightharpoonup> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "subst_map_by_map I B x = (case B x of None \<Rightarrow> I x | Some y \<Rightarrow> y)"

lemma subst_map_by_map_one [simp]:
  "subst_map_by_map I [x\<mapsto>c] = I(x:=c)"
  unfolding subst_map_by_map_def by auto

lemma subst_map_by_map_allNone [simp]:
  "subst_map_by_map I (\<lambda>x. None) = I"
  unfolding subst_map_by_map_def by auto

lemma subst_map_by_map_notin[simp]:
  "B x = None \<Longrightarrow> subst_map_by_map I B x = I x"
  unfolding subst_map_by_map_def by auto

lemma subst_map_by_map_notin_dom[simp]:
  "x\<notin>dom B \<Longrightarrow> subst_map_by_map I B x = I x"
  unfolding subst_map_by_map_def
  by (simp add: domIff)

lemma subst_map_by_map_in[simp]:
  "B x \<noteq> None \<Longrightarrow> subst_map_by_map I B x = the (B x)"
  unfolding subst_map_by_map_def by auto

lemma subst_map_by_map_rm_entry:
  assumes "B x \<noteq> None"
  shows "subst_map_by_map I B = subst_map_by_map (I(x:=the (B x))) (B(x:=None))"
proof (rule ext)
  fix a show "subst_map_by_map I B a = subst_map_by_map (I(x := the (B x))) (B(x := None)) a"
  proof (cases "a=x")
    case True
    then show ?thesis
      using assms by auto
  next
    case False
    then show ?thesis
    proof (cases "B a = None")
      case True
      then show ?thesis
        using \<open>a\<noteq>x\<close> by auto
    next
      case False
      then show ?thesis
        using \<open>a\<noteq>x\<close> by auto
    qed
  qed
qed

lemma subst_map_by_map_union:
  assumes "dom B1 \<inter> dom B2 = {}"
  shows "subst_map_by_map (subst_map_by_map I B1) B2 = subst_map_by_map I (B1 ++ B2)"
  (is "?l=?r")
proof (rule ext)
  fix x 
  consider (In1) "x\<in>dom B1" | (In2) "x\<in>dom B2" | (notIn) "x\<notin>dom B1 \<and> x\<notin>dom B2"
    using assms by auto
  then show "?l x = ?r x"
  proof (cases)
    case In1
    then show ?thesis
    proof -
      have "x\<notin>dom B2" 
        using assms In1 by auto
      then have "?l x = subst_map_by_map I B1 x"
        using subst_map_by_map_notin by simp
      also have "... = the (B1 x)"
        using In1 by auto
      also have "... = the ((B1 ++ B2) x)"
        by (simp add: \<open>x \<notin> dom B2\<close> map_add_dom_app_simps(3))
      also have "... = ?r x"
        using In1 by force
      finally show ?thesis 
        by simp
    qed
  next
    case In2
    then show ?thesis
    proof -
      have "x\<notin>dom B1" 
        using assms In2 by auto
      have "?l x = the (B2 x)"
        using subst_map_by_map_in In2 by auto
      also have "... = ?r x"
        using In2 by auto
      finally show ?thesis 
        by simp
    qed
  next
    case notIn
    then show ?thesis
    proof -
      have "?l x = subst_map_by_map I B1 x"
        using subst_map_by_map_notin notIn by auto
      also have "... = I x"
        using notIn by auto
      also have "... = ?r x"
        using notIn by auto
      finally show ?thesis
        by simp
    qed
  qed
qed

lemma map_restrict_add:
  assumes "dom B' \<subseteq> dom B"
      and a2:"\<And>x. x\<in>dom B' \<Longrightarrow> B x = B' x"
    shows "(B' ++ B |` (- dom B')) = B"
  (is "?l=?r")
proof (rule ext)
  fix x
  consider (InB') "x\<in>dom B'" | (InB) "x\<notin>dom B' \<and> x\<in>dom B" | (notIn) "x\<notin>dom B"
    using assms by blast
  then show "?l x = ?r x"
  proof (cases)
    case InB'
    then show ?thesis
    proof -
      have "?l x = B' x"
        using InB' by (simp add: map_add_dom_app_simps(3))
      also have "... = ?r x"
        using assms InB' by auto
      finally show ?thesis
        by simp
    qed
  next
    case InB
    then show ?thesis
    proof -
      have "?l x = (B |` (- dom B')) x"
        using InB by (simp add: map_add_dom_app_simps(2))
      also have "... = B x"
        using InB by auto
      finally show ?thesis
        by simp
    qed
  next
    case notIn
    then show ?thesis
    proof -
      have "?l x = None"
        using notIn assms by (metis Compl_iff domIff map_add_dom_app_simps(2) restrict_in)
      also have "... = ?r x"
        using notIn domIff by fastforce
      finally show ?thesis
        by simp
    qed
  qed
qed

lemma subst_map_by_map_split:
  assumes "dom B' \<subseteq> dom B"
      and a2:"\<And>x. x\<in>dom B' \<Longrightarrow> B x = B' x"
  shows "subst_map_by_map (subst_map_by_map I B') (B |` (- dom B')) = subst_map_by_map I B"
proof -
  have a1:"dom B' \<inter> dom (B |` (- dom B')) = {}"
    using assms by simp
  have b2:"(B' ++ B |` (- dom B')) = B"
    using map_restrict_add assms by auto
  show ?thesis
    using subst_map_by_map_union[OF a1] b2 by auto
qed

lemma subst_map_by_map_I_specify[simp]:
  "subst_map_by_map (I(x:=u)) (B(x:=None)) = (subst_map_by_map I (B(x:=None)))(x:=u)"
proof (rule ext)
  fix y
  show "subst_map_by_map (I(x:=u)) (B(x:=None)) y = ((subst_map_by_map I (B(x:=None)))(x:=u)) y"
  proof (cases "x=y")
    case True
    then show ?thesis
    proof -
      have eq1:"((subst_map_by_map I (B(x:=None)))(x:=u)) y = u"
        using True by simp
      have "subst_map_by_map (I(x:=u)) (B(x:=None)) y = (I(x:=u)) y"
        using True by auto
      also have "... = u"
        using True by auto
      finally show ?thesis
        using eq1 by auto
    qed
  next
    case False
    then show ?thesis
      unfolding subst_map_by_map_def by (metis (no_types, lifting) fun_upd_other)
  qed
qed
    

(* Given a n-ary vector, convert to a length n list. 
   Precondition: for v_to_l n w, w contains value for [1..n]. *)
primrec v_to_l':: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list" where
  "v_to_l' 0 w = []"
| "v_to_l' (Suc m) w = w (Suc m) # (v_to_l' m w)"

value "{1::nat .. 5}"

lemma image_union:
  "f ` A \<union> f ` B = f ` (A\<union>B)"
  by blast

lemma w_image:
  "w ` {1::nat..Suc m} = w ` {Suc m} \<union> (w ` {1::nat .. m})"
  using image_union atLeastAtMostSuc_conv by auto

lemma image_Suc:
  "{w i| (i::nat). i\<in>{1::nat .. Suc m}} = {w (Suc m)} \<union> (w ` {1::nat .. m})"
  using image_iff w_image by fastforce

lemma v_to_l'_image:
  "set (v_to_l' m w) = {w i| (i::nat). i\<in>{1::nat..m::nat}}"
proof (induction m)
  case 0
  then show ?case by auto
next
  case (Suc m')
  then show ?case
  proof -
    have "v_to_l' (Suc m') w = w (Suc m') # (v_to_l' m' w)"
      by simp
    hence "set (v_to_l' (Suc m') w) = ({w (Suc m')} \<union> set (v_to_l' m' w))"
      by auto
    also have "... = ({w (Suc m')} \<union> {w i| i. i\<in>{1::nat..m'::nat}})"
      using Suc.IH by auto
    finally show ?thesis
      using image_Suc[of "w" "m'"] by auto
  qed
qed


definition v_to_l::"nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list" where
  "v_to_l n w =  rev (v_to_l' n w)"

lemma v_to_l_image:
  "set (v_to_l n w) = {w i| (i::nat). i\<in>{1::nat..n::nat}}"
  using v_to_l'_image unfolding v_to_l_def
  by (metis set_rev)

fun l_to_v':: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "l_to_v' n (Suc m) (x#xs) = (l_to_v' n m xs) (n-m:=x)"
| "l_to_v' n 0 _ = (\<lambda>a. undefined)"
| "l_to_v' n _ [] = (\<lambda>a. undefined)"

lemma l_to_v'_Nil_simp[simp]:
  "l_to_v' n m [] x = undefined"
  by (metis l_to_v'.simps(2,3) old.nat.exhaust)
lemma l_to_v'_0_simp[simp]:
  "l_to_v' n 0 xs x = undefined"
  by auto

definition l_to_v:: "'a list \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "l_to_v xs = l_to_v' (length xs) (length xs) xs"

lemma l_to_v_empty_simp[simp]:
  "l_to_v [] a = undefined"
  unfolding l_to_v_def by auto

lemma l_to_v_nonempty_hd:
  "length xs > 0 \<Longrightarrow> l_to_v xs 1 = hd xs"
  unfolding l_to_v_def 
  by (metis add_diff_cancel_right' fun_upd_apply gr0_conv_Suc l_to_v'.simps(1) length_0_conv linorder_not_le list.collapse nle_le plus_1_eq_Suc)
  

lemma l_to_v'_ext:
  assumes "m\<in>{1..length xs}" and "n>0" and "length xs \<le> n"
  shows "l_to_v' n m xs \<in> extensional {n-m+1..n}"
  using assms
proof (induction "length xs" arbitrary:xs m)
  case 0
  then show ?case
    by auto
next
  case (Suc n')
  then show ?case
  proof (cases "m=1")
    case True
    then show ?thesis
    proof -
      have \<open>xs=hd xs # tl xs\<close>
        by (metis Suc.hyps(2) list.collapse list.size(3) nat.simps(3))
      hence "l_to_v' n m xs = (l_to_v' n 0 (tl xs)) (n-0:=hd xs)"
        using \<open>m=1\<close> l_to_v'.simps(1)[of "n" "0" "hd xs" "tl xs"] by auto
      also have "... = (\<lambda>a. undefined)(n:=hd xs)"
        by auto
      finally show ?thesis
        using \<open>m=1\<close> \<open>n>0\<close> unfolding extensional_def by simp
    qed
  next
    case False
    then show ?thesis
    proof -
      have \<open>m\<le>n\<close>
        using \<open>m\<in>{1..length xs}\<close> \<open>length xs \<le>n\<close> by auto
      have \<open>m>1\<close>
        using False Suc.prems(1) by auto
      then have \<open>Suc (n - m) \<le> n\<close>
        by (simp add: Suc_leI assms(2))
      have \<open>n - (m - 1) = n-m+1\<close>
        using \<open>length xs \<le> n\<close> \<open>m\<in>{1..length xs}\<close> by auto
      have \<open>m-1\<in>{1..length xs -1}\<close>
        by (metis Suc.hyps(2) Suc.prems(1) \<open>1 < m\<close> atLeastAtMost_iff diff_Suc_1 diff_diff_left diff_is_0_eq less_one linorder_not_less plus_1_eq_Suc)
      have \<open>xs=hd xs # tl xs\<close>
        by (metis Suc.hyps(2) list.collapse list.size(3) nat.simps(3))
      hence b1:"l_to_v' n m xs = (l_to_v' n (m-1) (tl xs)) (n-m+1:=hd xs)"
        using \<open>m>1\<close> \<open>n - (m - 1) = n-m+1\<close> l_to_v'.simps(1)[of "n" "m-1" "hd xs" "tl xs"] by auto
      from Suc.hyps(1)[of "tl xs" "m-1"] \<open>m-1\<in>{1..length xs -1}\<close> \<open>Suc n' = length xs\<close> \<open>length xs \<le> n\<close> \<open>n - (m - 1) = n-m+1\<close>
      have "l_to_v' n (m - 1) (tl xs) \<in> extensional {n-m+2..n}"
        by auto
      then show ?thesis
        using b1 \<open>m\<le>n\<close> \<open>Suc (n - m) \<le> n\<close> unfolding extensional_def by auto
    qed
  qed
qed

lemma l_to_v_ext: "length xs >0 \<Longrightarrow> l_to_v xs \<in> extensional {1..length xs}"
  using l_to_v'_ext unfolding l_to_v_def
  by (metis atLeastAtMost_iff cancel_comm_monoid_add_class.diff_cancel dual_order.refl less_one linorder_le_less_linear neq0_conv plus_nat.add_0)

lemma l_to_v_empty[simp]:
  "l_to_v [] = (\<lambda>a. undefined)"
  unfolding l_to_v_def by auto

lemma v_to_l_one_simp[simp]:
  "v_to_l 1 w = [w 1]"
  unfolding v_to_l_def by auto

definition vec_delete_shift:: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "vec_delete_shift i w = (\<lambda>j. (if j<i then w j else w (j+1)))"

lemma vec_delete_shift_empty [simp]: "vec_delete_shift k (\<lambda>a. undefined) = (\<lambda>a. undefined)"
  unfolding vec_delete_shift_def by auto

lemma vec_delete_shift_one_empty [simp]: "w\<in>extensional {1} \<Longrightarrow> vec_delete_shift 1 w a = undefined"
  unfolding extensional_def vec_delete_shift_def by auto

lemma vec_delete_shift_ext:
  assumes "w\<in>extensional {1..n}" and "i\<in>{1..n}"
  shows "vec_delete_shift i w \<in>extensional {1..n-1}"
  using assms 
  unfolding extensional_def vec_delete_shift_def
  by auto
  
lemma v_to_l'_len: "length (v_to_l' m w) = m"
  by (induction m) (auto)

lemma v_to_l_zero [simp]:"v_to_l 0 w = []"
  unfolding v_to_l_def by simp

lemma v_to_l_Suc [simp]: "v_to_l (Suc n) w = v_to_l n w @ [w (Suc n)]"
  unfolding v_to_l_def by simp

lemma v_to_l_len:
  shows "length (v_to_l m w) = m"
  unfolding v_to_l_def
  apply (induction m)
  by auto

lemma v_to_l_restrict':
  assumes a0:"\<And>i. i\<in>{1..m} \<Longrightarrow> v i = w i"
  shows "v_to_l m v = v_to_l m w"
  unfolding v_to_l_def
  using assms
  by (induction m) (auto)

lemma v_to_l'_restrict:
  assumes a0:"\<And>i. i\<in>{1..m} \<Longrightarrow> v i = w i"
  shows "v_to_l' m v = v_to_l' m w"
  unfolding v_to_l_def
  using assms
  by (induction m) (auto)


lemma list_rev_index':
  "l\<in>{1..length ls} \<Longrightarrow> (rev ls) ! (l-1) = ls ! (length ls - l)"
  using rev_nth 
  by (metis Suc_eq_plus1 add.commute atLeastAtMost_iff le_add_diff_inverse linorder_le_less_linear not_less_eq_eq)

lemma list_rev_index:
  "l\<in>{1..length ls} \<Longrightarrow> ((rev ls) \<sqdot>  l) = (ls \<sqdot> (length ls - l + 1))"
  using list_rev_index' unfolding get_member_def by auto

lemma v_to_l_wd:
  shows "i\<in>{1..n} \<Longrightarrow> (the ((v_to_l n w) \<sqdot> i)) = w i"
proof (induction n arbitrary:w)
  case 0
  then show ?case by auto
next
  case (Suc n')
  then show ?case
    unfolding v_to_l_def get_member_simp_in 
  proof -
    have \<open>i-1\<in>{0..n'}\<close>
      using Suc by auto
    have "rev (v_to_l' (Suc n') w) ! (i - 1) = rev (w (Suc n') # (v_to_l' n' w)) ! (i-1)"
      by auto
    also have "... = ((rev (v_to_l' n' w)) @ [w (Suc n')]) ! (i-1)"
      by auto
    finally have b1:"rev (v_to_l' (Suc n') w) ! (i - 1) = ((rev (v_to_l' n' w)) @ [w (Suc n')]) ! (i-1)"
      by auto
    consider (Eq) "i=Suc n'" | (Lt) "i< Suc n'"
      using \<open>i\<in>{1..Suc n'}\<close> by fastforce
    then show "the (rev (v_to_l' (Suc n') w) \<sqdot> i) = w i"
    proof (cases)
      case Eq
      then show ?thesis
      proof -
        have "((rev (v_to_l' n' w)) @ [w (Suc n')]) ! (i-1) = w (Suc n')"
          using Eq v_to_l'_len[of "n'" "w"] 
          by (metis diff_Suc_1 length_rev nth_append_length)
        then show ?thesis
          using b1 Eq v_to_l'_len[of "Suc n'" "w"] by auto
      qed
    next
      case Lt
      then show ?thesis
      proof -
        have a_i:"i\<in>{1..n'}"
          using \<open>i\<in>{1..Suc n'}\<close> Lt by auto
        have "((rev (v_to_l' n' w)) @ [w (Suc n')]) ! (i-1) = ((rev (v_to_l' n' w)) ! (i-1))"
          using v_to_l'_len[of "n'""w"] Lt b1 Suc 
          by (metis (no_types, lifting) ext One_nat_def Suc_diff_Suc Suc_less_eq
               diff_is_0_eq length_greater_0_conv length_rev list_rev_index'
              minus_nat.diff_0 not_less0 nth_Cons_Suc nth_append v_to_l'.simps(2) v_to_l'_len zero_less_one_class.zero_le_one)
        also have "... = (w i)"
          using Suc.IH[of "w"] Lt a_i v_to_l'_len[of "n'" "w"]
          unfolding v_to_l_def get_member_def  by fastforce
        finally show "the (rev (v_to_l' (Suc n') w) \<sqdot> i) = w i"
          using b1 v_to_l'_len[of "Suc n'" "w"] a_i by auto
      qed
    qed
  qed
qed


lemma tl_v_to_l_delete_shift:
  assumes "length xs > 0"
  shows "tl (v_to_l (length xs) ws) = v_to_l (length xs -1) (vec_delete_shift 1 ws)"
proof (induction "length xs" arbitrary: xs ws rule: nat_induct_one)
  case zero
  then show ?case using assms by auto
next
  case one
  then show ?case
  proof -
    from one obtain x where "xs = [x]" 
      by (metis impossible_Cons le_geq_cases length_0_conv less_one list.exhaust zero_neq_one)
    then have "v_to_l (length xs) ws = v_to_l (length xs -1) ws @ [ws (length xs)]"
      using v_to_l_Suc one by auto
    also have "... = [ws 1]"
      using one by auto
    finally have b1:"tl (v_to_l (length xs) ws) = []"
      by auto
    have b2:"v_to_l (length xs -1) (vec_delete_shift 1 ws) = []"
      using one by auto
    show ?case using b1 b2 by auto
  qed
next
  case (suc n)
  then show ?case
  proof -
    have \<open>n=length (tl xs)\<close>
      using suc by auto
    then have \<open>length (tl xs) = length xs - 1\<close>
      using suc by auto
    have \<open>length (tl xs) - 1 = n-1\<close>
      using \<open>n=length (tl xs)\<close> by auto
    from v_to_l_Suc
    have "v_to_l (length xs) ws = v_to_l (length xs -1) ws @ [ws (length xs)]"
      using assms by (metis diff_Suc_1 suc.hyps(3))
    then have "tl (v_to_l (Suc n) ws) = tl (v_to_l (length xs - 1) ws) @ [ws (Suc n)]"
      using suc diff_Suc_1 list.size(3) not_one_le_zero tl_append2 v_to_l_len
      by metis
    also have "... = v_to_l (n - 1) (vec_delete_shift 1 ws) @ [ws (Suc n)]"
      using suc.hyps(2)[OF \<open>n=length (tl xs)\<close>] \<open>length (tl xs) - 1 = n-1\<close> \<open>length (tl xs) = length xs - 1\<close> by auto
    also have "... = v_to_l (n-1) (vec_delete_shift 1 ws) @ [(vec_delete_shift 1 ws) n]"
      unfolding vec_delete_shift_def using \<open>1\<le>n\<close> by auto
    also have "... = v_to_l n (vec_delete_shift 1 ws)"
      using v_to_l_Suc[of "n-1" "vec_delete_shift 1 ws"] suc.hyps(1) by auto
    finally show ?case
      using \<open>Suc n = length xs\<close> by (metis diff_Suc_1)
  qed
qed

lemma l_to_v'_shift:
  assumes a1:"i\<in>{1..n}"
      and a2:"m\<in>{1..n}"
    shows "l_to_v' (n+1) m xs (i+1) = l_to_v' n m xs i"
  using assms
proof (induction xs arbitrary:m)
  case Nil
  then show ?case 
    by auto
next
  case (Cons h t)
  show ?case
    (is "?l=?r")
  proof -
    have \<open>n - (m - 1) = n - m +1\<close>
      using Cons.prems by auto
    have \<open>n+1-(m-1) = n-m+2\<close>
      using Cons.prems by auto
    hence eql:"?l= ((l_to_v' (n+1) (m-1) t)(n-m+2:=h)) (i+1)"
      by (metis Suc_diff_1 Cons.prems atLeastAtMost_iff l_to_v'.simps(1) not_gr0 not_one_le_zero)
    have eqr:"?r= ((l_to_v' n (m-1) t)(n-m+1:=h)) i"
      using \<open>n - (m - 1) = n - m +1\<close> 
      by (metis Cons.prems add.commute atLeastAtMost_iff l_to_v'.simps(1) le_add_diff_inverse2 plus_1_eq_Suc)
    have "((l_to_v' (n+1) (m-1) t)(n-m+2:=h)) (i+1) = ((l_to_v' n (m-1) t)(n-m+1:=h)) i"
    proof (cases "i=n-m+1")
      case True
      then show ?thesis
        by auto
    next
      case False
      then show ?thesis
      proof (cases "m=1")
        case True
        then show ?thesis by auto
      next
        case False
        then show ?thesis
        proof -
          have \<open>m-1\<in>{1..n}\<close>
            using \<open>m\<in>{1..n}\<close> False by auto
          from Cons.IH[OF a1 \<open>m-1\<in>{1..n}\<close>]
          have "l_to_v' (n + 1) (m - 1) t (i + 1) = l_to_v' n (m - 1) t i"
            by simp
          thus ?thesis
            using \<open>i\<noteq>n-m+1\<close> by auto
        qed
      qed
    qed
    thus ?thesis
      using eql eqr by auto
  qed
qed

lemma l_to_v'_ls_idx:
  assumes a_i:"i\<in>{1..m}" 
      and a_m:"m\<in>{1..length xs}"
      and a_n:"length xs \<le> n"
    shows "l_to_v' n m xs (n-(m-i)) = the (xs \<sqdot> i)"
  using assms
proof (induction "length xs" arbitrary: xs n m i)
  case 0
  then show ?case
    by simp
next
  case (Suc n')
  show ?case
    (is "?l=?r")
  proof -
    have \<open>xs=hd xs # tl xs\<close>
      by (metis Suc.hyps(2) list.collapse list.size(3) nat.simps(3))
    hence eql:"?l= ((l_to_v' n (m-1) (tl xs))(n-(m-1):=hd xs)) (n - (m - i))"
      by (metis One_nat_def Suc.prems(2) Suc_le_eq Suc_pred' atLeastAtMost_iff l_to_v'.simps(1))
    have "((l_to_v' n (m-1) (tl xs))(n-(m-1):=hd xs)) (n-(m-i)) = the (xs\<sqdot>i)"
    proof (cases "i=1")
      case True
      then show ?thesis
        unfolding get_member_def
        by (metis Suc.hyps(2) Suc_eq_plus1 \<open>xs = hd xs # tl xs\<close> atLeastAtMost_iff cancel_comm_monoid_add_class.diff_cancel fun_upd_same le_add2 le_refl nth_Cons_0
            option.sel)
    next
      case False
      then show ?thesis
      proof -
        have \<open>length (tl xs) \<le> n - 1\<close>
          by (simp add: Suc.prems(3) diff_le_mono)
        have \<open>n' = length (tl xs)\<close>
          by (metis Suc.hyps(2) diff_Suc_1 length_tl)
        hence \<open>m - 1 \<in> {1..length (tl xs)}\<close>
          by (metis False Suc.hyps(2) Suc.prems(1,2) Suc_eq_plus1 atLeastAtMost_iff diff_Suc_eq_diff_pred diff_is_0_eq diffs0_imp_equal le_add2 old.nat.exhaust)
        have \<open>i\<in>{2..m}\<close>
          using False Suc.prems by auto
        hence \<open>i - 1 \<in> {1..m - 1}\<close>
          by auto
        have \<open>m>1\<close>
          using Suc.prems False by auto
        hence \<open>m - 1 \<in> {1..n - 1}\<close>
          using Suc.prems by auto
        hence \<open>m\<in>{2..n}\<close>
          by auto
        have "n - (m - i) - 1 \<le> n-1"
          by auto
        have "n - (m - i) - 1 \<ge>1"
          using \<open>i\<in>{2..m}\<close> \<open>m\<in>{2..n}\<close> by auto
        have "n - (m - i) - 1 \<in>{1..n-1}"
          using \<open>n - (m - i) - 1 \<ge>1\<close> \<open>n - (m - i) - 1 \<le> n-1\<close> by auto
        hence "n - (m - i) - 1 = n-(m-(i-1))"
          by (metis Suc.prems(1) Suc_diff_le Suc_eq_plus1 atLeastAtMost_iff diff_diff_left ordered_cancel_comm_monoid_diff_class.diff_diff_right)
        have "((l_to_v' n (m-1) (tl xs))(n-(m-1):=hd xs)) (n-(m-i)) = (l_to_v' n (m-1) (tl xs)) (n-(m-i))"
          using False Suc.prems atLeastAtMost_iff by auto
        also have "... = ((l_to_v' (n-1) (m-1) (tl xs)) (n-(m-i)-1))"
          using l_to_v'_shift[OF \<open>n - (m - i) - 1 \<in>{1..n-1}\<close> \<open>m - 1 \<in> {1..n - 1}\<close>] 
          by (metis \<open>1 \<le> n - (m - i) - 1\<close> add.commute less_Suc_eq_le less_imp_diff_less not_less_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
        also have "... = the ((tl xs) \<sqdot> (i-1))"
          using Suc.hyps(1)[OF \<open>n' = length (tl xs)\<close> \<open>i - 1 \<in> {1..m - 1}\<close> \<open>m - 1 \<in> {1..length (tl xs)}\<close> \<open>length (tl xs) \<le> n - 1\<close>]
          by (metis One_nat_def Suc.prems(1) Suc_pred' atLeastAtMost_iff diff_diff_eq diff_right_commute less_eq_Suc_le plus_1_eq_Suc)
        also have "... = the (xs \<sqdot> i)"
          unfolding get_member_def using \<open>i - 1 \<in> {1..m - 1}\<close> \<open>xs = hd xs # tl xs\<close> \<open>m\<in>{2..n}\<close> \<open>m - 1 \<in> {1..length (tl xs)}\<close>
          by (smt (verit, del_insts) Suc.prems(1,2) Suc_diff_le atLeastAtMost_iff diff_Suc_1 dual_order.strict_trans1 nth_Cons_Suc verit_comp_simplify1(3))
        finally show ?thesis
          by auto
      qed
    qed
    thus ?thesis
      using eql by auto
  qed
qed

lemma l_to_v_ls_idx:
  assumes a_i:"i\<in>{1..length xs}"
  shows "l_to_v xs i = the (xs \<sqdot> i)"
  using l_to_v'_ls_idx[of "i" "length xs" "xs" "length xs"] assms
  unfolding l_to_v_def by force

lemma vec_delete_shift_tl:"vec_delete_shift 1 (l_to_v xs) = l_to_v (tl xs)"
proof (induction "length xs" arbitrary: xs rule:nat_induct_one)
  case zero
  then show ?case
    by auto
next
  case one
  then show ?case
  (is "?l=?r")
  proof -
    have "l_to_v xs \<in> extensional {1}"
      using l_to_v_ext one 
      by (metis atLeastAtMost_singleton zero_less_one)
    hence "?l= (\<lambda>x. undefined)"
      using vec_delete_shift_one_empty by auto
    have "?r = (\<lambda>x. undefined)"
      using one unfolding l_to_v_def by auto
    thus ?thesis
      using \<open>?l= (\<lambda>x. undefined)\<close> by auto
  qed
next
  case (suc m)
  show ?case
  proof (rule ext)
    fix x
    have \<open>xs = hd xs # tl xs\<close>
      by (metis One_nat_def suc.hyps list.exhaust_sel list.size(3) nat.sel(1,2) zero_neq_one)
    have \<open>length (tl xs) = m\<close>
      using suc.hyps by auto
    show "vec_delete_shift 1 (l_to_v xs) x = l_to_v (tl xs) x"
    proof (cases "x\<in>{1..length xs-1}")
      case True
      then show ?thesis
      (is "?l=?r")
      proof -
        have eqr:"?r = l_to_v' (length xs-1) (length xs-1) (tl xs) x"
          unfolding l_to_v_def by auto
        have "?l = (l_to_v xs) (x+1)"
          unfolding vec_delete_shift_def using \<open>x\<in>{1..length xs-1}\<close> by auto
        also have "... = ((l_to_v' (length xs) (length xs -1) (tl xs))(1:=hd xs)) (x+1)"
          unfolding l_to_v_def 
          by (metis Suc_eq_plus1 \<open>xs = hd xs # tl xs\<close> add_diff_cancel_right' l_to_v'.simps(1) plus_1_eq_Suc suc.hyps(3))
        also have "... = (l_to_v' (length xs) (length xs -1) (tl xs)) (x+1)"
          using True by auto
        also have "... = l_to_v' (length xs-1) (length xs-1) (tl xs) x"
          using l_to_v'_shift[of "x" "length xs-1" "length xs-1" "tl xs"] 
          by (metis Suc_eq_plus1 True \<open>length (tl xs) = m\<close> atLeastAtMost_iff length_tl nle_le suc.hyps(1,3))
        finally show "?l=?r"
          using eqr by auto
      qed
    next
      case False
      then show ?thesis
      (is "?l=?r")
      proof -
        have "l_to_v xs \<in> extensional {1..length xs}"
          using l_to_v_ext 
          by (metis suc.hyps zero_less_Suc)
        have "?l=undefined"
          using vec_delete_shift_ext[OF \<open>l_to_v xs \<in> extensional {1..length xs}\<close>] False suc.hyps
          unfolding extensional_def by auto
        have "?r=undefined"
          using l_to_v_ext[of "tl xs"] length_tl \<open>m\<ge>1\<close> \<open>x \<notin> {1..length xs - 1}\<close> 
          unfolding extensional_def by fastforce
        thus ?thesis
          using \<open>?l=undefined\<close> by auto
      qed
    qed
  qed
qed


lemma l_to_v_to_l:
  "v_to_l (length xs) (l_to_v xs) = xs"
proof (induction "length xs" arbitrary: xs)
  case 0
  then show ?case
    unfolding l_to_v_def v_to_l_def by auto
next
  case (Suc m)
  then show ?case
  proof -
    have \<open>xs=hd xs # tl xs\<close>
      by (metis Suc.hyps(2) Zero_not_Suc list.collapse list.size(3))
    have \<open>m=length (tl xs)\<close>
      by (metis Suc.hyps(2) diff_Suc_1 length_tl)
    have "length (v_to_l (length xs) (l_to_v xs)) = Suc m"
      by (simp add: Suc.hyps(2) v_to_l_len)
    hence r1:"v_to_l (length xs) (l_to_v xs) = (hd (v_to_l (length xs) (l_to_v xs))) # (tl (v_to_l (length xs) (l_to_v xs)))"
      by (simp add: v_to_l_len)
    have "hd (v_to_l (length xs) (l_to_v xs)) = l_to_v xs 1"
      using v_to_l_wd[of "1" "length xs" "l_to_v xs"] hd_conv_nth[of "v_to_l (length xs) (l_to_v xs)"] 
            \<open>Suc m=length xs\<close> v_to_l_len[of "length xs" "l_to_v xs"] get_member_simp_the_in[of "1" "v_to_l (length xs) (l_to_v xs)"]
      by (metis Suc_eq_plus1 atLeastAtMost_iff cancel_comm_monoid_add_class.diff_cancel le_add2 le_refl nth_Cons_0 r1)
    also have "... = hd xs"
      using l_to_v_nonempty_hd
      by (metis Suc.hyps(2) zero_less_Suc)
    finally have r_hd:"hd (v_to_l (length xs) (l_to_v xs)) = hd xs"
      by simp
    have "tl (v_to_l (length xs) (l_to_v xs)) = v_to_l (length xs-1) (vec_delete_shift 1 (l_to_v xs))"
      using tl_v_to_l_delete_shift by (metis Suc.hyps(2) zero_less_Suc)
    also have "... = v_to_l (length xs-1) (l_to_v (tl xs))"
      using vec_delete_shift_tl[of "xs"] by auto
    also have "... = tl xs"
      using Suc.hyps(1)[OF \<open>m=length (tl xs)\<close>] by simp
    finally show ?thesis
      using r1 r_hd \<open>xs = hd xs # tl xs\<close> by auto
  qed
qed

definition subst_map where
  "subst_map I xs w = subst_map' I xs (v_to_l (length xs) w)"

lemma subst_map_empty_simp [simp]:
  "subst_map I [] w = I"
  unfolding subst_map_def by auto

lemma subst_map_one_simp[simp]:
  "length xs = 1 \<Longrightarrow> subst_map I xs w = I(hd xs := w 1)"
proof -
  assume a:"length xs = 1"
  then have "xs = [hd xs]"
    by (metis cancel_comm_monoid_add_class.diff_cancel hd_Cons_tl length_0_conv length_tl list.distinct(1) v_to_l_one_simp v_to_l_zero)
  then have "subst_map I xs w = subst_map I [hd xs] w"
    by auto
  also have "... = I(hd xs := w 1)"
    unfolding subst_map_def by auto
  finally show ?thesis 
    by simp
qed

lemma subst_map_simp:
  assumes a_x:"length xs > 0"
  shows "subst_map I xs ws = (subst_map' I (tl xs) (tl (v_to_l (length xs) ws)))(hd xs:=ws 1)"
proof -
  have \<open>xs = hd xs # tl xs\<close>
    using a_x by auto
  have \<open>v_to_l (length xs) ws = hd (v_to_l (length xs) ws) # (tl (v_to_l (length xs) ws))\<close>
    using v_to_l_len[of "length xs" "ws"] a_x 
    by (metis gr_implies_not0 list.exhaust_sel list.size(3))
  then have b1:"subst_map I xs ws = (subst_map' I (tl xs) (tl (v_to_l (length xs) ws)))((hd xs):= hd (v_to_l (length xs) ws))"
    unfolding subst_map_def using \<open>xs = hd xs # tl xs\<close> 
    by (metis subst_map'.simps(2))
  have "hd (v_to_l (length xs) ws) = ws 1"
    using list_hd_index[of "v_to_l (length xs) ws"] v_to_l_wd[of "1" "length xs" "ws"] v_to_l_len[of "length xs" "ws"] a_x
    unfolding get_member_def
    by auto
  then show ?thesis
    using b1 by auto
qed

lemma subst_map_simp2:
  assumes a_x:"length xs > 0"
  shows "subst_map I xs ws = (subst_map I (tl xs) (vec_delete_shift 1 ws))(hd xs:=ws 1)"
proof -
  have "subst_map I xs ws = (subst_map' I (tl xs) (tl (v_to_l (length xs) ws)))(hd xs := ws 1)"
    using subst_map_simp[OF a_x] by simp
  also have "... = (subst_map' I (tl xs) (v_to_l (length xs - 1) (vec_delete_shift 1 ws)))(hd xs := ws 1)"
    using tl_v_to_l_delete_shift[OF a_x] by metis
  also have "... = (subst_map I (tl xs) (vec_delete_shift 1 ws))(hd xs:=ws 1)"
    unfolding subst_map_def using length_tl[of "xs"] by simp
  finally show ?thesis
    by simp
qed

lemma subst_map_notin:
  assumes "\<not> ListMem a xs"
    shows "subst_map I xs x a = I a"
  using assms
proof (induction "length xs" arbitrary: xs x rule:nat_induct_one)
  case zero
  then show ?case
  proof -
    from zero have "xs = []" by auto
    then show ?case by auto
  qed
next
  case one
  then show ?case
  proof -
    obtain b where "xs = [b]" 
      using \<open>1 = length xs\<close> 
      by (metis One_nat_def length_0_conv length_Suc_conv)
    then have "a\<noteq>b"
      using \<open>\<not> ListMem a xs\<close> elem by fastforce
    have "subst_map I xs x = I(b:=x 1)"
      using \<open>xs=[b]\<close> subst_map_one_simp \<open>1 = length xs\<close> by auto
    then show "subst_map I xs x a = I a"
      using \<open>a\<noteq>b\<close> by auto
  qed
next
  case (suc n)
  then show ?case
  proof -
    have eq:"subst_map I xs x = (subst_map I (tl xs) (vec_delete_shift 1 x))(hd xs:=x 1)"
      using subst_map_simp2 \<open>Suc n = length xs\<close>  by (metis zero_less_Suc)
    have c1:"n=length (tl xs)"
      using \<open>Suc n = length xs\<close> length_tl[of "xs"] by auto
    have c2:"\<not> ListMem a (tl xs)"
      using suc.prems  by (metis ListMem.simps list.collapse list.sel(2))
    have b1:"(subst_map I (tl xs) (vec_delete_shift 1 x)) a = I a"
      using suc.hyps(2)[OF c1 c2] by simp
    have b2:"hd xs \<noteq> a"
      using \<open>\<not> ListMem a xs\<close> by (metis elem length_Suc_conv list.sel(1) suc.hyps(3))
    show ?case
      using eq b1 b2 by auto
  qed
qed

lemma subst_map_in:
  assumes "ListMem a xs"
    and "length xs = n"
  shows "\<exists>i\<in>{1..n}. (a=xs!(i-1)) \<and> subst_map I xs x a = (x i)"
  using assms
proof (induction n arbitrary: xs x rule:nat_induct_one)
  case zero
  then show ?case
  using list_mem_index' by fastforce
next
  case one
  then show ?case
  proof -
    have eq:"subst_map I xs x a = (I(hd xs:= x 1)) a"
      using subst_map_one_simp[OF \<open>length xs = 1\<close>] by metis
    from \<open>ListMem a xs\<close> have "a = hd xs"
      using \<open>length xs = 1\<close> 
      by (metis One_nat_def less_SucE less_zeroE list_hd_index list_mem_index')
    then have "a=(xs ! 0) \<and> (I(hd xs:= x 1)) a = x 1"
      by (simp add: list_hd_index one.prems(2))
    then show ?case
      using eq by auto
  qed
next
  case (suc n)
  then show ?case
  proof -
    have eq:"subst_map I xs x = ((subst_map I (tl xs) (vec_delete_shift 1 x))(hd xs:=x 1))"
      using subst_map_simp2 
      by (metis suc.prems(2) zero_less_Suc)
    consider (Eq) "a = hd xs" | (Neq) "a\<noteq>hd xs"
      by auto
    then show ?thesis
    proof (cases)
      case Eq
      then show ?thesis
        using eq 
        by (metis One_nat_def atLeastAtMost_iff diff_0_eq_0 diff_Suc_Suc diff_is_0_eq fun_upd_same list_hd_index suc.prems(2) zero_less_Suc)
    next
      case Neq
      then show ?thesis
      proof -
        have a0:"subst_map I xs x a = subst_map I (tl xs) (vec_delete_shift 1 x) a"
          using Neq eq by auto
        have "ListMem a (tl xs)"
          using Neq \<open>ListMem a xs\<close> by (metis ListMem_iff list.collapse list.sel(2) set_ConsD)
        have "length (tl xs) = n"
          using \<open>length xs = Suc n\<close> by auto
        from suc.IH[of "tl xs" "vec_delete_shift 1 x"]
        obtain i where a_i:"i\<in>{1..n}" and b1:"subst_map I (tl xs) (vec_delete_shift 1 x) a = vec_delete_shift 1 x i" and b2:"a = tl xs ! (i - 1)"
          using \<open>ListMem a (tl xs)\<close> \<open>length (tl xs) = n\<close>
          by auto
        have "a = xs ! i"
          using b2 \<open>length xs = Suc n\<close> 
          by (metis Suc_diff_le a_i atLeastAtMost_iff diff_Suc_1 length_Suc_conv list.sel(3) nth_Cons_Suc)
        have "i+1\<in>{1..Suc n}"
          using a_i by auto
        have "i+1\<in>{1..Suc n} \<and> a = xs ! i \<and> subst_map I xs x a = x (i+1)"
          using \<open>i+1\<in>{1..Suc n}\<close> a0 \<open>a = xs ! i\<close> b1 a_i unfolding vec_delete_shift_def by auto
        thus ?thesis
          by force
      qed
    qed
  qed
qed


lemma subst_map_in_unique':
  assumes "ListMem a xs"
    and "length xs = n"
    and "distinct xs"
  shows "\<exists>!i\<in>{1..n}. (a=xs!(i-1)) \<and> subst_map I xs x a = (x i)"
proof -
  from subst_map_in[OF \<open>ListMem a xs\<close> \<open>length xs = n\<close>] 
  have "\<exists>i\<in>{1..n}. a = (xs ! (i-1)) \<and> subst_map I xs x a = x i"
    by auto
  from list_distinct_index[OF \<open>distinct xs\<close>]
  have b1:"\<And>i j. i \<in> {0..length xs - 1} \<Longrightarrow> j \<in> {0..length xs - 1} \<Longrightarrow> xs ! i = xs ! j \<Longrightarrow> i = j"
    by auto
  hence "\<And>i j. i \<in> {1..n} \<Longrightarrow> j \<in> {1..n} \<Longrightarrow> xs ! (i-1) = xs ! (j-1) \<Longrightarrow> i = j"
  proof -
    fix i j assume \<open>i\<in>{1..n}\<close> and \<open>j\<in>{1..n}\<close> and \<open>xs ! (i-1) = xs ! (j-1)\<close>
    have \<open>i-1\<in>{0..length xs-1}\<close>
      using \<open>length xs = n\<close>\<open>i\<in>{1..n}\<close> by auto
    have \<open>j-1\<in>{0..length xs-1}\<close>
      using \<open>length xs = n\<close>\<open>j\<in>{1..n}\<close> by auto
    have \<open>i-1=j-1\<close>
      using b1[OF \<open>i-1\<in>{0..length xs-1}\<close> \<open>j-1\<in>{0..length xs-1}\<close> \<open>xs ! (i-1) = xs ! (j-1)\<close>] by simp
    thus "i=j"
      using \<open>i \<in> {1..n}\<close> \<open>j \<in> {1..n}\<close> by auto
  qed
  thus ?thesis
    using \<open>\<exists>i\<in>{1..n}. a = (xs ! (i-1)) \<and> subst_map I xs x a = x i\<close> by blast
qed

lemma subst_map_in_unique:
  assumes "ListMem a xs"
    and "distinct xs"
  shows "\<exists>!i\<in>{1..(length xs)}. (a=xs!(i-1)) \<and> subst_map I xs x a = (x i)"
  using subst_map_in_unique' assms by blast

(* modify interp I with vector x on variables xs. *)
lemma ls_idx_subst_map:
  assumes "ListMem a xs"
    and "distinct xs"
  shows "subst_map I xs x a = (x (ls_idx xs a + 1))"
proof -
  obtain i where a_i:"i\<in>{1..length xs} \<and> (a=xs!(i-1)) \<and> subst_map I xs x a = (x i)"
            and "\<And>j. j\<in>{1..length xs} \<and> (a=xs!(j-1)) \<and> subst_map I xs x a = (x j) \<Longrightarrow> j=i"
    using subst_map_in_unique[OF \<open>ListMem a xs\<close> \<open>distinct xs\<close>] by metis
  have \<open>i-1 \<in> {0..length xs - 1} \<and> a=xs!(i-1)\<close> 
    using a_i by auto
  then have \<open>i-1=ls_idx xs a\<close>
    using list_mem_unique_index[OF \<open>ListMem a xs\<close> \<open>distinct xs\<close>] assms ls_idx_prop by auto
  thus ?thesis
    using a_i by auto
qed

lemma ls_idxI:
  assumes "ListMem a xs"
    and "distinct xs"
    and "i\<in>{0..length xs-1}"
    and "a=(xs ! i)"
  shows "i=ls_idx xs a"
  unfolding ls_idx_def using assms 
  by (smt (verit, ccfv_threshold) list_distinct_index theI')

lemma ls_idxI':
  assumes "ListMem a xs"
    and "distinct xs"
    and "i\<in>{1..length xs}"
    and "a=the (xs \<sqdot> i)"
  shows "i-1=ls_idx xs a"
  using ls_idxI[of "a" "xs" "i-1"] assms unfolding get_member_def by auto

lemma ls_idx_inj:
  assumes 
    "distinct xs"
  and "ListMem a xs"
  and "ListMem b xs"
  and "ls_idx xs a = ls_idx xs b"
shows "a = b"
proof -
  have "a = xs ! (ls_idx xs a)"
    using ls_idx_prop[OF \<open>ListMem a xs\<close> \<open>distinct xs\<close>] by auto
  have "b = xs ! (ls_idx xs b)"
    using ls_idx_prop[OF \<open>ListMem b xs\<close> \<open>distinct xs\<close>] by auto
  thus ?thesis
    using \<open>a = xs ! (ls_idx xs a)\<close> \<open>ls_idx xs a = ls_idx xs b\<close> by auto
qed

lemma ls_idx_use:
  assumes "distinct xs" and "ListMem y xs"
  shows "ls_idx xs y = i \<Longrightarrow> y = xs ! i"
  using assms ls_idx_prop by fastforce

lemma ls_mem_ls_idx[simp]:
  shows "length xs > 0 \<Longrightarrow> k\<in>{0..length xs -1} \<Longrightarrow> ListMem (xs ! k) xs"
proof (induction "length xs" arbitrary:k xs rule:nat_induct_one)
  case zero
  then show ?case by auto
next
  case one
  then show ?case 
    using ListMem_iff by force
next
  case (suc n)
  show ?case
    using suc.hyps(2)[of "tl xs" "k-1"] suc 
    by (metis ListMem_iff atLeastAtMost_iff diff_Suc_1 in_set_conv_nth le_imp_less_Suc)
qed
  
lemma ls_idx_repeat [simp]:
  assumes "length xs > 0"
      and "distinct xs"
      and "k\<in>{0..length xs -1}"
    shows "ls_idx xs (xs ! k) = k"
proof (cases "length xs")
  case 0
  then show ?thesis using assms by auto
next
  case (Suc m)
  then show ?thesis
    using ls_idxI[of "xs ! k" "xs" "k"] ls_mem_ls_idx[of "xs" "k"] assms by auto
qed
  
lemma ls_map_to_map_add_entry:
  assumes a1:"i\<in>{1..length xs}" and a2:"distinct xs"
  shows "ls_map_to_map xs (B(i\<mapsto>y))= (ls_map_to_map xs B) ++ [xs ! (i-1) \<mapsto>y]"
  (is "?l=?r")
proof (cases "length xs")
  case 0
  then show ?thesis using a1 by force
next
  case (Suc m)
  show ?thesis 
  proof (rule ext)
    fix x
    consider (isI) "x = xs ! (i-1)" | (notI_inxs) "x\<noteq> xs ! (i-1) \<and> x\<in> set xs"  | (NotIn) "x\<notin> set xs"
      by auto
    then show "?l x = ?r x"
    proof (cases)
      case isI
      then show ?thesis
      proof -
        have \<open>length xs > 0\<close>
          using Suc by auto
        have b1:"ListMem x xs"
          using isI a1 
          by (metis get_member_simp_the_in idx_ls_mem)
        have b2: "ls_idx xs (xs ! (i-1)) = i-1"
          using ls_idx_repeat[of "xs" "i-1"] \<open>length xs > 0\<close> a2 a1 by auto
        hence eql:"ls_map_to_map xs (B(i \<mapsto> y)) x = Some y"
          using isI a1 b1 unfolding ls_map_to_map_def by auto
        have eqr:"?r x = Some y"
          using isI by auto
        show ?thesis
          using eql eqr by auto
      qed
    next
      case notI_inxs
      then show ?thesis
      proof -
        have eqr:"?r x = ls_map_to_map xs B x"
          using notI_inxs by auto
        have "ls_idx xs x \<noteq> i-1"
          using notI_inxs ls_idx_inj by (metis ListMem_iff a2 ls_idx_prop)
        hence "(B(i \<mapsto> y)) (ls_idx xs x + 1) = B (ls_idx xs x + 1)"
          by auto
        hence eql:"?l x = ls_map_to_map xs B x"
          unfolding ls_map_to_map_def by auto
        show ?thesis
          using eql eqr by auto
      qed
    next
      case NotIn
      then show ?thesis
        unfolding ls_map_to_map_def using a1 by auto
    qed
  qed
qed

lemma subst_map_notin_comm:
  assumes "\<not> ListMem a xs"
      and "distinct xs"
    shows "(subst_map I xs x)(a:=u) = subst_map (I(a:=u)) xs x"
proof (rule ext)
  fix b show "((subst_map I xs x)(a := u)) b = subst_map (I(a := u)) xs x b"
  proof (cases "a=b")
    case True
    then show ?thesis
      using subst_map_notin[OF \<open>\<not> ListMem a xs\<close>] 
      by (metis fun_upd_same)
  next
    case False
    then show ?thesis
    proof (cases "ListMem b xs")
      case True
      then show ?thesis 
      proof -
        have eq1:"((subst_map I xs x)(a := u)) b = subst_map I xs x b"
          using \<open>a\<noteq>b\<close> by auto
        also obtain i where b1:"... = x i" and \<open>b = xs ! (i - 1)\<close> and \<open>i \<in> {1..length xs}\<close>
          using subst_map_in_unique[OF \<open>ListMem b xs\<close> \<open>distinct xs\<close>]
          by meson
        from subst_map_in_unique[OF \<open>ListMem b xs\<close> \<open>distinct xs\<close>]
        obtain j where b2:"subst_map (I(a := u)) xs x b = x j" and \<open>b = xs ! (j - 1)\<close> and \<open>j\<in>{1..length xs}\<close>
          by meson
        have \<open>i-1\<in>{0..length xs-1}\<close> 
          using \<open>i \<in> {1..length xs}\<close> by auto
        have \<open>j-1\<in>{0..length xs-1}\<close> 
          using \<open>j \<in> {1..length xs}\<close> by auto        
        have \<open>i-1=j-1\<close>
          using \<open>b = xs ! (i - 1)\<close> \<open>b = xs ! (j - 1)\<close> \<open>i-1\<in>{0..length xs-1}\<close> \<open>j-1\<in>{0..length xs-1}\<close> list_mem_unique_index[OF \<open>ListMem b xs\<close> \<open>distinct xs\<close>]
          by auto
        then have \<open>i=j\<close>
          using \<open>i \<in> {1..length xs}\<close> \<open>j \<in> {1..length xs}\<close> by auto
        then show ?thesis
          using eq1 b1 b2 by auto
      qed
    next
      case False
      then show ?thesis
        using subst_map_notin[OF \<open>\<not> ListMem a xs\<close>] \<open>a\<noteq>b\<close> assms subst_map_notin
        by (metis fun_upd_apply)
    qed
  qed
qed

lemma subst_map_in_comm:
  assumes "ListMem a xs"
      and "distinct xs"
    shows "(subst_map I xs x)(a:=u) = subst_map I xs (x(ls_idx xs a+1 := u))"
proof (rule ext)
  fix b 
  have "ls_idx xs a \<in> {0..length xs-1}"
    using ls_idx_prop assms by auto
  show "((subst_map I xs x)(a := u)) b = subst_map I xs (x(ls_idx xs a+1 := u)) b"
    (is "?l=?r")
  proof (cases "a=b")
    case True
    then show ?thesis
    proof -
      have eql:"?l = u"
        using \<open>a=b\<close> by auto
      have eqr1:"?r = (x(ls_idx xs a + 1 := u)) (ls_idx xs b + 1)"
        using ls_idx_subst_map[OF \<open>ListMem a xs\<close> \<open>distinct xs\<close>] \<open>a=b\<close> 
        by blast
      also have "... = u"
        using \<open>a=b\<close> by auto
      thus ?thesis
        using eql eqr1 by auto
    qed
  next
    case False
    then show ?thesis
    proof (cases "ListMem b xs")
      case True
      then show ?thesis
      proof -
        have "?l = subst_map I xs x b"
          using \<open>a\<noteq>b\<close> by simp
        also have "... = x (ls_idx xs b + 1)"
          using ls_idx_subst_map[OF \<open>ListMem b xs\<close> \<open>distinct xs\<close>] by auto
        finally have eql:"?l = x (ls_idx xs b + 1)"
          by auto
        have "ls_idx xs a \<noteq> ls_idx xs b"
          using \<open>a\<noteq>b\<close> ls_idx_inj assms \<open>ListMem b xs\<close> by blast

        have "?r = (x(ls_idx xs a+1 := u)) (ls_idx xs b + 1)"
          using ls_idx_subst_map[OF \<open>ListMem b xs\<close>  \<open>distinct xs\<close>] by blast
        also have "... = x (ls_idx xs b + 1)"
          using \<open>ls_idx xs a \<noteq> ls_idx xs b\<close> by auto
        finally show "?l = ?r"
          using eql by auto
      qed
    next
      case False
      then show ?thesis
        using \<open>a\<noteq>b\<close> subst_map_notin assms
        by (metis (mono_tags, lifting) fun_upd_apply)
    qed
  qed
qed

lemma subst_map__subst_map_by_map_compat:
  assumes "length xs = length gs"
      and a1:"distinct xs"
  shows "subst_map' I xs gs = subst_map_by_map I (ls_to_map xs gs)"
proof (rule ext)
  fix x show "subst_map' I xs gs x = subst_map_by_map I (ls_to_map xs gs) x"
  proof (cases "ListMem x xs")
    case True
    then show ?thesis
    proof -
      have "subst_map I xs (l_to_v gs) x = ((l_to_v gs) (ls_idx xs x + 1))"
        using ls_idx_subst_map[OF \<open>ListMem x xs\<close> \<open>distinct xs\<close>] by auto
      then have b1:"subst_map' I xs gs x = ((l_to_v gs) (ls_idx xs x + 1))"
        using l_to_v_to_l[of "gs"] assms unfolding subst_map_def by auto
      have "ls_to_map xs gs x = Some (gs ! ls_idx xs x)"
        using ls_to_map_simp[OF \<open>ListMem x xs\<close>] by auto
      hence b2:"subst_map_by_map I (ls_to_map xs gs) x = (gs ! ls_idx xs x)"
        unfolding subst_map_by_map_def by auto
      have "ls_idx xs x + 1 \<in> {1..length xs}"
        using ls_idx_prop[OF \<open>ListMem x xs\<close> \<open>distinct xs\<close>]
        by (smt (z3) Suc_eq_plus1 Suc_eq_plus1_left True atLeastAtMost_iff diff_is_0_eq diff_le_self le_add2 le_add_diff_inverse le_less_Suc_eq less_imp_diff_less
          list_mem_index' verit_comp_simplify1(3))
      have "(l_to_v gs) (ls_idx xs x + 1) = gs ! (ls_idx xs x)"
        using l_to_v_ls_idx ls_idx_prop[OF \<open>ListMem x xs\<close> \<open>distinct xs\<close>] get_member_simp_the_in[OF \<open>ls_idx xs x + 1 \<in> {1..length xs}\<close>]
              \<open>ls_idx xs x + 1 \<in> {1..length xs}\<close> \<open>length xs = length gs\<close>
        by (metis add_diff_cancel_right' get_member_simp_the_in)
      thus ?thesis
        using b1 b2 by auto
    qed
  next
    case False
    then show ?thesis
    proof -
      have "subst_map' I xs gs x = I x"
        using subst_map_notin[OF \<open>\<not>ListMem x xs\<close>] l_to_v_to_l[of "gs"] \<open>length xs = length gs\<close> 
        unfolding subst_map_def by metis
      have "subst_map_by_map I (ls_to_map xs gs) x = I x"
        using \<open>\<not>ListMem x xs\<close> unfolding ls_to_map_def 
        by (simp add: ListMem_iff subst_map_by_map_def)
      thus ?thesis
        using \<open>subst_map' I xs gs x = I x\<close> by auto
    qed
  qed
qed

lemma subst_map__subst_map_by_map_compat2:
  assumes "length xs = length gs"
      and a1:"distinct xs"
    shows "subst_map I xs (l_to_v gs) = subst_map_by_map I (ls_to_map xs gs)"
  unfolding subst_map_def 
  using subst_map__subst_map_by_map_compat[OF \<open>length xs = length gs\<close> \<open>distinct xs\<close>] assms by (simp add: l_to_v_to_l)

lemma v_to_l_to_v:
  assumes "ws\<in>extensional {1..n}" and "n>0"
  shows "l_to_v (v_to_l n ws) = ws"
proof (rule ext)
  fix x show "l_to_v (v_to_l n ws) x = ws x"
  proof (cases "x\<in>{1..n}")
    case True
    then show ?thesis
    proof -
      have "l_to_v (v_to_l n ws) x = the ((v_to_l n ws) \<sqdot> x)"
        using l_to_v_ls_idx[of "x" "v_to_l n ws"] v_to_l_len True by metis
      also have "... = (ws x)"
        using v_to_l_wd[of "x" "n" "ws"] True by auto
      finally show ?thesis 
        by auto
    qed
  next
    case False
    then show ?thesis
    proof - 
      have "l_to_v (v_to_l n ws) \<in> extensional {1..n}"
        using l_to_v_ext[of "v_to_l n ws"] v_to_l_len[of "n" "ws"] \<open>n>0\<close> by auto
      hence b1:"l_to_v (v_to_l n ws) x = undefined"
        using False by (meson extensional_arb)
      have "ws x = undefined"
        using assms(1) False by (meson extensional_arb)
      thus ?thesis
        using b1 by auto
    qed
  qed
qed

lemma subst_map__subst_map_by_map_compat3:
  assumes a1:"distinct xs"
      and a2:"ws\<in>extensional {1..length xs}"
    shows "subst_map I xs ws = subst_map_by_map I (ls_to_map xs (v_to_l (length xs) ws))"
proof (cases "length xs")
  case 0
  then show ?thesis 
    by auto
next
  case (Suc n')
  then show ?thesis
  proof -
    have b1:"length xs = length (v_to_l (length xs) ws)"
      using v_to_l_len by metis
    have "l_to_v (v_to_l (length xs) ws) = ws"
      using v_to_l_to_v[of "ws" "length xs"] a2 \<open>length xs = Suc n'\<close> by auto
    thus "subst_map I xs ws = subst_map_by_map I (ls_to_map xs (v_to_l (length xs) ws))"
      using subst_map__subst_map_by_map_compat2[OF b1 a1] by auto
  qed
qed

end
