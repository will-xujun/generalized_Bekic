theory Locales
  imports
    Util
    "HOL-Library.FuncSet"
    "HOL-Algebra.Congruence"
    "HOL-Algebra.Order"
    "HOL-Algebra.Complete_Lattice"
begin

lemma (in complete_lattice) supI:
  assumes "least L a (Upper L A)"
  shows "a=\<Squnion>\<^bsub>L\<^esub>A"
proof -
  have "\<Squnion>\<^bsub>L\<^esub>A = (SOME x. least L x (Upper L A))"
    by (simp add: sup_def)
  also have "... = a"
    using assms least_unique by auto
  finally show ?thesis by auto
qed

lemma (in complete_lattice) supElim:
  "A\<subseteq>carrier L \<Longrightarrow> is_lub L (\<Squnion>A) A"
  using local.sup_lub by auto

lemma (in complete_lattice) infI:
  assumes "greatest L a (Lower L A)"
  shows "a=\<Sqinter>A"
proof -
  have "\<Sqinter>\<^bsub>L\<^esub>A = (SOME x. greatest L x (Lower L A))"
    by (simp add: inf_def)
  also have "... = a"
    using assms greatest_unique by auto
  finally show ?thesis by auto
qed

lemma (in complete_lattice) proj_carrier: "A \<subseteq> {1..n} \<rightarrow>\<^sub>E carrier L \<Longrightarrow> i\<in>{1..n} \<Longrightarrow> {f i| f. f\<in> A}\<subseteq> carrier L"
  by blast

lemma (in complete_lattice) vect_lub_is_coordwise_ub: " x \<in> A \<Longrightarrow> A \<subseteq> {1..n} \<rightarrow>\<^sub>E carrier L \<Longrightarrow> x \<in> {1..n} \<rightarrow>\<^sub>E carrier L \<Longrightarrow>i\<in>{1..n} \<Longrightarrow> x i \<sqsubseteq> \<Squnion>{f i |f. f \<in> A}"
proof - assume a1:"A \<subseteq> {1..n} \<rightarrow>\<^sub>E carrier L" and a2:"x \<in> {1..n} \<rightarrow>\<^sub>E carrier L" and a3:"i\<in>{1..n}" and a4:"x\<in>A"
  have b1:"{f i| f. f\<in> A} \<subseteq> carrier L" 
    using a1 a3 proj_carrier by blast
  have "x i \<in> {f i| f. f\<in> A}" 
    using a4 by auto
  then show "x i \<sqsubseteq> \<Squnion>{f i |f. f \<in> A}"
    using b1 by (simp add: sup_upper)
qed


lemma (in complete_lattice) vect_glb_is_coordwise_lb: " x \<in> A \<Longrightarrow> A \<subseteq> {1..n} \<rightarrow>\<^sub>E carrier L \<Longrightarrow> x \<in> {1..n} \<rightarrow>\<^sub>E carrier L \<Longrightarrow> i\<in>{1..n} \<Longrightarrow> \<Sqinter>{f i |f. f \<in> A} \<sqsubseteq> x i"
proof - assume a1:"A \<subseteq> {1..n} \<rightarrow>\<^sub>E carrier L" and a2:"x \<in> {1..n} \<rightarrow>\<^sub>E carrier L" and a3:"i\<in>{1..n}" and a4:"x\<in>A"
  have b1:"{f i| f. f\<in> A} \<subseteq> carrier L"
    using a1 a3 proj_carrier by blast
  have "x i \<in> {f i| f. f\<in> A}" 
    using a4 by auto
  then show "\<Sqinter>{f i |f. f \<in> A} \<sqsubseteq> x i"
    using b1 by (simp add: inf_lower)
qed

lemma (in complete_lattice) vect_lub_is_least: 
  "A \<subseteq> {1..n} \<rightarrow>\<^sub>E carrier L \<Longrightarrow> x \<in> {1..n} \<rightarrow>\<^sub>E carrier L \<Longrightarrow> \<forall>y. y \<in> A \<and> y \<in> {1..n} \<rightarrow>\<^sub>E carrier L \<longrightarrow> (\<forall>i\<in>{1..n}. y i \<sqsubseteq> x i) \<Longrightarrow> i\<in>{1..n} \<Longrightarrow> \<Squnion>{f i |f. f \<in> A} \<sqsubseteq> x i"
proof - assume a1:"x \<in> {1..n} \<rightarrow>\<^sub>E carrier L" and a2:"\<forall>y. y \<in> A \<and> y \<in> {1..n} \<rightarrow>\<^sub>E carrier L \<longrightarrow> (\<forall>i\<in>{1..n}. y i \<sqsubseteq> x i)"
  and a3:"i\<in>{1..n}" and a4:"A \<subseteq> {1..n} \<rightarrow>\<^sub>E carrier L"
  have b1:"{f i| f. f\<in> A} \<subseteq> carrier L"
    using proj_carrier a4 a3 by force
  have "\<And>y. y\<in>{f i| f. f\<in> A} \<Longrightarrow> y \<sqsubseteq> x i"
    using a2 a4 a3 by blast
  then show "\<Squnion>{f i |f. f \<in> A} \<sqsubseteq> x i"
    using a1 a3 b1 by (meson PiE_mem weak.sup_least)
qed

lemma (in complete_lattice) vect_glb_is_greatest: 
  "A \<subseteq> {1..n} \<rightarrow>\<^sub>E carrier L \<Longrightarrow> x \<in> {1..n} \<rightarrow>\<^sub>E carrier L \<Longrightarrow> \<forall>y. y \<in> A \<and> y \<in> {1..n} \<rightarrow>\<^sub>E carrier L \<longrightarrow> (\<forall>i\<in>{1..n}. x i \<sqsubseteq> y i) \<Longrightarrow> i\<in>{1..n} \<Longrightarrow> x i \<sqsubseteq> \<Sqinter>{f i |f. f \<in> A}"
proof - assume a1:"x \<in> {1..n} \<rightarrow>\<^sub>E carrier L" and a2:"\<forall>y. y \<in> A \<and> y \<in> {1..n} \<rightarrow>\<^sub>E carrier L \<longrightarrow> (\<forall>i\<in>{1..n}. x i \<sqsubseteq> y i)"
  and a3:"i\<in>{1..n}" and a4:"A \<subseteq> {1..n} \<rightarrow>\<^sub>E carrier L"
  have b1:"{f i| f. f\<in> A} \<subseteq> carrier L"
    using proj_carrier a4 a3 by force
  have "\<And>y. y\<in>{f i| f. f\<in> A} \<Longrightarrow> x i \<sqsubseteq> y"
    using a2 a4 a3 by blast
  then show "x i \<sqsubseteq> \<Sqinter>{f i |f. f \<in> A}"
    using a1 a3 b1 by (meson PiE_mem weak.inf_greatest)
qed

lemma vec_eqI [intro]: "f\<in>{1..n} \<rightarrow>\<^sub>E A \<Longrightarrow> g\<in>{1..n} \<rightarrow>\<^sub>E A \<Longrightarrow> (\<And>i. i\<in>{1..n} \<Longrightarrow> f i = g i) \<Longrightarrow> f = g"
  using FuncSet.PiE_ext by blast

section \<open> Additional lemmas for the complete_lattice locale \<close>

lemma (in complete_lattice) LFP_compare:
  assumes ale:"\<And>x. x\<in>carrier L \<Longrightarrow> f x \<sqsubseteq> g x" 
    and af: "f\<in> carrier L \<rightarrow> carrier L"
    and ag: "g\<in> carrier L \<rightarrow> carrier L"
  shows "LFP f \<sqsubseteq> LFP g"
  unfolding LEAST_FP_def
proof - 
  have "\<And>u. u\<in>carrier L \<Longrightarrow> g u \<sqsubseteq> u \<Longrightarrow> f u \<sqsubseteq> u"
  proof - fix u assume a0:"u\<in>carrier L" and a1:"g u \<sqsubseteq> u"
    have "f u \<in> carrier L"
      using a0 af by auto
    have "g u \<in> carrier L"
      using a0 ag by auto
    have "f u \<sqsubseteq> g u" 
      using ale a0 by auto
    then show "f u \<sqsubseteq> u"
      using a0 a1 local.le_trans \<open>f u \<in> carrier L\<close> \<open>g u \<in> carrier L\<close> by blast
  qed
  then have "{u \<in> carrier L. g u \<sqsubseteq> u} \<subseteq> {u \<in> carrier L. f u \<sqsubseteq> u}"
    by auto
  then show "\<Sqinter>{u \<in> carrier L. f u \<sqsubseteq> u} \<sqsubseteq> \<Sqinter>{u \<in> carrier L. g u \<sqsubseteq> u}"
    by (metis (mono_tags, lifting) LEAST_FP_def LFP_closed LFP_greatest LFP_lowerbound \<open>\<And>u. u \<in> carrier L \<Longrightarrow> g u \<sqsubseteq> u \<Longrightarrow> f u \<sqsubseteq> u\<close>)
qed

lemma (in complete_lattice) LFP_eqI:
  assumes ale:"\<And>x. x\<in>carrier L \<Longrightarrow> f x = g x" 
    and af: "f\<in> carrier L \<rightarrow> carrier L"
    and ag: "g\<in> carrier L \<rightarrow> carrier L"
  shows "LFP f = LFP g"
  using LFP_closed LFP_greatest LFP_lowerbound ale local.le_antisym by presburger


section \<open> A general locale for binary product of complete lattices \<close>

(* {E1,...,En}. E1\<times>...\<times>En. 
  f:{1..n} \<rightarrow> (E1 \<squnion> ...\<squnion> En) such that f(i) \<in> Ei

  (1,e1), (2,e2), ...
  Question: A library for disjoint set?
  
 *)

locale prod_lattice_bin = 
  E: complete_lattice E + F:complete_lattice F for E (structure) and F (structure)

definition (in prod_lattice_bin) prod_lub where
  "prod_lub A = (\<Squnion>\<^bsub>E\<^esub> (fst ` A), \<Squnion>\<^bsub>F\<^esub> (snd ` A))"

definition (in prod_lattice_bin) prod_glb where
  "prod_glb A = (\<Sqinter>\<^bsub>E\<^esub> (fst ` A), \<Sqinter>\<^bsub>F\<^esub> (snd ` A))"

definition (in prod_lattice_bin) prod_le where
  "prod_le f g \<equiv> le E (fst f) (fst g) \<and> le F (snd f) (snd g)"

lemma (in prod_lattice_bin) prod_in_carrier:
  "A \<subseteq> carrier E \<times> carrier F \<Longrightarrow> fst ` A \<subseteq> carrier E"
  by auto

lemma (in prod_lattice_bin) prod_in_carrier2:
  "A \<subseteq> carrier E \<times> carrier F \<Longrightarrow> snd ` A \<subseteq> carrier F"
  by auto

lemma (in prod_lattice_bin) prod_lub_in_carrier:
  "A \<subseteq> carrier E \<times> carrier F \<Longrightarrow> fst (prod_lub A) \<in> carrier E"
  unfolding prod_lub_def
  using E.sup_closed by (simp add: prod_in_carrier)

lemma (in prod_lattice_bin) prod_glb_in_carrier:
  "A \<subseteq> carrier E \<times> carrier F \<Longrightarrow> fst (prod_glb A) \<in> carrier E"
  unfolding prod_glb_def
  using E.inf_closed by (simp add: prod_in_carrier)

lemma (in prod_lattice_bin) prod_lub_in_carrier2:
  "A \<subseteq> carrier E \<times> carrier F \<Longrightarrow> snd (prod_lub A) \<in> carrier F"
  unfolding prod_lub_def
  using F.sup_closed by (simp add: prod_in_carrier2)

lemma (in prod_lattice_bin) prod_glb_in_carrier2:
  "A \<subseteq> carrier E \<times> carrier F \<Longrightarrow> snd (prod_glb A) \<in> carrier F"
  unfolding prod_glb_def
  using E.inf_closed by (simp add: prod_in_carrier2)

lemma (in prod_lattice_bin) prod_lub_is_ub: 
  "A \<subseteq> carrier E \<times> carrier F \<Longrightarrow> x\<in>A \<Longrightarrow> prod_le x (prod_lub A)"
  unfolding prod_le_def prod_lub_def
proof
  assume a1:"A \<subseteq> carrier E \<times> carrier F" and a2:"x \<in> A"
  then show "fst x \<sqsubseteq> fst (\<Squnion>fst ` A, \<Squnion>\<^bsub>F\<^esub>snd ` A)" 
    using a1 a2 by (simp add: E.sup_upper prod_in_carrier)
next
  assume a1:"A \<subseteq> carrier E \<times> carrier F" and a2:"x \<in> A"
  show "snd x \<sqsubseteq>\<^bsub>F\<^esub> snd (\<Squnion>fst ` A, \<Squnion>\<^bsub>F\<^esub>snd ` A)" 
    using a1 a2 by (simp add: F.sup_upper prod_in_carrier2)
qed

lemma (in prod_lattice_bin) prod_glb_is_lb: 
  "A \<subseteq> carrier E \<times> carrier F \<Longrightarrow> x\<in>A \<Longrightarrow> prod_le (prod_glb A) x"
  unfolding prod_le_def prod_glb_def
proof
  assume a1:"A \<subseteq> carrier E \<times> carrier F" and a2:"x \<in> A"
  then show "fst (\<Sqinter>fst ` A, \<Sqinter>\<^bsub>F\<^esub>snd ` A) \<sqsubseteq> fst x" 
    using a1 a2 by (simp add: E.inf_lower prod_in_carrier)
next
  assume a1:"A \<subseteq> carrier E \<times> carrier F" and a2:"x \<in> A"
  show "snd (\<Sqinter>fst ` A, \<Sqinter>\<^bsub>F\<^esub>snd ` A) \<sqsubseteq>\<^bsub>F\<^esub> snd x"
    using a1 a2 by (simp add: F.inf_lower prod_in_carrier2)
qed

lemma (in prod_lattice_bin) prod_lub_least_Upper:
  "A \<subseteq> carrier E \<times> carrier F \<Longrightarrow> x\<in>carrier E \<times> carrier F \<Longrightarrow> 
    (\<And> y. y\<in>A \<Longrightarrow> prod_le y x) \<Longrightarrow>
    prod_le (prod_lub A) x"
  using prod_lub_in_carrier[of "A"] prod_lub_in_carrier2[of "A"] prod_in_carrier prod_in_carrier2
  unfolding prod_le_def prod_lub_def
  using E.sup_least[of "fst ` A" "fst x"] F.sup_least[of "snd ` A" "snd x"] by force

lemma (in prod_lattice_bin) prod_glb_greatest_Lower:
  "A \<subseteq> carrier E \<times> carrier F \<Longrightarrow> x\<in>carrier E \<times> carrier F \<Longrightarrow> 
    (\<And> y. y\<in>A \<Longrightarrow> prod_le x y) \<Longrightarrow>
    prod_le x (prod_glb A)"
  using prod_glb_in_carrier[of "A"] prod_glb_in_carrier2[of "A"] prod_in_carrier prod_in_carrier2
  unfolding prod_le_def prod_glb_def
  using E.inf_greatest[of "fst ` A" "fst x"] F.inf_greatest[of "snd ` A" "snd x"] by force

lemma (in prod_lattice_bin) prod_glb_is_glb:
  "A \<subseteq> carrier E \<times> carrier F \<Longrightarrow> is_glb \<lparr>carrier = carrier E \<times> carrier F, eq = (=), le = prod_le\<rparr> (prod_glb A) A"
  unfolding prod_glb_def Lower_def greatest_def apply auto
  using prod_glb_def prod_glb_is_lb apply presburger
  using prod_glb_in_carrier apply (simp add: prod_in_carrier)
  using prod_glb_in_carrier2 apply (simp add: prod_in_carrier2)
proof - fix a b assume a1:"A \<subseteq> carrier E \<times> carrier F" 
    and a2:"\<forall>aa ba. (aa, ba) \<in> A \<and> aa \<in> carrier E \<and> ba \<in> carrier F \<longrightarrow> prod_le (a, b) (aa, ba)"
    and a3:"a \<in> carrier E" 
    and a4:"b\<in> carrier F" show "prod_le (a, b) (\<Sqinter>fst ` A, \<Sqinter>\<^bsub>F\<^esub>snd ` A)"
    using prod_glb_greatest_Lower[of "A""(a,b)"] a1 a2 a3 a4 unfolding prod_glb_def by blast
qed

lemma (in prod_lattice_bin) prod_lub_is_lub:
  "A \<subseteq> carrier E \<times> carrier F \<Longrightarrow> is_lub \<lparr>carrier = carrier E \<times> carrier F, eq = (=), le = prod_le\<rparr> (prod_lub A) A"
  unfolding prod_lub_def Upper_def least_def apply auto
  using prod_lub_def prod_lub_is_ub apply presburger
  using prod_lub_in_carrier apply (simp add: prod_in_carrier)
  using prod_lub_in_carrier2 apply (simp add: prod_in_carrier2)
proof - fix a b assume a1:"A \<subseteq> carrier E \<times> carrier F" 
    and a2:"\<forall>aa ba. (aa, ba) \<in> A \<and> aa \<in> carrier E \<and> ba \<in> carrier F \<longrightarrow> prod_le (aa, ba) (a, b)"
    and a3:"a \<in> carrier E" 
    and a4:"b\<in> carrier F" show "prod_le (\<Squnion>fst ` A, \<Squnion>\<^bsub>F\<^esub>snd ` A) (a, b)"
    using prod_lub_least_Upper[of "A""(a,b)"] a1 a2 a3 a4 unfolding prod_lub_def by blast
qed

sublocale prod_lattice_bin \<subseteq> complete_lattice 
  "\<lparr> carrier = carrier E \<times> carrier F, eq=(=), le=prod_le \<rparr>"
  apply unfold_locales apply (auto)
  using prod_le_def apply auto
  using E.le_trans apply blast
  using F.le_trans apply blast
  using prod_lub_is_lub unfolding prod_lub_def apply blast
  using prod_glb_is_glb unfolding prod_glb_def apply blast
  done

definition (in prod_lattice_bin) E_times_F where
  "E_times_F = \<lparr> carrier = carrier E \<times> carrier F, eq=(=), le=prod_le \<rparr>"

lemma (in prod_lattice_bin) prod_carrierE [simp]: "carrier E_times_F = carrier E \<times> carrier F"
  unfolding E_times_F_def by auto
lemma (in prod_lattice_bin) prod_le_equiv [simp]: "x \<sqsubseteq>\<^bsub>E_times_F\<^esub> y = (fst x \<sqsubseteq> fst y \<and> snd x \<sqsubseteq>\<^bsub>F\<^esub> snd y)"
  unfolding E_times_F_def prod_le_def by auto
lemma (in prod_lattice_bin) prod_leI [intro]: "(fst x \<sqsubseteq> fst y \<and> snd x \<sqsubseteq>\<^bsub>F\<^esub> snd y) \<Longrightarrow> x \<sqsubseteq>\<^bsub>E_times_F\<^esub> y"
  using prod_le_equiv by auto


section \<open> A general locale for complete lattice isomorphisms \<close>

locale complete_lattice_hom =
  E: complete_lattice E + F: complete_lattice F for E (structure) and F (structure)
+ fixes \<phi> and \<psi> and TE and TF
assumes funcset_forward: "\<phi>\<in> carrier E \<rightarrow>\<^sub>E carrier F"
  and   funcset_back: "\<psi> \<in> carrier F \<rightarrow>\<^sub>E carrier E"
  and   opE: "TE \<in> carrier E \<rightarrow>\<^sub>E carrier E"
  and   opF: "TF \<in> carrier F \<rightarrow>\<^sub>E carrier F"
  and   hom_le_forward: "\<And>x y. x\<in> carrier E \<Longrightarrow> y\<in> carrier E \<Longrightarrow> x \<sqsubseteq>\<^bsub>E\<^esub> y \<Longrightarrow> \<phi> x \<sqsubseteq>\<^bsub>F\<^esub> \<phi> y"
  and   hom_le_back: "\<And>x y. x\<in> carrier F \<Longrightarrow> y\<in> carrier F \<Longrightarrow> x \<sqsubseteq>\<^bsub>F\<^esub> y \<Longrightarrow> \<psi> x \<sqsubseteq>\<^bsub>E\<^esub> \<psi> y"
  and   left_inv: "\<And>x. x\<in> carrier E \<Longrightarrow> \<psi> (\<phi> x) = x"
  and   right_inv: "\<And>x. x\<in> carrier F \<Longrightarrow> \<phi> (\<psi> x) = x"
  and   comm: "\<And>x. x\<in>carrier E \<Longrightarrow> (\<phi> \<circ> TE) x = (TF \<circ> \<phi>) x"

lemma (in complete_lattice_hom) hom_inv_le_forward: "\<And>x y. x\<in> carrier E \<Longrightarrow> y\<in> carrier E \<Longrightarrow> x \<sqsubseteq>\<^bsub>inv_gorder E\<^esub> y \<Longrightarrow> \<phi> x \<sqsubseteq>\<^bsub>inv_gorder F\<^esub> \<phi> y"
  using hom_le_forward by auto
lemma (in complete_lattice_hom) hom_inv_le_back: "\<And>x y. x\<in> carrier F \<Longrightarrow> y\<in> carrier F \<Longrightarrow> x \<sqsubseteq>\<^bsub>inv_gorder F\<^esub> y \<Longrightarrow> \<psi> x \<sqsubseteq>\<^bsub>inv_gorder E\<^esub> \<psi> y"
  using hom_le_back by auto

lemma (in complete_lattice_hom) forward_isotone: "isotone E F \<phi>"
  unfolding isotone_def using E.weak_partial_order_axioms F.weak_partial_order_axioms apply simp
  apply rule apply rule
  using hom_le_forward by auto

lemma (in complete_lattice_hom) backward_isotone: "isotone F E \<psi>"
  unfolding isotone_def using E.weak_partial_order_axioms F.weak_partial_order_axioms apply simp
  apply rule apply rule
  using hom_le_back by auto

lemma (in complete_lattice_hom) inj_forward[simp]: "\<lbrakk> x\<in>carrier E; y\<in>carrier E \<rbrakk> \<Longrightarrow> \<phi> x \<sqsubseteq>\<^bsub>F\<^esub> \<phi> y \<longleftrightarrow> x \<sqsubseteq> y"
  apply (auto simp add:hom_le_forward)
proof - 
  assume a1:"x\<in>carrier E" and a2:"y\<in>carrier E" and a3:"\<phi> x \<sqsubseteq>\<^bsub>F\<^esub> \<phi> y"
  have "\<psi> (\<phi> x) \<sqsubseteq> \<psi> (\<phi> y)" 
    using hom_le_back funcset_forward funcset_back a1 a2 a3 left_inv by (metis (no_types, lifting) PiE_E)
  then show "x \<sqsubseteq> y"
    using left_inv a1 a2 by auto
qed

lemma (in complete_lattice_hom) inj_back[simp]: "\<lbrakk> x\<in>carrier F; y\<in>carrier F \<rbrakk> \<Longrightarrow> \<psi> x \<sqsubseteq>\<^bsub>E\<^esub> \<psi> y \<longleftrightarrow> x \<sqsubseteq>\<^bsub>F\<^esub> y"
  apply (auto simp add:hom_le_back)
proof - 
  assume a1:"x\<in>carrier F" and a2:"y\<in>carrier F" and a3:"\<psi> x \<sqsubseteq> \<psi> y"
  have "\<phi> (\<psi> x) \<sqsubseteq>\<^bsub>F\<^esub> \<phi> (\<psi> y)" 
    using hom_le_back funcset_forward funcset_back a1 a2 a3 right_inv left_inv by (meson PiE_E hom_le_forward)
  then show "x \<sqsubseteq>\<^bsub>F\<^esub> y"
    using right_inv a1 a2 by auto
qed

lemma (in complete_lattice) sup_lub:
  "A\<subseteq>carrier L \<Longrightarrow> is_lub L a A \<longleftrightarrow> (a=\<Squnion>\<^bsub>L\<^esub>A)"
  using supI supElim by blast

lemma (in complete_lattice_hom) sup_compat_forward: "A\<subseteq> carrier E \<Longrightarrow> \<phi> (\<Squnion>\<^bsub>E\<^esub> A) = (\<Squnion>\<^bsub>F\<^esub> (\<phi> ` A))"
proof - assume a1:"A\<subseteq> carrier E" show "\<phi> (\<Squnion>\<^bsub>E\<^esub> A) = (\<Squnion>\<^bsub>F\<^esub> (\<phi> ` A))"
  proof (rule F.supI)
    have b2:"\<And>y. y\<in> \<phi> ` A \<Longrightarrow> y \<sqsubseteq>\<^bsub>F\<^esub> \<phi>(\<Squnion>A)"
    proof - fix y assume "y \<in> \<phi> ` A"
      then obtain a where b1:"a\<in>A \<and> y=\<phi> a" by auto
      then have "a \<sqsubseteq> (\<Squnion>A)" 
        using E.supElim a1 E.sup_upper by auto
      then show "y \<sqsubseteq>\<^bsub>F\<^esub> \<phi>(\<Squnion>A)"
        using b1 hom_le_forward funcset_forward by (meson E.sup_closed a1 subset_eq)
    qed
    have b3:"\<And>x. x\<in> Upper F (\<phi> ` A) \<Longrightarrow> \<phi> (\<Squnion>A) \<sqsubseteq>\<^bsub>F\<^esub> x"
    proof -
      fix x assume a2:"x\<in> Upper F (\<phi> ` A)"
      show "\<phi> (\<Squnion>A) \<sqsubseteq>\<^bsub>F\<^esub> x"
      proof - 
        have a3:"x\<in>carrier F" using a2 unfolding Upper_def by blast
        have "\<And>a. a\<in>A \<Longrightarrow> \<phi> a \<sqsubseteq>\<^bsub>F\<^esub> x" 
          using a1 a2 funcset_forward unfolding Upper_def by blast
        then have "\<And>a. a\<in>A \<Longrightarrow> a \<sqsubseteq> \<psi> x"
          using right_inv hom_le_back funcset_back a1 a3 by (metis (no_types, lifting) PiE_mem inj_forward subsetD)
        then have "\<Squnion>A \<sqsubseteq> \<psi> x"
          by (metis E.weak_complete_lattice_axioms PiE_mem a1 a3 funcset_back weak_complete_lattice.sup_least)
        then show "\<phi> (\<Squnion>\<^bsub>E\<^esub> A) \<sqsubseteq>\<^bsub>F\<^esub> x"
          by (metis (no_types, lifting) E.weak_complete_lattice_axioms PiE_E a1 a3 funcset_forward inj_back left_inv weak_complete_lattice.sup_closed)
      qed
    qed
    from b2 b3 show "is_lub F (\<phi> (\<Squnion>A)) (\<phi> ` A)"
      by (metis (no_types, lifting) E.sup_closed PiE_mem Upper_closed Upper_memI a1 funcset_forward least_def)
  qed
qed

lemma back_complete_lattice_hom:
  assumes "complete_lattice_hom E F \<phi> \<psi> TE TF"
  shows "complete_lattice_hom F E \<psi> \<phi> TF TE"
proof (rule complete_lattice_hom.intro)
  from assms complete_lattice_hom.axioms
  show "complete_lattice F" by blast
  from assms complete_lattice_hom.axioms
  show "complete_lattice E" by blast
  show "complete_lattice_hom_axioms F E \<psi> \<phi> TF TE"
    unfolding complete_lattice_hom_axioms_def
    using complete_lattice_hom.axioms(3)[of "E" "F" "\<phi>" "\<psi>" "TE" "TF"] assms
    unfolding complete_lattice_hom_axioms_def
    by (smt (verit, best) PiE_mem comp_apply)
qed

lemma (in complete_lattice_hom) sup_compat_back: "A\<subseteq> carrier F \<Longrightarrow> \<psi> (\<Squnion>\<^bsub>F\<^esub> A) = (\<Squnion>\<^bsub>E\<^esub> (\<psi> ` A))"
proof -
  assume a1:"A\<subseteq> carrier F"
  interpret backL: complete_lattice_hom "F" "E" "\<psi>" "\<phi>" "TF" "TE"
    using back_complete_lattice_hom complete_lattice_hom_axioms by blast
  show ?thesis
    using backL.sup_compat_forward a1 by auto
qed

lemma (in complete_lattice) dual_complete_lattice: 
  assumes "complete_lattice L"
  shows "complete_lattice (inv_gorder L)"
proof -
  interpret dual: weak_complete_lattice "inv_gorder L"
    using dual_weak_complete_lattice by blast
  show ?thesis
    apply unfold_locales
      apply (simp add: eq_is_equal)
    using dual.sup_exists dual.inf_exists by auto
qed

lemma (in complete_lattice_hom) dual_lattice_hom:
  assumes "complete_lattice_hom E F \<phi> \<psi> TE TF"
  shows "complete_lattice_hom (inv_gorder E) (inv_gorder F) \<phi> \<psi> TE TF"
proof -
  have dualE: "complete_lattice (inv_gorder E)"
    using E.dual_complete_lattice Locales.complete_lattice_hom.axioms assms by blast
  have dualF: "complete_lattice (inv_gorder F)"
    using F.dual_complete_lattice Locales.complete_lattice_hom.axioms assms by blast
  have dual_axioms: "complete_lattice_hom_axioms (inv_gorder E) (inv_gorder F) \<phi> \<psi> TE TF"
    unfolding complete_lattice_hom_axioms_def apply simp
    using Locales.complete_lattice_hom.axioms[of "E" "F" "\<phi>" "\<psi>" "TE" "TF"] assms
    unfolding complete_lattice_hom_axioms_def by auto   
  show ?thesis
    using dualE dualF dual_axioms complete_lattice_hom.intro[of "inv_gorder E" "inv_gorder F" "\<phi>" "\<psi>" "TE" "TF"]
    by auto
qed

lemma (in complete_lattice_hom) complete_lattice_hom_dual_elims:
  assumes "complete_lattice_hom E F \<phi> \<psi> TE TF"
  shows "complete_lattice (inv_gorder E)"
  using dual_lattice_hom complete_lattice_hom.axioms(1) assms by auto

lemma (in complete_lattice_hom) comm2: "\<And>x. x\<in>carrier F \<Longrightarrow> (\<psi> \<circ> TF) x = (TE \<circ> \<psi>) x"
proof -
  fix x assume a1:"x\<in>carrier F" show "(\<psi> \<circ> TF) x = (TE \<circ> \<psi>) x"
  proof -
    have "\<phi> (TE (\<psi> x)) = TF (\<phi> (\<psi> x))" 
      using comm a1 funcset_back by auto
    then have "\<psi> (\<phi> (TE (\<psi> x))) = \<psi> (TF (\<phi> (\<psi> x)))"
      by auto
    then have "TE (\<psi> x) = \<psi> (TF x)"
      using left_inv right_inv a1 funcset_back funcset_forward opE opF PiE_mem by metis
    then show ?thesis by auto
  qed
qed

lemma (in complete_lattice_hom) inf_compat_forward: "A\<subseteq> carrier E \<Longrightarrow> \<phi> (\<Sqinter>\<^bsub>E\<^esub> A) = (\<Sqinter>\<^bsub>F\<^esub> (\<phi> ` A))"
proof -
  assume a1:"A\<subseteq> carrier E"
  interpret dual_hom: complete_lattice_hom "(inv_gorder E)" "(inv_gorder F)" "\<phi>" "\<psi>" "TE" "TF"
    using dual_lattice_hom complete_lattice_hom_axioms by auto
  have "\<phi> (\<Squnion>\<^bsub>inv_gorder E\<^esub> A) = (\<Squnion>\<^bsub>inv_gorder F\<^esub> (\<phi> ` A))"
    using dual_hom.sup_compat_forward a1 by auto
  then show ?thesis
    using sup_dual by auto
qed

lemma (in complete_lattice_hom) inf_compat_back: "A\<subseteq> carrier F \<Longrightarrow> \<psi> (\<Sqinter>\<^bsub>F\<^esub> A) = (\<Sqinter>\<^bsub>E\<^esub> (\<psi> ` A))"
proof -
  assume a1:"A\<subseteq> carrier F"
  interpret dual_hom: complete_lattice_hom "(inv_gorder F)" "(inv_gorder E)" "\<psi>" "\<phi>" "TF" "TE"
    using dual_lattice_hom complete_lattice_hom_axioms back_complete_lattice_hom by auto
  have "\<psi> (\<Squnion>\<^bsub>inv_gorder F\<^esub> A) = (\<Squnion>\<^bsub>inv_gorder E\<^esub> (\<psi> ` A))"
    using dual_hom.sup_compat_forward a1 by auto
  then show ?thesis
    using sup_dual by auto
qed  

lemma (in complete_lattice_hom) LFP_compat_forward: "LFP\<^bsub>F\<^esub> TF = \<phi> (LFP TE)"
  (is "?lhs=?rhs") unfolding LEAST_FP_def
proof -
  have "?rhs = \<Sqinter>\<^bsub>F\<^esub> \<phi> ` {u \<in> carrier E. TE u \<sqsubseteq> u}"
    unfolding LEAST_FP_def using inf_compat_forward by auto
  also have "... = \<Sqinter>\<^bsub>F\<^esub> \<phi> ` {\<psi> (\<phi> u) |u. u\<in>carrier E \<and> TE (\<psi> (\<phi> u)) \<sqsubseteq> \<psi> (\<phi> u)}"
    using left_inv by (metis (no_types, opaque_lifting))
  also have "... = \<Sqinter>\<^bsub>F\<^esub> { \<phi> (\<psi> (\<phi> u)) |u. u\<in>carrier E \<and> TE (\<psi> (\<phi> u)) \<sqsubseteq> \<psi> (\<phi> u)}"
    by (metis image_Collect image_image)
  also have "... = \<Sqinter>\<^bsub>F\<^esub> { \<phi> u |u. u\<in>carrier E \<and> \<psi> (TF (\<phi> u)) \<sqsubseteq> \<psi> (\<phi> u)}"
    using comm2 funcset_forward right_inv by (metis (lifting) PiE_mem comp_eq_dest_lhs )
  also have "... = \<Sqinter>\<^bsub>F\<^esub> { v |v. v\<in>carrier F \<and> \<psi> (TF v) \<sqsubseteq> \<psi> v}"
    using left_inv by (metis (lifting) PiE_mem funcset_back funcset_forward right_inv)
  also have "... = \<Sqinter>\<^bsub>F\<^esub> { v |v. v\<in>carrier F \<and> (TF v) \<sqsubseteq>\<^bsub>F\<^esub> v}"
    using inj_back opF by (meson PiE_E)
  finally have "?rhs=?lhs" 
    unfolding LEAST_FP_def by auto
  then show "\<Sqinter>\<^bsub>F\<^esub>{u \<in> carrier F. TF u \<sqsubseteq>\<^bsub>F\<^esub> u} = \<phi> (\<Sqinter>{u \<in> carrier E. TE u \<sqsubseteq> u})"
    unfolding LEAST_FP_def by auto
qed

lemma (in complete_lattice_hom) GFP_compat_forward: "GFP\<^bsub>F\<^esub> TF = \<phi> (GFP TE)"
proof -
  interpret dual_hom: complete_lattice_hom "(inv_gorder E)" "(inv_gorder F)" "\<phi>" "\<psi>" "TE" "TF"
    using dual_lattice_hom complete_lattice_hom_axioms by auto
  have b1:"GFP\<^bsub>F\<^esub> TF = LFP\<^bsub>inv_gorder F\<^esub> TF"
    using LFP_dual by auto
  have b2:"\<phi> (GFP TE) = \<phi> (LFP\<^bsub>inv_gorder E\<^esub> TE)"
    using LFP_dual by auto
  have b3:"LFP\<^bsub>inv_gorder F\<^esub> TF = \<phi> (LFP\<^bsub>inv_gorder E\<^esub> TE)"
    using dual_hom.LFP_compat_forward by auto
  show ?thesis using b1 b2 b3 by auto
qed
  
lemma (in complete_lattice_hom) Lfp_compat_back: "LFP TE = \<psi> (LFP\<^bsub>F\<^esub> TF)"
proof -
  interpret backL: complete_lattice_hom "F" "E" "\<psi>" "\<phi>" "TF" "TE"
    using back_complete_lattice_hom complete_lattice_hom_axioms by blast
  from local.backL.LFP_compat_forward
  show ?thesis by auto
qed

lemma (in complete_lattice_hom) GFP_compat_back: "GFP TE = \<psi> (GFP\<^bsub>F\<^esub> TF)"
proof -
  interpret backL: complete_lattice_hom "F" "E" "\<psi>" "\<phi>" "TF" "TE"
    using back_complete_lattice_hom complete_lattice_hom_axioms by blast
  from local.backL.GFP_compat_forward
  show ?thesis by auto
qed


section \<open> The binary Bekic principle \<close>

definition fun_proj1_basic:: "('a \<times> 'b \<Rightarrow> 'a \<times> 'b) \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a" where 
  "fun_proj1_basic f A = (\<lambda>x\<in>A. fst (f x))"

definition fun_proj2_basic:: "('a \<times> 'b \<Rightarrow> 'a \<times> 'b) \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'b" where
  "fun_proj2_basic f A = (\<lambda>x\<in>A. snd (f x))"

definition (in prod_lattice_bin) fun_proj1:: "('a \<times> 'c \<Rightarrow> 'a \<times> 'c) \<Rightarrow> 'a \<times> 'c \<Rightarrow> 'a" (\<open>\<pi>1 _\<close>) where
  "fun_proj1 f x = fun_proj1_basic f (carrier E \<times> carrier F) x"

definition (in prod_lattice_bin) fun_proj2:: "('a \<times> 'c \<Rightarrow> 'a \<times> 'c) \<Rightarrow> 'a \<times> 'c \<Rightarrow> 'c" (\<open>\<pi>2 _\<close>) where
  "fun_proj2 f x = fun_proj2_basic f (carrier E \<times> carrier F) x"

lemma (in prod_lattice_bin) funcset_proj1:
  assumes "f \<in> carrier E \<times> carrier F \<rightarrow>\<^sub>E carrier E \<times> carrier F"
  shows "(\<pi>1 f) \<in> carrier E \<times> carrier F \<rightarrow>\<^sub>E carrier E"
  unfolding fun_proj1_def fun_proj1_basic_def apply auto
proof -
  fix a b assume "a\<in>carrier E" and "b\<in>carrier F"
  then have "(a,b)\<in>carrier E \<times> carrier F" by auto
  then have "f (a,b) \<in> carrier E \<times> carrier F"
    using assms by auto
  then show "fst (f (a,b)) \<in> carrier E" 
    by auto
qed

lemma (in prod_lattice_bin) funcset_proj2:
  assumes "f \<in> carrier E \<times> carrier F \<rightarrow>\<^sub>E carrier E \<times> carrier F"
  shows "(\<pi>2 f) \<in> carrier E \<times> carrier F \<rightarrow>\<^sub>E carrier F"
  unfolding fun_proj2_def fun_proj2_basic_def apply auto
proof -
  fix a b assume "a\<in>carrier E" and "b\<in>carrier F"
  then have "(a,b)\<in>carrier E \<times> carrier F" by auto
  then have "f (a,b) \<in> carrier E \<times> carrier F"
    using assms by auto
  then show "snd (f (a,b)) \<in> carrier F" 
    by auto
qed
 
lemma (in prod_lattice_bin) mono_proj2:
  assumes a_car:"f \<in> carrier E \<times> carrier F \<rightarrow>\<^sub>E carrier E \<times> carrier F"
      and a_mono:"Mono\<^bsub>E_times_F\<^esub> f"
    shows "isotone E_times_F F \<pi>2 f"
  unfolding E_times_F_def
proof 
  show "weak_partial_order \<lparr>carrier = carrier E \<times> carrier F, eq = (=), le = prod_le\<rparr>"
    by (simp add: weak_partial_order_axioms)
  show "weak_partial_order F"
    by (simp add: F.weak_partial_order_axioms)
  fix x y assume a1:"x\<in> carrier \<lparr>carrier = carrier E \<times> carrier F, eq = (=), le = prod_le\<rparr>" 
    and a2:"y\<in> carrier \<lparr>carrier = carrier E \<times> carrier F, eq = (=), le = prod_le\<rparr>" 
    and a3:"x \<sqsubseteq>\<^bsub>\<lparr>carrier = carrier E \<times> carrier F, eq = (=), le = prod_le\<rparr>\<^esub> y"
  show "(\<pi>2 f) x \<sqsubseteq>\<^bsub>F\<^esub> (\<pi>2 f) y"
    unfolding fun_proj2_def fun_proj2_basic_def using a_mono a1 a2 a3 unfolding isotone_def prod_le_def by auto
qed

lemma (in prod_lattice_bin) mono_proj1:
  assumes a_car:"f \<in> carrier E \<times> carrier F \<rightarrow>\<^sub>E carrier E \<times> carrier F"
      and a_mono:"Mono\<^bsub>E_times_F\<^esub> f"
    shows "isotone E_times_F E \<pi>1 f"
  unfolding E_times_F_def
proof 
  show "weak_partial_order \<lparr>carrier = carrier E \<times> carrier F, eq = (=), le = prod_le\<rparr>"
    by (simp add: weak_partial_order_axioms)
  show "weak_partial_order E"
    by (simp add: E.weak_partial_order_axioms)
  fix x y assume a1:"x\<in> carrier \<lparr>carrier = carrier E \<times> carrier F, eq = (=), le = prod_le\<rparr>" 
    and a2:"y\<in> carrier \<lparr>carrier = carrier E \<times> carrier F, eq = (=), le = prod_le\<rparr>" 
    and a3:"x \<sqsubseteq>\<^bsub>\<lparr>carrier = carrier E \<times> carrier F, eq = (=), le = prod_le\<rparr>\<^esub> y"
  show "(\<pi>1 f) x \<sqsubseteq>\<^bsub>E\<^esub> (\<pi>1 f) y"
    unfolding fun_proj1_def fun_proj1_basic_def using a_mono a1 a2 a3 unfolding isotone_def prod_le_def by auto
qed

lemma (in prod_lattice_bin) mono_specialize1:
  assumes a_car:"f \<in> carrier E \<times> carrier F \<rightarrow>\<^sub>E carrier E"
    and a_iso: "isotone E_times_F E f"
    and a_b: "b\<in>carrier F"
  shows "Mono\<^bsub>E\<^esub> (\<lambda>x. f (x,b))"
  unfolding isotone_def
  apply (auto simp add:E.weak_partial_order_axioms)
proof -
  fix x y assume ax:"x\<in> carrier E" and ay:"y\<in>carrier E" and a_le:"x\<sqsubseteq> y"
  show "f (x, b) \<sqsubseteq> f (y, b)"
    using a_iso unfolding isotone_def apply simp
    using a_b a_le ax ay by auto
qed

lemma (in prod_lattice_bin) mono_specialize2:
  assumes a_car:"f \<in> carrier E \<times> carrier F \<rightarrow>\<^sub>E carrier F"
    and a_iso: "isotone E_times_F F f"
    and a_b: "a\<in>carrier E"
  shows "Mono\<^bsub>F\<^esub> (\<lambda>y. f (a,y))"
  unfolding isotone_def
  apply (auto simp add: F.weak_partial_order_axioms)
proof -
  fix x y assume ax:"x\<in> carrier F" and ay:"y\<in>carrier F" and a_le:"x\<sqsubseteq>\<^bsub>F\<^esub> y"
  show "f (a,x) \<sqsubseteq>\<^bsub>F\<^esub> f (a,y)"
    using a_iso unfolding isotone_def apply simp
    using a_b a_le ax ay by auto
qed

lemma (in prod_lattice_bin) pi_compat:
  "x\<in> carrier E\<times>carrier F \<Longrightarrow> fst (f x) = (\<pi>1 f) x \<and> snd (f x) = (\<pi>2 f) x"
  unfolding fun_proj1_def fun_proj2_def fun_proj1_basic_def fun_proj2_basic_def by auto

theorem (in prod_lattice_bin) Bekic_principle:
  fixes f ::"'a \<times> 'c \<Rightarrow> 'a \<times> 'c"
  assumes a_car:"f \<in> carrier E \<times> carrier F \<rightarrow>\<^sub>E carrier E \<times> carrier F"
      and a_mono:"Mono\<^bsub>E_times_F\<^esub> f"
    shows "LFP\<^bsub>E_times_F\<^esub> f = (LFP\<^bsub>E\<^esub> (\<lambda>x. (\<pi>1 f) (x, LFP\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) (x,y)))), 
                               LFP\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) ((LFP\<^bsub>E\<^esub> (\<lambda>x. (\<pi>1 f) (x,y)), y))))"
proof - 
  let ?f1 = "\<pi>1 f"
  let ?f2 = "\<pi>2 f"
  let ?a = "fst (LFP\<^bsub>E_times_F\<^esub> f)"
  let ?b = "snd (LFP\<^bsub>E_times_F\<^esub> f)"

  have b_lfp_car:"(LFP\<^bsub>E_times_F\<^esub> f) \<in> carrier E_times_F"
    using LFP_closed unfolding E_times_F_def by auto

  have b1:"(?a, ?b) = LFP\<^bsub>E_times_F\<^esub> f"
    by auto
  have b_a_car: "?a\<in>carrier E"
    using b_lfp_car by auto
  have b_b_car: "?b\<in>carrier F"
    using b_lfp_car by auto

  have b2:"f (LFP\<^bsub>E_times_F\<^esub> f) = LFP\<^bsub>E_times_F\<^esub> f"
    using a_car a_mono LFP_fixed_point unfolding E_times_F_def fps_def by auto
  then have eq_a:"?a = ?f1 (?a,?b)" 
    unfolding fun_proj1_def fun_proj1_basic_def using b1 b_lfp_car by auto
  have eq_b:"?b = ?f2 (?a, ?b)"
    unfolding fun_proj2_def fun_proj2_basic_def using b1 b2 b_lfp_car by auto

  have "Mono\<^bsub>F\<^esub> (\<lambda>y. ?f2 (?a,y))" 
    using mono_proj2[of "f"] mono_specialize2[of "\<pi>2 f" "?a"] b_a_car a_mono funcset_proj2[of "f"] a_car by auto
  then have b11:"LFP\<^bsub>F\<^esub> (\<lambda>y. ?f2 (?a,y)) \<sqsubseteq>\<^bsub>F\<^esub> ?b"
    using \<open>?b = ?f2 (?a, ?b)\<close> F.LFP_least_fixed_point[of "(\<lambda>y. (\<pi>2 f) (fst (LFP\<^bsub>E_times_F\<^esub> f), y))" "snd (LFP\<^bsub>E_times_F\<^esub> f)"]
    using F.LFP_lowerbound F.le_refl b_b_car by presburger

  have "Mono\<^bsub>E\<^esub> (\<lambda>x. ?f1 (x,?b))" 
    using mono_proj1[of "f"] mono_specialize1[of "\<pi>1 f" "?b"] b_b_car a_mono funcset_proj1[of "f"] a_car by auto
  then have b12:"LFP\<^bsub>E\<^esub> (\<lambda>x. ?f1 (x,?b)) \<sqsubseteq>\<^bsub>E\<^esub> ?a"
    using \<open>?a = ?f1 (?a, ?b)\<close> E.LFP_least_fixed_point[of "(\<lambda>x. (\<pi>1 f) (x, snd (LFP\<^bsub>E_times_F\<^esub> f)))" "fst (LFP\<^bsub>E_times_F\<^esub> f)"]
    using E.LFP_lowerbound E.le_refl b_a_car by presburger

  have "?f1 (?a,LFP\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) (?a,y))) \<sqsubseteq> ?a"
    using eq_a b11 mono_proj1[of "f"] a_mono a_car use_iso2[of "E_times_F" "E" "\<pi>1 f"] b_a_car b_b_car F.LFP_closed
    by (metis (lifting) E.le_refl SigmaI fst_conv prod_carrierE prod_le_equiv snd_conv)
  then have rhs_le_lhs_a:"LFP\<^bsub>E\<^esub> (\<lambda>x. (\<pi>1 f) (x, LFP\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) (x,y)))) \<sqsubseteq> ?a"
    using LEAST_FP_def[of "E" "\<lambda>x. (\<pi>1 f) (x, LFP\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) (x, y)))"] 
          E.inf_lower[of "{u \<in> carrier E. (\<pi>1 f) (u, LFP\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) (u, y))) \<sqsubseteq> u}" "?a"]
          b_a_car by auto

  have rhs_le_lhs_b:"?f2 (LFP\<^bsub>E\<^esub> (\<lambda>x. (\<pi>1 f) (x,?b)),?b) \<sqsubseteq>\<^bsub>F\<^esub> ?b"
    using eq_b b11 mono_proj2[of "f"] a_mono a_car use_iso2[of "E_times_F" "F" "\<pi>2 f"] b_a_car b_b_car E.LFP_closed
    by (metis (no_types, lifting) F.le_refl SigmaI b12 fst_eqD prod_carrierE prod_leI snd_conv)
  then have rhs_le_lhs_b:"LFP\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) ((LFP\<^bsub>E\<^esub> (\<lambda>x. (\<pi>1 f) (x,y)), y))) \<sqsubseteq>\<^bsub>F\<^esub> ?b"
    using LEAST_FP_def[of "F" "\<lambda>y. (\<pi>2 f) ((LFP\<^bsub>E\<^esub> (\<lambda>x. (\<pi>1 f) (x,y)), y))"]
          F.inf_lower[of "{u \<in> carrier F. (\<pi>2 f) (LFP (\<lambda>x. (\<pi>1 f) (x, u)), u) \<sqsubseteq>\<^bsub>F\<^esub> u}"]
          b_b_car by auto
    
  let ?a' = "LFP (\<lambda>x. (\<pi>1 f) (x, LFP\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) (x, y))))"
  let ?b' = "LFP\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) (LFP (\<lambda>x. (\<pi>1 f) (x, y)), y))"
  let ?a'' = "LFP (\<lambda>x. (\<pi>1 f) (x, ?b'))"
  let ?b'' = "LFP\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) (?a', y))"

  have c1:"(\<pi>1 f) (?a', ?b'') = ?a'"
  proof -
    have pre1:"Mono (\<lambda>x. (\<pi>1 f) (x, LFP\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) (x, y))))"
      using E.weak_partial_order_axioms
    proof 
      show "weak_partial_order E" using E.weak_partial_order_axioms by simp
      fix x y assume a1:"x\<in>carrier E" and a2:"y\<in>carrier E" and a3:"x\<sqsubseteq> y" 
      show "(\<pi>1 f) (x, LFP\<^bsub>F\<^esub> (\<lambda>z. (\<pi>2 f) (x, z))) \<sqsubseteq> (\<pi>1 f) (y, LFP\<^bsub>F\<^esub> (\<lambda>z. (\<pi>2 f) (y, z)))"
        apply (rule use_iso2[of "E_times_F" "E" "\<pi>1 f" "(x, LFP\<^bsub>F\<^esub> (\<lambda>z. (\<pi>2 f) (x, z)))" "(y, LFP\<^bsub>F\<^esub> (\<lambda>z. (\<pi>2 f) (y, z)))"])
        using mono_proj1[of "f"] a_mono a_car apply simp
        using a1 F.LFP_closed apply simp
        using a2 F.LFP_closed apply simp
        apply (rule prod_leI)
        using a3 apply auto
      proof - 
        have b0:"\<And>z. z\<in>carrier F \<Longrightarrow> (\<pi>2 f) (x, z) \<sqsubseteq>\<^bsub>F\<^esub> (\<pi>2 f) (y, z)"
          using mono_proj2[of "f"] a_mono a_car use_iso2[of "E_times_F" "F" "\<pi>2 f"] a3 a1 a2 by auto
        have b1:"(\<lambda>z. (\<pi>2 f) (x, z)) \<in> carrier F \<rightarrow> carrier F"
          using funcset_proj2[of "f"] a_car a1 by auto
        have b2:"(\<lambda>z. (\<pi>2 f) (y, z)) \<in> carrier F \<rightarrow> carrier F"
          using funcset_proj2[of "f"] a_car a2 by auto
        show "LFP\<^bsub>F\<^esub> (\<lambda>z. (\<pi>2 f) (x, z)) \<sqsubseteq>\<^bsub>F\<^esub> LFP\<^bsub>F\<^esub> (\<lambda>z. (\<pi>2 f) (y, z))"
          using F.LFP_compare[of "(\<lambda>z. (\<pi>2 f) (x, z))" "(\<lambda>z. (\<pi>2 f) (y, z))"] b0 b1 b2 by auto
      qed
    qed
    have pre2:"(\<lambda>x. (\<pi>1 f) (x, LFP\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) (x, y)))) \<in> carrier E \<rightarrow> carrier E"
      using funcset_proj1 a_car by blast
    show ?thesis
      using E.LFP_fixed_point[of "\<lambda>x. (\<pi>1 f) (x, LFP\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) (x, y)))"] pre1 pre2 E.LFP_closed E.eq_is_equal
      unfolding fps_def by auto
  qed

  have c2:"?b' = (\<pi>2 f) (?a'', ?b')"
  proof (rule F.LFP_unfold[of "(\<lambda>y. (\<pi>2 f) (LFP (\<lambda>x. (\<pi>1 f) (x, y)), y))"])
    show "Mono\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) (LFP (\<lambda>x. (\<pi>1 f) (x, y)), y))"
      using F.weak_partial_order_axioms
    proof show "weak_partial_order F" using F.weak_partial_order_axioms by simp
      fix x y assume a1:"x \<in> carrier F" and a2:"y \<in> carrier F" and a3:"x \<sqsubseteq>\<^bsub>F\<^esub> y"
      show "(\<pi>2 f) (LFP (\<lambda>xa. (\<pi>1 f) (xa, x)), x) \<sqsubseteq>\<^bsub>F\<^esub> (\<pi>2 f) (LFP (\<lambda>x. (\<pi>1 f) (x, y)), y)"
      proof -
        have "LFP (\<lambda>xa. (\<pi>1 f) (xa, x)) \<sqsubseteq> LFP (\<lambda>x. (\<pi>1 f) (x, y))"
          apply (rule E.LFP_compare[of "\<lambda>z. (\<pi>1 f) (z,x)" "\<lambda>z. (\<pi>1 f) (z,y)"])
          using funcset_proj1 a_car mono_proj1[of "f"]
                use_iso2[of "E_times_F" "E" "\<pi>1 f"] a1 a2 a3 a_mono by auto
        then show ?thesis
          using mono_proj2[of "f"] a_car use_iso2[of "E_times_F" "F" "\<pi>2 f"] a1 a2 a3 E.LFP_closed a_mono by auto
      qed
    qed
    show "(\<lambda>y. (\<pi>2 f) (LFP (\<lambda>x. (\<pi>1 f) (x, y)), y)) \<in> carrier F \<rightarrow> carrier F"
      using E.LFP_closed funcset_proj2 a_car by blast
  qed

  have c3:"?b'' = (\<pi>2 f) (?a', ?b'')"
  proof (rule F.LFP_unfold)
    show "Mono\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) (LFP (\<lambda>x. (\<pi>1 f) (x, LFP\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) (x, y)))), y))"
      using F.weak_partial_order_axioms
    proof show "weak_partial_order F" using F.weak_partial_order_axioms by simp
      fix x y assume a1:"x \<in> carrier F" and a2:"y \<in> carrier F" and a3:"x \<sqsubseteq>\<^bsub>F\<^esub> y"
      show "(\<pi>2 f) (LFP (\<lambda>x. (\<pi>1 f) (x, LFP\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) (x, y)))), x) \<sqsubseteq>\<^bsub>F\<^esub> (\<pi>2 f) (LFP (\<lambda>x. (\<pi>1 f) (x, LFP\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) (x, y)))), y)"
        apply (rule use_iso2[of "E_times_F" "F" "\<pi>2 f"])
        using mono_proj2[of "f"] a_car a_mono apply simp
        using E.LFP_closed a1 a2 a3 by auto
    qed
    show "(\<lambda>y. (\<pi>2 f) (LFP (\<lambda>x. (\<pi>1 f) (x, LFP\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) (x, y)))), y)) \<in> carrier F \<rightarrow> carrier F"
      using E.LFP_closed funcset_proj2 a_car by blast
  qed
  have c4:"?a'' = (\<pi>1 f) (?a'', ?b')"
  proof (rule E.LFP_unfold)
    show "Mono (\<lambda>x. (\<pi>1 f) (x, LFP\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) (LFP (\<lambda>x. (\<pi>1 f) (x, y)), y))))"
      using E.weak_partial_order_axioms
    proof show "weak_partial_order E" using E.weak_partial_order_axioms by simp
      fix x y assume a1:"x \<in> carrier E" and a2:"y \<in> carrier E" and a3:"x \<sqsubseteq>\<^bsub>E\<^esub> y"
      show "(\<pi>1 f) (x, LFP\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) (LFP (\<lambda>x. (\<pi>1 f) (x, y)), y))) \<sqsubseteq> (\<pi>1 f) (y, LFP\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) (LFP (\<lambda>x. (\<pi>1 f) (x, y)), y)))"
        apply (rule use_iso2[of "E_times_F" "E" "\<pi>1 f"])
        using mono_proj1[of "f"] a_car a_mono apply simp
        using E.LFP_closed a1 a2 a3 by auto
    qed
    show "(\<lambda>x. (\<pi>1 f) (x, LFP\<^bsub>F\<^esub> (\<lambda>y. (\<pi>2 f) (LFP (\<lambda>x. (\<pi>1 f) (x, y)), y)))) \<in> carrier E \<rightarrow> carrier E"
      using F.LFP_closed funcset_proj1 a_car by blast
  qed
  from c1 c3 have "f (?a',?b'') = (?a',?b'')"
    using pi_compat[of "(?a',?b'')" "f"] E.LFP_closed F.LFP_closed by (metis (no_types, lifting) ext mem_Sigma_iff split_pairs)
  then have lhs_le_rhs_a:"?a \<sqsubseteq> ?a'"
    using LFP_least_fixed_point[of "f" "(?a',?b'')"] a_mono a_car
  by (metis (lifting) E.LFP_closed E_times_F_def F.LFP_closed LFP_lowerbound fst_conv local.le_refl mem_Sigma_iff prod_carrierE prod_lattice_bin.prod_le_equiv prod_lattice_bin_axioms)
  from c2 c4 have "f (?a'',?b') = (?a'', ?b')"
    using pi_compat[of "(?a'',?b')" "f"] E.LFP_closed F.LFP_closed by (metis (no_types, lifting) ext mem_Sigma_iff split_pairs)
  then have lhs_le_rhs_b:"?b \<sqsubseteq>\<^bsub>F\<^esub> ?b'"
    using LFP_least_fixed_point[of "f" "(?a'',?b')"] a_mono a_car
  by (metis (lifting) E.LFP_closed E_times_F_def F.LFP_closed LFP_lowerbound local.le_refl mem_Sigma_iff prod_carrierE prod_lattice_bin.prod_le_equiv prod_lattice_bin_axioms snd_conv)

  show ?thesis
    using rhs_le_lhs_a rhs_le_lhs_b lhs_le_rhs_a lhs_le_rhs_b
    by (simp add: E.le_antisym F.le_antisym b_a_car b_b_car split_pairs2)
qed

section \<open>general Cartesian product of lattices\<close>

(*Given a list of lattices Ls, returns the k-th carrier*)
definition get_carrier:: "'a gorder list \<Rightarrow> nat \<Rightarrow> 'a set" where
  "get_carrier Ls k = carrier (Ls ! (k-1))"

(*Given a list of lattices Ls, returns the union of their carriers*)
definition lattice_union:: "'a gorder list \<Rightarrow> 'a set" where
  "lattice_union Ls = \<Union>{get_carrier Ls k| k. k\<in>{1..length Ls}}"

(*Given a list of lattices Ls, returns the funcset containing all tuples in their cartesian product*)
definition car_prod_carrier:: "'a gorder list \<Rightarrow> (nat \<Rightarrow> 'a) set" where
  "car_prod_carrier Ls = {f\<in>{1..length Ls} \<rightarrow>\<^sub>E lattice_union Ls. \<forall>i\<in>{1..length Ls}. f i \<in> get_carrier Ls i}"

lemma car_prod_carrierI[intro]: "
  (\<And>i. i\<in>{1..length Ls} \<Longrightarrow> x i \<in> carrier (Ls ! (i-1))) 
  \<Longrightarrow> (\<And>i. i\<notin>{1..length Ls} \<Longrightarrow> x i = undefined)
  \<Longrightarrow> x\<in> car_prod_carrier Ls"
  unfolding car_prod_carrier_def lattice_union_def get_carrier_def by fastforce

(*Given two functions, returns the less-than relation for tuples from this list*)
definition tuple_le:: "'a gorder list \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool" (\<open>\<lhd>\<^bsub>_\<^esub> _ _\<close> 10) where
  "tuple_le Ls f g \<equiv> \<forall>i\<in>{1..length Ls}. le (Ls ! (i-1)) (f i) (g i)"

(*Given a list of lattices Ls, returns a structure for their catesian product*)
definition cart_prod:: "'a gorder list \<Rightarrow> _" (\<open>\<Otimes>_\<close>) where
  "cart_prod Ls = \<lparr> carrier = car_prod_carrier Ls ,eq=(=), le=tuple_le Ls \<rparr>"

lemma le_cart_prod: "le (\<Otimes>Ls) = tuple_le Ls"
  unfolding cart_prod_def by simp

definition invert_tuple_le:: "'a gorder list \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool" (\<open>\<^bsub>_\<^esub> _ _\<close> 10) where
  "invert_tuple_le Ls f g \<equiv> \<forall>i\<in>{1..length Ls}. le (inv_gorder (Ls ! (i-1))) (f i) (g i)"

definition invert_Ls:: "'a gorder list \<Rightarrow> 'a gorder list" where
  "invert_Ls Ls = map (inv_gorder) Ls"

lemma invert_Ls_length[simp]: "length (invert_Ls Ls) = length Ls"
  unfolding invert_Ls_def by auto

lemma kth_carrier: "x\<in> carrier (\<Otimes>Ls) \<Longrightarrow> i\<in>{1..length Ls} \<Longrightarrow> x i \<in> carrier (Ls ! (i-1))"
  unfolding cart_prod_def car_prod_carrier_def get_carrier_def
  by auto

lemma carrier_simps[simp]: "carrier (\<Otimes>Ls) = car_prod_carrier Ls"
  unfolding cart_prod_def by auto

lemma carrier_invert_Ls_member: 
  assumes "i\<in>{1..length Ls}"
  shows "carrier (invert_Ls Ls ! (i-1)) = carrier (Ls ! (i-1))"
  using assms unfolding invert_Ls_def by auto

lemma carrier_invert_Ls: "carrier (\<Otimes>(invert_Ls Ls)) = carrier (\<Otimes>Ls)"
  apply simp
  unfolding car_prod_carrier_def get_carrier_def invert_Ls_def
proof -
  have b1:"\<And>i. i\<in>{1..length (map inv_gorder Ls)} \<Longrightarrow> carrier (map inv_gorder Ls ! (i - 1)) = carrier (Ls ! (i-1))"
    by auto
  hence "lattice_union (map inv_gorder Ls) = lattice_union Ls"
    unfolding lattice_union_def get_carrier_def by auto
  thus "{f \<in> {1..length (map inv_gorder Ls)} \<rightarrow>\<^sub>E lattice_union (map inv_gorder Ls). \<forall>i\<in>{1..length (map inv_gorder Ls)}. f i \<in> carrier (map inv_gorder Ls ! (i - 1))} =
    {f \<in> {1..length Ls} \<rightarrow>\<^sub>E lattice_union Ls. \<forall>i\<in>{1..length Ls}. f i \<in> carrier (Ls ! (i - 1))}"
    using b1 by auto
qed

lemma eq_Ls [simp]: "eq (\<Otimes>Ls) = (=)"
  unfolding cart_prod_def by auto

lemma eq_invert_Ls: "eq (\<Otimes>(invert_Ls Ls)) = eq (\<Otimes>Ls)"
  by auto

lemma invert_tuple_le_simp: "tuple_le (invert_Ls Ls) f g = (\<forall>i\<in>{1..length Ls}. le (inv_gorder (Ls ! (i-1))) (f i) (g i))"
  unfolding tuple_le_def invert_Ls_def by force

lemma le_invert_Ls: "le (\<Otimes>(invert_Ls Ls)) = invert_tuple_le Ls"
  unfolding cart_prod_def invert_Ls_def invert_tuple_le_def
  using invert_tuple_le_simp unfolding invert_Ls_def by fastforce

lemma cart_carrier_criterion[intro]: "
  (\<And>i. i\<in>{1..length Ls} \<Longrightarrow> x i \<in> carrier (Ls ! (i-1))) 
  \<Longrightarrow> (\<And>i. i\<notin>{1..length Ls} \<Longrightarrow> x i = undefined)
  \<Longrightarrow> x\<in> carrier (\<Otimes>Ls)"
  using car_prod_carrierI carrier_simps by auto

lemma cart_carrier_iff: 
  "(x\<in> carrier (\<Otimes>Ls)) = ((\<forall>i\<in>{1..length Ls}. x i \<in> carrier (Ls ! (i-1))) \<and> (\<forall>i. i\<notin>{1..length Ls} \<longrightarrow> x i = undefined))"
proof 
  assume \<open>x\<in>carrier (\<Otimes>Ls)\<close>
  then show "(\<forall>i\<in>{1..length Ls}. x i \<in> carrier (Ls ! (i-1))) \<and> (\<forall>i. i \<notin> {1..length Ls} \<longrightarrow> x i = undefined)"
    unfolding carrier_simps car_prod_carrier_def get_carrier_def by blast
next
  assume "(\<forall>i\<in>{1..length Ls}. x i \<in> carrier (Ls ! (i-1))) \<and> (\<forall>i. i \<notin> {1..length Ls} \<longrightarrow> x i = undefined)"
  then show "x\<in> carrier (\<Otimes>Ls)"
    using cart_carrier_criterion by auto
qed

lemma complete_lattice_po: "complete_lattice L \<Longrightarrow> partial_order L"
  by (simp add: complete_lattice_def partial_order.axioms(1))

lemma complete_lattice_weak: "complete_lattice L \<Longrightarrow> weak_complete_lattice L"
  by (simp add: complete_lattice.inf_exists complete_lattice.sup_exists complete_lattice_po partial_order.axioms(1) weak_complete_lattice_axioms.intro
      weak_complete_lattice_def)

lemma complete_lattice_le_refl: "complete_lattice L \<Longrightarrow> (\<And>x. x\<in>carrier L \<Longrightarrow> x \<sqsubseteq>\<^bsub>L\<^esub> x)"
  by (simp add: complete_lattice_def partial_order.axioms(1) weak_partial_order.le_refl)

lemma complete_lattice_le_antisym: "complete_lattice L \<Longrightarrow> (\<And>x y. x\<in>carrier L \<Longrightarrow> y\<in>carrier L \<Longrightarrow> x \<sqsubseteq>\<^bsub>L\<^esub> y \<Longrightarrow> y\<sqsubseteq>\<^bsub>L\<^esub> x \<Longrightarrow> x = y)"
  by (meson complete_lattice_po partial_order.le_antisym)

lemma complete_lattice_le_trans: "complete_lattice L \<Longrightarrow> (\<And>x y z. x\<in>carrier L \<Longrightarrow> y\<in>carrier L \<Longrightarrow> z\<in>carrier L \<Longrightarrow> x \<sqsubseteq>\<^bsub>L\<^esub> y \<Longrightarrow> y\<sqsubseteq>\<^bsub>L\<^esub> z \<Longrightarrow> x \<sqsubseteq>\<^bsub>L\<^esub> z)"
  by (meson complete_lattice_po partial_order_def weak_partial_order.le_trans)

lemma (in partial_order) supremumI:
  "A \<subseteq>carrier L \<Longrightarrow> y\<in>carrier L \<Longrightarrow> (\<And>x. x\<in>A \<Longrightarrow> x\<sqsubseteq>y) \<Longrightarrow> (\<And>z. z\<in>carrier L \<Longrightarrow> (\<And>x. x\<in>A \<Longrightarrow> x\<sqsubseteq>z) \<Longrightarrow> y\<sqsubseteq>z) \<Longrightarrow> is_lub L y A"
  unfolding least_def Upper_def
  by (simp add: inf.absorb_iff1)

lemma (in partial_order) infimumI:
  "A \<subseteq>carrier L \<Longrightarrow> y\<in>carrier L \<Longrightarrow> (\<And>x. x\<in>A \<Longrightarrow> y\<sqsubseteq>x) \<Longrightarrow> (\<And>z. z\<in>carrier L \<Longrightarrow> (\<And>x. x\<in>A \<Longrightarrow> z\<sqsubseteq>x) \<Longrightarrow> z\<sqsubseteq>y) \<Longrightarrow> is_glb L y A"
  unfolding greatest_def Lower_def
  by (simp add: inf.absorb_iff1)

lemma car_prod_le_form[simp]: "x \<sqsubseteq>\<^bsub>\<Otimes>Ls\<^esub> y = (\<lhd>\<^bsub>Ls\<^esub> x y)"
  unfolding cart_prod_def tuple_le_def by auto

lemma car_prod_carrier_form[simp]: "carrier (\<Otimes>Ls) = car_prod_carrier Ls"
  unfolding cart_prod_def by auto

(*The background locale for general cartesian products.
  Parameters:
    Ls    a list of ordered sets
  Assumptions:
    1. Ls is nonempty
    2. each member of Ls is a complete lattice
*)
locale cart_prod_lattice = 
  fixes Ls::"'a gorder list"
  assumes Ls_len_pos: "length Ls > 0"
      and Ls_comp_lat: "\<And>i. i\<in>{1..length Ls} \<Longrightarrow> complete_lattice (Ls ! (i-1))"
begin

lemma tuple_le_refl: "\<And>x. x \<in> car_prod_carrier Ls \<Longrightarrow> \<lhd>\<^bsub>Ls\<^esub> x x"
  unfolding tuple_le_def
proof -
  fix x assume ass:"x\<in>car_prod_carrier Ls"
  have "\<And>i. i\<in>{1..length Ls} \<Longrightarrow> x i \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> x i"
  proof - fix i assume a1:"i\<in>{1..length Ls}"
    have b1:"complete_lattice (Ls ! (i-1))"
      using Ls_comp_lat a1 by auto
    have "x i \<in> carrier (Ls ! (i-1))"
      using ass a1 unfolding car_prod_carrier_def get_carrier_def by auto
    then show "x i \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> x i"
      using b1 complete_lattice_le_refl by metis
  qed
  then show "\<forall>i\<in>{1..length Ls}. x i \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> x i"
    by auto
qed

lemma tuple_le_antisym: "\<And>x y. \<lhd>\<^bsub>Ls\<^esub> x y \<Longrightarrow> \<lhd>\<^bsub>Ls\<^esub> y x \<Longrightarrow> x \<in> car_prod_carrier Ls \<Longrightarrow> y \<in> car_prod_carrier Ls \<Longrightarrow> x = y"
  unfolding tuple_le_def
proof - 
  fix x y assume a1:"\<forall>i\<in>{1..length Ls}. x i \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> y i"
  and a2:"\<forall>i\<in>{1..length Ls}. y i \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> x i"
  and ax:"x \<in> car_prod_carrier Ls"
  and ay:"y \<in> car_prod_carrier Ls"
  show "x=y"
  proof (rule vec_eqI[where n="length Ls" and A="lattice_union Ls"])
    show "x \<in> {1..length Ls} \<rightarrow>\<^sub>E lattice_union Ls"
      using ax unfolding car_prod_carrier_def by auto
    show "y \<in> {1..length Ls} \<rightarrow>\<^sub>E lattice_union Ls"
      using ay unfolding car_prod_carrier_def by auto
    show "\<And>i. i \<in> {1..length Ls} \<Longrightarrow> x i = y i"
    proof -
      fix i assume a_i:"i\<in>{1..length Ls}"
      have b1:"complete_lattice (Ls ! (i-1))"
        using Ls_comp_lat a_i by auto
      have bx':"x i \<in> carrier (Ls ! (i-1))"
        using kth_carrier ax a_i by auto
      have by': "y i \<in> carrier (Ls ! (i-1))"
        using kth_carrier ay a_i by auto
      show "x i = y i"
        using a1 a2 a_i b1 bx' by' complete_lattice_le_antisym by metis
    qed
  qed
qed

lemma tuple_le_trans:
  "\<And>x y z. \<lhd>\<^bsub>Ls\<^esub> x y \<Longrightarrow> \<lhd>\<^bsub>Ls\<^esub> y z \<Longrightarrow> x \<in> car_prod_carrier Ls \<Longrightarrow> y \<in> car_prod_carrier Ls \<Longrightarrow> z \<in> car_prod_carrier Ls \<Longrightarrow> \<lhd>\<^bsub>Ls\<^esub> x z"
  unfolding tuple_le_def 
proof -
  fix x y z 
  assume a_xy:"\<forall>i\<in>{1..length Ls}. x i \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> y i"
     and a_yz:"\<forall>i\<in>{1..length Ls}. y i \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> z i"
     and in_x:"x \<in> car_prod_carrier Ls"
     and in_y:"y \<in> car_prod_carrier Ls"
     and in_z:"z \<in> car_prod_carrier Ls"
  have "\<And>i. i\<in>{1..length Ls} \<Longrightarrow> x i \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> z i"
  proof -
    fix i assume a_i:"i\<in>{1..length Ls}"
    have comp_lat_i:"complete_lattice (Ls ! (i-1))"
      using Ls_comp_lat a_i by auto
    have b_x: "x i \<in>carrier (Ls ! (i-1))"
      using in_x kth_carrier a_i by auto
    have b_y: "y i\<in>carrier (Ls ! (i-1))"
      using in_y kth_carrier a_i by auto
    have b_z: "z i\<in>carrier (Ls ! (i-1))"
      using in_z kth_carrier a_i by auto
    show "x i \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> z i"
      using b_x b_y b_z a_xy a_yz comp_lat_i complete_lattice_le_trans[of "(Ls ! (i-1))""x i" "y i" "z i"] a_i by auto
  qed
  then show "\<forall>i\<in>{1..length Ls}. x i \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> z i"
    by auto
qed

subsection \<open>vectorial least upper bound\<close>

(* Given a set of tuples, return Sup of the set. Ls is used as information.*)
definition tuple_lub:: "(nat \<Rightarrow> 'a) set \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "tuple_lub A = (\<lambda>i\<in>{1..length Ls}. \<Squnion>\<^bsub>(Ls ! (i-1))\<^esub>{v i|v. v\<in>A})"

(* Arguments about the well-definedness of tuple lub*)
lemma tuple_lub_form: "A\<subseteq>car_prod_carrier Ls \<Longrightarrow> i\<in>{1..length Ls} \<Longrightarrow> tuple_lub A i = \<Squnion>\<^bsub>(Ls ! (i-1))\<^esub>{v i |v. v \<in> A}"
  unfolding tuple_lub_def by auto

lemma tuple_lub_extension: "i\<notin>{1..length Ls} \<Longrightarrow> tuple_lub A i = undefined"
  unfolding tuple_lub_def by auto

lemma tuple_lub_carrier: "A\<subseteq>car_prod_carrier Ls \<Longrightarrow> i\<in>{1..length Ls} \<Longrightarrow> tuple_lub A i \<in> carrier (Ls ! (i-1))"
  unfolding tuple_lub_def
proof -
  assume a_i: "i\<in>{1..length Ls}" and a_A:"A \<subseteq> car_prod_carrier Ls"
  have "{v i |v. v \<in> A} \<subseteq> carrier (Ls ! (i-1))"
    using a_i kth_carrier a_A car_prod_carrier_form by blast
  then have "\<Squnion>\<^bsub>(Ls ! (i-1))\<^esub>{v i|v. v\<in>A} \<in> carrier (Ls ! (i-1))"
    using weak_complete_lattice.sup_closed[of "(Ls ! (i-1))" "{v i |v. v \<in> A}"] Ls_comp_lat[of "i"] a_i complete_lattice_weak by auto
  then show "(\<lambda>i\<in>{1..length Ls}. \<Squnion>\<^bsub>(Ls ! (i-1))\<^esub>{v i |v. v \<in> A}) i \<in> carrier (Ls ! (i-1))"
    using a_i by auto
qed

lemma tuple_lub_closed:"A\<subseteq>car_prod_carrier Ls \<Longrightarrow> tuple_lub A \<in>car_prod_carrier Ls"
proof -
  assume ass:"A\<subseteq>car_prod_carrier Ls"
  show "tuple_lub A \<in>car_prod_carrier Ls"
  proof (rule car_prod_carrierI)
    show "\<And>i. i \<notin> {1..length Ls} \<Longrightarrow> tuple_lub A i = undefined"
      using tuple_lub_extension by auto
  next
    show "\<And>i. i \<in> {1..length Ls} \<Longrightarrow> tuple_lub A i \<in> carrier (Ls ! (i-1))"
      using tuple_lub_carrier ass by auto
  qed
qed

lemma tuple_lub_ub:"A\<subseteq> car_prod_carrier Ls \<Longrightarrow> x\<in>A \<Longrightarrow> \<lhd>\<^bsub>Ls\<^esub> x (tuple_lub A)"
proof -
  assume ass:"A\<subseteq>car_prod_carrier Ls" and a_x:"x\<in>A"
  show "\<lhd>\<^bsub>Ls\<^esub> x (tuple_lub A)"
    unfolding tuple_le_def
  proof 
    fix i
    assume a_i:"i\<in>{1..length Ls}"
    have b1:"{v i |v. v \<in> A} \<subseteq> carrier (Ls ! (i-1))"
      using ass a_i kth_carrier car_prod_carrier_form by blast
    have "x i\<in>{v i |v. v \<in> A}"
      using kth_carrier a_i ass a_x by blast
    then have "x i \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> \<Squnion>\<^bsub>(Ls ! (i-1))\<^esub>{v i |v. v \<in> A}"
      using b1
      by (meson a_i cart_prod_lattice.Ls_comp_lat cart_prod_lattice_axioms complete_lattice_weak weak_complete_lattice.sup_upper)
    then show "x i \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> tuple_lub A i"
      using tuple_lub_form ass a_i by auto
  qed
qed

lemma tuple_lub_least:"A\<subseteq> car_prod_carrier Ls \<Longrightarrow> (\<And>y. y\<in>car_prod_carrier Ls \<Longrightarrow> (\<And>x. x\<in>A \<Longrightarrow> \<lhd>\<^bsub>Ls\<^esub> x y) \<Longrightarrow> \<lhd>\<^bsub>Ls\<^esub> (tuple_lub A) y)"
  unfolding tuple_le_def
proof 
  fix y i
  assume a1:"A\<subseteq> car_prod_carrier Ls" and a2:"y \<in> car_prod_carrier Ls" and a3:"\<And>x. x \<in> A \<Longrightarrow> \<forall>i\<in>{1..length Ls}. x i \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> y i"
  and a_i:"i \<in> {1..length Ls}"
  have "\<Squnion>\<^bsub>(Ls ! (i-1))\<^esub>{v i |v. v \<in> A} \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> y i"
  proof -
    interpret ith_comp_lat: complete_lattice "(Ls ! (i-1))"
      using Ls_comp_lat a_i by auto
    have lhs_car:"{v i |v. v \<in> A} \<subseteq> carrier (Ls ! (i-1))"
      using a1 a_i kth_carrier car_prod_carrier_form by blast
    have rhs_car:"y i \<in> carrier (Ls ! (i-1))"
      using a_i a2 kth_carrier car_prod_carrier_form by blast
    have "\<And>v. v\<in>A \<Longrightarrow> v i \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> y i"
      using a3 a_i by auto
    then show ?thesis 
      using lhs_car rhs_car ith_comp_lat.weak.sup_least[of "{v i |v. v \<in> A}" "y i"] by blast
  qed
  then show "tuple_lub A i \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> y i"
    using tuple_lub_form a_i a1 by auto
qed

subsection \<open>vectorial greatest lower bound\<close>

(* Given a set of tuples, return Inf of the set. Ls is used as information.*)
definition tuple_glb:: "(nat \<Rightarrow> 'a) set \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "tuple_glb A = (\<lambda>i\<in>{1..length Ls}. \<Sqinter>\<^bsub>(Ls ! (i-1))\<^esub>{v i|v. v\<in>A})"

(* Arguments about the well-definedness of tuple glb*)
lemma tuple_glb_form: "A\<subseteq>car_prod_carrier Ls \<Longrightarrow> i\<in>{1..length Ls} \<Longrightarrow> tuple_glb A i = \<Sqinter>\<^bsub>(Ls ! (i-1))\<^esub>{v i |v. v \<in> A}"
  unfolding tuple_glb_def by auto

lemma tuple_glb_extension: "i\<notin>{1..length Ls} \<Longrightarrow> tuple_glb A i = undefined"
  unfolding tuple_glb_def by auto

lemma tuple_glb_carrier: "A\<subseteq>car_prod_carrier Ls \<Longrightarrow> i\<in>{1..length Ls} \<Longrightarrow> tuple_glb A i \<in> carrier (Ls ! (i-1))"
  unfolding tuple_glb_def
proof -
  assume a_i: "i\<in>{1..length Ls}" and a_A:"A \<subseteq> car_prod_carrier Ls"
  have "{v i |v. v \<in> A} \<subseteq> carrier (Ls ! (i-1))"
    using a_i kth_carrier a_A car_prod_carrier_form by blast
  then have "\<Sqinter>\<^bsub>(Ls ! (i-1))\<^esub>{v i|v. v\<in>A} \<in> carrier (Ls ! (i-1))"
    using weak_complete_lattice.inf_closed[of "(Ls ! (i-1))" "{v i |v. v \<in> A}"] Ls_comp_lat[of "i"] a_i complete_lattice_weak by auto
  then show "(\<lambda>i\<in>{1..length Ls}. \<Sqinter>\<^bsub>(Ls ! (i-1))\<^esub>{v i |v. v \<in> A}) i \<in> carrier (Ls ! (i-1))"
    using a_i by auto
qed

lemma tuple_glb_closed:"A\<subseteq>car_prod_carrier Ls \<Longrightarrow> tuple_glb A \<in>car_prod_carrier Ls"
proof -
  assume ass:"A\<subseteq>car_prod_carrier Ls"
  show "tuple_glb A \<in>car_prod_carrier Ls"
  proof (rule car_prod_carrierI)
    show "\<And>i. i \<notin> {1..length Ls} \<Longrightarrow> tuple_glb A i = undefined"
      using tuple_glb_extension by auto
  next
    show "\<And>i. i \<in> {1..length Ls} \<Longrightarrow> tuple_glb A i \<in> carrier (Ls ! (i-1))"
      using tuple_glb_carrier ass by auto
  qed
qed

lemma tuple_glb_lb:"A\<subseteq> car_prod_carrier Ls \<Longrightarrow> x\<in>A \<Longrightarrow> \<lhd>\<^bsub>Ls\<^esub> (tuple_glb A) x"
proof -
  assume ass:"A\<subseteq>car_prod_carrier Ls" and a_x:"x\<in>A"
  show "\<lhd>\<^bsub>Ls\<^esub> (tuple_glb A) x"
    unfolding tuple_le_def
  proof 
    fix i
    assume a_i:"i\<in>{1..length Ls}"
    have b1:"{v i |v. v \<in> A} \<subseteq> carrier (Ls ! (i-1))"
      using ass a_i kth_carrier car_prod_carrier_form by blast
    have "x i\<in>{v i |v. v \<in> A}"
      using kth_carrier a_i ass a_x by blast
    then have "\<Sqinter>\<^bsub>(Ls ! (i-1))\<^esub>{v i |v. v \<in> A} \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> x i"
      using b1
      by (meson Ls_comp_lat a_i complete_lattice_weak weak_complete_lattice.inf_lower)
    then show "tuple_glb A i \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> x i "
      using tuple_glb_form ass a_i by auto
  qed
qed

lemma tuple_glb_greatest:"A\<subseteq> car_prod_carrier Ls \<Longrightarrow> (\<And>y. y\<in>car_prod_carrier Ls \<Longrightarrow> (\<And>x. x\<in>A \<Longrightarrow> \<lhd>\<^bsub>Ls\<^esub> y x) \<Longrightarrow> \<lhd>\<^bsub>Ls\<^esub> y (tuple_glb A))"
  unfolding tuple_le_def
proof 
  fix y i
  assume a1:"A\<subseteq> car_prod_carrier Ls" and a2:"y \<in> car_prod_carrier Ls" and a3:"\<And>x. x \<in> A \<Longrightarrow> \<forall>i\<in>{1..length Ls}. y i \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> x i"
  and a_i:"i \<in> {1..length Ls}"
  have "y i \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> \<Sqinter>\<^bsub>(Ls ! (i-1))\<^esub>{v i |v. v \<in> A}"
  proof -
    interpret ith_comp_lat: complete_lattice "(Ls ! (i-1))"
      using Ls_comp_lat a_i by auto
    have lhs_car:"{v i |v. v \<in> A} \<subseteq> carrier (Ls ! (i-1))"
      using a1 a_i kth_carrier car_prod_carrier_form by blast
    have rhs_car:"y i \<in> carrier (Ls ! (i-1))"
      using a_i a2 kth_carrier car_prod_carrier_form by blast
    have "\<And>v. v\<in>A \<Longrightarrow> y i \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> v i"
      using a3 a_i by auto
    then show ?thesis 
      using lhs_car rhs_car ith_comp_lat.weak.inf_greatest[of "{v i |v. v \<in> A}" "y i"] by blast
  qed
  then show "y i \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> tuple_glb A i"
    using tuple_glb_form a_i a1 by auto
qed

end

lemma le_inv_cart_prod: "le (inv_gorder (\<Otimes>Ls)) = invert_tuple_le Ls"
proof (rule ext)+
  fix f g
  have "le (inv_gorder (\<Otimes>Ls)) f g = le (\<Otimes>Ls) g f"
    by auto
  also have "... = (\<forall>i\<in>{1..length Ls}. g i \<sqsubseteq>\<^bsub>Ls ! (i - 1)\<^esub> f i)"
    unfolding cart_prod_def tuple_le_def by auto
  also have "... = (\<forall>i\<in>{1..length Ls}. f i \<sqsubseteq>\<^bsub>inv_gorder (Ls ! (i - 1))\<^esub> g i)"
    by auto
  also have "... = invert_tuple_le Ls f g"
    unfolding invert_tuple_le_def by auto
  finally show "le (inv_gorder (\<Otimes>Ls)) f g = invert_tuple_le Ls f g"
    by auto
qed

lemma inv_cart_prod_is_cart_prod_inv: "inv_gorder (\<Otimes>Ls) = \<Otimes>(invert_Ls Ls)"
  using carrier_invert_Ls eq_invert_Ls le_invert_Ls le_inv_cart_prod
  by (metis (full_types) gorder.select_convs(1) gorder.surjective old.unit.exhaust)

sublocale cart_prod_lattice \<subseteq> partial_order "\<Otimes>Ls"
  unfolding cart_prod_def
  apply unfold_locales
  using tuple_le_refl tuple_le_antisym tuple_le_trans by auto

lemma(in cart_prod_lattice) tuple_lub_lub : "A \<subseteq> carrier \<Otimes>Ls \<Longrightarrow> is_lub (\<Otimes>Ls) (tuple_lub A) A"
  using supremumI[where y="tuple_lub A" and A="A"]
        tuple_lub_least tuple_lub_ub tuple_lub_closed by simp

lemma(in cart_prod_lattice) lub_exists: "A \<subseteq> carrier \<Otimes>Ls \<Longrightarrow> \<exists>s. is_lub (\<Otimes>Ls) s A"
  using tuple_lub_lub by auto

lemma(in cart_prod_lattice) tuple_glb_glb : "A \<subseteq> carrier (\<Otimes>Ls) \<Longrightarrow> is_glb (\<Otimes>Ls) (tuple_glb A) A"
  using infimumI[where y="tuple_glb A" and A="A"]
        tuple_glb_greatest tuple_glb_lb tuple_glb_closed by simp

lemma(in cart_prod_lattice) glb_exists: "A \<subseteq> carrier (\<Otimes>Ls) \<Longrightarrow> \<exists>s. is_glb (\<Otimes>Ls) s A"
  using tuple_glb_glb by auto

sublocale cart_prod_lattice \<subseteq> complete_lattice "\<Otimes>Ls"
  apply unfold_locales
  using lub_exists glb_exists by auto

lemma (in cart_prod_lattice) vect_carrier: "carrier (\<Otimes>Ls) = {f\<in>{1..length Ls} \<rightarrow>\<^sub>E lattice_union Ls. \<forall>i\<in>{1..length Ls}. f i \<in> get_carrier Ls i}"
  unfolding cart_prod_def car_prod_carrier_def by auto

lemma (in cart_prod_lattice) vect_notinrange_undef: "f\<in>carrier (\<Otimes>Ls) \<Longrightarrow> i\<notin> {1..length Ls} \<Longrightarrow> f i = undefined"
  unfolding vect_carrier by auto

lemma (in cart_prod_lattice) vect_eqI [intro]: 
  "f\<in>carrier (\<Otimes>Ls) \<Longrightarrow> g\<in>carrier (\<Otimes>Ls) 
  \<Longrightarrow> (\<And>i. i\<in>{1..length Ls} \<Longrightarrow> f i = g i) \<Longrightarrow> f = g"
proof -
  assume \<open>\<And>i. i\<in>{1..length Ls} \<Longrightarrow> f i = g i\<close> and \<open>f\<in>carrier (\<Otimes>Ls)\<close> and \<open>g\<in>carrier (\<Otimes>Ls)\<close>
  have "\<And>i. f i = g i"
  proof -
    fix i
    show "f i = g i"
    proof (cases "i\<in>{1..length Ls}")
      case True
      then show ?thesis 
        using \<open>\<And>i. i\<in>{1..length Ls} \<Longrightarrow> f i = g i\<close> by auto
    next
      case False
      then show ?thesis
        using vect_notinrange_undef \<open>f\<in>carrier (\<Otimes>Ls)\<close> \<open>g\<in>carrier (\<Otimes>Ls)\<close> by metis
    qed
  qed
  then show ?thesis
    by auto
qed


lemma invert_preserve_funcset:
  "(F \<in> carrier (\<Otimes>(invert_Ls Ls)) \<rightarrow>\<^sub>E carrier (\<Otimes>(invert_Ls Ls))) = (F\<in>carrier (\<Otimes>Ls) \<rightarrow>\<^sub>E carrier (\<Otimes>Ls))"
  using carrier_invert_Ls[of "Ls"] by simp

lemma invert_cart_prod_lattice:
  assumes "cart_prod_lattice (Ls)"
  shows "cart_prod_lattice (invert_Ls Ls)"
  apply (rule cart_prod_lattice.intro)
  using cart_prod_lattice.Ls_len_pos[OF assms] unfolding invert_Ls_def apply auto[1]
  using cart_prod_lattice.Ls_comp_lat[OF assms] complete_lattice.dual_complete_lattice by fastforce

lemma invert_preserve_mono:
  assumes "cart_prod_lattice Ls" 
  shows 
  "Mono\<^bsub>\<Otimes>(invert_Ls Ls)\<^esub> F = Mono\<^bsub>\<Otimes>Ls\<^esub> F"
proof -
  interpret Lat: cart_prod_lattice "invert_Ls Ls"
    using invert_cart_prod_lattice[OF assms] by simp
  show ?thesis
    using Lat.inv_isotone[of "\<Otimes>Ls" "\<Otimes>Ls" "F"] inv_cart_prod_is_cart_prod_inv[of "Ls"] by auto
qed

definition proj:: "nat \<Rightarrow> ((nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a" (\<open>(Pr\<^bsub>_\<^esub> _)\<close>) where
  "proj i f = (\<lambda>v . f v i)"

lemma proj_simp [simp]: "proj i f x = f x i"
  unfolding proj_def by auto

function nested:: "'a gorder list \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a option) \<Rightarrow> ( (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) ) \<Rightarrow> 'a" 
where
  "nested Ls i B f = (if i\<notin>{1..length Ls} then undefined else if B i\<noteq>None then undefined else
      LFP\<^bsub>(Ls ! (i-1))\<^esub> (\<lambda>(xi::'a)\<in>carrier (Ls ! (i-1)). (Pr\<^bsub>i\<^esub> f) (\<lambda>(j::nat)\<in>{1..length Ls}. if j=i then xi else 
        (if B j \<noteq> None then (the (B j)) else nested Ls j (B(i \<mapsto> xi)) f))))"
  by pat_completeness auto
termination
proof (relation "measure (\<lambda>((Ls::'b gorder list),(i::nat), (B::nat \<Rightarrow> 'b option), (f::(nat\<Rightarrow>'b) \<Rightarrow> (nat \<Rightarrow> 'b))). card {j\<in>{1..length Ls}. B j=None})")
  show "wf (measure (\<lambda>(Ls, i, B, f). card {j \<in> {1..length Ls}. B j = None}))"
    by auto
next
  fix Ls i B f xi xa
  assume a1:"\<not> i \<notin> {1..length (Ls::'b gorder list)}" and a3:"\<not> (B::nat\<Rightarrow>'b option) i \<noteq> None" and a4:"xa \<noteq> i" and a5:"\<not> B xa \<noteq> None"
  show "((Ls, xa, B(i \<mapsto> xi), f), Ls, i, B, (f::(nat\<Rightarrow>'b) \<Rightarrow> (nat \<Rightarrow> 'b))) \<in> measure (\<lambda>(Ls, i, B, f). card {j \<in> {1..length Ls}. B j = None})"
  proof (auto simp add:a1 a5 a3 a4)
    let ?lhs = "{j. j \<noteq> i \<and> (j \<noteq> i \<longrightarrow> Suc 0 \<le> j \<and> j \<le> length Ls \<and> B j = None)}"
    let ?rhs = "{j. Suc 0 \<le> j \<and> j \<le> length Ls \<and> B j = None}"
    have r_fin:"finite ?rhs"
      using finite_nat_set_iff_bounded_le by auto
    have b1:"i\<in>{1..length Ls}"
      using a1 by auto
    have b3:"B i = None"
      using a3 by auto
    have c1:"?lhs \<subseteq> ?rhs"
      by auto
    then have lhs_le_rhs:"card ?lhs \<le> card ?rhs"
      using r_fin card_mono by blast
    have c2:"i\<in> {j. 1 \<le> j \<and> j \<le> length Ls \<and> B j = None}"
      using b3 b1 by auto
    have c3:"i\<notin> {j. j \<noteq> i \<and> (j \<noteq> i \<longrightarrow> 1 \<le> j \<and> j \<le> length Ls \<and> B j = None)}"
      by auto
    have "?lhs < ?rhs"
      using lhs_le_rhs c2 c3 by auto
    then show "card ?lhs < card ?rhs"
      using psubset_card_mono r_fin by blast
  qed
qed

function nested_gfp:: "'a gorder list \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a option) \<Rightarrow> ( (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) ) \<Rightarrow> 'a" 
where
  "nested_gfp Ls i B f = (if i\<notin>{1..length Ls} then undefined else if B i\<noteq>None then undefined else
     GFP\<^bsub>(Ls ! (i-1))\<^esub> (\<lambda>(xi::'a)\<in>carrier (Ls ! (i-1)). (Pr\<^bsub>i\<^esub> f) (\<lambda>(j::nat)\<in>{1..length Ls}. if j=i then xi else 
        (if B j \<noteq> None then (the (B j)) else nested_gfp Ls j (B(i \<mapsto> xi)) f))))"
  by pat_completeness auto
termination
proof (relation "measure (\<lambda>((Ls::'b gorder list),(i::nat), (B::nat \<Rightarrow> 'b option), (f::(nat\<Rightarrow>'b) \<Rightarrow> (nat \<Rightarrow> 'b))). card {j\<in>{1..length Ls}. B j=None})")
  show "wf (measure (\<lambda>(Ls, i, B, f). card {j \<in> {1..length Ls}. B j = None}))"
    by auto
next
  fix Ls i B f xi xa
  assume a1:"\<not> i \<notin> {1..length (Ls::'b gorder list)}" and a3:"\<not> (B::nat\<Rightarrow>'b option) i \<noteq> None" and a4:"xa \<noteq> i" and a5:"\<not> B xa \<noteq> None"
  show "((Ls, xa, B(i \<mapsto> xi), f), Ls, i, B, (f::(nat\<Rightarrow>'b) \<Rightarrow> (nat \<Rightarrow> 'b))) \<in> measure (\<lambda>(Ls, i, B, f). card {j \<in> {1..length Ls}. B j = None})"
  proof (auto simp add:a1 a5 a3 a4)
    let ?lhs = "{j. j \<noteq> i \<and> (j \<noteq> i \<longrightarrow> Suc 0 \<le> j \<and> j \<le> length Ls \<and> B j = None)}"
    let ?rhs = "{j. Suc 0 \<le> j \<and> j \<le> length Ls \<and> B j = None}"
    have r_fin:"finite ?rhs"
      using finite_nat_set_iff_bounded_le by auto
    have b1:"i\<in>{1..length Ls}"
      using a1 by auto
    have b3:"B i = None"
      using a3 by auto
    have c1:"?lhs \<subseteq> ?rhs"
      by auto
    then have lhs_le_rhs:"card ?lhs \<le> card ?rhs"
      using r_fin card_mono by blast
    have c2:"i\<in> {j. 1 \<le> j \<and> j \<le> length Ls \<and> B j = None}"
      using b3 b1 by auto
    have c3:"i\<notin> {j. j \<noteq> i \<and> (j \<noteq> i \<longrightarrow> 1 \<le> j \<and> j \<le> length Ls \<and> B j = None)}"
      by auto
    have "?lhs < ?rhs"
      using lhs_le_rhs c2 c3 by auto
    then show "card ?lhs < card ?rhs"
      using psubset_card_mono r_fin by blast
  qed
qed

lemma (in cart_prod_lattice) nested_simps_defined:"i\<in>{1..length Ls} \<Longrightarrow> B i \<noteq>None \<Longrightarrow> nested Ls i B f = undefined"
  by auto

lemma (in cart_prod_lattice) nested_simps_undefined:"i\<in>{1..length Ls} \<Longrightarrow> B i=None \<Longrightarrow> nested Ls i B f = 
  LFP\<^bsub>(Ls ! (i-1))\<^esub> (\<lambda>xi\<in>carrier (Ls ! (i-1)). (Pr\<^bsub>i\<^esub> f) (\<lambda>(j::nat)\<in>{1..length Ls}. if j=i then xi else 
              (if B j \<noteq> None then (the (B j)) else nested Ls j (B(i \<mapsto> xi)) f)))"
  by auto

lemma (in cart_prod_lattice) nested_gfp_simps_undefined:"i\<in>{1..length Ls} \<Longrightarrow> B i=None \<Longrightarrow> nested_gfp Ls i B f = 
  GFP\<^bsub>(Ls ! (i-1))\<^esub> (\<lambda>xi\<in>carrier (Ls ! (i-1)). (Pr\<^bsub>i\<^esub> f) (\<lambda>(j::nat)\<in>{1..length Ls}. if j=i then xi else 
              (if B j \<noteq> None then (the (B j)) else nested_gfp Ls j (B(i \<mapsto> xi)) f)))"
  by auto

lemma (in cart_prod_lattice) nested_closed: "i\<in>{1..length Ls} \<Longrightarrow> B i = None \<Longrightarrow> nested Ls i B f \<in> carrier (Ls ! (i-1))"
proof - 
  assume a_i:"i\<in>{1..length Ls}" and \<open>B i =None\<close>
  interpret ith_comp_lat: complete_lattice "(Ls ! (i-1))"
    using Ls_comp_lat a_i by auto
  have "nested Ls i B f = LFP\<^bsub>(Ls ! (i-1))\<^esub> (\<lambda>xi\<in>carrier (Ls ! (i-1)). (Pr\<^bsub>i\<^esub> f) (\<lambda>(j::nat)\<in>{1..length Ls}. 
        if j=i then xi else 
          (if B j \<noteq> None then (the (B j)) else nested Ls j (B(i \<mapsto> xi)) f)))"
    using nested_simps_undefined[of "i" "B" "f"] \<open>B i=None\<close> a_i by auto
  then show "nested Ls i B f \<in> carrier (Ls ! (i-1))"
    using ith_comp_lat.LFP_closed by auto
qed

lemma (in cart_prod_lattice) nested_gfp_losed: "i\<in>{1..length Ls} \<Longrightarrow> B i = None \<Longrightarrow> nested_gfp Ls i B f \<in> carrier (Ls ! (i-1))"
proof - 
  assume a_i:"i\<in>{1..length Ls}" and \<open>B i =None\<close>
  interpret ith_comp_lat: complete_lattice "(Ls ! (i-1))"
    using Ls_comp_lat a_i by auto
  have "nested_gfp Ls i B f = GFP\<^bsub>(Ls ! (i-1))\<^esub> (\<lambda>xi\<in>carrier (Ls ! (i-1)). (Pr\<^bsub>i\<^esub> f) (\<lambda>(j::nat)\<in>{1..length Ls}. 
        if j=i then xi else 
          (if B j \<noteq> None then (the (B j)) else nested_gfp Ls j (B(i \<mapsto> xi)) f)))"
    using nested_gfp_simps_undefined[of "i" "B" "f"] \<open>B i=None\<close> a_i by auto
  then show "nested_gfp Ls i B f \<in> carrier (Ls ! (i-1))"
    using ith_comp_lat.GFP_closed by auto
qed

lemma invert_Ls_member:
  assumes "i\<in>{1::nat..length Ls}"
  shows "invert_Ls Ls ! (i - 1) = inv_gorder (Ls ! (i-1))"
  unfolding invert_Ls_def using assms nth_map by auto

lemma nested_invert_is_nested_gfp:
  assumes a_i:"i\<in>{1::nat..length Ls}" and a_B:"B i = None" and cp:"cart_prod_lattice Ls"
  shows "nested (invert_Ls Ls) i B F = nested_gfp Ls i B F"
  using assms
proof (induction "card {j\<in>{1..length Ls}. B j = None}" arbitrary:B i rule:nat.induct)
  case zero
  then show ?case
    by auto
next
  case (Suc n)
  then show ?case
  proof -
    interpret L: cart_prod_lattice "Ls"
      using cp by auto
    have a1:"cart_prod_lattice (invert_Ls Ls)"
      using invert_cart_prod_lattice[OF cp] by simp
    have a2:"i\<in>{1::nat .. length (invert_Ls Ls)}"
      using Suc.prems by auto
    have "nested (invert_Ls Ls) i B F =   
            LFP\<^bsub>(invert_Ls Ls ! (i-1))\<^esub> (\<lambda>xi\<in>carrier (invert_Ls Ls ! (i-1)). (Pr\<^bsub>i\<^esub> F) (\<lambda>(j::nat)\<in>{1..length Ls}. if j=i then xi else 
              (if B j \<noteq> None then (the (B j)) else nested (invert_Ls Ls) j (B(i \<mapsto> xi)) F)))"
      using cart_prod_lattice.nested_simps_undefined[OF a1 a2 ] Suc.prems(2) by auto
    also have "... =
            LFP\<^bsub>(invert_Ls Ls ! (i-1))\<^esub> (\<lambda>xi\<in>carrier (invert_Ls Ls ! (i-1)). (Pr\<^bsub>i\<^esub> F) (\<lambda>(j::nat)\<in>{1..length Ls}. if j=i then xi else 
              (if B j \<noteq> None then (the (B j)) else nested_gfp Ls j (B(i \<mapsto> xi)) F)))"
    proof -
      have "\<And>xi j. xi\<in>carrier (invert_Ls Ls ! (i-1)) \<Longrightarrow> j\<in>{1::nat..length Ls} \<Longrightarrow> B j=None \<Longrightarrow> i\<noteq>j \<Longrightarrow>
             nested (invert_Ls Ls) j (B(i \<mapsto> xi)) F = nested_gfp Ls j (B(i \<mapsto> xi)) F"
      proof -
        fix xi j assume a_xi:"xi\<in>carrier (invert_Ls Ls ! (i-1))" and a_j:"j\<in>{1::nat..length Ls}" and a_Bj:"B j = None" and "i\<noteq>j"
        have b1_1:"n = card {j \<in> {1..length Ls}. (B(i \<mapsto> xi)) j = None}"
        proof -
          have "{j \<in> {1..length Ls}. (B(i \<mapsto> xi)) j = None} = {j \<in> {1..length Ls}. B j = None} - {i}"
            using \<open>B i = None\<close> \<open>i\<in>{1..length Ls}\<close> by auto
          thus ?thesis
            using Suc.hyps(2) Suc.prems(1,2) by force
        qed
        have b1_2:"(B(i \<mapsto> xi)) j = None"
          using a_Bj \<open>i\<noteq>j\<close> by auto
        show "nested (invert_Ls Ls) j (B(i \<mapsto> xi)) F = nested_gfp Ls j (B(i \<mapsto> xi)) F"
          using Suc.hyps(1)[OF b1_1 a_j b1_2 cp] by force
      qed
      thus ?thesis
        by (smt (verit, ccfv_SIG) restrict_ext)
    qed
    also have "... =
      LFP\<^bsub>(inv_gorder (Ls ! (i-1)))\<^esub> (\<lambda>xi\<in>carrier (invert_Ls Ls ! (i-1)). (Pr\<^bsub>i\<^esub> F) (\<lambda>(j::nat)\<in>{1..length Ls}. if j=i then xi else 
              (if B j \<noteq> None then (the (B j)) else nested_gfp Ls j (B(i \<mapsto> xi)) F)))"
      using invert_Ls_member[OF \<open>i\<in>{1..length Ls}\<close>] by auto
    also have "... = 
      GFP\<^bsub>(Ls ! (i-1))\<^esub> (\<lambda>xi\<in>carrier (Ls ! (i-1)). (Pr\<^bsub>i\<^esub> F) (\<lambda>(j::nat)\<in>{1..length Ls}. if j=i then xi else 
              (if B j \<noteq> None then (the (B j)) else nested_gfp Ls j (B(i \<mapsto> xi)) F)))"
      using LFP_dual[of "Ls !(i-1)"] carrier_invert_Ls_member[OF \<open>i\<in>{1..length Ls}\<close>] by auto
    also have "... = nested_gfp Ls i B F"
      using L.nested_gfp_simps_undefined[OF \<open>i\<in>{1..length Ls}\<close>] \<open>B i=None\<close> by auto
    finally show ?thesis
      by simp
  qed
qed

definition carrier_spl:: "'a gorder list \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a) set" where
  "carrier_spl Ls i = car_prod_carrier (remove_at (i-1) Ls)"

lemma length_minus_1:"(i::nat)\<in>{1..length Ls} \<Longrightarrow> length (remove_at (i-1) Ls) = length Ls - 1"
  unfolding remove_at_def 
proof (simp)
  assume "Suc 0 \<le> i \<and> i \<le> length Ls"
  then have "(min (length Ls) (i - Suc 0)) = (i - Suc 0)" by auto
  then show "min (length Ls) (i - Suc 0) + length Ls - i = length Ls - Suc 0"
    by (simp add: \<open>Suc 0 \<le> i \<and> i \<le> length Ls\<close>)
qed

lemma carrier_spl_form':"i\<in>{1..length Ls} \<Longrightarrow> carrier_spl Ls i = 
  {f\<in>{1..length Ls-1} \<rightarrow>\<^sub>E lattice_union (remove_at (i-1) Ls). \<forall>j\<in>{1..length Ls - 1}. f j \<in> get_carrier (remove_at (i-1) Ls) j}"
  unfolding carrier_spl_def car_prod_carrier_def
  using length_minus_1[of "i" "Ls"]
  by presburger

lemma get_carrier_form[simp]: "get_carrier Ls j = carrier (Ls ! (j-1))"
  unfolding get_carrier_def by auto

lemma remove_at_nth_lt: "i\<in>{1..length Ls} \<Longrightarrow> j\<in>{1..length Ls} \<Longrightarrow> j<i \<Longrightarrow> (nth (remove_at (i-1) Ls) (j-1)) = (Ls ! (j-1))"
  unfolding remove_at_def
  by (simp add: less_diff_conv nth_append)

lemma remove_at_nth_ge: "i\<in>{1..length Ls} \<Longrightarrow> j\<in>{1..length Ls} \<Longrightarrow> j\<ge>i \<Longrightarrow> (nth (remove_at (i-1) Ls) (j-1)) = (Ls ! j)"
  unfolding remove_at_def
proof (induction j arbitrary:i Ls)
  case 0
  then show ?case by auto
next
  case (Suc j)
  then show ?case
  proof (cases Ls)
    case Nil
    then show ?thesis
      using \<open>i \<in> {1..length Ls}\<close> by simp
  next
    case (Cons x xs)
    then show ?thesis
    proof (cases "i=1")
      case True
      then show ?thesis
        using \<open>Ls = x # xs\<close> by simp
    next
      case False
      then show ?thesis
      proof (simp add:\<open>Ls=Cons x xs\<close>)
        from \<open>i \<le> Suc j\<close> have b1:"j-1 \<ge> i-2" 
          by auto
        have b6:"i-1\<le>j"
          using \<open>i \<le> Suc j\<close> by auto
        have b2:"i-1 \<ge> 1" 
          using False \<open>i\<in>{1..length Ls}\<close> by auto
        then have b3:"j > 0"
          using Suc.prems(3) by linarith
        have b5:"j \<in> {1..length xs}"
          using \<open>Suc j \<in> {1..length Ls}\<close> \<open>Ls = x # xs\<close> b3 by auto
        have b4:"i-1\<in>{1..length xs}"
          using \<open>i\<in>{1..length Ls}\<close> \<open>Ls=Cons x xs\<close> b2 by auto
        have "(take (i - Suc 0) (x # xs) @ drop (i - Suc 0) xs) ! j = ((x # take (i-2) xs) @ (drop (i-1) xs)) ! j"
          by (metis False One_nat_def Suc.prems(1) Suc_1 atLeastAtMost_iff diff_Suc_eq_diff_pred diff_is_0_eq le_antisym take_Cons')
        also have "... = ((take (i-2) xs) @ (drop (i-1) xs)) ! (j-1)"
          using b3 by auto
        also have "... = xs ! j"
          using Suc.IH[of "i-1" "xs"] b4 b5 b6 by (metis Suc_1 b2 diff_Suc_eq_diff_pred le_add_diff_inverse2)
        finally show "(take (i - Suc 0) (x # xs) @ drop (i - Suc 0) xs) ! j = xs ! j" 
          by auto
      qed
    qed
  qed
qed

lemma remove_at_nth_ge2: "i\<in>{1..length Ls} \<Longrightarrow> j\<in>{1..length Ls-1} \<Longrightarrow> j\<ge>i \<Longrightarrow> (nth (remove_at (i-1) Ls) (j-1)) = (Ls ! j)"
  using remove_at_nth_ge[of "i" "Ls" "j"] by auto

lemma carrier_spl_form: "i\<in>{1..length Ls} \<Longrightarrow> carrier_spl Ls i = 
  {f\<in>{1..length Ls-1} \<rightarrow>\<^sub>E lattice_union (remove_at (i-1) Ls). \<forall>j\<in>{1..length Ls - 1}. (j<i \<longrightarrow> f j \<in> carrier (Ls ! (j-1)))
    \<and> (j \<ge> i \<longrightarrow> f j \<in> carrier (Ls ! j))}"
proof -
  assume a_i:"i\<in>{1..length Ls}"
  have "\<forall>f. ((\<forall>j\<in>{1..length Ls - 1}. ((j<i \<longrightarrow> f j \<in> carrier (Ls ! (j-1))) \<and> (j \<ge> i \<longrightarrow> f j \<in> carrier (Ls ! j)))) = (\<forall>j\<in>{1..length Ls - 1}. f j \<in> carrier ((remove_at (i-1) Ls)!(j-1))))"
  proof 
    fix f
    show "((\<forall>j\<in>{1..length Ls - 1}. ((j < i \<longrightarrow> f j \<in> carrier (Ls ! (j-1))) \<and> (i \<le> j \<longrightarrow> f j \<in> carrier (Ls ! j)))) =
         (\<forall>j\<in>{1..length Ls - 1}. f j \<in> carrier ((remove_at (i-1) Ls)!(j-1))))"
    proof 
      show "\<forall>j\<in>{1..length Ls - 1}. (j < i \<longrightarrow> f j \<in> carrier (Ls ! (j-1))) \<and> (i \<le> j \<longrightarrow> f j \<in> carrier (Ls ! j)) \<Longrightarrow>
            \<forall>j\<in>{1..length Ls - 1}. f j \<in> carrier (remove_at (i - 1) Ls ! (j-1))"
      proof 
        fix j
        assume ass:"\<forall>j\<in>{1..length Ls - 1}. (j < i \<longrightarrow> f j \<in> carrier (Ls ! (j-1))) \<and> (i \<le> j \<longrightarrow> f j \<in> carrier (Ls ! j))" and \<open>j\<in>{1..length Ls - 1}\<close>
        show "f j \<in> carrier (remove_at (i - 1) Ls ! (j-1))"
        proof (cases "j<i")
          case True
          then show ?thesis 
            using remove_at_nth_lt[of "i" "Ls" "j"] \<open>j\<in>{1..length Ls - 1}\<close> a_i
            by (metis ass atLeastAtMost_iff get_member_def leD less_imp_diff_less not_le_imp_less)
        next
          case False
          then show ?thesis
            using remove_at_nth_ge2[of "i" "Ls" "j"] \<open>j\<in>{1..length Ls -1}\<close> a_i ass
            by (metis add_diff_cancel_right' get_member_def le_geq_cases)
        qed
      qed
    next
      assume ass:"\<forall>j\<in>{1..length Ls - 1}. f j \<in> carrier (remove_at (i - 1) Ls ! (j-1))"
      show "\<forall>j\<in>{1..length Ls - 1}. (j < i \<longrightarrow> f j \<in> carrier (Ls ! (j-1))) \<and> (i \<le> j \<longrightarrow> f j \<in> carrier (Ls ! j))"
      proof
        fix j
        assume "j\<in>{1..length Ls-1}"
        show "(j < i \<longrightarrow> f j \<in> carrier (Ls ! (j-1))) \<and> (i \<le> j \<longrightarrow> f j \<in> carrier (Ls ! j))"
        proof
          show "j < i \<longrightarrow> f j \<in> carrier (Ls ! (j-1))"
            using remove_at_nth_lt[of "i" "Ls" "j"] \<open>j\<in>{1..length Ls - 1}\<close> a_i ass
            unfolding get_member_def
            by (metis atLeastAtMost_iff less_imp_diff_less linorder_not_le)
          show "i \<le> j \<longrightarrow> f j \<in> carrier (Ls ! j)"
            using remove_at_nth_ge2[of "i" "Ls" "j"] \<open>j\<in>{1..length Ls - 1}\<close> a_i ass
            unfolding get_member_def
            by (metis diff_add_inverse2)
        qed
      qed
    qed
  qed
  then show ?thesis
    using carrier_spl_form'[of "i" "Ls"] a_i by force
qed

lemma remove_at__sublist: "i\<in>{1..length Ls} \<Longrightarrow> j\<in>{1..length Ls-1} \<Longrightarrow> \<exists>k\<in>{1..length Ls}. ((remove_at (i-1) Ls) ! (j-1)) = (Ls ! (k-1))"
proof - assume a_i:"i\<in>{1..length Ls}" and a_j:"j\<in>{1..length Ls-1}"
  show ?thesis
  proof (cases "j<i")
    case True
    then show ?thesis
      using remove_at_nth_lt a_i a_j unfolding get_member_def
    by (metis (no_types, opaque_lifting) atLeastAtMost_iff dual_order.trans le_eq_less_or_eq)
  next
    case False
    then show ?thesis
    proof -
      have "remove_at (i - 1) Ls ! (j - 1) = Ls ! j" 
        using remove_at_nth_ge2[of "i" "Ls" "j"] a_i a_j False by auto
      then show ?thesis 
        using a_j unfolding get_member_def
      by (metis (no_types, opaque_lifting) Suc_eq_plus1 add.commute add_diff_cancel_left' atLeastAtMost_iff diff_Suc_eq_diff_pred diff_is_0_eq le_antisym nat_le_linear)
    qed
  qed
qed

lemma (in cart_prod_lattice) remove_at_comp_lat: "j\<in>{1..length Ls} \<Longrightarrow> i\<in>{1..length Ls-1} \<Longrightarrow> complete_lattice ((remove_at (j-1) Ls) ! (i-1))"
proof -
  assume \<open>i \<in> {1..length Ls - 1}\<close> and \<open>j\<in>{1..length Ls}\<close>
  then have "\<exists>k\<in>{1..length Ls}. ((remove_at (j-1) Ls) ! (i-1)) = (Ls ! (k-1))"
    using remove_at__sublist \<open>i \<in> {1..length Ls - 1}\<close> by auto
  then show ?thesis 
    using Ls_comp_lat by auto
qed 

lemma (in cart_prod_lattice) in_carrier_spl_I: "i\<in>{1..length Ls}
  \<Longrightarrow> ((\<And>h. h \<in> {1..length Ls - 1} \<Longrightarrow> (h < i \<longrightarrow> v h \<in> carrier (Ls ! (h-1))) \<and> (i \<le> h \<longrightarrow> v h \<in> carrier (Ls ! h))))
  \<Longrightarrow> (\<And>y. y\<notin>{1..length Ls-1} \<Longrightarrow> v y = undefined)
  \<Longrightarrow> v\<in>carrier_spl Ls i"
proof -
  assume a_i:"i \<in> {1..length Ls}"
    and a_h:"(\<And>h. h \<in> {1..length Ls - 1} \<Longrightarrow> (h < i \<longrightarrow> v h \<in> carrier (Ls ! (h-1))) \<and> (i \<le> h \<longrightarrow> v h \<in> carrier (Ls ! h)))"
    and a_ext:"\<And>y. y \<notin> {1..length Ls - 1} \<Longrightarrow> v y = undefined"
  have "length (remove_at (i-1) Ls) = length Ls-1"
    using a_i length_minus_1 by auto
  have b_funcset:"v \<in> {1..length Ls-1} \<rightarrow>\<^sub>E lattice_union (remove_at (i - 1) Ls)"
    unfolding lattice_union_def
  proof (rule PiE_I)
    fix x assume a_x:"x\<in>{1..length Ls - 1}"
    have c1:"x<i \<Longrightarrow> v x \<in> (get_carrier (remove_at (i - 1) Ls) x)"
    proof -
      assume \<open>x<i\<close>
      then have b1:"v x \<in> carrier (Ls ! (x-1))" 
        using a_h[of "x"] a_x by auto
      have b2:"(get_carrier (remove_at (i - 1) Ls) x) = carrier (Ls ! (x-1))"
        using \<open>x<i\<close> remove_at_nth_lt[of "i" "Ls" "x"] a_i a_x 
        unfolding get_member_def get_carrier_def by auto
      then have c1:"x<i \<Longrightarrow> v x \<in> (get_carrier (remove_at (i - 1) Ls) x)"
        using b1 by auto
      show "v x \<in> (get_carrier (remove_at (i - 1) Ls) x)"
        using b1 b2 by auto
    qed
    have c2:"x\<ge>i \<Longrightarrow> v x \<in> get_carrier (remove_at (i - 1) Ls) x"
    proof -
      assume \<open>x\<ge>i\<close>
      then have b1:"v x \<in> carrier (Ls ! x)"
        using a_h a_x by auto
      have "get_carrier (remove_at (i - 1) Ls) x = carrier (Ls ! x)"
        using remove_at_nth_ge[of "i" "Ls" "x"] a_i a_x \<open>x\<ge>i\<close>
        unfolding get_member_def get_carrier_def by auto
      then show "v x \<in> get_carrier (remove_at (i - 1) Ls) x"
        using b1 by auto
    qed
    show "v x \<in> \<Union> {get_carrier (remove_at (i - 1) Ls) k |k. k \<in> {1..length (remove_at (i - 1) Ls)}}"
      using c1 c2 a_x length_minus_1[of "i" "Ls"] a_i
      by (smt (verit, del_insts) UnionI le_geq_cases mem_Collect_eq)
  next
    show "\<And>x. x \<notin> {1..length Ls - 1} \<Longrightarrow> v x = undefined"
      using a_ext by auto
  qed
  have b_car:"\<forall>ia\<in>{1..length (remove_at (i - 1) Ls)}. v ia \<in> get_carrier (remove_at (i - 1) Ls) ia"
  proof
    fix x
    assume a_x:"x\<in>{1..length (remove_at (i - 1) Ls)}"
    show "v x\<in>get_carrier (remove_at (i - 1) Ls) x"
    proof -
      have c1:"x<i \<Longrightarrow> v x \<in> (get_carrier (remove_at (i - 1) Ls) x)"
      proof -
        assume \<open>x<i\<close>
        have b2:"(get_carrier (remove_at (i - 1) Ls) x) = carrier (Ls ! (x-1))"
          using \<open>x<i\<close> remove_at_nth_lt[of "i" "Ls" "x"] a_i a_x 
          unfolding get_member_def get_carrier_def by auto
        then have b1:"v x \<in> carrier (Ls ! (x-1))" 
          using a_h[of "x"] a_x length_minus_1[of "i" "Ls"] \<open>x<i\<close> a_i by auto
        show "v x \<in> (get_carrier (remove_at (i - 1) Ls) x)"
          using b1 b2 by auto
      qed
      have c2:"x\<ge>i \<Longrightarrow> v x \<in> get_carrier (remove_at (i - 1) Ls) x"
      proof -
        assume \<open>x\<ge>i\<close>
        have b2:"get_carrier (remove_at (i - 1) Ls) x = carrier (Ls ! x)"
          using remove_at_nth_ge[of "i" "Ls" "x"] a_i a_x \<open>x\<ge>i\<close> length_minus_1[of "i""Ls"]
          unfolding get_member_def get_carrier_def by auto
        have b1:"v x \<in> carrier (Ls ! x)"
          using a_h a_x length_minus_1[of "i" "Ls"] a_i \<open>x\<ge>i\<close> by auto
        then show "v x \<in> get_carrier (remove_at (i - 1) Ls) x"
          using b1 b2 by auto
      qed
      show ?thesis 
        using c1 c2 le_geq_cases by auto
    qed
  qed
  show "v\<in>carrier_spl Ls i"
    unfolding carrier_spl_def car_prod_carrier_def 
    using b_funcset b_car length_minus_1[of "i""Ls"] a_i by auto
qed

lemma (in cart_prod_lattice) carrier_spl_criterion: 
  assumes "i\<in>{1..length Ls}"
  shows "((\<forall>h\<in>{1..length Ls - 1}. (h < i \<longrightarrow> v h \<in> carrier (Ls ! (h-1))) \<and> (i \<le> h \<longrightarrow> v h \<in> carrier (Ls ! h))) 
          \<and> (\<forall>y. y\<notin>{1..length Ls-1} \<longrightarrow> v y = undefined)) = (v\<in>carrier_spl Ls i)"
proof
  show "(\<forall>h\<in>{1..length Ls - 1}. (h < i \<longrightarrow> v h \<in> carrier (Ls ! (h-1))) \<and> (i \<le> h \<longrightarrow> v h \<in> carrier (Ls ! h))) \<and> (\<forall>y. y \<notin> {1..length Ls - 1} \<longrightarrow> v y = undefined) \<Longrightarrow>
    v \<in> carrier_spl Ls i"
    using in_carrier_spl_I assms by auto
next
  assume ass:"v\<in>carrier_spl Ls i"
  show "(\<forall>h\<in>{1..length Ls - 1}. (h < i \<longrightarrow> v h \<in> carrier (Ls ! (h-1))) \<and> (i \<le> h \<longrightarrow> v h \<in> carrier (Ls ! h))) \<and> (\<forall>y. y \<notin> {1..length Ls - 1} \<longrightarrow> v y = undefined)"
  proof
    from carrier_spl_form[of "i" "Ls"] ass assms
      have b1:"v\<in>{f \<in> {1..length Ls - 1} \<rightarrow>\<^sub>E lattice_union (remove_at (i - 1) Ls).
            \<forall>j\<in>{1..length Ls - 1}. (j < i \<longrightarrow> f j \<in> carrier (Ls ! (j-1))) \<and> (i \<le> j \<longrightarrow> f j \<in> carrier (Ls ! j))}" by auto
    show "\<forall>h\<in>{1..length Ls - 1}. (h < i \<longrightarrow> v h \<in> carrier (Ls ! (h-1))) \<and> (i \<le> h \<longrightarrow> v h \<in> carrier (Ls ! h))"
    proof -
      from b1
      have "\<forall>j\<in>{1..length Ls - 1}. (j < i \<longrightarrow> v j \<in> carrier (Ls ! (j-1))) \<and> (i \<le> j \<longrightarrow> v j \<in> carrier (Ls ! j))"
        by auto
      then show ?thesis by auto
    qed
    from b1 have "v\<in>{1..length Ls - 1} \<rightarrow>\<^sub>E lattice_union (remove_at (i - 1) Ls)"
      by auto
    then have "v\<in>extensional {1..length Ls -1}"
      using PiE_iff by auto
    then show "\<forall>y. y \<notin> {1..length Ls - 1} \<longrightarrow> v y = undefined"
      by (metis extensional_arb)
  qed
qed
    
    
definition (in cart_prod_lattice) n_to_two:: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<times> 'a" where
  "n_to_two j v = ((\<lambda>k\<in>{1..length Ls-1}. (if k < j then v k else v (k+1))),v j)"

lemma (in cart_prod_lattice) n_to_two_fst_ext: 
  "y\<notin>{1..length Ls-1} \<Longrightarrow> fst (n_to_two j v) y = undefined"
  unfolding n_to_two_def by auto

lemma (in cart_prod_lattice) n_to_two_simps_lt:
  "y\<in>{1..length Ls-1} \<Longrightarrow> y<j \<Longrightarrow> fst (n_to_two j v) y = v y"
  unfolding n_to_two_def by auto

lemma (in cart_prod_lattice) n_to_two_simps_geq:
  "y\<in>{1..length Ls-1} \<Longrightarrow> y\<ge>j \<Longrightarrow> fst (n_to_two j v) y = v (y+1)"
  unfolding n_to_two_def by auto

lemma (in cart_prod_lattice) n_to_two_simps_snd:
  "snd (n_to_two j v) = v j"
  unfolding n_to_two_def by auto

lemma (in cart_prod_lattice) n_two__carrier:
  assumes a_v:"v\<in>carrier (\<Otimes>Ls)"
  and a_j:"j\<in>{1..length Ls}"
shows "fst (n_to_two j v) \<in> carrier_spl Ls j"
      "snd (n_to_two j v) \<in> carrier (Ls ! (j-1))"
proof -
  show "fst (n_to_two j v) \<in> carrier_spl Ls j"
  proof (rule in_carrier_spl_I)
    show "j\<in>{1..length Ls}"
      using a_j by auto
  next
    fix h assume a_h:"h\<in>{1..length Ls -1}"
    show "(h < j \<longrightarrow> fst (n_to_two j v) h \<in> carrier (Ls ! (h-1))) \<and> (j \<le> h \<longrightarrow> fst (n_to_two j v) h \<in> carrier (Ls ! h))"
    proof
      show "h < j \<longrightarrow> fst (n_to_two j v) h \<in> carrier (Ls ! (h-1))"
      proof 
        assume "h<j"
        have b1:"fst (n_to_two j v) h = v h"
          using n_to_two_simps_lt[of "h" "j" "v"] a_h \<open>h<j\<close> by auto
        have "v h \<in> carrier (Ls ! (h-1))"
          using a_v kth_carrier[of "v" "Ls" "h"] a_h \<open>h < j\<close> a_j by auto
        then show "fst (n_to_two j v) h \<in> carrier (Ls ! (h-1))"
          using b1 by auto
      qed
    next
      show "j \<le> h \<longrightarrow> fst (n_to_two j v) h \<in> carrier (Ls ! h)"
      proof
        assume "j\<le>h"
        have b1:"fst (n_to_two j v) h = v (h+1)"
          using n_to_two_simps_geq[of "h" "j" "v"] a_h \<open>j\<le>h\<close> by auto      
        have "v (h+1) \<in> carrier (Ls ! h)"
          using a_h a_v kth_carrier[of "v" "Ls" "h+1"] by auto
        then show "fst (n_to_two j v) h \<in> carrier (Ls ! h)"
          using b1 by auto
      qed
    qed
  next
    fix y assume a_y:"y\<notin>{1..length Ls -1}"
    then show "fst (n_to_two j v) y = undefined"
      using n_to_two_fst_ext by auto
  qed
next
  show "snd (n_to_two j v) \<in> carrier (Ls ! (j-1))"
  proof -
    have "snd (n_to_two j v) = v j"
      using n_to_two_simps_snd by auto
    then show ?thesis 
      using a_v kth_carrier a_j by auto
  qed
qed

definition (in cart_prod_lattice) two_to_n:: "nat \<Rightarrow> (nat \<Rightarrow> 'a)\<times>'a  \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "two_to_n i = (\<lambda>tup\<in> carrier_spl Ls i \<times> carrier (Ls ! (i-1)). (\<lambda>j\<in>{1..length Ls}. if j=i then (snd tup) else if j<i then (fst tup) j else (fst tup) (j-1)))"

lemma (in cart_prod_lattice) two_to_n_simps: 
  assumes a_v:"v\<in>carrier_spl Ls i"
      and a_y:"y\<in>carrier (Ls ! (i-1))"
      and a_i:"i\<in>{1..length Ls}"
      and a_j:"j\<in>{1..length Ls}"
    shows "two_to_n i (v,y) i = y" "j<i \<Longrightarrow> two_to_n i (v,y) j = v j" "j>i \<Longrightarrow> two_to_n i (v,y) j = v (j-1)"
  unfolding two_to_n_def 
  using assms by auto

lemma (in cart_prod_lattice) two_to_n_ext: 
  assumes a_v:"v\<in>carrier_spl Ls i"
      and a_y:"y\<in>carrier (Ls ! (i-1))"
      and a_i:"i\<in>{1..length Ls}"
      and a_j:"j\<notin>{1..length Ls}"
    shows "two_to_n i (v,y) j = undefined"
  unfolding two_to_n_def 
  using assms by auto

lemma (in cart_prod_lattice) two_n__carrier:
  "j\<in>{1..length Ls} \<Longrightarrow> v\<in>carrier_spl Ls j \<Longrightarrow> y\<in>carrier (Ls!(j-1)) \<Longrightarrow> two_to_n j (v,y) \<in> carrier (\<Otimes>Ls)"
proof (rule cart_carrier_criterion)
  fix i assume a_j: "j \<in> {1..length Ls}" and a_v:"v \<in> carrier_spl Ls j" and a_y:"y \<in> carrier (Ls!(j-1))" and a_i:"i \<in> {1..length Ls}"
  show "two_to_n j (v, y) i \<in> carrier (Ls ! (i-1))"
  proof (cases "i<j")
    case True
    then show ?thesis
    proof -
      from a_v have "\<forall>i\<in>{1..length Ls - 1}. (i < j \<longrightarrow> v i \<in> carrier (Ls ! (i-1))) \<and> (j \<le> i \<longrightarrow> v i \<in> carrier (Ls ! i))"
        using carrier_spl_criterion[of "j" "v"] a_j by auto
      then show ?thesis
        using two_to_n_simps(2)[of "v" "j" "y" "i"] a_v a_y a_i a_j \<open>i<j\<close> by auto
    qed
  next
    case False
    then show ?thesis
    proof -
      from False have "i\<ge>j" by auto
      from a_v have b1:"\<forall>i\<in>{1..length Ls - 1}. (i < j \<longrightarrow> v i \<in> carrier (Ls ! (i-1))) \<and> (j \<le> i \<longrightarrow> v i \<in> carrier (Ls ! i))"
        using carrier_spl_criterion[of "j" "v"] a_j by auto
      then show ?thesis
      proof (cases "j=i")
        case True
        then show ?thesis
          using two_to_n_simps(1)[of "v" "j" "y" "i"] a_y a_v a_i a_j by auto
      next
        case False
        then show ?thesis
        proof -
          from False \<open>i\<ge>j\<close> have "i>j" by auto
          then show ?thesis
          proof -
            from two_to_n_simps(3)[of "v" "j" "y" "i"]
            have b2:"two_to_n j (v,y) i = v (i - 1)" 
              using a_v a_y a_j a_i \<open>i>j\<close> by auto
            have "i-1\<in>{1..length Ls-1}"
              using a_i a_j \<open>i>j\<close>
              by (metis add.commute add_le_imp_le_diff atLeastAtMost_iff diff_diff_cancel le_add_diff_inverse le_geq_cases less_one minus_nat.diff_0)
            then have "v (i-1) \<in> carrier (Ls ! (i-1))"
              using b1 \<open>i>j\<close> a_i by fastforce
            then show ?thesis
              using b2 by auto
          qed
        qed
      qed
    qed    
  qed
  fix i assume a_j:"j\<in>{1..length Ls}" and a_v:"v\<in>carrier_spl Ls j" and a_y:"y\<in> carrier (Ls !(j-1))" and a_i:"i\<notin>{1..length Ls}"
  show " two_to_n j (v, y) i = undefined "
    using two_to_n_ext[of "v" "j" "y" "i"] a_v a_y a_i a_j by auto
qed   

lemma (in cart_prod_lattice) two_to_n_eq:
  assumes a_v:"v\<in>carrier_spl Ls j"
      and a_y:"y\<in>carrier (Ls ! (j-1))"
      and a_j:"j\<in>{1..length Ls}"
  shows "two_to_n j (v,y) = (\<lambda>h\<in>{1..length Ls}. if h=j then y else if h<j then v h else v (h-1))"
proof
  show "two_to_n j (v, y) \<in> carrier \<Otimes>Ls"
    using two_n__carrier[OF a_j a_v a_y] by simp
  have hj_car: "\<And>h. h\<in>{1..length Ls-1} \<Longrightarrow> h<j \<Longrightarrow> v h \<in> carrier (Ls!(h-1))"
    using carrier_spl_form[of "j" "Ls"] a_v a_j by blast
  have jh_car: "\<And>h. h\<in>{1..length Ls-1} \<Longrightarrow> h\<ge>j \<Longrightarrow> v h \<in> carrier (Ls!h)"
    using carrier_spl_form[of "j" "Ls"] a_v a_j by blast
  have "\<And>i. i \<in> {1..length Ls} \<Longrightarrow> (\<lambda>h\<in>{1..length Ls}. if h = j then y else if h < j then v h else v (h - 1)) i \<in> carrier (Ls ! (i-1))"
  proof -
    fix i assume a_i:"i\<in>{1..length Ls}"
    have b1:"i=j \<Longrightarrow> (\<lambda>h\<in>{1..length Ls}. if h = j then y else if h < j then v h else v (h - 1)) i \<in> carrier (Ls ! (i-1))"
      using a_y a_j a_i by simp
    have b2:"i<j \<Longrightarrow> (\<lambda>h\<in>{1..length Ls}. if h = j then y else if h < j then v h else v (h - 1)) i \<in> carrier (Ls ! (i-1))"
      using hj_car[of "i"] a_j a_i by simp
    have b3:"i>j \<Longrightarrow> (\<lambda>h\<in>{1..length Ls}. if h = j then y else if h < j then v h else v (h - 1)) i \<in> carrier (Ls ! (i-1))"
      using jh_car[of "i-1"] a_j a_i by force
    show "(\<lambda>h\<in>{1..length Ls}. if h = j then y else if h < j then v h else v (h - 1)) i \<in> carrier (Ls ! (i-1))"
      using b1 b2 b3 by auto
  qed
  then show "(\<lambda>h\<in>{1..length Ls}. if h = j then y else if h < j then v h else v (h - 1)) \<in> carrier \<Otimes>Ls"
    using cart_carrier_criterion[of "Ls" "(\<lambda>h\<in>{1..length Ls}. if h = j then y else if h < j then v h else v (h - 1))"]
    by auto
  fix i assume a_i:"i \<in> {1..length Ls}"
  show "two_to_n j (v, y) i = (\<lambda>h\<in>{1..length Ls}. if h = j then y else if h < j then v h else v (h - 1)) i"
    using two_to_n_simps[OF a_v a_y a_j a_i] a_i a_j by auto
qed

lemma (in cart_prod_lattice) two_to_n_eq':
  assumes a_v:"v\<in>carrier_spl Ls j"
      and a_w:"w\<in>carrier_spl Ls j"
      and a_y:"y\<in>carrier (Ls ! (j-1))"
      and a_j:"j\<in>{1..length Ls}"
      and a_vw:"\<And>h. h\<in>{1..length Ls-1} \<Longrightarrow> v h = w h"
  shows "two_to_n j (v,y) = (\<lambda>h\<in>{1..length Ls}. if h=j then y else if h<j then w h else w (h-1))"
  using assms two_to_n_eq 
  by (metis (no_types, lifting) ext cart_prod_lattice.carrier_spl_criterion cart_prod_lattice_axioms)


lemma (in cart_prod_lattice) n_two__two_n_id:
  assumes a1:"v\<in>carrier_spl Ls j" and a2:"y\<in>carrier (Ls ! (j-1))" and a_j:"j\<in>{1..length Ls}"
  shows "n_to_two j (two_to_n j (v,y)) = (v,y)"
proof (rule)
  have b_tup_car:"(v,y)\<in> carrier_spl Ls j \<times> carrier (Ls ! (j-1))"
    using a1 a2 by auto
  have R1:"fst (n_to_two j (two_to_n j (v, y))) = v"
    unfolding n_to_two_def
  proof -
    have "(\<lambda>k\<in>{1..length Ls - 1}. if k < j then two_to_n j (v, y) k else two_to_n j (v, y) (k + 1)) = v"
    proof -
      from a1 have b1:"v\<in>{1..length Ls-1} \<rightarrow>\<^sub>E lattice_union (remove_at (j-1) Ls)"
        using carrier_spl_form[of "j" "Ls"] a_j by auto
      show "(\<lambda>k\<in>{1..length Ls - 1}. if k < j then two_to_n j (v, y) k else two_to_n j (v, y) (k + 1)) = v"
      proof (rule restrict_eqR)
        show "v \<in> extensional {1..length Ls - 1}"
          using b1 PiE_iff by auto
      next
        fix k assume \<open>k\<in>{1..length Ls-1}\<close>
        then show "(if k < j then two_to_n j (v, y) k else two_to_n j (v, y) (k + 1)) = v k"
        proof (cases "k<j")
          case True
          then show ?thesis
          proof -
            from two_to_n_simps[of "v" "j" "y" "k"] \<open>k\<in>{1..length Ls-1}\<close> a_j a1 a2 True 
            have "two_to_n j (v, y) k = v k"
              by (meson Nat.le_trans atLeastAtMost_iff nat_less_le)
            then show ?thesis
              using True by auto
          qed
        next
          case False
          then show ?thesis
          proof -
            from False have \<open>k\<ge>j\<close> by auto
            from two_to_n_simps a1 a2 \<open>k\<in>{1..length Ls-1}\<close> a_j
            have "two_to_n j (v,y) (k+1) = v k"
            proof (cases "k=j")
              case True
              then show ?thesis
                using two_to_n_simps(3)[of "v" "j" "y" "k+1"] a1 a2 \<open>k\<in>{1..length Ls-1}\<close> a_j by auto
            next
              case False
              then have "k>j" 
                using \<open>\<not> k < j\<close> by auto
              then show ?thesis
                using two_to_n_simps(3)[of "v" "j" "y" "k+1"] a1 a2 \<open>k\<in>{1..length Ls-1}\<close> a_j by auto
            qed
            then show ?thesis 
              using \<open>k\<ge>j\<close> by auto
          qed
        qed
      qed
    qed
    then show "fst (\<lambda>k\<in>{1..length Ls - 1}. if k < j then two_to_n j (v, y) k else two_to_n j (v, y) (k + 1), two_to_n j (v, y) j) = v"
      by auto
  qed
  then show "fst (n_to_two j (two_to_n j (v, y))) = fst (v, y)"
    by auto
next
  have "snd (n_to_two j (two_to_n j (v, y))) = y"
    unfolding n_to_two_def
  proof -
    have "two_to_n j (v, y) j = y"
      using two_to_n_simps(1) a1 a2 a_j by auto
    then show "snd (\<lambda>k\<in>{1..length Ls - 1}. if k < j then two_to_n j (v, y) k else two_to_n j (v, y) (k + 1), two_to_n j (v, y) j) = y"
      by auto
  qed
  then show "snd (n_to_two j (two_to_n j (v, y))) = snd (v, y)"
    by auto
qed

lemma (in cart_prod_lattice) two_n__n_two_id:
  assumes a_x:"x\<in>carrier (\<Otimes>Ls)" and a_j:"j\<in>{1..length Ls}"
  shows "two_to_n j (fst (n_to_two j x), snd (n_to_two j x)) = x"
proof (rule vect_eqI)
  have b1:"fst (n_to_two j x) \<in> carrier_spl Ls j"
    using n_two__carrier(1) a_x a_j by auto
  have b2:"snd (n_to_two j x) \<in> carrier (Ls!(j-1))"
    using n_two__carrier(2) a_x a_j by auto
  show "x \<in> carrier \<Otimes>Ls"
    using a_x by auto
  show "two_to_n j (fst (n_to_two j x), snd (n_to_two j x)) \<in> carrier \<Otimes>Ls"
    using b1 b2 two_n__carrier a_j a_x by blast
  fix i assume a_i:"i\<in>{1..length Ls}"
  show "two_to_n j (fst (n_to_two j x), snd (n_to_two j x)) i = x i"
  proof (cases "i<j")
    case True
    then show ?thesis
    proof -
      have "two_to_n j (fst (n_to_two j x), snd (n_to_two j x)) i = fst (n_to_two j x) i"
        using two_to_n_simps(2)[of "fst (n_to_two j x)" "j" "snd (n_to_two j x)" "i"] b1 b2 True a_j a_i by auto
      also have "... = x i"
        using n_to_two_simps_lt[of "i" "j" "x"] a_i \<open>i<j\<close> using a_j by auto
      finally show "two_to_n j (fst (n_to_two j x), snd (n_to_two j x)) i = x i"
        by simp
    qed
  next
    case False
    then show ?thesis
    proof (cases "j=i")
      case True
      then show ?thesis
      proof -
        have "two_to_n j (fst (n_to_two j x), snd (n_to_two j x)) i = snd (n_to_two j x)"
          using two_to_n_simps(1)[of "fst (n_to_two j x)" "j" "snd (n_to_two j x)" "i"] b1 b2 True a_i a_j by auto
        also have "... = x i"
          using \<open>j=i\<close> n_to_two_simps_snd by auto
        finally show ?thesis by auto
      qed
    next
      case False
      then show ?thesis 
      proof -
        have "i>j" using \<open>\<not>j=i\<close> \<open>\<not>i<j\<close> by auto
        have "two_to_n j (fst (n_to_two j x), snd (n_to_two j x)) i = fst (n_to_two j x) (i-1)"
          using two_to_n_simps(3)[of "fst (n_to_two j x)" "j" "snd (n_to_two j x)" "i"] \<open>i>j\<close> a_j a_i b1 b2 by auto
        also have "... = x i"
          using n_to_two_simps_geq[of "i-1" "j" "x"] \<open>i>j\<close> a_i a_j by auto
        finally show ?thesis by simp
    qed
  qed
qed
qed

definition Sp_Ls::"nat \<Rightarrow> 'a gorder list \<Rightarrow> 'a gorder list" (\<open>SpLs\<^bsub>_\<^esub> _\<close>) where
  "Sp_Ls i Ls = remove_at (i-1) Ls"

lemma length_minus_1'[simp]:"(i::nat)\<in>{1..length Ls} \<Longrightarrow> length (SpLs\<^bsub>i\<^esub> Ls) = length Ls - 1"
  using length_minus_1 unfolding Sp_Ls_def by auto

lemma SpLs_nth_lt: "i\<in>{1..length Ls} \<Longrightarrow> j\<in>{1..length Ls} \<Longrightarrow> j<i \<Longrightarrow> ((Sp_Ls i Ls) ! (j-1)) = (Ls ! (j-1))"
  unfolding get_member_def Sp_Ls_def using remove_at_nth_lt by force

lemma SpLs_nth_ge: "i\<in>{1..length Ls} \<Longrightarrow> j\<in>{1..length Ls} \<Longrightarrow> i\<le>j \<Longrightarrow> ((Sp_Ls i Ls) ! (j-1)) = (Ls ! j)"
  unfolding get_member_def Sp_Ls_def using remove_at_nth_ge by (metis diff_add_inverse2)
  
lemma carrier_spl_simp[simp]: "carrier (\<Otimes>(SpLs\<^bsub>j\<^esub> Ls)) = carrier_spl Ls j"
  unfolding carrier_spl_def Sp_Ls_def car_prod_carrier_def cart_prod_def by simp

lemma (in cart_prod_lattice) Ls_le_criterion:
  "v \<sqsubseteq>\<^bsub>\<Otimes>Ls\<^esub> w = (\<forall>i\<in>{1..length Ls}. v i\<sqsubseteq>\<^bsub>Ls!(i-1)\<^esub> w i)"
  unfolding cart_prod_def tuple_le_def by auto

lemma (in cart_prod_lattice) SpLs_le_criterion:
  assumes a_vw:"\<And>j. j\<in>{1..length Ls-1} \<Longrightarrow> (j<i \<longrightarrow> v j\<sqsubseteq>\<^bsub>Ls!(j-1)\<^esub> w j) \<and> (j\<ge>i \<longrightarrow> v j\<sqsubseteq>\<^bsub>Ls!j\<^esub> w j)"
    and a_v:"v\<in>carrier (\<Otimes>(SpLs\<^bsub>i\<^esub> Ls))"
    and a_w:"w\<in>carrier (\<Otimes>(SpLs\<^bsub>i\<^esub> Ls))"
    and a_i:"i\<in>{1..length Ls}"
  shows "v \<sqsubseteq>\<^bsub>\<Otimes>(SpLs\<^bsub>i\<^esub> Ls)\<^esub> w"
  unfolding cart_prod_def tuple_le_def
proof (auto)
  have a_v':"v\<in>carrier_spl Ls i"
    using a_v carrier_spl_simp by auto
  have a_w':"w\<in>carrier_spl Ls i"
    using a_w carrier_spl_simp by auto
  have v_prop:"(\<forall>j\<in>{1..length Ls - 1}. (j < i \<longrightarrow> v j \<in> carrier (Ls!(j-1))) \<and> (i \<le> j \<longrightarrow> v j \<in> carrier (Ls ! j) ))"
    using carrier_spl_criterion[of "i" "v"] a_i a_v' by auto
  have w_prop:"(\<forall>j\<in>{1..length Ls - 1}. (j < i \<longrightarrow> w j \<in> carrier (Ls!(j-1))) \<and> (i \<le> j \<longrightarrow> w j \<in> carrier (Ls ! j)))"
    using carrier_spl_criterion[of "i" "w"] a_i a_w' by auto
  fix j assume \<open>Suc 0 \<le> j\<close> and \<open>j \<le> length SpLs\<^bsub>i\<^esub> Ls\<close>
  show "v j \<sqsubseteq>\<^bsub>(SpLs\<^bsub>i\<^esub> Ls) ! (j-Suc 0)\<^esub> w j"
  proof (cases "j<i")
    have a_j:\<open>j\<in>{1..length Ls-1}\<close>
      using \<open>j \<le> length SpLs\<^bsub>i\<^esub> Ls\<close> \<open>Suc 0 \<le> j\<close> a_i length_minus_1' by auto
    case True
    then show ?thesis
    proof -
      have b1:"((SpLs\<^bsub>i\<^esub> Ls) ! (j-1)) = (Ls!(j-1))"
        using SpLs_nth_lt[of "i" "Ls" "j"] a_i a_j \<open>j<i\<close> by auto
      have "v j \<sqsubseteq>\<^bsub>Ls ! (j-1)\<^esub> w j"
        using a_vw[of "j"] \<open>j<i\<close> a_j by auto
      then show ?thesis
        using b1 by auto
    qed
  next
    case False
    then show ?thesis
    proof -
      have a_j:"j\<in>{1..length Ls-1}"
        using \<open>j \<le> length SpLs\<^bsub>i\<^esub> Ls\<close> \<open>Suc 0 \<le> j\<close> a_i length_minus_1' by auto
      have \<open>j\<ge>i\<close>
        using \<open>\<not>j<i\<close> by auto
      have b1:"((SpLs\<^bsub>i\<^esub> Ls) ! (j-1)) = (Ls!j)"
        using SpLs_nth_ge[of "i" "Ls" "j"] a_i a_j \<open>j\<ge>i\<close> by auto
      have "v j \<sqsubseteq>\<^bsub>Ls ! j\<^esub> w j"
        using a_vw[of "j"] \<open>j\<ge>i\<close> a_j by auto
      then show ?thesis
        using b1 by auto
    qed      
  qed
qed

lemma (in cart_prod_lattice) SpLs_le_implies:
  assumes a_v:"v\<in>carrier (\<Otimes>(SpLs\<^bsub>i\<^esub> Ls))"
    and a_w:"w\<in>carrier (\<Otimes>(SpLs\<^bsub>i\<^esub> Ls))"
    and a_vw:"v \<sqsubseteq>\<^bsub>\<Otimes>(SpLs\<^bsub>i\<^esub> Ls)\<^esub> w"
    and a_i:"i\<in>{1..length Ls}"
    and a_j:"j\<in>{1..length Ls-1}"
  shows "j<i \<Longrightarrow> v j\<sqsubseteq>\<^bsub>Ls!(j-1)\<^esub> w j"  
        "j\<ge>i \<Longrightarrow> v j\<sqsubseteq>\<^bsub>Ls!j \<^esub> w j"
proof -
  have \<open>j\<in>{1..length Ls}\<close>
    using a_j by auto
  have a_vw':"\<forall>j\<in>{1..length Ls-1}. v j \<sqsubseteq>\<^bsub>(SpLs\<^bsub>i\<^esub> Ls)!(j-1)\<^esub> w j"
    using a_vw length_minus_1' a_i unfolding cart_prod_def tuple_le_def by auto
  assume \<open>j<i\<close>
  show "v j\<sqsubseteq>\<^bsub>Ls!(j-1)\<^esub> w j"
    using a_vw' a_i \<open>j\<in>{1..length Ls}\<close> SpLs_nth_lt[of "i" "Ls" "j"] \<open>j<i\<close> by force
next
  have \<open>j\<in>{1..length Ls}\<close>
    using a_j by auto
  have a_vw':"\<forall>j\<in>{1..length Ls-1}. v j \<sqsubseteq>\<^bsub>(SpLs\<^bsub>i\<^esub> Ls)!(j-1)\<^esub> w j"
    using a_vw length_minus_1' a_i unfolding cart_prod_def tuple_le_def by auto
  assume \<open>i\<le>j\<close>
  show "v j \<sqsubseteq>\<^bsub>Ls ! j\<^esub> w j"
    using a_vw' a_i a_j SpLs_nth_ge[of "i" "Ls" "j"] \<open>i\<le>j\<close> by fastforce
qed

lemma (in cart_prod_lattice) n_to_two__le:
  assumes a_v:"v\<in>carrier (\<Otimes>Ls)"
  and a_w:"w\<in>carrier (\<Otimes>Ls)"
  and a_vw:"v\<sqsubseteq>\<^bsub>\<Otimes>Ls\<^esub> w"
  and a_i:"i\<in>{1..length Ls}"
shows "fst (n_to_two i v) \<sqsubseteq>\<^bsub>\<Otimes>(SpLs\<^bsub>i\<^esub> Ls)\<^esub> fst (n_to_two i w)"
      "snd (n_to_two i v) \<sqsubseteq>\<^bsub>(Ls!(i-1))\<^esub> snd (n_to_two i w)"
proof (rule SpLs_le_criterion)
  show "i\<in>{1..length Ls}"
    using a_i by auto
  show "fst (n_to_two i v) \<in> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
    using n_two__carrier(1)[of "v" "i"] carrier_spl_simp a_i a_v by auto
  show "fst (n_to_two i w) \<in> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
    using n_two__carrier(1)[of "w" "i"] carrier_spl_simp a_i a_w by auto
  fix j assume a_j:"j\<in>{1..length Ls-1}"
  have d1:"j < i \<Longrightarrow> fst (n_to_two i v) j \<sqsubseteq>\<^bsub>Ls ! (j-1)\<^esub> fst (n_to_two i w) j"
  proof -
    assume \<open>j<i\<close>
    have b1:"fst (n_to_two i v) j = v j"
      using n_to_two_simps_lt[of "j" "i" "v"] a_j \<open>j<i\<close> by auto
    have b2:"fst (n_to_two i w) j = w j"
      using n_to_two_simps_lt[of "j" "i" "w"] a_j \<open>j<i\<close> by auto
    have "v j \<sqsubseteq>\<^bsub>Ls ! (j-1)\<^esub> w j"
      using a_vw Ls_le_criterion a_j by auto
    then show ?thesis
      using b1 b2 by auto
  qed
  have d2:"i \<le> j \<Longrightarrow> fst (n_to_two i v) j \<sqsubseteq>\<^bsub>Ls ! j\<^esub> fst (n_to_two i w) j"
  proof -
    assume \<open>i \<le> j\<close>
    have b1:"fst (n_to_two i v) j = v (j+1)"
      using n_to_two_simps_geq[of "j" "i" "v"] a_j \<open>i \<le> j\<close> by auto
    have b2:"fst (n_to_two i w) j = w (j+1)"
      using n_to_two_simps_geq[of "j" "i" "w"] a_j \<open>i \<le> j\<close> by auto
    have \<open>j+1\<in>{1..length Ls}\<close>
      using a_j by auto
    have "v (j+1) \<sqsubseteq>\<^bsub>Ls ! j\<^esub> w (j+1)"
      using a_vw Ls_le_criterion a_j \<open>j+1\<in>{1..length Ls}\<close> 
      by (metis add.commute add_diff_cancel_left')
    then show ?thesis
      using b1 b2 by auto
  qed
  show "(j < i \<longrightarrow> fst (n_to_two i v) j \<sqsubseteq>\<^bsub>Ls ! (j-1)\<^esub> fst (n_to_two i w) j) \<and> (i \<le> j \<longrightarrow> fst (n_to_two i v) j \<sqsubseteq>\<^bsub>Ls ! j\<^esub> fst (n_to_two i w) j)"
    using d1 d2 by auto
next
  have "v i \<sqsubseteq>\<^bsub>Ls ! (i-1)\<^esub> w i"
    using Ls_le_criterion a_i a_vw by auto
  then show "snd (n_to_two i v) \<sqsubseteq>\<^bsub>Ls ! (i-1)\<^esub> snd (n_to_two i w)"
    using n_to_two_simps_snd by auto
qed

lemma hat_j_prod_locale_external:
  assumes "cart_prod_lattice Ls"
  shows "length Ls > 1 \<Longrightarrow> j\<in>{1..length Ls} \<Longrightarrow> cart_prod_lattice (Sp_Ls j Ls)"
  unfolding Sp_Ls_def
proof (rule cart_prod_lattice.intro)
  interpret base_locale: cart_prod_lattice "Ls"
    using assms by auto
  show "1 < length Ls \<Longrightarrow> j \<in> {1..length Ls} \<Longrightarrow> 0 < length (remove_at (j - 1) Ls)"    
    using length_minus_1[of "j" "Ls"] by auto
next
  fix i assume \<open>1<length Ls\<close> and a_j:\<open>j\<in>{1..length Ls}\<close> and a_i:\<open>i\<in>{1..length (remove_at (j - 1) Ls)}\<close>
  then show "complete_lattice (remove_at (j - 1) Ls ! (i-1))"
    using cart_prod_lattice.remove_at_comp_lat[of "Ls" "j" "i"] length_minus_1[of "j" "Ls"] a_i a_j assms by auto
qed

lemma (in cart_prod_lattice) hat_j_prod_locale:
  "length Ls > 1 \<Longrightarrow> j\<in>{1..length Ls} \<Longrightarrow> cart_prod_lattice (Sp_Ls j Ls)"
  apply (rule cart_prod_lattice.intro)
  unfolding Sp_Ls_def 
  using length_minus_1[of "j" "Ls"] remove_at_comp_lat[of "j"] by auto

lemma (in cart_prod_lattice) two_to_n__le:
  assumes a_v:"v\<in>carrier (\<Otimes>SpLs\<^bsub>i\<^esub> Ls)"
    and a_w:"w\<in>carrier (\<Otimes>SpLs\<^bsub>i\<^esub> Ls)"
    and ai_car:"ai\<in>carrier (Ls!(i-1))"
    and bi_car:"bi\<in>carrier (Ls!(i-1))"
    and a_vw:"v \<sqsubseteq>\<^bsub>\<Otimes>SpLs\<^bsub>i\<^esub> Ls\<^esub> w"
    and a_ab:"ai \<sqsubseteq>\<^bsub>Ls!(i-1)\<^esub> bi"
    and a_i:"i\<in>{1..length Ls}"
  shows "two_to_n i (v,ai) \<sqsubseteq>\<^bsub>\<Otimes>Ls\<^esub> two_to_n i (w,bi)"
proof -
  have "\<forall>ia\<in>{1..length Ls}. two_to_n i (v, ai) ia \<sqsubseteq>\<^bsub>Ls ! (ia-1)\<^esub> two_to_n i (w, bi) ia"
  proof
    fix j assume a_j:"j\<in>{1..length Ls}"
    show "two_to_n i (v, ai) j \<sqsubseteq>\<^bsub>Ls ! (j-1)\<^esub> two_to_n i (w, bi) j"
    proof (cases "j<i")
      case True
      then show ?thesis
        using two_to_n_simps(2) a_v a_w a_vw \<open>j<i\<close> a_i a_j carrier_spl_simp[of "i" "Ls"] a_vw
              SpLs_le_implies(1)[of "v" "i" "w" "j"] ai_car bi_car
        by auto
    next
      case False
      then show ?thesis
      proof (cases "i=j")
        case True
        then show ?thesis
          using two_to_n_simps(1) a_v a_w ai_car bi_car a_i a_j a_ab carrier_spl_simp by metis
      next
        case False
        then show ?thesis
        proof -
          have \<open>i<j\<close> 
            using \<open>i \<noteq> j\<close> \<open>\<not> j < i\<close> by auto
          have b1:"two_to_n i (v, ai) j = v (j-1)"
            using two_to_n_simps(3) a_v ai_car carrier_spl_simp a_i a_j \<open>i<j\<close> by blast
          have b2:"two_to_n i (w, bi) j = w (j-1)"
            using two_to_n_simps(3) a_w bi_car carrier_spl_simp a_i a_j \<open>i<j\<close> by blast
          have "v (j-1) \<sqsubseteq>\<^bsub>Ls ! (j-1)\<^esub> w (j-1)"
            using SpLs_le_implies(2)[of "v" "i" "w" "j-1"] a_vw a_i a_j \<open>i<j\<close> a_v a_w by auto
          then show ?thesis
            using b1 b2 by auto
        qed
      qed
    qed
  qed
  then show ?thesis
    using Ls_le_criterion[of "two_to_n i (v, ai)" "two_to_n i (w, bi)"] by auto
qed

(* Given F:L1\<times>...\<times>Ln, and ai\<in>Li, returns (SpF)(x1,...,\hat xi,...,xn) =(F1(x1,...,ai,...,xn),...,\hat Fi,...,Fn(x1,...,ai,...,xn)) *)
definition (in cart_prod_lattice) specialize_fn:: "nat \<Rightarrow> 'a \<Rightarrow> ((nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)) \<Rightarrow> ((nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a))" (\<open>Sp\<^bsub>_,_\<^esub> _\<close>) where
  "specialize_fn i ai f = (\<lambda>v \<in> carrier_spl Ls i. (\<lambda>(j::nat)\<in>{1..length Ls-1}. if j<i then (Pr\<^bsub>j\<^esub> f) (two_to_n i (v,ai)) else (Pr\<^bsub>j+1\<^esub> f) (two_to_n i (v,ai))))"

lemma (in cart_prod_lattice) specialize_fn_simps:
  "v \<in> carrier_spl Ls i \<Longrightarrow> j\<in>{1..length Ls - 1} \<Longrightarrow> j<i \<Longrightarrow> (Sp\<^bsub>i,ai\<^esub> f) v j = (Pr\<^bsub>j\<^esub> f) (two_to_n i (v,ai))"
  "v \<in> carrier_spl Ls i \<Longrightarrow> j\<in>{1..length Ls - 1} \<Longrightarrow> j\<ge>i \<Longrightarrow> (Sp\<^bsub>i,ai\<^esub> f) v j = (Pr\<^bsub>j+1\<^esub> f) (two_to_n i (v,ai))"
  unfolding specialize_fn_def by auto

lemma (in cart_prod_lattice) specialize_fn_carrier:
  assumes f_wd:"f\<in> carrier (\<Otimes>Ls) \<rightarrow> carrier (\<Otimes>Ls)"
  shows
  "v \<in> carrier_spl Ls i \<Longrightarrow> i\<in>{1..length Ls} \<Longrightarrow> ai\<in>carrier (Ls!(i-1)) \<Longrightarrow> j\<in>{1..length Ls - 1} \<Longrightarrow> j<i \<Longrightarrow> (Sp\<^bsub>i,ai\<^esub> f) v j \<in> carrier (Ls ! (j-1))"
  "v \<in> carrier_spl Ls i \<Longrightarrow> i\<in>{1..length Ls} \<Longrightarrow> ai\<in>carrier (Ls!(i-1)) \<Longrightarrow> j\<in>{1..length Ls - 1} \<Longrightarrow> j\<ge>i \<Longrightarrow> (Sp\<^bsub>i,ai\<^esub> f) v j \<in> carrier (Ls ! j)"
  "v \<in> carrier_spl Ls i \<Longrightarrow> j\<notin>{1..length Ls - 1} \<Longrightarrow> (Sp\<^bsub>i,ai\<^esub> f) v j = undefined"
proof -
  assume a_v:"v\<in>carrier_spl Ls i" and a_j:"j\<in>{1..length Ls-1}" and a_i:"i\<in>{1..length Ls}" and ai_car:"ai\<in>carrier (Ls!(i-1))" and \<open>j<i\<close>
  have a_j':"j\<in>{1..length Ls}"
    using a_j by auto
  have b1:"Sp\<^bsub>i,ai\<^esub> f v j = (Pr\<^bsub>j\<^esub> f) (two_to_n i (v,ai))"
    using specialize_fn_simps a_v a_j \<open>j<i\<close> by auto
  have "two_to_n i (v,ai) \<in> carrier (\<Otimes>Ls)"
    using two_n__carrier[of "i" "v" "ai"] a_v a_i ai_car by auto
  then have "f (two_to_n i (v,ai)) \<in> carrier (\<Otimes>Ls)"
    using f_wd by auto
  then have b2:"f (two_to_n i (v,ai)) j \<in> carrier (Ls ! (j-1))"
    using cart_carrier_iff a_j' by blast
  have "(Pr\<^bsub>j\<^esub> f) (two_to_n i (v,ai)) = f (two_to_n i (v,ai)) j"
    unfolding proj_def by auto
  then show "(Sp\<^bsub>i,ai\<^esub> f) v j \<in> carrier (Ls ! (j-1))"
    using b1 b2 by auto
next
  assume a_v:"v\<in>carrier_spl Ls i" and a_j:"j\<in>{1..length Ls-1}" and a_i:"i\<in>{1..length Ls}" and ai_car:"ai\<in>carrier (Ls!(i-1))" and \<open>j\<ge>i\<close>
  have a_j':"j+1\<in>{1..length Ls}"
    using a_j by auto
  have b1:"Sp\<^bsub>i,ai\<^esub> f v j = (Pr\<^bsub>j+1\<^esub> f) (two_to_n i (v,ai))"
    using specialize_fn_simps a_v a_j \<open>j\<ge>i\<close> by auto
  have "two_to_n i (v,ai) \<in> carrier (\<Otimes>Ls)"
    using two_n__carrier[of "i" "v" "ai"] a_v a_i ai_car by auto
  then have "f (two_to_n i (v,ai)) \<in> carrier (\<Otimes>Ls)"
    using f_wd by auto
  then have b2:"f (two_to_n i (v,ai)) (j+1) \<in> carrier (Ls!j)"
    using cart_carrier_iff a_j' 
    by (metis (no_types, opaque_lifting) add.commute add_diff_cancel_left')
  have "(Pr\<^bsub>j+1\<^esub> f) (two_to_n i (v,ai)) = f (two_to_n i (v,ai)) (j+1)"
    unfolding proj_def by auto
  then show "(Sp\<^bsub>i,ai\<^esub> f) v j \<in> carrier (Ls ! j)"
    using b1 b2 by auto
next
  assume a_v:"v\<in>carrier_spl Ls i" and \<open>j \<notin> {1..length Ls - 1}\<close>
  then show "Sp\<^bsub>i,ai\<^esub> f v j = undefined"
    unfolding specialize_fn_def by auto
qed

lemma (in cart_prod_lattice) in_carrier_spl_I': "i\<in>{1..length Ls}
  \<Longrightarrow> ((\<And>h. h \<in> {1..length Ls - 1} \<Longrightarrow> (h < i \<longrightarrow> v h \<in> carrier (Ls ! (h-1))) \<and> (i \<le> h \<longrightarrow> v h \<in> carrier (Ls ! h))))
  \<Longrightarrow> (\<And>y. y\<notin>{1..length Ls-1} \<Longrightarrow> v y = undefined)
  \<Longrightarrow> v\<in>carrier (\<Otimes>(SpLs\<^bsub>i\<^esub> Ls))"
  using carrier_spl_simp in_carrier_spl_I by blast

lemma (in cart_prod_lattice) specialize_fn_n_two:
  assumes a_i:"i\<in>{1..length Ls}"
      and a_len: "length Ls > 1"
      and a_v:"v\<in>carrier_spl Ls i"
      and ai_car:"ai\<in>carrier (Ls!(i-1))"
      and a_f:"f\<in>carrier (\<Otimes>Ls) \<rightarrow> carrier (\<Otimes>Ls)"
    shows "(Sp\<^bsub>i,ai\<^esub> f) v = fst (n_to_two i (f (two_to_n i (v, ai))))"
proof -
  interpret i_sub_locale: cart_prod_lattice "SpLs\<^bsub>i\<^esub> Ls"
    using hat_j_prod_locale a_len a_i by auto
  show "specialize_fn i ai f v = fst (n_to_two i (f (two_to_n i (v, ai))))"
  proof (rule i_sub_locale.vect_eqI)
    show "(Sp\<^bsub>i,ai\<^esub> f) v \<in> carrier (\<Otimes>(SpLs\<^bsub>i\<^esub> Ls))"
    proof (rule in_carrier_spl_I')
      show "i\<in>{1..length Ls}"
        using a_i by auto
    next
      fix h assume a_h:\<open>h \<in> {1..length Ls - 1}\<close>
      have b1:"h<i \<Longrightarrow> (Sp\<^bsub>i,ai\<^esub> f) v h \<in> carrier (Ls ! (h-1))"
        using specialize_fn_carrier(1) a_f a_v a_i ai_car a_h by blast
      have b2:"i \<le> h \<Longrightarrow> Sp\<^bsub>i,ai\<^esub> f v h \<in> carrier (Ls ! h)"
        using specialize_fn_carrier(2) a_f a_v a_i ai_car a_h by blast
      show "(h < i \<longrightarrow> Sp\<^bsub>i,ai\<^esub> f v h \<in> carrier (Ls ! (h-1))) \<and> (i \<le> h \<longrightarrow> Sp\<^bsub>i,ai\<^esub> f v h \<in> carrier (Ls ! h))"
        using b1 b2 by auto
    next
      fix h assume a_h:"h \<notin> {1..length Ls - 1}"
      then show "Sp\<^bsub>i,ai\<^esub> f v h = undefined"
        using specialize_fn_carrier(3) a_v a_f by blast
    qed
  next
    show "fst (n_to_two i (f (two_to_n i (v, ai)))) \<in> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
    proof -
      have "(two_to_n i (v, ai)) \<in> carrier (\<Otimes>Ls)"
        using two_n__carrier a_i a_v ai_car by auto
      then have "f (two_to_n i (v, ai)) \<in> carrier (\<Otimes>Ls)"
        using a_f by auto
      then have "fst (n_to_two i (f (two_to_n i (v, ai)))) \<in> carrier_spl Ls i"
        using n_two__carrier(1)[of "f (two_to_n i (v, ai))"] a_v a_i by auto  
      then show "fst (n_to_two i (f (two_to_n i (v, ai)))) \<in> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
        using carrier_spl_simp by auto
    qed
  next
    fix h assume "h\<in>{1..length SpLs\<^bsub>i\<^esub> Ls}"
    then have a_h:"h\<in>{1..length Ls-1}"
      using a_i length_minus_1' by auto
    show "Sp\<^bsub>i,ai\<^esub> f v h = fst (n_to_two i (f (two_to_n i (v, ai)))) h"
    proof (cases "h<i")
      case True
      then show ?thesis
      proof -
        have b1:"fst (n_to_two i (f (two_to_n i (v, ai)))) h = f (two_to_n i (v, ai)) h"
          using n_to_two_simps_lt a_h \<open>h<i\<close> by auto
        have "Sp\<^bsub>i,ai\<^esub> f v h = Pr\<^bsub>h\<^esub> f (two_to_n i (v, ai))"
          using specialize_fn_simps(1)[of "v" "i" "h" "ai" "f" ] a_v a_h \<open>h<i\<close> by auto
        also have "... = f (two_to_n i (v, ai)) h"
          unfolding proj_def by auto
        finally show "Sp\<^bsub>i,ai\<^esub> f v h = fst (n_to_two i (f (two_to_n i (v, ai)))) h"
          using b1 by auto
      qed
    next
      case False
      then show ?thesis
      proof -
        have \<open>h\<ge>i\<close>
          using \<open>\<not>h<i\<close> by auto
        have b1:"fst (n_to_two i (f (two_to_n i (v, ai)))) h = f (two_to_n i (v, ai)) (h+1)"
          using n_to_two_simps_geq a_h \<open>h\<ge>i\<close> by auto
        have "Sp\<^bsub>i,ai\<^esub> f v h = Pr\<^bsub>h+1\<^esub> f (two_to_n i (v, ai))"
          using specialize_fn_simps(2)[of "v" "i" "h" "ai" "f" ] a_v a_h \<open>h\<ge>i\<close> by auto
        also have "... = f (two_to_n i (v, ai)) (h+1)"
          unfolding proj_def by auto
        finally show "Sp\<^bsub>i,ai\<^esub> f v h = fst (n_to_two i (f (two_to_n i (v, ai)))) h"
          using b1 by auto
      qed
    qed
  qed
qed

lemma (in cart_prod_lattice) specialize_fn_vec_carrier:
  assumes a_i:"i\<in>{1..length Ls}"
      and a_len: "length Ls > 1"
      and a_v:"v\<in>carrier_spl Ls i"
      and ai_car:"ai\<in>carrier (Ls!(i-1))"
      and a_f:"f\<in>carrier (\<Otimes>Ls) \<rightarrow> carrier (\<Otimes>Ls)"
    shows "(Sp\<^bsub>i,ai\<^esub> f) v \<in> carrier (\<Otimes>SpLs\<^bsub>i\<^esub> Ls)"
proof -
  have b1:"Sp\<^bsub>i,ai\<^esub> f v = fst (n_to_two i (f (two_to_n i (v, ai))))"
    using assms specialize_fn_n_two by auto
  have "two_to_n i (v, ai) \<in> carrier (\<Otimes>Ls)"
    using two_n__carrier a_i a_v ai_car by auto
  then have "f (two_to_n i (v, ai)) \<in> carrier (\<Otimes>Ls)"
    using a_f by auto
  then have "fst (n_to_two i (f (two_to_n i (v, ai)))) \<in> carrier_spl Ls i"
    using n_two__carrier(1) a_v a_i by auto
  then show ?thesis
    using b1 carrier_spl_simp by auto
qed

lemma (in cart_prod_lattice) specialize_fn_funcset:
  assumes a_i:"i\<in>{1..length Ls}"
      and a_len: "length Ls > 1"
      and ai_car:"ai\<in>carrier (Ls!(i-1))"
      and a_f:"f\<in>carrier (\<Otimes>Ls) \<rightarrow> carrier (\<Otimes>Ls)"
    shows "(Sp\<^bsub>i,ai\<^esub> f) \<in> carrier (\<Otimes>SpLs\<^bsub>i\<^esub> Ls) \<rightarrow> carrier (\<Otimes>SpLs\<^bsub>i\<^esub> Ls)"
  using specialize_fn_vec_carrier carrier_spl_simp assms by blast

lemma (in cart_prod_lattice) specialize_fn_ext:
  assumes a_i:"i\<in>{1..length Ls}"
      and a_len: "length Ls > 1"
      and ai_car:"ai\<in>carrier (Ls!(i-1))"
    shows "(Sp\<^bsub>i,ai\<^esub> f) \<in> extensional (carrier (\<Otimes>SpLs\<^bsub>i\<^esub> Ls))"
  unfolding extensional_def specialize_fn_def carrier_spl_simp by auto

lemma (in cart_prod_lattice) specialize_fn_PiE:
  assumes a_i:"i\<in>{1..length Ls}"
      and a_len: "length Ls > 1"
      and ai_car:"ai\<in>carrier (Ls!(i-1))"
      and a_f:"f\<in>carrier (\<Otimes>Ls) \<rightarrow> carrier (\<Otimes>Ls)"
    shows "(Sp\<^bsub>i,ai\<^esub> f) \<in> carrier (\<Otimes>SpLs\<^bsub>i\<^esub> Ls) \<rightarrow>\<^sub>E carrier (\<Otimes>SpLs\<^bsub>i\<^esub> Ls)"
proof 
  show "\<And>x. x \<in> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls \<Longrightarrow> Sp\<^bsub>i,ai\<^esub> f x \<in> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
  proof -
    have "(Sp\<^bsub>i,ai\<^esub> f) \<in> carrier (\<Otimes>SpLs\<^bsub>i\<^esub> Ls) \<rightarrow> carrier (\<Otimes>SpLs\<^bsub>i\<^esub> Ls)"
      using specialize_fn_funcset[of "i" "ai" "f"] assms by auto
    then show "\<And>x. x \<in> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls \<Longrightarrow> Sp\<^bsub>i,ai\<^esub> f x \<in> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
      by auto
  qed
  show "\<And>x. x \<notin> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls \<Longrightarrow> Sp\<^bsub>i,ai\<^esub> f x = undefined"
    using specialize_fn_ext assms unfolding extensional_def by blast
qed


lemma (in cart_prod_lattice) mono_specialize_mono:
  assumes f_wd:"F\<in> carrier (\<Otimes>Ls) \<rightarrow> carrier (\<Otimes>Ls)"
  and a_i:"i\<in>{1..length Ls}"
  and a_len: "length Ls > 1"
  and ai_car: "ai\<in>carrier (Ls!(i-1))"
  and f_mono:"Mono\<^bsub>\<Otimes>Ls\<^esub> F"
shows "Mono\<^bsub>\<Otimes>(SpLs\<^bsub>i\<^esub> Ls)\<^esub> (Sp\<^bsub>i,ai\<^esub> F)"
proof
  interpret hat_i_sublocale: cart_prod_lattice "(SpLs\<^bsub>i\<^esub> Ls)"
    using hat_j_prod_locale a_len a_i by auto
  show "weak_partial_order \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
    using hat_i_sublocale.weak_partial_order_axioms by auto
  show "weak_partial_order \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
    using hat_i_sublocale.weak_partial_order_axioms by auto
  fix x y assume a_x:"x \<in> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls" and a_y:"y \<in> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
    and a_xy:"x \<sqsubseteq>\<^bsub>\<Otimes>SpLs\<^bsub>i\<^esub> Ls\<^esub> y"
  show "(Sp\<^bsub>i,ai\<^esub> F) x \<sqsubseteq>\<^bsub>\<Otimes>SpLs\<^bsub>i\<^esub> Ls\<^esub> (Sp\<^bsub>i,ai\<^esub> F) y"
  proof -
    have "(Sp\<^bsub>i,ai\<^esub> F) x \<sqsubseteq>\<^bsub>\<Otimes>SpLs\<^bsub>i\<^esub> Ls\<^esub> (Sp\<^bsub>i,ai\<^esub> F) y"
    proof (rule SpLs_le_criterion)
      show "i \<in> {1..length Ls}"
        using a_i by auto
      show "(Sp\<^bsub>i,ai\<^esub> F) y \<in> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
        using specialize_fn_vec_carrier[of "i" "y"] a_i a_len f_wd ai_car a_y carrier_spl_simp[of "i" "Ls"] by auto
      show "(Sp\<^bsub>i,ai\<^esub> F) x \<in> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
        using specialize_fn_vec_carrier[of "i" "x"] a_i a_len f_wd ai_car a_x carrier_spl_simp[of "i" "Ls"] by auto
      fix j assume a_j:"j\<in>{1..length Ls - 1}"
      have d1:"j < i \<Longrightarrow> Sp\<^bsub>i,ai\<^esub> F x j \<sqsubseteq>\<^bsub>Ls ! (j-1)\<^esub> Sp\<^bsub>i,ai\<^esub> F y j"
      proof -
        assume \<open>j<i\<close>
        have b3:"(Sp\<^bsub>i,ai\<^esub> F) x j = F (two_to_n i (x, ai)) j"
          using specialize_fn_simps(1)[of "x" "i" "j" "ai" "F"] a_x a_j \<open>j<i\<close> carrier_spl_simp unfolding proj_def by auto
        have b4:"(Sp\<^bsub>i,ai\<^esub> F) y j = F (two_to_n i (y, ai)) j"
          using specialize_fn_simps(1)[of "y" "i" "j" "ai" "F"] a_y a_j \<open>j<i\<close> carrier_spl_simp unfolding proj_def by auto
        have b1:"two_to_n i (x, ai) \<in> carrier (\<Otimes>Ls)"
          using two_n__carrier a_i a_x ai_car carrier_spl_simp by blast
        have b2:"two_to_n i (y, ai) \<in> carrier (\<Otimes>Ls)"
          using two_n__carrier a_i a_y ai_car carrier_spl_simp by blast
        have "two_to_n i (x, ai) \<sqsubseteq>\<^bsub>\<Otimes>Ls\<^esub> two_to_n i (y, ai)"
          using two_to_n__le[of "x" "i" "y" "ai" "ai"] a_x a_y ai_car a_xy a_i by (metis Ls_comp_lat complete_lattice_le_refl)
        then have "F (two_to_n i (x, ai)) \<sqsubseteq>\<^bsub>\<Otimes>Ls\<^esub> F (two_to_n i (y, ai))"
          using f_mono b1 b2 use_iso1 by force
        then show ?thesis
          using b3 b4 Ls_le_criterion a_j by auto
      qed
      have d2:"j \<ge> i \<Longrightarrow> Sp\<^bsub>i,ai\<^esub> F x j \<sqsubseteq>\<^bsub>Ls ! j\<^esub> Sp\<^bsub>i,ai\<^esub> F y j"
      proof -
        assume \<open>j \<ge> i\<close>
        have \<open>j+1 \<in> {1..length Ls}\<close>
          using a_j by auto
        have b3:"(Sp\<^bsub>i,ai\<^esub> F) x j = F (two_to_n i (x, ai)) (j+1)"
          using specialize_fn_simps(2)[of "x" "i" "j" "ai" "F"] a_x a_j \<open>j \<ge> i\<close> carrier_spl_simp unfolding proj_def by auto
        have b4:"(Sp\<^bsub>i,ai\<^esub> F) y j = F (two_to_n i (y, ai)) (j+1)"
          using specialize_fn_simps(2)[of "y" "i" "j" "ai" "F"] a_y a_j \<open>j \<ge> i\<close> carrier_spl_simp unfolding proj_def by auto
        have b1:"two_to_n i (x, ai) \<in> carrier (\<Otimes>Ls)"
          using two_n__carrier a_i a_x ai_car carrier_spl_simp by blast
        have b2:"two_to_n i (y, ai) \<in> carrier (\<Otimes>Ls)"
          using two_n__carrier a_i a_y ai_car carrier_spl_simp by blast
        have "two_to_n i (x, ai) \<sqsubseteq>\<^bsub>\<Otimes>Ls\<^esub> two_to_n i (y, ai)"
          using two_to_n__le[of "x" "i" "y" "ai" "ai"] a_x a_y ai_car a_xy a_i by (metis Ls_comp_lat complete_lattice_le_refl)
        then have "F (two_to_n i (x, ai)) \<sqsubseteq>\<^bsub>\<Otimes>Ls\<^esub> F (two_to_n i (y, ai))"
          using f_mono b1 b2 use_iso1 by force
        then show ?thesis
          using b3 b4 Ls_le_criterion a_j \<open>j+1 \<in> {1..length Ls}\<close> add_diff_cancel_right'
          by metis
      qed
      show "(j < i \<longrightarrow> Sp\<^bsub>i,ai\<^esub> F x j \<sqsubseteq>\<^bsub>Ls ! (j-1)\<^esub> Sp\<^bsub>i,ai\<^esub> F y j) \<and> (i \<le> j \<longrightarrow> Sp\<^bsub>i,ai\<^esub> F x j \<sqsubseteq>\<^bsub>Ls ! j\<^esub> Sp\<^bsub>i,ai\<^esub> F y j)"
        using d1 d2 by auto
    qed
    then show "Sp\<^bsub>i,ai\<^esub> F x \<sqsubseteq>\<^bsub>\<Otimes>SpLs\<^bsub>i\<^esub> Ls\<^esub> Sp\<^bsub>i,ai\<^esub> F y"
      by auto
  qed
qed

lemma (in cart_prod_lattice) mono_proj_iso:
  assumes f_wd:"F\<in> carrier (\<Otimes>Ls) \<rightarrow> carrier (\<Otimes>Ls)"
  and a_i:"i\<in>{1..length Ls}"
  and f_mono:"Mono\<^bsub>\<Otimes>Ls\<^esub> F"
shows "isotone (\<Otimes>Ls) (Ls!(i-1)) (Pr\<^bsub>i\<^esub> F)"
proof
  show "weak_partial_order \<Otimes>Ls"
    by (simp add: weak_partial_order_axioms)
  show "weak_partial_order (Ls ! (i-1))"
    using Ls_comp_lat a_i complete_lattice_po partial_order.axioms(1) by blast
  fix x y assume \<open>x\<in>carrier (\<Otimes>Ls)\<close> and \<open>y\<in>carrier (\<Otimes>Ls)\<close> and \<open>x \<sqsubseteq>\<^bsub>\<Otimes>Ls\<^esub> y\<close>
  show "(Pr\<^bsub>i\<^esub> F) x \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> (Pr\<^bsub>i\<^esub> F) y"
  proof -
    have "F x \<sqsubseteq>\<^bsub>\<Otimes>Ls\<^esub> F y"
      using f_mono use_iso1 \<open>x\<in>carrier (\<Otimes>Ls)\<close> \<open>y\<in>carrier (\<Otimes>Ls)\<close> \<open>x \<sqsubseteq>\<^bsub>\<Otimes>Ls\<^esub> y\<close> by fastforce
    then show ?thesis 
      unfolding proj_def using a_i Ls_le_criterion by blast
  qed
qed

lemma (in cart_prod_lattice) mono_proj_lam_mono:
  assumes f_wd:"F\<in> carrier (\<Otimes>Ls) \<rightarrow> carrier (\<Otimes>Ls)"
  and a_i:"i\<in>{1..length Ls}"
  and f_mono:"Mono\<^bsub>\<Otimes>Ls\<^esub> F"
  and v_car: "v\<in> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
shows "Mono\<^bsub>(Ls ! (i-1))\<^esub> (\<lambda>x\<in>carrier (Ls ! (i-1)). (Pr\<^bsub>i\<^esub> F) (two_to_n i (v,x)))"
proof 
  show "weak_partial_order (Ls ! (i-1))"
    using Ls_comp_lat a_i complete_lattice_po partial_order.axioms(1) by blast
  show "weak_partial_order (Ls ! (i-1))"
    using Ls_comp_lat a_i complete_lattice_po partial_order.axioms(1) by blast
next
  fix x y assume a_x:"x\<in>carrier (Ls ! (i-1))" and a_y:"y\<in>carrier (Ls ! (i-1))" and a_xy:"x \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> y"
  show "(\<lambda>x\<in>carrier (Ls ! (i - 1)). Pr\<^bsub>i\<^esub> F (two_to_n i (v, x))) x \<sqsubseteq>\<^bsub>Ls ! (i - 1)\<^esub> (\<lambda>x\<in>carrier (Ls ! (i - 1)). Pr\<^bsub>i\<^esub> F (two_to_n i (v, x))) y"
  (is "?l \<sqsubseteq>\<^bsub>Ls ! (i-1)\<^esub> ?r")
  proof -
    have b_x:"two_to_n i (v, x) \<in> carrier (\<Otimes>Ls)"
      using two_n__carrier[OF a_i] v_car a_x unfolding carrier_spl_simp by auto
    have b_y:"two_to_n i (v, y) \<in> carrier (\<Otimes>Ls)"
      using two_n__carrier[OF a_i] v_car a_y unfolding carrier_spl_simp by auto    
    have eql:"?l = (Pr\<^bsub>i\<^esub> F) (two_to_n i (v, x))"
      using a_x by auto
    have eqr:"?r = (Pr\<^bsub>i\<^esub> F) (two_to_n i (v, y))"
      using a_y by auto
    have iso_proj_F:"isotone \<Otimes>Ls (Ls ! (i-1)) Pr\<^bsub>i\<^esub> F"
      using mono_proj_iso[OF f_wd a_i f_mono] by auto
    have "(two_to_n i (v, x)) \<sqsubseteq>\<^bsub>\<Otimes>Ls\<^esub> (two_to_n i (v, y))"
      using two_to_n__le[OF v_car v_car a_x a_y] a_xy a_i 
      by (metis a_y carrier_spl_simp fst_conv n_to_two__le(1) n_two__two_n_id two_n__carrier v_car weak_partial_order.le_refl weak_partial_order_axioms)
    then have "(Pr\<^bsub>i\<^esub> F) (two_to_n i (v, x)) \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> (Pr\<^bsub>i\<^esub> F) (two_to_n i (v, y))"
      using iso_proj_F use_iso2[of "\<Otimes>Ls" "(Ls ! (i-1))" "Pr\<^bsub>i\<^esub> F" "two_to_n i (v, x)" "two_to_n i (v, y)"] b_x b_y by auto
    then show ?thesis
      using eql eqr by auto
  qed
qed

lemma (in cart_prod_lattice) mono_proj_lam_mono_app:
  assumes f_wd:"F\<in> carrier (\<Otimes>Ls) \<rightarrow> carrier (\<Otimes>Ls)"
  and a_i:"i\<in>{1..length Ls}"
  and f_mono:"Mono\<^bsub>\<Otimes>Ls\<^esub> F"
  and v_car: "v\<in> carrier (Ls ! (i-1)) \<rightarrow> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
  and v_mono: "\<And>x y. x\<in>carrier (Ls ! (i-1)) \<Longrightarrow> y\<in>carrier (Ls ! (i-1)) \<Longrightarrow> x \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> y \<Longrightarrow> v x \<sqsubseteq>\<^bsub>\<Otimes>SpLs\<^bsub>i\<^esub> Ls\<^esub> v y"
shows "Mono\<^bsub>(Ls ! (i-1))\<^esub> (\<lambda>x\<in>carrier (Ls ! (i-1)). (Pr\<^bsub>i\<^esub> F) (two_to_n i (v x, x)))"
proof 
  show "weak_partial_order (Ls ! (i-1))"
    using Ls_comp_lat a_i complete_lattice_po partial_order.axioms(1) by blast
  show "weak_partial_order (Ls ! (i-1))"
    using Ls_comp_lat a_i complete_lattice_po partial_order.axioms(1) by blast
  fix x y assume a_x:"x\<in>carrier (Ls ! (i-1))" and a_y:"y\<in>carrier (Ls ! (i-1))" and a_xy:"x \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> y"
  show "(\<lambda>x\<in>carrier (Ls ! (i-1)). (Pr\<^bsub>i\<^esub> F) (two_to_n i (v x, x))) x \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> (\<lambda>x\<in>carrier (Ls ! (i-1)). (Pr\<^bsub>i\<^esub> F) (two_to_n i (v x, x))) y"
  (is "?l \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> ?r")
  proof -
    have vx_vy: "v x \<sqsubseteq>\<^bsub>\<Otimes>SpLs\<^bsub>i\<^esub> Ls\<^esub> v y"
      using v_mono[OF a_x a_y a_xy] by auto
    have vx_car: "v x \<in>carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
      using v_car a_x by auto
    have vy_car: "v y \<in>carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
      using v_car a_y by auto
    have b_x:"two_to_n i (v x, x) \<in> carrier (\<Otimes>Ls)"
      using two_n__carrier[OF a_i] v_car a_x unfolding carrier_spl_simp by auto
    have b_y:"two_to_n i (v y, y) \<in> carrier (\<Otimes>Ls)"
      using two_n__carrier[OF a_i] v_car a_y unfolding carrier_spl_simp by auto    
    have eql:"?l = (Pr\<^bsub>i\<^esub> F) (two_to_n i (v x, x))"
      using a_x by auto
    have eqr:"?r = (Pr\<^bsub>i\<^esub> F) (two_to_n i (v y, y))"
      using a_y by auto
    have iso_proj_F:"isotone \<Otimes>Ls (Ls ! (i-1)) Pr\<^bsub>i\<^esub> F"
      using mono_proj_iso[OF f_wd a_i f_mono] by auto
    have "(two_to_n i (v x, x)) \<sqsubseteq>\<^bsub>\<Otimes>Ls\<^esub> (two_to_n i (v y, y))"
      using two_to_n__le[OF vx_car vy_car a_x a_y vx_vy] v_car a_xy a_i 
      by (metis a_y carrier_spl_simp fst_conv n_to_two__le(1) n_two__two_n_id two_n__carrier v_car weak_partial_order.le_refl weak_partial_order_axioms)
    then have "(Pr\<^bsub>i\<^esub> F) (two_to_n i (v x, x)) \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> (Pr\<^bsub>i\<^esub> F) (two_to_n i (v y, y))"
      using iso_proj_F use_iso2[of "\<Otimes>Ls" "(Ls ! (i-1))" "Pr\<^bsub>i\<^esub> F" "two_to_n i (v x, x)" "two_to_n i (v y, y)"] b_x b_y by auto
    then show ?thesis
      using eql eqr by auto
  qed
qed

lemma (in cart_prod_lattice) nested_subst_mono:
  assumes f_wd:"F\<in> carrier (\<Otimes>Ls) \<rightarrow> carrier (\<Otimes>Ls)"
  and a_i:"i\<in>{1..length Ls}"
  and a_j:"j\<in>{1..length Ls}"
  and a_x:"x\<in>carrier (Ls ! (j-1))"
  and a_y:"y\<in>carrier (Ls ! (j-1))"
  and a_xy:"x \<sqsubseteq>\<^bsub>(Ls ! (j-1))\<^esub> y"
  and a_ij: "i\<noteq>j"
  and a_Bi_undef: "B i = None"
  and f_mono:"Mono\<^bsub>\<Otimes>Ls\<^esub> F"
  and a_B_wd: "\<And>k. k\<in>{1..length Ls} \<Longrightarrow> B k \<noteq>None \<Longrightarrow> the (B k) \<in> carrier (Ls!(k-1))"
shows "nested Ls i (B(j\<mapsto>x)) F \<sqsubseteq>\<^bsub>Ls!(i-1)\<^esub> nested Ls i (B(j\<mapsto>y)) F"
  using assms
proof (induction "card {j\<in>{1..length Ls}. B j = None}" arbitrary:B i j rule:nat.induct)
  case zero
  then show ?case
    using a_i zero by auto
next
  case (Suc m)
  then show ?case
    (is "?l \<sqsubseteq>\<^bsub>Ls!(i-1)\<^esub> ?r")
  proof -
    have a_B':"(B(j \<mapsto> x)) i = None"
      using Suc by auto
    have a_B'':"(B(j \<mapsto> y)) i = None"
      using Suc by auto
    have eq_l1:"?l = LFP\<^bsub>Ls!(i-1)\<^esub> (\<lambda>xi\<in>carrier (Ls!(i-1)). (Pr\<^bsub>i\<^esub> F) (\<lambda>k\<in>{1..length Ls}. if k=i then xi else 
              (if (B(j\<mapsto>x)) k \<noteq> None then (the ((B(j\<mapsto>x)) k)) else nested Ls k (B(j\<mapsto>x, i \<mapsto> xi)) F)))"
      (is "?l = ?l1")
      using nested_simps_undefined[OF Suc.prems(2)] a_B' by blast
    have eq_r1:"?r = LFP\<^bsub>(Ls!(i-1))\<^esub> (\<lambda>xi\<in>carrier (Ls!(i-1)). (Pr\<^bsub>i\<^esub> F) (\<lambda>k\<in>{1..length Ls}. if k=i then xi else 
              (if (B(j\<mapsto>y)) k \<noteq> None then (the ((B(j\<mapsto>y)) k)) else nested Ls k (B(j\<mapsto>y, i \<mapsto> xi)) F)))"
      (is "?r = ?r1")
      using nested_simps_undefined[OF Suc.prems(2)] a_B'' by blast
    have other_case:"\<And>k z. z\<in>carrier (Ls!(i-1)) \<Longrightarrow> k\<in>{1..length Ls} \<Longrightarrow> k\<noteq>i \<Longrightarrow> k\<noteq>j \<Longrightarrow> B k = None \<Longrightarrow> nested Ls k (B(j\<mapsto>x, i \<mapsto> z)) F \<sqsubseteq>\<^bsub>Ls!(k-1)\<^esub> nested Ls k (B(j\<mapsto>y, i \<mapsto> z)) F"
    proof -
      fix k z assume a_z:"z\<in> carrier (Ls!(i-1))" and a_k:"k\<in>{1..length Ls}" and ki:"k\<noteq>i" and kj:"k\<noteq>j" and \<open>B k = None\<close>
      have b1:"m = card {j \<in> {1..length Ls}. (B(i\<mapsto>z)) j = None}"
      proof -
        have "\<And>j. j\<in>{1..length Ls} \<Longrightarrow> (((B(i\<mapsto>z)) j = None) = (j\<noteq>i \<and> B j = None))"
        proof 
          fix j assume a_j:"j \<in> {1..length Ls}" and \<open>(B(i \<mapsto> z)) j = None\<close>
          show "j \<noteq> i \<and> B j = None"
          proof
            show "j\<noteq>i" 
              using \<open>(B(i \<mapsto> z)) j = None\<close> by auto
            show "B j = None" 
              using \<open>(B(i \<mapsto> z)) j = None\<close> \<open>j\<noteq>i\<close> by auto
          qed
        next
          fix j assume a_j:"j\<in>{1..length Ls}" and \<open>j \<noteq> i \<and> B j = None\<close>
          show "(B(i \<mapsto> z)) j = None"
            using \<open>j \<noteq> i \<and> B j = None\<close> by auto
        qed
        then have "{j \<in> {1..length Ls}. (B(i\<mapsto>z)) j = None} = {j \<in> {1..length Ls}. j\<noteq>i \<and> B j = None}"
          by auto
        also have "... = {j \<in> {1..length Ls}. B j = None} \<inter> {j \<in> {1..length Ls}. j\<noteq>i}"
          by blast
        also have "... = {j \<in> {1..length Ls}. B j = None} - {i}"
          by auto
        finally have "{j \<in> {1..length Ls}. (B(i\<mapsto>z)) j = None} = {j \<in> {1..length Ls}. B j = None} - {i}"
          by simp
        then show ?thesis
          using \<open>Suc m = card {j \<in> {1..length Ls}. B j = None}\<close> Suc.prems(2,8) by force
      qed
      have b2:"F \<in> carrier \<Otimes>Ls \<rightarrow> carrier \<Otimes>Ls"
        using Suc by auto
      have \<open>(B(i \<mapsto> z)) k = None\<close>
        using \<open>B k = None\<close> \<open>k\<noteq>i\<close> by auto
      have b3:"\<And>k. k \<in> {1..length Ls} \<Longrightarrow> (B(i \<mapsto> z)) k \<noteq> None \<Longrightarrow> the ((B(i \<mapsto> z)) k) \<in> carrier (Ls ! (k-1))"
        using Suc.prems a_z 
        by (metis fun_upd_apply option.sel)
      from Suc.hyps(1)[OF b1 b2 \<open>k\<in>{1..length Ls}\<close> \<open>j\<in>{1..length Ls}\<close> \<open>x\<in>carrier (Ls!(j-1))\<close> \<open>y\<in>carrier (Ls!(j-1))\<close> \<open>x \<sqsubseteq>\<^bsub>(Ls!(j-1))\<^esub> y\<close> \<open>k\<noteq>j\<close> \<open>(B(i \<mapsto> z)) k = None\<close> \<open>Mono\<^bsub>\<Otimes>Ls\<^esub> F\<close>]
      show "nested Ls k (B(j\<mapsto>x, i \<mapsto> z)) F \<sqsubseteq>\<^bsub>Ls!(k-1)\<^esub> nested Ls k (B(j\<mapsto>y, i \<mapsto> z)) F"
        using \<open>i\<noteq>j\<close> fun_upd_twist b3 by metis
    qed
    
    have lem_carrier_x: "\<And>z. z\<in>(carrier (Ls!(i-1))) \<Longrightarrow> (\<lambda>k\<in>{1..length Ls}. if k=i then z else (if (B(j\<mapsto>x)) k \<noteq> None then (the ((B(j\<mapsto>x)) k)) else nested Ls k (B(j\<mapsto>x, i \<mapsto> z)) F)) \<in>carrier (\<Otimes>Ls)"
    proof -
      fix z assume a_z:"z\<in>carrier (Ls!(i-1))"
      let ?x = "(\<lambda>k\<in>{1..length Ls}. if k=i then z else (if (B(j\<mapsto>x)) k \<noteq> None then (the ((B(j\<mapsto>x)) k)) else nested Ls k (B(j\<mapsto>x, i \<mapsto> z)) F))"
      show "(\<lambda>k\<in>{1..length Ls}. if k=i then z else (if (B(j\<mapsto>x)) k \<noteq> None then (the ((B(j\<mapsto>x)) k)) else nested Ls k (B(j\<mapsto>x, i \<mapsto> z)) F)) \<in>carrier (\<Otimes>Ls)"
      proof (rule cart_carrier_criterion)
        fix h assume \<open>h\<notin>{1..length Ls}\<close>
        then show "(\<lambda>k\<in>{1..length Ls}. if k = i then z else if (B(j \<mapsto> x)) k \<noteq> None then the ((B(j \<mapsto> x)) k) else nested Ls k (B(j \<mapsto> x, i \<mapsto> z)) F) h = undefined"
          by auto
      next
        fix h assume \<open>h\<in>{1..length Ls}\<close>
        then show "(\<lambda>k\<in>{1..length Ls}. if k = i then z else if (B(j \<mapsto> x)) k \<noteq> None then the ((B(j \<mapsto> x)) k) else nested Ls k (B(j \<mapsto> x, i \<mapsto> z)) F) h \<in> carrier (Ls ! (h-1))"
        proof -
          have b1:"h=i \<Longrightarrow> z\<in>carrier (Ls!(i-1))"
            using a_z by auto
          have b2:"h\<noteq>i \<Longrightarrow> (B(j \<mapsto> x)) h \<noteq> None \<Longrightarrow> the ((B(j \<mapsto> x)) h) \<in> carrier (Ls ! (h-1))"
            using Suc.prems(10) 
            by (metis Suc.prems(4) \<open>h \<in> {1..length Ls}\<close> fun_upd_apply option.sel)
          have b3:"h\<noteq>i \<Longrightarrow> (B(j \<mapsto> x)) h = None \<Longrightarrow> nested Ls h (B(j \<mapsto> x, i \<mapsto> z)) F \<in> carrier (Ls ! (h-1))"
            using nested_closed 
            by (metis \<open>h \<in> {1..length Ls}\<close> fun_upd_other)
          show ?thesis 
            using b1 b2 b3 \<open>h \<in> {1..length Ls}\<close> by auto
        qed
      qed
    qed
    have lem_carrier_y: "\<And>z. z\<in>(carrier (Ls! (i-1))) \<Longrightarrow> (\<lambda>k\<in>{1..length Ls}. if k=i then z else (if (B(j\<mapsto>y)) k \<noteq> None then (the ((B(j\<mapsto>y)) k)) else nested Ls k (B(j\<mapsto>y, i \<mapsto> z)) F)) \<in>carrier (\<Otimes>Ls)"
    proof -
      fix z assume a_z:"z\<in>carrier (Ls! (i-1))"
      let ?x = "(\<lambda>k\<in>{1..length Ls}. if k=i then z else (if (B(j\<mapsto>y)) k \<noteq> None then (the ((B(j\<mapsto>y)) k)) else nested Ls k (B(j\<mapsto>y, i \<mapsto> z)) F))"
      show "(\<lambda>k\<in>{1..length Ls}. if k=i then z else (if (B(j\<mapsto>y)) k \<noteq> None then (the ((B(j\<mapsto>y)) k)) else nested Ls k (B(j\<mapsto>y, i \<mapsto> z)) F)) \<in>carrier (\<Otimes>Ls)"
      proof (rule cart_carrier_criterion)
        fix h assume \<open>h\<notin>{1..length Ls}\<close>
        then show "(\<lambda>k\<in>{1..length Ls}. if k = i then z else if (B(j \<mapsto> y)) k \<noteq> None then the ((B(j \<mapsto> y)) k) else nested Ls k (B(j \<mapsto> y, i \<mapsto> z)) F) h = undefined"
          by auto
      next
        fix h assume \<open>h\<in>{1..length Ls}\<close>
        then show "(\<lambda>k\<in>{1..length Ls}. if k = i then z else if (B(j \<mapsto> y)) k \<noteq> None then the ((B(j \<mapsto> y)) k) else nested Ls k (B(j \<mapsto> y, i \<mapsto> z)) F) h \<in> carrier (Ls! (h-1))"
        proof -
          have b1:"h=i \<Longrightarrow> z\<in>carrier (Ls! (i-1))"
            using a_z by auto
          have b2:"h\<noteq>i \<Longrightarrow> (B(j \<mapsto> y)) h \<noteq> None \<Longrightarrow> the ((B(j \<mapsto> y)) h) \<in> carrier (Ls! (h-1))"
            using Suc.prems(10) 
            by (metis Suc.prems(5) \<open>h \<in> {1..length Ls}\<close> fun_upd_apply option.sel)
          have b3:"h\<noteq>i \<Longrightarrow> (B(j \<mapsto> y)) h = None \<Longrightarrow> nested Ls h (B(j \<mapsto> y, i \<mapsto> z)) F \<in> carrier (Ls !(h-1))"
            using nested_closed 
            by (metis \<open>h \<in> {1..length Ls}\<close> fun_upd_other)
          show ?thesis 
            using b1 b2 b3 \<open>h \<in> {1..length Ls}\<close> by auto
        qed
      qed
    qed
    have lem:"\<And>z. z\<in>(carrier (Ls! (i-1))) \<Longrightarrow> (Pr\<^bsub>i\<^esub> F) (\<lambda>k\<in>{1..length Ls}. if k=i then z else (if (B(j\<mapsto>x)) k \<noteq> None then (the ((B(j\<mapsto>x)) k)) else nested Ls k (B(j\<mapsto>x, i \<mapsto> z)) F))
                             \<sqsubseteq>\<^bsub>(Ls! (i-1))\<^esub> (Pr\<^bsub>i\<^esub> F) (\<lambda>k\<in>{1..length Ls}. if k=i then z else (if (B(j\<mapsto>y)) k \<noteq> None then (the ((B(j\<mapsto>y)) k)) else nested Ls k (B(j\<mapsto>y, i \<mapsto> z)) F))"
    proof -
      fix z assume a_z:"z\<in>carrier (Ls! (i-1))"
      let ?x = "(\<lambda>k\<in>{1..length Ls}. if k=i then z else (if (B(j\<mapsto>x)) k \<noteq> None then (the ((B(j\<mapsto>x)) k)) else nested Ls k (B(j\<mapsto>x, i \<mapsto> z)) F))"
      let ?y = "(\<lambda>k\<in>{1..length Ls}. if k=i then z else (if (B(j\<mapsto>y)) k \<noteq> None then (the ((B(j\<mapsto>y)) k)) else nested Ls k (B(j\<mapsto>y, i \<mapsto> z)) F))"
      have "?x \<in> carrier (\<Otimes>Ls)"
        using lem_carrier_x[OF a_z] by auto
      have "?y \<in> carrier (\<Otimes>Ls)"
        using lem_carrier_y[OF a_z] by auto
      have "?x \<sqsubseteq>\<^bsub>\<Otimes>Ls\<^esub> ?y"
      proof -
        have "(\<And>i. i\<in>{1..length Ls} \<Longrightarrow> ?x i \<sqsubseteq>\<^bsub>(Ls! (i-1))\<^esub> ?y i)"
        proof -
          fix h assume a_h:\<open>h\<in>{1..length Ls}\<close>
          show "?x h \<sqsubseteq>\<^bsub>Ls ! (h-1)\<^esub> ?y h"
          proof (cases "h=i")
            case True
            then show ?thesis
              using a_h Ls_comp_lat a_z complete_lattice_le_refl by force
          next
            case False
            then show ?thesis
            proof (cases "(B(j \<mapsto> x)) h \<noteq> None")
              case True
              then show ?thesis
              proof (cases "h=j")
                case True
                then show ?thesis
                  using \<open>(B(j \<mapsto> x)) h \<noteq> None\<close> a_h \<open>x \<sqsubseteq>\<^bsub>Ls!(j-1)\<^esub> y\<close> Suc.prems(7) by auto
              next
                case False
                then show ?thesis
                  using \<open>(B(j \<mapsto> x)) h \<noteq> None\<close> a_h Suc.prems(10) Ls_comp_lat a_B'' complete_lattice_le_refl by fastforce
              qed
            next
              case False
              then show ?thesis
                (is "?l \<sqsubseteq>\<^bsub>Ls ! (h-1)\<^esub> ?r")
              proof -
                have \<open>h\<noteq>j\<close> using \<open>\<not> (B(j \<mapsto> x)) h \<noteq> None\<close> by auto
                have eql:"?l = nested Ls h (B(j \<mapsto> x, i \<mapsto> z)) F"
                  using \<open>h\<in>{1..length Ls}\<close> \<open>h\<noteq>i\<close> \<open>\<not> (B(j \<mapsto> x)) h \<noteq> None\<close> by auto
                have eqr:"?r = nested Ls h (B(j \<mapsto> y, i \<mapsto> z)) F"
                  using \<open>h\<in>{1..length Ls}\<close> \<open>h\<noteq>i\<close> \<open>\<not> (B(j \<mapsto> x)) h \<noteq> None\<close> by auto
                have \<open>B h = None\<close>
                  using \<open>h\<noteq>j\<close> \<open>\<not> (B(j \<mapsto> x)) h \<noteq> None\<close> by auto
                have "nested Ls h (B(j \<mapsto> x, i \<mapsto> z)) F \<sqsubseteq>\<^bsub>Ls ! (h-1)\<^esub> nested Ls h (B(j \<mapsto> y, i \<mapsto> z)) F"
                  using other_case[OF a_z a_h \<open>h\<noteq>i\<close> \<open>h\<noteq>j\<close> \<open>B h = None\<close>] by simp
                then show ?thesis
                  using eql eqr by auto
              qed
            qed
          qed
        qed
        then show ?thesis
          using Ls_le_criterion by auto
      qed
      then show "(Pr\<^bsub>i\<^esub> F) ?x \<sqsubseteq>\<^bsub>Ls!(i-1)\<^esub> (Pr\<^bsub>i\<^esub> F) ?y"
        using mono_proj_iso[OF \<open>F \<in> carrier \<Otimes>Ls \<rightarrow> carrier \<Otimes>Ls\<close> \<open>i \<in> {1..length Ls}\<close> \<open>Mono\<^bsub>\<Otimes>Ls\<^esub> F\<close>] use_iso2[of "\<Otimes>Ls" "Ls!(i-1)" "Pr\<^bsub>i\<^esub> F" "?x" "?y"]
              \<open>?x \<in> carrier (\<Otimes>Ls)\<close> \<open>?y \<in> carrier (\<Otimes>Ls)\<close>
        by auto
    qed
    then have l1_le_r1: "?l1 \<sqsubseteq>\<^bsub>Ls ! (i-1)\<^esub> ?r1"
    proof -
      interpret Ls_i: complete_lattice "Ls!(i-1)"
        using Ls_comp_lat Suc.prems by blast
      show ?thesis
      proof -
        let ?f = "\<lambda>z\<in>carrier (Ls!(i-1)). (Pr\<^bsub>i\<^esub> F) (\<lambda>k\<in>{1..length Ls}. if k=i then z else (if (B(j\<mapsto>x)) k \<noteq> None then (the ((B(j\<mapsto>x)) k)) else nested Ls k (B(j\<mapsto>x, i \<mapsto> z)) F))"
        let ?g = "\<lambda>z\<in>carrier (Ls!(i-1)). (Pr\<^bsub>i\<^esub> F) (\<lambda>k\<in>{1..length Ls}. if k=i then z else (if (B(j\<mapsto>y)) k \<noteq> None then (the ((B(j\<mapsto>y)) k)) else nested Ls k (B(j\<mapsto>y, i \<mapsto> z)) F))"
        have f_funcset:"?f \<in> carrier (Ls!(i-1)) \<rightarrow> carrier (Ls!(i-1))"
        proof
          fix z assume a_z:\<open>z\<in>carrier (Ls!(i-1))\<close>
          have "(\<lambda>k\<in>{1..length Ls}. if k = i then z else if (B(j \<mapsto> x)) k \<noteq> None then the ((B(j \<mapsto> x)) k) else nested Ls k (B(j \<mapsto> x, i \<mapsto> z)) F) \<in> carrier (\<Otimes>Ls)"
            using lem_carrier_x[OF a_z] by auto
          then have "F (\<lambda>k\<in>{1..length Ls}. if k = i then z else if (B(j \<mapsto> x)) k \<noteq> None then the ((B(j \<mapsto> x)) k) else nested Ls k (B(j \<mapsto> x, i \<mapsto> z)) F) \<in> carrier (\<Otimes>Ls)"
            using proj_carrier Suc.prems by auto
          then show "Pr\<^bsub>i\<^esub> F (\<lambda>k\<in>{1..length Ls}. if k = i then z else if (B(j \<mapsto> x)) k \<noteq> None then the ((B(j \<mapsto> x)) k) else nested Ls k (B(j \<mapsto> x, i \<mapsto> z)) F) \<in> carrier (Ls!(i-1))"
            unfolding proj_def using cart_carrier_iff 
            using Suc.prems(2) by blast
        qed
        have g_funcset:"?g \<in> carrier (Ls!(i-1)) \<rightarrow> carrier (Ls!(i-1))"
        proof
          fix z assume a_z:\<open>z\<in>carrier (Ls!(i-1))\<close>
          have "(\<lambda>k\<in>{1..length Ls}. if k = i then z else if (B(j \<mapsto> y)) k \<noteq> None then the ((B(j \<mapsto> y)) k) else nested Ls k (B(j \<mapsto> y, i \<mapsto> z)) F) \<in> carrier (\<Otimes>Ls)"
            using lem_carrier_y[OF a_z] by auto
          then have "F (\<lambda>k\<in>{1..length Ls}. if k = i then z else if (B(j \<mapsto> y)) k \<noteq> None then the ((B(j \<mapsto> y)) k) else nested Ls k (B(j \<mapsto> y, i \<mapsto> z)) F) \<in> carrier (\<Otimes>Ls)"
            using proj_carrier Suc.prems by auto
          then show "Pr\<^bsub>i\<^esub> F (\<lambda>k\<in>{1..length Ls}. if k = i then z else if (B(j \<mapsto> y)) k \<noteq> None then the ((B(j \<mapsto> y)) k) else nested Ls k (B(j \<mapsto> y, i \<mapsto> z)) F) \<in> carrier (Ls!(i-1))"
            unfolding proj_def using cart_carrier_iff 
            using Suc.prems(2) by blast
        qed
        from Ls_i.LFP_compare lem f_funcset g_funcset
        show ?thesis by auto
      qed
    qed
    show ?thesis
      using eq_l1 eq_r1 l1_le_r1 by auto
  qed
qed

definition (in cart_prod_lattice) specialize_env:: "nat \<Rightarrow> (nat \<Rightarrow> 'a option) \<Rightarrow> (nat \<Rightarrow> 'a option)" (\<open>Sp\<^bsub>_\<^esub> _\<close>) where
  "specialize_env i B j = (if j\<notin>{1..length Ls-1} then None else if j<i then B j else B (j+1))"

lemma (in cart_prod_lattice) specialize_env_simps:
  "k\<in>{1..length Ls-1} \<Longrightarrow> k<j \<Longrightarrow> (Sp\<^bsub>j\<^esub> B) k = B k"
  "k\<in>{1..length Ls-1} \<Longrightarrow> k\<ge>j \<Longrightarrow> (Sp\<^bsub>j\<^esub> B) k = B (k+1)"
  "k\<notin>{1..length Ls-1} \<Longrightarrow> (Sp\<^bsub>j\<^esub> B) k = None"
  unfolding specialize_env_def by auto

lemma (in cart_prod_lattice) special_env_eq:
  assumes a_i:"i\<in>{1..length Ls-1}" 
      and a_j:"j\<in>{1..length Ls}" 
      and B_ext:"\<And>i. i\<notin>{1..length Ls} \<Longrightarrow> B i = None" 
      and C_ext:"\<And>i. i\<notin>{1..length Ls} \<Longrightarrow> C i = None"
  shows
  "i<j \<Longrightarrow> (\<And>k. k\<in>{1..length Ls} \<Longrightarrow> k\<noteq>i \<Longrightarrow> k\<noteq>j \<Longrightarrow> B k = C k) \<Longrightarrow> (B i = Some xi) \<Longrightarrow> (Sp\<^bsub>j\<^esub> B) = ((Sp\<^bsub>j\<^esub> C)(i\<mapsto>xi))"
  "i\<ge>j \<Longrightarrow> (\<And>k. k\<in>{1..length Ls} \<Longrightarrow> k\<noteq>i+1 \<Longrightarrow> k\<noteq>j \<Longrightarrow> B k = C k) \<Longrightarrow> (B (i+1) = Some xi) \<Longrightarrow> (Sp\<^bsub>j\<^esub> B) = ((Sp\<^bsub>j\<^esub> C)(i\<mapsto>xi))"
proof -
  assume \<open>i<j\<close> and a1:"\<And>k. k\<in>{1..length Ls} \<Longrightarrow> k\<noteq>i \<Longrightarrow> k\<noteq>j \<Longrightarrow> B k = C k" and a2:"B i = Some xi"
  show "(Sp\<^bsub>j\<^esub> B) = ((Sp\<^bsub>j\<^esub> C)(i\<mapsto>xi))"
    unfolding specialize_env_def
  proof (rule ext)
    fix k show "(if k \<notin> {1..length Ls - 1} then None else if k < j then B k else B (k + 1)) 
                = ((\<lambda>ja. if ja \<notin> {1..length Ls - 1} then None else if ja < j then C ja else C (ja + 1))(i \<mapsto> xi)) k"
    proof (cases "i=k")
      case True
      then show ?thesis
        using \<open>i<j\<close> a2 a_i by auto
    next
      case False
      then show ?thesis
      proof (cases "k\<notin>{1..length Ls - 1}")
        case True
        then show ?thesis
        using \<open>i\<noteq>k\<close> extensional_arb by auto
      next
        case False
        then show ?thesis
        proof -
          from \<open> \<not> k \<notin> {1..length Ls - 1}\<close> have \<open>k\<in>{1..length Ls-1}\<close> by auto
          have "((\<lambda>ja. if ja \<notin> {1..length Ls - 1} then None else if ja < j then C ja else C (ja + 1))(i \<mapsto> xi)) k = (if k < j then C k else C (k + 1))"
            using \<open>i\<noteq>k\<close> \<open>k\<in>{1..length Ls-1}\<close> by auto
          also have "... = (if k < j then B k else B (k + 1))"
            using a1 \<open>i\<noteq>k\<close> a2 B_ext C_ext
            by (metis (mono_tags, lifting) Suc_eq_plus1 Suc_lessD \<open>i < j\<close> extensional_arb not_less_eq)
          finally show ?thesis 
            using \<open>k\<in>{1..length Ls-1}\<close> by auto
        qed
      qed
    qed
  qed
  next
  assume \<open>j\<le>i\<close> and a1:"\<And>k. k\<in>{1..length Ls} \<Longrightarrow> k\<noteq>i+1 \<Longrightarrow> k\<noteq>j \<Longrightarrow> B k = C k" and a2:"B (i+1) = Some xi"
  show "(Sp\<^bsub>j\<^esub> B) = (Sp\<^bsub>j\<^esub> C)(i \<mapsto> xi)"
    unfolding specialize_env_def
  proof (rule ext)
    fix k show "(if k \<notin> {1..length Ls - 1} then None else if k < j then B k else B (k + 1))
              = ((\<lambda>ja. if ja \<notin> {1..length Ls - 1} then None else if ja < j then C ja else C (ja + 1))(i \<mapsto> xi)) k"
    proof (cases "i=k")
      case True
      then show ?thesis
        using \<open>j\<le>i\<close> a2 a_i by auto
    next
      case False
      then show ?thesis
      proof (cases "k\<notin>{1..length Ls - 1}")
        case True
        then show ?thesis
        using \<open>i\<noteq>k\<close> extensional_arb by auto
      next
        case False
        then show ?thesis
        proof -
          from \<open> \<not> k \<notin> {1..length Ls - 1}\<close> have \<open>k\<in>{1..length Ls-1}\<close> by auto
          have "((\<lambda>ja. if ja \<notin> {1..length Ls - 1} then None else if ja < j then C ja else C (ja + 1))(i \<mapsto> xi)) k = (if k < j then C k else C (k + 1))"
            using \<open>i\<noteq>k\<close> \<open>k\<in>{1..length Ls-1}\<close> by auto
          also have "... = (if k < j then B k else B (k + 1))"
          proof (cases "k<j")                   
            case True
            then show ?thesis 
              using a1 B_ext C_ext \<open>k\<in>{1..length Ls-1}\<close> a_j \<open>j \<le> i\<close> by auto
          next
            case False
            then show ?thesis
              using a1[of "k+1"] B_ext C_ext \<open>k \<in> {1..length Ls - 1}\<close> a_j \<open>j \<le> i\<close> \<open>i\<noteq>k\<close> by auto
          qed
          finally show ?thesis 
            using \<open>k\<in>{1..length Ls-1}\<close> by auto
        qed
      qed
    qed
  qed
qed

definition Bot::"nat \<Rightarrow> 'a option" where
  "Bot i = None"

lemma Bot_undefined:"Bot i = None"
  unfolding Bot_def by auto

lemma Bot_ext:"\<And>A x. x\<in>A \<Longrightarrow> Bot x = None"
  unfolding Bot_def extensional_def by auto

lemma Bot_ext':"j\<in>{1..length Ls} \<Longrightarrow> (\<And>i. i\<notin>{1..length Ls} \<Longrightarrow> (Bot(j \<mapsto> aj)) i = None)"
proof -
  assume \<open>j\<in>{1..length Ls}\<close>
  then show "\<And>i. i\<notin>{1..length Ls} \<Longrightarrow> (Bot(j \<mapsto> aj)) i = None"
    using Bot_ext by auto 
qed

lemma Bot_defined: "((Bot(j\<mapsto>aj)) i \<noteq> None) = (i=j)"
  unfolding Bot_def
  by auto

lemma (in cart_prod_lattice) Bot_specialize_Bot:
  "(Sp\<^bsub>i\<^esub> Bot) = Bot"
  unfolding specialize_env_def Bot_def
  by auto

lemma (in cart_prod_lattice) Bot_specialize:
  "j\<in>{1..length Ls} \<Longrightarrow> i\<in>{1..length Ls} \<Longrightarrow> j<i \<Longrightarrow> (Sp\<^bsub>i\<^esub> (Bot(j \<mapsto> aj))) = Bot(j\<mapsto>aj)"
  "j\<in>{1..length Ls} \<Longrightarrow> i\<in>{1..length Ls} \<Longrightarrow> j>i \<Longrightarrow> (Sp\<^bsub>i\<^esub> (Bot(j \<mapsto> aj))) = Bot(j-1\<mapsto>aj)"
proof -
  assume a_j:"j\<in>{1..length Ls}" and \<open>j<i\<close> and a_i:"i\<in>{1..length Ls}"
  have a_j':"j\<in>{1..length Ls-1}"
    using a_j \<open>j<i\<close> a_i by auto
  have b1:"\<And>k. k\<notin>{1..length Ls -1} \<Longrightarrow> (Sp\<^bsub>i\<^esub> (Bot(j \<mapsto> aj))) k = None"
    unfolding specialize_env_def by auto
  have Sp_ext: "\<And>i. i\<notin>{1..length Ls-1} \<Longrightarrow>(Sp\<^bsub>i\<^esub> (Bot(j \<mapsto> aj))) i = None"
    unfolding specialize_env_def by auto
  have "\<And>i. i\<notin>{1..length Ls-1} \<Longrightarrow> (Bot(j\<mapsto>aj)) i = None"
    using a_j' 
    by (metis Bot_defined)
  then have b1:"(\<And>k. k\<in>{1..length Ls-1} \<Longrightarrow> (Sp\<^bsub>i\<^esub> (Bot(j \<mapsto> aj))) k = (Bot (j\<mapsto>aj)) k) \<Longrightarrow> (Sp\<^bsub>i\<^esub> (Bot(j \<mapsto> aj))) = Bot(j\<mapsto>aj)"
    using Sp_ext 
    by (metis (lifting) ext specialize_env_simps(3))
  have "\<And>k. k\<in>{1..length Ls-1} \<Longrightarrow> (Sp\<^bsub>i\<^esub> (Bot(j \<mapsto> aj))) k = (Bot (j\<mapsto>aj)) k"
    by (metis Bot_defined \<open>j < i\<close> add_lessD1 le_geq_cases specialize_env_simps(1,2))
  then show "(Sp\<^bsub>i\<^esub> (Bot(j \<mapsto> aj))) = Bot(j\<mapsto>aj)"
    using b1 by auto
next
  assume a_j:"j\<in>{1..length Ls}" and \<open>j>i\<close> and a_i:"i\<in>{1..length Ls}"
  have a_j':"j-1\<in>{1..length Ls-1}"
    using a_j \<open>j>i\<close> a_i by auto
  have Sp_ext: "\<And>i. i\<notin>{1..length Ls-1} \<Longrightarrow>(Sp\<^bsub>i\<^esub> (Bot(j \<mapsto> aj))) i = None"
    unfolding specialize_env_def by auto
  have "\<And>i. i\<notin>{1..length Ls-1} \<Longrightarrow> (Bot(j-1 \<mapsto> aj)) i = None"
    using a_j' Bot_undefined by auto
  then have b1:"(\<And>k. k\<in>{1..length Ls-1} \<Longrightarrow> (Sp\<^bsub>i\<^esub> (Bot(j \<mapsto> aj))) k = (Bot (j-1\<mapsto>aj)) k) \<Longrightarrow> (Sp\<^bsub>i\<^esub> (Bot(j \<mapsto> aj))) = Bot(j-1\<mapsto>aj)"
    using Sp_ext
    by (metis (no_types, lifting) ext specialize_env_simps(3))
  have "\<And>k. k\<in>{1..length Ls-1} \<Longrightarrow> (Sp\<^bsub>i\<^esub> (Bot(j \<mapsto> aj))) k = (Bot (j-1\<mapsto>aj)) k"
  proof -
    fix k assume a_k:"k\<in>{1..length Ls-1}"
    show "(Sp\<^bsub>i\<^esub> (Bot(j \<mapsto>aj))) k = (Bot (j-1\<mapsto>aj)) k"
    proof (cases "k<i")
      case True
      then show ?thesis
        using \<open>j>i\<close> specialize_env_simps(1)[of "k" "i" "Bot(j \<mapsto> aj)"] a_k unfolding Bot_def 
        by fastforce
    next
      case False
      then show ?thesis
      proof (cases "k=j-1")
        case True
        then show ?thesis 
          using \<open>\<not> k < i\<close> specialize_env_simps(2)[of "k" "i" "Bot(j \<mapsto> aj)"] a_k 
          by auto
      next
        case False
        then show ?thesis
          using \<open>\<not> k < i\<close> specialize_env_simps(2)[of "k" "i" "Bot(j \<mapsto> aj)"] a_k
          by (simp add: Bot_undefined)
      qed
    qed
  qed
  then show "(Sp\<^bsub>i\<^esub> (Bot(j \<mapsto> aj))) = Bot(j-1\<mapsto>aj)"
    using b1 by auto
qed
  

lemma (in cart_prod_lattice) nested_subst_mono_Bot:
  assumes f_wd:"F\<in> carrier (\<Otimes>Ls) \<rightarrow> carrier (\<Otimes>Ls)"
  and a_i:"i\<in>{1..length Ls}"
  and a_j:"j\<in>{1..length Ls}"
  and a_x:"x\<in>carrier (Ls!(j-1))"
  and a_y:"y\<in>carrier (Ls!(j-1))"
  and a_xy:"x \<sqsubseteq>\<^bsub>(Ls!(j-1))\<^esub> y"
  and a_ij: "i\<noteq>j"
  and f_mono:"Mono\<^bsub>\<Otimes>Ls\<^esub> F"
shows "nested Ls i (Bot(j\<mapsto>x)) F \<sqsubseteq>\<^bsub>Ls!(i-1)\<^esub> nested Ls i (Bot(j\<mapsto>y)) F"
  using nested_subst_mono[OF f_wd a_i a_j a_x a_y a_xy a_ij] Bot_undefined f_mono by metis


lemma (in cart_prod_lattice) n_to_two_in_carrier: 
  assumes a_j:"j\<in>{1..length Ls}"
      and a_x:"x\<in>carrier (\<Otimes>Ls)"
        shows "fst (n_to_two j x)\<in> carrier_spl Ls j"
proof (rule in_carrier_spl_I)
  show "j\<in>{1..length Ls}" 
    using a_j by auto
  show "\<And>y. y \<notin> {1..length Ls - 1} \<Longrightarrow> fst (n_to_two j x) y = undefined"
    using n_to_two_fst_ext by auto
  show "\<And>h. h \<in> {1..length Ls - 1} \<Longrightarrow> (h < j \<longrightarrow> fst (n_to_two j x) h \<in> carrier (Ls ! (h-1))) \<and> (j \<le> h \<longrightarrow> fst (n_to_two j x) h \<in> carrier (Ls ! h))"
  proof (rule)
    show "\<And>h. h \<in> {1..length Ls - 1} \<Longrightarrow> h < j \<longrightarrow> fst (n_to_two j x) h \<in> carrier (Ls ! (h-1))"
    proof 
      fix h assume \<open>h\<in>{1..length Ls-1}\<close> and \<open>h<j\<close>
      show "fst (n_to_two j x) h \<in> carrier (Ls ! (h-1))"
      proof -
        have "x h \<in> carrier (Ls ! (h-1))"
          using a_x \<open>h\<in>{1..length Ls-1}\<close> kth_carrier[of "x" "Ls" "h"]
          by (metis atLeastAtMost_iff diff_is_0_eq' le_geq_cases less_imp_diff_less less_irrefl_nat zero_less_diff)
        then show ?thesis
          using n_to_two_simps_lt[of "h" "j" "x"] \<open>h<j\<close> \<open>h\<in>{1..length Ls-1}\<close> a_x by auto
      qed
    qed
    show "\<And>h. h \<in> {1..length Ls - 1} \<Longrightarrow> j \<le> h \<longrightarrow> fst (n_to_two j x) h \<in> carrier (Ls ! h)"
    proof
      fix h assume \<open>h \<in> {1..length Ls - 1}\<close> and \<open>j\<le>h\<close>
      show "fst (n_to_two j x) h \<in> carrier (Ls ! h)"
      proof -
        have "x (h+1) \<in> carrier (Ls ! h)"
          using a_x \<open>h\<in>{1..length Ls-1}\<close> kth_carrier[of "x" "Ls" "h+1"] atLeastAtMost_iff by fastforce
        then show ?thesis
          using n_to_two_simps_geq[of "h" "j" "x"] \<open>j\<le>h\<close> \<open>h \<in> {1..length Ls - 1}\<close> by auto
      qed
    qed
  qed
qed

lemma (in cart_prod_lattice) specialize_proj_eq:
  assumes a_j:"j\<in>{1..length Ls}"
    and a_i:"i\<in>{1..length Ls}"
    and a_x_j:"x j = aj"
    and a_x:"x\<in>carrier (\<Otimes>Ls)"
  shows "i<j \<Longrightarrow> (Pr\<^bsub>i\<^esub> f) x = (Pr\<^bsub>i\<^esub> (Sp\<^bsub>j,aj\<^esub> f)) (fst (n_to_two j x))"
        "i>j \<Longrightarrow> (Pr\<^bsub>i\<^esub> f) x = (Pr\<^bsub>i-1\<^esub> (Sp\<^bsub>j,aj\<^esub> f)) (fst (n_to_two j x))"
proof -
  assume \<open>i<j\<close>
  have a_i':"i\<in>{1..length Ls-1}"
    using a_j a_i \<open>i<j\<close> by auto
  have "fst (n_to_two j x) \<in> carrier_spl Ls j"
    using n_to_two_in_carrier a_j a_x by auto
  then have "(Pr\<^bsub>i\<^esub> (Sp\<^bsub>j,aj\<^esub> f)) (fst (n_to_two j x)) = (\<lambda>ja\<in>{1..length Ls - 1}. if ja < j then f (two_to_n j (fst (n_to_two j x), aj)) ja else f (two_to_n j (fst (n_to_two j x), aj)) (ja + 1)) i"
    unfolding proj_def specialize_fn_def by auto
  also have "... = (if i < j then f (two_to_n j (fst (n_to_two j x), aj)) i else f (two_to_n j (fst (n_to_two j x), aj)) (i + 1))"
    using a_i' by auto
  also have "... = (if i < j then f x i else f x (i + 1))"
    using two_n__n_two_id[of "x" "j"] n_to_two_simps_snd[of "j" "x"] a_x_j a_x a_j by auto
  also have "... = f x i"
    using \<open>i<j\<close> by auto
  also have "... = (Pr\<^bsub>i\<^esub> f) x"
    unfolding proj_def by auto
  finally show "Pr\<^bsub>i\<^esub> f x = Pr\<^bsub>i\<^esub> Sp\<^bsub>j,aj\<^esub> f (fst (n_to_two j x))"
    by auto
next
  assume \<open>j<i\<close>
  then have \<open>i-1\<in>{1..length Ls-1}\<close>
    using a_i a_j by auto
  have b1:"(fst (n_to_two j x)) \<in> carrier_spl Ls j"
    using n_to_two_in_carrier a_j a_x by auto    
  have "(Pr\<^bsub>i-1\<^esub> (Sp\<^bsub>j,aj\<^esub> f)) (fst (n_to_two j x)) = (\<lambda>v\<in>carrier_spl Ls j. \<lambda>ja\<in>{1..length Ls - 1}. if ja < j then f (two_to_n j (v, aj)) ja else f (two_to_n j (v, aj)) (ja + 1)) (fst (n_to_two j x)) (i - 1)"
    unfolding proj_def specialize_fn_def by auto
  also have "... = (\<lambda>ja\<in>{1..length Ls - 1}. if ja < j then f (two_to_n j ((fst (n_to_two j x)), aj)) ja else f (two_to_n j ((fst (n_to_two j x)), aj)) (ja + 1)) (i-1)"
    using b1 by auto
  also have "... = (if i-1 < j then f (two_to_n j ((fst (n_to_two j x)), aj)) (i-1) else f (two_to_n j ((fst (n_to_two j x)), aj)) (i-1 + 1))"
    using \<open>i-1\<in>{1..length Ls-1}\<close> by auto
  also have "... = f (two_to_n j ((fst (n_to_two j x)), aj)) i"
    using \<open>j<i\<close> by auto
  also have "... = f x i"
    using two_n__n_two_id[of "x" "j"] n_to_two_simps_snd[of "j" "x"] a_x_j a_x a_j by auto
  also have "... = (Pr\<^bsub>i\<^esub> f) x"
    unfolding proj_def by auto
  finally show "Pr\<^bsub>i\<^esub> f x = Pr\<^bsub>i - 1\<^esub> (Sp\<^bsub>j,aj\<^esub> f) (fst (n_to_two j x))"
    by auto
qed

lemma (in cart_prod_lattice) nested_sp_compat':
  fixes i::"nat" and j::"nat" and f::"(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" and B::"nat \<Rightarrow> 'a option" and aj::"'a"
  assumes B_car:"\<And>i. i\<in>{1..length Ls} \<Longrightarrow> B i \<noteq> None \<Longrightarrow> the (B i) \<in> carrier (Ls!(i-1))"
      and B_ext:"\<And>i. i\<notin>{1..length Ls} \<Longrightarrow> B i = None"
      and a_i:"i\<in>{1..length Ls}"
      and a_j:"j\<in>{1..length Ls}"
      and a_car:"f\<in>car_prod_carrier Ls \<rightarrow>\<^sub>E car_prod_carrier Ls" 
      and aj_car:"aj\<in>carrier (Ls!(j-1))"
    shows "(i<j \<longrightarrow> nested Ls i (B(j:=Some aj)) f = nested (SpLs\<^bsub>j\<^esub> Ls) i (Sp\<^bsub>j\<^esub> B) (Sp\<^bsub>j,aj\<^esub> f)) \<and> (i>j \<longrightarrow> nested Ls i (B(j:=Some aj)) f = nested (SpLs\<^bsub>j\<^esub> Ls) (i-1) (Sp\<^bsub>j\<^esub> B) (Sp\<^bsub>j,aj\<^esub> f))"
  using a_i B_car B_ext
proof (cases "length Ls = 1")
  case True
  then show ?thesis 
    using a_i a_j by auto
next
  case False
  then show ?thesis
  proof -
    assume \<open>length Ls\<noteq>1\<close>
    then have len_ls:"((length Ls)::nat) > 1" 
      using Ls_len_pos by linarith
    show "(i < j \<longrightarrow> nested Ls i (B(j := Some aj)) f = nested (SpLs\<^bsub>j\<^esub> Ls) i (Sp\<^bsub>j\<^esub> B) (Sp\<^bsub>j,aj\<^esub> f)) \<and> (j < i \<longrightarrow> nested Ls i (B(j := Some aj)) f = nested (SpLs\<^bsub>j\<^esub> Ls) (i - 1) (Sp\<^bsub>j\<^esub> B) (Sp\<^bsub>j,aj\<^esub> f))"
      using a_i B_car B_ext
    proof (induction "card {j\<in>{1..length Ls}. B j = None}" arbitrary:B i rule:nat.induct)
      case zero
      then show ?case (is "?r1 \<and> ?r2")
      proof -
        have all_defined:"\<And>j. j\<in>{1..length Ls} \<Longrightarrow> B j \<noteq> None"
          using zero by auto
        then have b0:"nested Ls i (B(j \<mapsto> aj)) f = undefined"
          using zero.prems(1) nested_simps_defined[of "i" "(B(j \<mapsto> aj))" "f"] by fastforce
        have b1:"i<j \<longrightarrow> nested (SpLs\<^bsub>j\<^esub> Ls) i (Sp\<^bsub>j\<^esub> B) (Sp\<^bsub>j,aj\<^esub> f) = undefined"
        proof
          assume "i<j"
          then have "i\<in>{1..length Ls-1}"
            using \<open>i \<in> {1..length Ls}\<close> a_j by auto
          then have "(Sp\<^bsub>j\<^esub> B) i \<noteq> None"
            using all_defined unfolding specialize_env_def by auto
          then show "nested (SpLs\<^bsub>j\<^esub> Ls) i (Sp\<^bsub>j\<^esub> B) (Sp\<^bsub>j,aj\<^esub> f) = undefined"
            using nested_simps_defined by auto
        qed
        have b2:"j<i \<longrightarrow> nested (SpLs\<^bsub>j\<^esub> Ls) (i-1) (Sp\<^bsub>j\<^esub> B) (Sp\<^bsub>j,aj\<^esub> f) = undefined"
        proof
          assume "j<i"
          then have "i-1\<in>{1..length Ls-1}"
            using \<open>i\<in>{1..length Ls}\<close> a_j by auto
          then have "(Sp\<^bsub>j\<^esub> B) (i-1) \<noteq> None"
            using all_defined \<open>j<i\<close> less_diff_conv2 unfolding specialize_env_def by auto
          then show "nested (SpLs\<^bsub>j\<^esub> Ls) (i-1) (Sp\<^bsub>j\<^esub> B) (Sp\<^bsub>j,aj\<^esub> f) = undefined"
            using nested_simps_defined by auto
        qed
        show "?r1 \<and> ?r2"
          using b1 b2 b0 by presburger
      qed
    next
      case (Suc m)
      then show ?case (is "(i<j \<longrightarrow> ?l1 = ?r1) \<and> (j<i \<longrightarrow> ?l2 = ?r2)")
      proof -
        interpret j_sub_locale: cart_prod_lattice "Sp_Ls j Ls"
          using hat_j_prod_locale len_ls a_j by auto
        (* IH is here *)
        have IH:"\<And>xi (k::nat). k\<in>{1..length Ls} 
            \<Longrightarrow> i\<noteq>j 
            \<Longrightarrow> B i = None
            \<Longrightarrow> (\<And>j. j\<notin>{1..length Ls} \<Longrightarrow> (B(i \<mapsto> xi)) j = None)
            \<Longrightarrow> (\<And>j. j \<in> {1..length Ls} \<Longrightarrow> (B(i \<mapsto> xi)) j \<noteq> None \<Longrightarrow> the ((B(i \<mapsto> xi)) j) \<in> carrier (Ls ! (j-1)))
            \<Longrightarrow> (k<j \<longrightarrow> nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f = nested (SpLs\<^bsub>j\<^esub> Ls) k (Sp\<^bsub>j\<^esub> (B(i\<mapsto>xi))) (Sp\<^bsub>j,aj\<^esub> f)) \<and>
                (k>j \<longrightarrow> nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f = nested (SpLs\<^bsub>j\<^esub> Ls) (k-1) (Sp\<^bsub>j\<^esub> (B(i\<mapsto>xi))) (Sp\<^bsub>j,aj\<^esub> f))"
          proof -
            fix xi k
            assume a_k:"k \<in> {1..length Ls}" and Bi_undef:"B i = None" and i_neq_j:"i\<noteq>j"
              and IHB_car:"\<And>j. j \<in> {1..length Ls} \<Longrightarrow> (B(i \<mapsto> xi)) j \<noteq> None \<Longrightarrow> the ((B(i \<mapsto> xi)) j) \<in> carrier (Ls ! (j-1))"
              and IHB_ext:"\<And>j. j\<notin>{1..length Ls} \<Longrightarrow> (B(i \<mapsto> xi)) j = None"
            have i_in:"i\<in>{j\<in>{1..length Ls}. B j = None}"
              using Bi_undef \<open>i\<in>{1..length Ls}\<close> by auto
            have "{j\<in>{1..length Ls}. (B(i\<mapsto>xi)) j = None} = {j\<in>{1..length Ls}. B j = None} - {i}"
              using \<open>i\<in>{1..length Ls}\<close> Bi_undef by auto
            then have B_card:"m= card {j\<in>{1..length Ls}. (B(i\<mapsto>xi)) j = None}"
              using Suc.hyps(2) card_Diff_singleton i_in by auto
            then have b1:"k < j \<Longrightarrow> nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f = nested (SpLs\<^bsub>j\<^esub> Ls) k (Sp\<^bsub>j\<^esub> (B(i \<mapsto> xi))) Sp\<^bsub>j,aj\<^esub> f"
              using a_k Suc.hyps(1)[where B="B(i\<mapsto>xi)" and i="k"] IHB_car IHB_ext
              by (metis (no_types, lifting) fun_upd_twist i_neq_j option.distinct(1) option.sel)
            have b2:"k>j \<Longrightarrow> nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f = nested (SpLs\<^bsub>j\<^esub> Ls) (k-1) (Sp\<^bsub>j\<^esub> (B(i\<mapsto>xi))) (Sp\<^bsub>j,aj\<^esub> f)"
              using a_k B_card Suc.hyps(1)[where B="B(i\<mapsto>xi)" and i="k"] IHB_car IHB_ext
              by (metis (no_types, lifting) fun_upd_twist i_neq_j option.discI option.sel)
            show "(k<j \<longrightarrow> nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f = nested (SpLs\<^bsub>j\<^esub> Ls) k (Sp\<^bsub>j\<^esub> (B(i\<mapsto>xi))) (Sp\<^bsub>j,aj\<^esub> f)) \<and>
                (k>j \<longrightarrow> nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f = nested (SpLs\<^bsub>j\<^esub> Ls) (k-1) (Sp\<^bsub>j\<^esub> (B(i\<mapsto>xi))) (Sp\<^bsub>j,aj\<^esub> f))"
              using b1 b2 by auto
          qed
    
        have lem1:"i\<noteq>j \<Longrightarrow>
          ?l1 = (if (B i \<noteq> None) then undefined else
            LFP\<^bsub>(Ls ! (i-1))\<^esub>
            (\<lambda>xi\<in>carrier (Ls!(i-1)). (Pr\<^bsub>i\<^esub> f) (\<lambda>(k::nat)\<in>{1..length Ls}. 
              (if k=i then xi else if k=j then aj else if (B k\<noteq>None) then (the (B k)) else (nested Ls k (B(j\<mapsto>aj, i\<mapsto>xi)) f)))))"
          using \<open>i\<in>{1..length Ls}\<close> a_j
        proof -
          let ?rhs = "(if (B i \<noteq> None) then undefined else
            LFP\<^bsub>(Ls ! (i-1))\<^esub>
            (\<lambda>xi\<in>carrier (Ls!(i-1)). (Pr\<^bsub>i\<^esub> f) (\<lambda>(k::nat)\<in>{1..length Ls}. 
              (if k=i then xi else if k=j then aj else if (B k\<noteq>None) then (the (B k)) else (nested Ls k (B(j\<mapsto>aj, i\<mapsto>xi)) f)))))"
          assume \<open>i\<noteq>j\<close>
          have "?l1 =(if i \<notin> {1..length Ls} then undefined
             else if (B(j\<mapsto>aj)) i \<noteq> None then undefined
             else LFP\<^bsub>(Ls ! (i-1))\<^esub> (\<lambda>xi\<in>carrier (Ls ! (i-1)). (Pr\<^bsub>i\<^esub> f) (\<lambda>ja\<in>{1..length Ls}. if ja = i then xi else if (B(j \<mapsto> aj)) ja \<noteq> None then the ((B(j \<mapsto> aj)) ja) else nested Ls ja (B(j \<mapsto> aj, i \<mapsto> xi)) f)))"
            using nested.simps[of "Ls" "i" "B(j\<mapsto>aj)" "f"] by auto
          also have "... = (if (B(j \<mapsto> aj)) i \<noteq> None then undefined
            else LFP\<^bsub>(Ls ! (i-1))\<^esub> (\<lambda>xi\<in>carrier (Ls ! (i-1)). 
            (Pr\<^bsub>i\<^esub> f) (\<lambda>ja\<in>{1..length Ls}. if ja = i then xi else if (B(j \<mapsto> aj)) ja \<noteq> None then the ((B(j \<mapsto> aj)) ja) else nested Ls ja (B(j \<mapsto> aj, i \<mapsto> xi)) f)))"
            using \<open>i \<in> {1..length Ls}\<close> by auto
          also have "... = (if B i \<noteq> None then undefined
                            else LFP\<^bsub>(Ls ! (i-1))\<^esub> 
                            (\<lambda>xi\<in>carrier (Ls ! (i-1)). (Pr\<^bsub>i\<^esub> f) (\<lambda>ja\<in>{1..length Ls}. if ja = i then xi else if ja=j then aj else if B ja \<noteq> None then the (B ja) else nested Ls ja (B(j \<mapsto> aj, i \<mapsto> xi)) f)))"
            using \<open>i\<noteq>j\<close> by (smt (verit, ccfv_SIG) fun_upd_other fun_upd_same option.discI option.sel restrict_ext)
          finally show "?l1 = ?rhs"
            by auto
        qed
    
        have lem2_i_lt_j:"\<And>xi. xi\<in>carrier (Ls ! (i-1)) 
          \<Longrightarrow> B i =None
          \<Longrightarrow> i<j
          \<Longrightarrow> (Pr\<^bsub>i\<^esub> f) (\<lambda>(k::nat)\<in>{1..length Ls}. if k=i then xi else if k=j then aj else if B k\<noteq>None then the (B k) else nested Ls k (B(j\<mapsto>aj,i\<mapsto>xi)) f) = 
              (Pr\<^bsub>i\<^esub> (Sp\<^bsub>j,aj\<^esub> f)) (\<lambda>(h::nat)\<in>{1..length Ls-1}. 
                if h=i then xi else if (Sp\<^bsub>j\<^esub> B) h \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) h) 
                  else
                  if h<j then nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i\<mapsto>xi)) (Sp\<^bsub>j,aj\<^esub> f) 
                     else nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i\<mapsto>xi)) (Sp\<^bsub>j,aj\<^esub> f))"
          unfolding specialize_fn_def
        proof -
          fix xi assume i_lt_j:"i<j" and xi_car:"xi\<in>carrier (Ls ! (i-1))" and Bi_undefined:"B i=None"
          let ?v = "(\<lambda>h\<in>{1..length Ls - 1}.
               if h = i then xi
               else if ((Sp\<^bsub>j\<^esub> B) h) \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) h)
                    else if h < j
                         then nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i \<mapsto> xi))
                               (\<lambda>v\<in>(carrier_spl Ls j). \<lambda>ja\<in>{1..length Ls - 1}. (if ja < j then (Pr\<^bsub>ja\<^esub> f) (two_to_n j (v, aj)) else (Pr\<^bsub>ja + 1\<^esub> f) (two_to_n j (v, aj))))
                         else nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i \<mapsto> xi))
                               (\<lambda>v\<in>(carrier_spl Ls j). \<lambda>ja\<in>{1..length Ls - 1}. (if ja < j then (Pr\<^bsub>ja\<^esub> f) (two_to_n j (v, aj)) else (Pr\<^bsub>ja + 1\<^esub> f) (two_to_n j (v, aj)))))"
          have v_in_car:"?v\<in>carrier_spl Ls j"
          proof (rule in_carrier_spl_I)
            show "j \<in> {1..length Ls}"
                using a_j by auto
            next
              show "\<And>h. h\<in>{1..length Ls -1} \<Longrightarrow> ((h<j \<longrightarrow> ?v h \<in> carrier (Ls ! (h-1))) \<and> (h\<ge>j \<longrightarrow> ?v h \<in> carrier (Ls ! h)))"
              proof
                fix h
                assume a_h:"h\<in>{1..length Ls-1}"
                have "h<j \<Longrightarrow> ?v h \<in> carrier (Ls ! (h-1))" 
                  using xi_car
                proof - assume \<open>h<j\<close>
                  show "?v h \<in> carrier (Ls ! (h-1))"
                  proof (cases "h=i")
                    case True
                    then show ?thesis 
                      using xi_car \<open>i<j\<close> \<open>i\<in>{1..length Ls}\<close> a_j by auto
                  next
                    case False
                    then show ?thesis
                    proof (cases "Sp\<^bsub>j\<^esub> B h \<noteq> None")
                      case True
                      then show ?thesis
                      proof -
                        have b1:"Sp\<^bsub>j\<^esub> B h = B h"
                          using \<open>h<j\<close> a_h unfolding specialize_env_def by auto
                        then have "?v h = the (B h)"
                          using a_h \<open>(Sp\<^bsub>j\<^esub> B) h \<noteq> None\<close> \<open>h \<noteq> i\<close> by auto
                        then show ?thesis
                          using \<open>h\<in>{1..length Ls-1}\<close> \<open>Sp\<^bsub>j\<^esub> B h \<noteq> None\<close> Suc(4)[of "h"] b1 by auto
                      qed
                    next
                      case False
                      then show ?thesis
                      proof -
                        have b1:"Sp\<^bsub>j\<^esub> B h = B h"
                          using \<open>h<j\<close> a_h unfolding specialize_env_def by auto
                        then have Bh_undef:"B h = None"
                          using False by auto
                        then have "?v h = 
                          (if h < j then nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i\<mapsto> xi)) (\<lambda>v\<in>carrier_spl Ls j. \<lambda>ja\<in>{1..length Ls - 1}. if ja < j then (Pr\<^bsub>ja\<^esub> f) (two_to_n j (v, aj)) else (Pr\<^bsub>ja + 1\<^esub> f) (two_to_n j (v, aj)))
                           else nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i \<mapsto> xi)) (\<lambda>v\<in>carrier_spl Ls j. \<lambda>ja\<in>{1..length Ls - 1}. if ja < j then (Pr\<^bsub>ja\<^esub> f) (two_to_n j (v, aj)) else (Pr\<^bsub>ja + 1\<^esub> f) (two_to_n j (v, aj))))"
                          using \<open>h\<in>{1..length Ls-1}\<close> \<open>h\<noteq>i\<close> b1 by auto
                        also have "... = nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i\<mapsto>xi)) (\<lambda>v\<in>carrier_spl Ls j. \<lambda>ja\<in>{1..length Ls - 1}. if ja < j then (Pr\<^bsub>ja\<^esub> f) (two_to_n j (v, aj)) else (Pr\<^bsub>ja + 1\<^esub> f) (two_to_n j (v, aj)))"
                          (is "?l = ?r")
                          using \<open>h<j\<close> by auto
                        finally have b0:"?v h = ?r" by auto
                        have b2:"((SpLs\<^bsub>j\<^esub> Ls) ! (h-1)) = (Ls! (h-1))"
                          unfolding Sp_Ls_def get_member_def using remove_at_nth_lt[of "j" "Ls" "h"] \<open>h<j\<close> a_j \<open>h \<in> {1..length Ls - 1}\<close> by auto
                        have b3: "((Sp\<^bsub>j\<^esub> B)(i \<mapsto> xi)) h = None"
                          using b1 Bh_undef \<open>h\<noteq>i\<close> by auto
                        have "length (SpLs\<^bsub>j\<^esub> Ls) = length Ls - 1"
                          unfolding Sp_Ls_def using length_minus_1 a_j by auto
                        then have "?r \<in> carrier (Ls ! (h-1))"
                          using j_sub_locale.nested_closed[of "h" "(Sp\<^bsub>j\<^esub> B)(i\<mapsto>xi)"] \<open>h\<in>{1..length Ls-1}\<close> b2 b3
                          by (metis (no_types, lifting))
                        then show "?v h \<in> carrier (Ls ! (h-1))" 
                          using b0 by auto
                      qed
                    qed
                  qed
                qed
                then show "h<j \<longrightarrow> ?v h \<in> carrier (Ls ! (h-1))" 
                  by auto
              next
                fix h
                assume a_h:"h\<in>{1..length Ls-1}"
                have "h\<ge>j \<Longrightarrow> ?v h \<in> carrier (Ls ! h)"
                proof -
                  assume \<open>h\<ge>j\<close>
                  then have \<open>h\<noteq>i\<close> 
                    using \<open>i<j\<close> by auto
                  then have b1:"?v h = (if (Sp\<^bsub>j\<^esub> B) h \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) h)
                  else if h < j then nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i\<mapsto>xi)) (\<lambda>v\<in>carrier_spl Ls j. \<lambda>ja\<in>{1..length Ls - 1}. if ja < j then (Pr\<^bsub>ja\<^esub> f) (two_to_n j (v, aj)) else (Pr\<^bsub>ja + 1\<^esub> f) (two_to_n j (v, aj)))
                  else nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i\<mapsto>xi)) (\<lambda>v\<in>carrier_spl Ls j. \<lambda>ja\<in>{1..length Ls - 1}. if ja < j then (Pr\<^bsub>ja\<^esub> f) (two_to_n j (v, aj)) else (Pr\<^bsub>ja + 1\<^esub> f) (two_to_n j (v, aj))))"
                    (is "_ = ?r")
                    using a_h by auto
                  have b2:"(Sp\<^bsub>j\<^esub> B) h \<noteq> None \<Longrightarrow> ?r = the ((Sp\<^bsub>j\<^esub> B) h)" 
                    by auto
                  also have b3:"... = the (B (h+1))" 
                    unfolding specialize_env_def using \<open>h\<ge>j\<close> a_h by auto
                  have b4:"(Sp\<^bsub>j\<^esub> B) h = B (h+1)"
                    using \<open>j \<le> h\<close> a_h specialize_env_simps(2) by presburger
                  have "(Sp\<^bsub>j\<^esub> B) h \<noteq> None \<Longrightarrow> the (B (h+1)) \<in> carrier (Ls ! h)"
                    using Suc.prems(2)[of "h+1"] b4 a_h b3 by auto
                  then have b4:"(Sp\<^bsub>j\<^esub> B) h \<noteq> None \<Longrightarrow> ?v h \<in> carrier (Ls ! h)"
                    using b1 b2 b3 by auto

                  have c1:"(Sp\<^bsub>j\<^esub> B) h = None \<Longrightarrow> 
                    ?r = nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i\<mapsto> xi)) (\<lambda>v\<in>carrier_spl Ls j. \<lambda>ja\<in>{1..length Ls - 1}. if ja < j then (Pr\<^bsub>ja\<^esub> f) (two_to_n j (v, aj)) else (Pr\<^bsub>ja + 1\<^esub> f) (two_to_n j (v, aj)))"
                    by auto
                  then have "?r \<in> carrier (SpLs\<^bsub>j\<^esub> Ls ! (h-1))"
                    using j_sub_locale.nested_closed[of "h" "(Sp\<^bsub>j\<^esub> B)(i \<mapsto> xi)"] length_minus_1[of "j" "Ls"] a_j a_h unfolding Sp_Ls_def
                    by (metis (no_types, lifting) \<open>Sp\<^bsub>j\<^esub> B h \<noteq> None \<Longrightarrow> the (B (h + 1)) \<in> carrier (Ls ! h)\<close> \<open>h \<noteq> i\<close> \<open>j \<le> h\<close> b3 diff_add_inverse2 fun_upd_other get_member_def remove_at_nth_ge2)
                  then have "?r \<in> carrier (Ls ! h)"
                    using remove_at_nth_ge[of "j" "Ls" "h"] a_j a_h \<open>h\<ge>j\<close> unfolding Sp_Ls_def get_member_def by auto
                  then have c2:"(Sp\<^bsub>j\<^esub> B) h = None \<Longrightarrow> ?v h \<in> carrier (Ls ! h)"
                    using b1 by auto
                  show "?v h \<in> carrier (Ls ! h)"
                    using b4 c2 by fastforce
                qed
                then show "h\<ge>j \<longrightarrow> ?v h \<in> carrier (Ls ! h)" by auto       
              qed
            next
              show "\<And>y. y\<notin>{1..length Ls -1} \<Longrightarrow> ?v y = undefined"
              proof -
                fix y assume a_y:"y\<notin>{1..length Ls -1}"
                show "?v y = undefined"
                  by (meson FuncSet.restrict_apply a_y)
              qed
          qed

          have R1:"(Pr\<^bsub>i\<^esub> (\<lambda>v\<in>carrier_spl Ls j. \<lambda>ja\<in>{1..length Ls - 1}. if ja < j then (Pr\<^bsub>ja\<^esub> f) (two_to_n j (v, aj)) else (Pr\<^bsub>ja + 1\<^esub> f) (two_to_n j (v, aj)))) ?v
                 = (Pr\<^bsub>i\<^esub> f) (two_to_n j (?v, aj))"
            (is "?lhs = ?rhs")
          proof -
            have "?lhs = (\<lambda>v\<in>carrier_spl Ls j. \<lambda>ja\<in>{1..length Ls - 1}. if ja < j then (Pr\<^bsub>ja\<^esub> f) (two_to_n j (v, aj)) else (Pr\<^bsub>ja + 1\<^esub> f) (two_to_n j (v, aj))) ?v i"
              using proj_simp[of "i" "(\<lambda>v\<in>carrier_spl Ls j. \<lambda>ja\<in>{1..length Ls - 1}. if ja < j then (Pr\<^bsub>ja\<^esub> f) (two_to_n j (v, aj)) else (Pr\<^bsub>(ja + 1)\<^esub> f) (two_to_n j (v, aj)))" "?v"]
              unfolding carrier_spl_def by auto
            also have c2:"... = (\<lambda>i\<in>{1..length Ls - 1}. if i < j then (Pr\<^bsub>i\<^esub> f) (two_to_n j (?v, aj)) else (Pr\<^bsub>i + 1\<^esub> f) (two_to_n j (?v, aj))) i"
              using v_in_car by auto
            also have c3:"... = (Pr\<^bsub>i\<^esub> f) (two_to_n j (?v, aj))"
              using \<open>i\<in>{1..length Ls}\<close> len_ls a_j \<open>i<j\<close> by auto
            finally show "?lhs = ?rhs"
              by auto
          qed
          have R2:"two_to_n j (?v, aj) = (\<lambda>k\<in>{1..length Ls}. if k = i then xi else if k = j then aj else if B k \<noteq> None then the (B k) else nested Ls k (B(j \<mapsto>aj, i \<mapsto> xi)) f)"
          proof (rule vect_eqI)
            show "two_to_n j (?v,aj) \<in> carrier (\<Otimes>Ls)"
              using v_in_car aj_car two_n__carrier[of "j" "?v" "aj"] a_j by auto
          next
            show "(\<lambda>k\<in>{1..length Ls}. if k = i then xi else if k = j then aj else if B k \<noteq> None then the (B k) else nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f) \<in> carrier \<Otimes>Ls"
            proof (rule cart_carrier_criterion)
              fix h assume \<open>h\<in>{1..length Ls}\<close>
              show "(\<lambda>k\<in>{1..length Ls}. if k = i then xi else if k = j then aj else if B k \<noteq> None then the (B k) else nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f) h \<in> carrier (Ls ! (h-1))"
                (is "?conc")
              proof -
                have r1:"(\<lambda>k\<in>{1..length Ls}. if k = i then xi else if k = j then aj else if B k \<noteq> None then the (B k) else nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f) h 
                    = (if h = i then xi else if h = j then aj else if B h \<noteq> None then the (B h) else nested Ls h (B(j \<mapsto> aj, i \<mapsto> xi)) f)"
                  using \<open>h\<in>{1..length Ls}\<close> by auto               
                have s1:"h=i \<Longrightarrow> xi\<in>carrier (Ls ! (h-1))"                   
                  using xi_car by auto                
                have s2:"h=j \<Longrightarrow> aj\<in>carrier (Ls ! (h-1))"                   
                  using aj_car by auto                 
                have s3:"B h \<noteq> None \<Longrightarrow> the (B h)\<in> carrier (Ls ! (h-1))"                    
                  using Suc.prems(2)[of "h"] \<open>h\<in>{1..length Ls}\<close> by auto                  
                have s4:"h\<noteq> i \<Longrightarrow> h\<noteq> j \<Longrightarrow> B h = None \<Longrightarrow> nested Ls h (B(j \<mapsto> aj, i \<mapsto> xi)) f \<in> carrier (Ls ! (h-1))"             
                  using nested_closed[of "h" "B(j \<mapsto> aj, i \<mapsto> xi)"] \<open>h \<in> {1..length Ls}\<close> by auto
                have "(if h = i then xi else if h = j then aj else if B h \<noteq> None then the (B h) else nested Ls h (B(j \<mapsto> aj, i \<mapsto> xi)) f) \<in> carrier (Ls ! (h-1))" 
                  using s1 s2 s3 s4 by auto
                then show "?conc"
                  using r1 by auto
              qed
            next
              fix k assume \<open>k \<notin> {1..length Ls}\<close>
              then show "(\<lambda>k\<in>{1..length Ls}. if k = i then xi else if k = j then aj else if B k \<noteq> None then the (B k) else nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f) k = undefined"
                by auto
            qed
          next
            fix k assume \<open>k\<in>{1..length Ls}\<close>
            show "two_to_n j (?v,aj) k = (\<lambda>k\<in>{1..length Ls}. if k = i then xi else if k = j then aj else if B k \<noteq> None then the (B k) else nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f) k"
              (is "?l=?r")
            proof (cases "j=k")
              case True
              then show ?thesis
              proof -
                have b1:"?l=aj"
                  using two_to_n_simps(1)[of "?v" "j" "aj" "j"] \<open>j=k\<close> a_j aj_car v_in_car by auto
                have b2:"?r=aj"
                  using \<open>j=k\<close> \<open>k\<in>{1..length Ls}\<close> i_lt_j by auto
                show ?thesis 
                  using b1 b2 by auto
              qed
            next
              case False
              then show ?thesis
              proof (cases "i=k")
                case True
                then show ?thesis
                proof -
                  have b1:"?l=xi"
                    using two_to_n_simps(2)[of "?v" "j" "aj" "k"] i_lt_j \<open>i=k\<close> a_j aj_car v_in_car \<open>k\<in>{1..length Ls}\<close> by auto
                  have b2:"?r=xi"
                    using \<open>k\<in>{1..length Ls}\<close> \<open>i=k\<close> by auto
                  show ?thesis 
                    using b1 b2 by auto
                qed
              next
                case False
                then show ?thesis
                proof (cases "k<j")
                  case True
                  then show ?thesis
                  proof -
                    have c1:"Sp\<^bsub>j\<^esub> B k = B k"
                      unfolding specialize_env_def using \<open>k<j\<close> \<open>k\<in>{1..length Ls}\<close> a_j by auto
                    have c2:"?l = ?v k"
                      using two_to_n_simps(2)[of "?v" "j" "aj" "k"] \<open>k\<in>{1..length Ls}\<close> \<open>k<j\<close> a_j aj_car v_in_car by auto
                    have c3:"B k \<noteq> None \<Longrightarrow> ?v k = the (B k)"
                      using c1 \<open>k\<in>{1..length Ls}\<close> \<open>k<j\<close> a_j \<open>i\<noteq>k\<close> by auto
                    have c4:"B k \<noteq> None \<Longrightarrow> ?r = the (B k)"
                      using \<open>k\<in>{1..length Ls}\<close> \<open>i\<noteq>k\<close> \<open>k<j\<close> by auto
                    have c5:"B k\<noteq> None \<Longrightarrow> ?l=?r"
                      using c2 c3 c4 by auto

                    have a_i':"i\<in>{1..length Ls-1}"
                      using a_j \<open>i<j\<close> Suc.prems(1) by auto
                    have d_Bext:"\<And>j. j\<notin>{1..length Ls} \<Longrightarrow> (B(i \<mapsto> xi)) j = None"
                      using \<open>\<And>j. j\<notin>{1..length Ls} \<Longrightarrow> B j = None\<close> a_i'
                      by fastforce
                    have d1:"B k = None \<Longrightarrow> 
                      ?l= nested (SpLs\<^bsub>j\<^esub> Ls) k ((Sp\<^bsub>j\<^esub> B)(i\<mapsto>xi)) (\<lambda>v\<in>carrier_spl Ls j. \<lambda>ja\<in>{1..length Ls - 1}. if ja < j then (Pr\<^bsub>ja\<^esub> f) (two_to_n j (v, aj)) else (Pr\<^bsub>ja + 1\<^esub> f) (two_to_n j (v, aj)))"
                      using c2 \<open>k<j\<close> a_j \<open>i\<noteq>k\<close> \<open>k\<in>{1..length Ls}\<close> c1 length_minus_1 nested.simps by auto
                    have d2:"B k = None \<Longrightarrow>
                      ?r= nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f"
                      using \<open>k\<in>{1..length Ls}\<close> \<open>i\<noteq>k\<close> \<open>k<j\<close> by auto
                    have d3':"\<And>j. j \<in> {1..length Ls} \<Longrightarrow> (B(i \<mapsto> xi)) j \<noteq> None \<Longrightarrow> the ((B(i \<mapsto> xi)) j) \<in> carrier (Ls ! (j-1))"
                      using Suc.prems(2) xi_car 
                      by (metis fun_upd_other fun_upd_same option.sel)
                    from IH[of "k" "xi"] \<open>k<j\<close> i_lt_j d3' \<open>k\<in>{1..length Ls}\<close> Bi_undefined d_Bext
                    have "(k<j \<longrightarrow> nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f = nested (SpLs\<^bsub>j\<^esub> Ls) k (Sp\<^bsub>j\<^esub> (B(i\<mapsto>xi))) (Sp\<^bsub>j,aj\<^esub> f)) \<and>
                          (k>j \<longrightarrow> nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f = nested (SpLs\<^bsub>j\<^esub> Ls) (k-1) (Sp\<^bsub>j\<^esub> (B(i\<mapsto>xi))) (Sp\<^bsub>j,aj\<^esub> f))"
                      by auto
                    then have d3:"B k = None \<Longrightarrow>
                      ?r= nested (SpLs\<^bsub>j\<^esub> Ls) k (Sp\<^bsub>j\<^esub> (B(i\<mapsto>xi))) (Sp\<^bsub>j,aj\<^esub> f)"
                      using \<open>k<j\<close> d2 by auto
                    have d4:"Sp\<^bsub>j\<^esub> (B(i\<mapsto>xi)) = ((Sp\<^bsub>j\<^esub> B)(i\<mapsto>xi))"
                      using special_env_eq(1)[of "i" "j" "B(i\<mapsto>xi)" "B" "xi"] \<open>i < j\<close> a_j a_i' d_Bext \<open>\<And>j. j\<notin>{1..length Ls} \<Longrightarrow> B j = None\<close> by auto
                    have "(Sp\<^bsub>j,aj\<^esub> f) = (\<lambda>v\<in>carrier_spl Ls j. \<lambda>ja\<in>{1..length Ls - 1}. if ja < j then (Pr\<^bsub>ja\<^esub> f) (two_to_n j (v, aj)) else (Pr\<^bsub>ja + 1\<^esub> f) (two_to_n j (v, aj)))"
                      unfolding specialize_fn_def by auto
                    then have d5:"B k = None \<Longrightarrow> ?l=?r"
                      using d1 d3 d4 by auto
                    show "?l=?r"
                      using c5 d5 by auto
                  qed
                next
                  case False
                  then show ?thesis
                    (is "?l=?r")
                  proof -
                    have \<open>k>j\<close>
                      using \<open>\<not>k<j\<close> \<open>j\<noteq>k\<close> by auto
                    then have \<open>k-1\<ge>j\<close> 
                      by simp
                    have \<open>k-1\<in>{1..length Ls-1}\<close>
                      using a_j \<open>k-1\<ge>j\<close> \<open>k\<in>{1..length Ls}\<close> by auto
                    have \<open>i\<noteq>k-1\<close>
                      using \<open>k-1\<ge>j\<close> \<open>i<j\<close> by auto
                    have c1:"(Sp\<^bsub>j\<^esub> B) (k-1) = B k"
                      using \<open>k-1\<ge>j\<close> \<open>k-1\<in>{1..length Ls-1}\<close> unfolding specialize_env_def by auto
                    have c2:"?l = ?v (k-1)"
                      using two_to_n_simps(3)[of "?v" "j" "aj" "k"] \<open>k\<in>{1..length Ls}\<close> \<open>k>j\<close> a_j aj_car v_in_car by auto
                    have c3:"B k \<noteq> None \<Longrightarrow> ?v (k-1) = the (B k)"
                      using c1 \<open>k\<in>{1..length Ls}\<close> \<open>k-1\<ge>j\<close> a_j \<open>i\<noteq>k-1\<close> by auto
                    have c4:"B k \<noteq> None \<Longrightarrow> ?r = the (B k)"
                      using \<open>k\<in>{1..length Ls}\<close> \<open>i\<noteq>k\<close> \<open>k>j\<close> by auto
                    have c5:"B k\<noteq> None \<Longrightarrow> ?l=?r"
                      using c2 c3 c4 by auto
                    have a_i':"i\<in>{1..length Ls-1}"
                      using a_j \<open>i<j\<close> Suc.prems(1) by auto
                    have d_Bext:"\<And>j. j\<notin>{1..length Ls} \<Longrightarrow> (B(i \<mapsto> xi)) j = None"
                      using \<open>\<And>j. j\<notin>{1..length Ls} \<Longrightarrow> B j = None\<close> a_i'
                      by fastforce
                    have d1:"B k = None \<Longrightarrow> 
                      ?l= nested (SpLs\<^bsub>j\<^esub> Ls) (k-1) ((Sp\<^bsub>j\<^esub> B)(i \<mapsto> xi)) (\<lambda>v\<in>carrier_spl Ls j. \<lambda>ja\<in>{1..length Ls - 1}. if ja < j then (Pr\<^bsub>ja\<^esub> f) (two_to_n j (v, aj)) else (Pr\<^bsub>ja + 1\<^esub> f) (two_to_n j (v, aj)))"
                      using c2 \<open>k-1\<ge>j\<close> a_j \<open>i\<noteq>k-1\<close> \<open>k-1\<in>{1..length Ls-1}\<close> c1 length_minus_1 nested.simps by auto
                    have d2:"B k = None \<Longrightarrow>
                      ?r= nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f"
                      using \<open>k\<in>{1..length Ls}\<close> \<open>i\<noteq>k\<close> \<open>k>j\<close> by auto
                    have d3':"\<And>j. j \<in> {1..length Ls} \<Longrightarrow> (B(i \<mapsto> xi)) j \<noteq> None \<Longrightarrow> the ((B(i \<mapsto> xi)) j) \<in> carrier (Ls ! (j-1))"
                      using Suc.prems(2) xi_car 
                      by (metis fun_upd_apply option.sel)
                    from IH[of "k" "xi"] \<open>k>j\<close> i_lt_j d3' \<open>k\<in>{1..length Ls}\<close> Bi_undefined d_Bext
                    have "(k<j \<longrightarrow> nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f = nested (SpLs\<^bsub>j\<^esub> Ls) k (Sp\<^bsub>j\<^esub> (B(i\<mapsto>xi))) (Sp\<^bsub>j,aj\<^esub> f)) \<and>
                          (k>j \<longrightarrow> nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f = nested (SpLs\<^bsub>j\<^esub> Ls) (k-1) (Sp\<^bsub>j\<^esub> (B(i\<mapsto>xi))) (Sp\<^bsub>j,aj\<^esub> f))"
                      by auto
                    then have d3:"B k = None \<Longrightarrow>
                      ?r= nested (SpLs\<^bsub>j\<^esub> Ls) (k-1) (Sp\<^bsub>j\<^esub> (B(i\<mapsto>xi))) (Sp\<^bsub>j,aj\<^esub> f)"
                      using \<open>k>j\<close> d2 by auto
                    have d4:"Sp\<^bsub>j\<^esub> (B(i\<mapsto>xi)) = ((Sp\<^bsub>j\<^esub> B)(i\<mapsto>xi))"
                      using special_env_eq(1)[of "i" "j" "B(i\<mapsto>xi)" "B" "xi"] \<open>i < j\<close> a_j a_i' d_Bext \<open>\<And>j. j\<notin>{1..length Ls} \<Longrightarrow> B j = None\<close> by auto
                    have "(Sp\<^bsub>j,aj\<^esub> f) = (\<lambda>v\<in>carrier_spl Ls j. \<lambda>ja\<in>{1..length Ls - 1}. if ja < j then (Pr\<^bsub>ja\<^esub> f) (two_to_n j (v, aj)) else (Pr\<^bsub>ja + 1\<^esub> f) (two_to_n j (v, aj)))"
                      unfolding specialize_fn_def by auto
                    then have d5:"B k = None \<Longrightarrow> ?l=?r"
                      using d1 d3 d4 by auto
                    show "?l=?r"
                      using c5 d5 by auto
                  qed
                qed
              qed
            qed
          qed
          show "(Pr\<^bsub>i\<^esub> f) (\<lambda>k\<in>{1..length Ls}. if k=i then xi else if k=j then aj else if B k\<noteq>None then the (B k) else nested Ls k (B(j\<mapsto>aj,i\<mapsto>xi)) f) =
                (Pr\<^bsub>i\<^esub> (\<lambda>v\<in>carrier_spl Ls j. \<lambda>ja\<in>{1..length Ls - 1}. if ja < j then (Pr\<^bsub>ja\<^esub> f) (two_to_n j (v, aj)) else (Pr\<^bsub>ja + 1\<^esub> f) (two_to_n j (v, aj)))) ?v"
            using R1 R2 by auto
        qed
        then have lem3_i_lt_j:"\<And>xi. xi\<in>carrier (Ls ! (i-1)) \<Longrightarrow> B i = None
          \<Longrightarrow> i<j 
          \<Longrightarrow> (Pr\<^bsub>i\<^esub> f) (\<lambda>(k::nat)\<in>{1..length Ls}. if k=i then xi else if k=j then aj else if B k\<noteq> None then the (B k) else nested Ls k (B(j\<mapsto>aj,i\<mapsto>xi)) f) = 
              (Pr\<^bsub>i\<^esub> (Sp\<^bsub>j,aj\<^esub> f)) (\<lambda>(h::nat)\<in>{1..length Ls-1}. 
                if h=i then xi else if (Sp\<^bsub>j\<^esub> B) h \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) h) 
                  else nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i\<mapsto>xi)) (Sp\<^bsub>j,aj\<^esub> f))"                
          by presburger
        have lem4_i_lt_j: "B i = None
          \<Longrightarrow> i<j
          \<Longrightarrow> nested (SpLs\<^bsub>j\<^esub> Ls) i (Sp\<^bsub>j\<^esub> B) (Sp\<^bsub>j,aj\<^esub> f)
              = LFP\<^bsub>(Ls ! (i-1))\<^esub> (\<lambda>xi\<in>carrier (Ls ! (i-1)). 
                (Pr\<^bsub>i\<^esub> (Sp\<^bsub>j,aj\<^esub> f)) (\<lambda>h\<in>{1..length Ls - 1}. if h = i then xi else if ((Sp\<^bsub>j\<^esub> B) h) \<noteq> None then the (((Sp\<^bsub>j\<^esub> B) h)) else nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i\<mapsto>xi)) (Sp\<^bsub>j,aj\<^esub> f)))"
          (is "?one \<Longrightarrow> ?two \<Longrightarrow> ?l=?r")
        proof -
          assume Bi_undefined:"B i =None" and \<open>i<j\<close>
          have \<open>i\<in>{1..length Ls-1}\<close>
            using \<open>i<j\<close> a_j \<open>i\<in>{1..length Ls}\<close> by auto
          have \<open>Sp\<^bsub>j\<^esub> B i = B i\<close>
            using \<open>i<j\<close> \<open>i\<in>{1..length Ls-1}\<close> unfolding specialize_env_def by auto
          have "?l=(if i \<notin> {1..length SpLs\<^bsub>j\<^esub> Ls} then undefined
          else if Sp\<^bsub>j\<^esub> B i \<noteq> None then undefined
          else LFP\<^bsub>(SpLs\<^bsub>j\<^esub> Ls) ! (i-1)\<^esub>
                (\<lambda>xi\<in>carrier (SpLs\<^bsub>j\<^esub> Ls ! (i-1)). Pr\<^bsub>i\<^esub> (Sp\<^bsub>j,aj\<^esub> f) (\<lambda>ja\<in>{1..length SpLs\<^bsub>j\<^esub> Ls}. if ja = i then xi else if (Sp\<^bsub>j\<^esub> B) ja \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) ja) else nested (SpLs\<^bsub>j\<^esub> Ls) ja ((Sp\<^bsub>j\<^esub> B)(i \<mapsto> xi)) (Sp\<^bsub>j,aj\<^esub> f))))"
            using nested.simps[of "SpLs\<^bsub>j\<^esub> Ls" "i" "Sp\<^bsub>j\<^esub> B" "Sp\<^bsub>j,aj\<^esub> f"] by auto
          also have "... = (if i \<notin> {1..length Ls-1} then undefined
                else LFP\<^bsub>(SpLs\<^bsub>j\<^esub> Ls) ! (i-1)\<^esub>
                (\<lambda>xi\<in>carrier (SpLs\<^bsub>j\<^esub> Ls ! (i-1)). 
                Pr\<^bsub>i\<^esub> (Sp\<^bsub>j,aj\<^esub> f) (\<lambda>ja\<in>{1..length Ls-1}. if ja = i then xi else if (Sp\<^bsub>j\<^esub> B) ja \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) ja) else nested (SpLs\<^bsub>j\<^esub> Ls) ja ((Sp\<^bsub>j\<^esub> B)(i \<mapsto> xi)) (Sp\<^bsub>j,aj\<^esub> f))))"
            using length_minus_1[of "j" "Ls"] a_j \<open>Sp\<^bsub>j\<^esub> B i = B i\<close> Bi_undefined unfolding Sp_Ls_def by presburger
          also have "... = (
                LFP\<^bsub>Ls ! (i-1)\<^esub>
                (\<lambda>xi\<in>carrier (Ls!(i-1)). 
                Pr\<^bsub>i\<^esub> (Sp\<^bsub>j,aj\<^esub> f) (\<lambda>ja\<in>{1..length Ls - 1}. if ja = i then xi else if (Sp\<^bsub>j\<^esub> B) ja \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) ja) else nested (SpLs\<^bsub>j\<^esub> Ls) ja ((Sp\<^bsub>j\<^esub> B)(i \<mapsto> xi)) (Sp\<^bsub>j,aj\<^esub> f))))"
            using \<open>i\<in>{1..length Ls-1}\<close> remove_at_nth_lt[of "j" "Ls" "i"] \<open>i<j\<close> a_j unfolding Sp_Ls_def get_member_def by auto
          finally show "?l = ?r"
            by auto
        qed
        then have lem5_i_lt_j:"B i =None
          \<Longrightarrow> i<j
          \<Longrightarrow> nested Ls i (B(j\<mapsto>aj)) f = nested (SpLs\<^bsub>j\<^esub> Ls) i (Sp\<^bsub>j\<^esub> B) (Sp\<^bsub>j,aj\<^esub> f)"
          using lem1 lem3_i_lt_j by (smt (verit, ccfv_SIG) nat_neq_iff restrict_ext)
        have lem6_i_lt_j:"B i \<noteq> None \<Longrightarrow> i<j \<Longrightarrow> nested Ls i (B(j \<mapsto> aj)) f = nested (SpLs\<^bsub>j\<^esub> Ls) i (Sp\<^bsub>j\<^esub> B) (Sp\<^bsub>j,aj\<^esub> f)"
          using nested_simps_defined[of "i"] \<open>i\<in>{1..length Ls}\<close> a_j unfolding specialize_env_def by auto
        then have claim_i_lt_j:"i<j \<longrightarrow> nested Ls i (B(j \<mapsto> aj)) f = nested (SpLs\<^bsub>j\<^esub> Ls) i (Sp\<^bsub>j\<^esub> B) (Sp\<^bsub>j,aj\<^esub> f)"
          using lem5_i_lt_j by auto

        have lem2_i_gt_j:"\<And>xi. xi\<in>carrier (Ls ! (i-1)) \<Longrightarrow> B i = None
          \<Longrightarrow> i>j
          \<Longrightarrow> (Pr\<^bsub>i\<^esub> f) (\<lambda>k\<in>{1..length Ls}. if k=i then xi else if k=j then aj else if B k\<noteq> None then the (B k) else nested Ls k (B(j\<mapsto>aj,i\<mapsto>xi)) f) = 
              (Pr\<^bsub>i-1\<^esub> (Sp\<^bsub>j,aj\<^esub> f)) (\<lambda>h\<in>{1..length Ls-1}. 
                if h=i-1 then xi else if (Sp\<^bsub>j\<^esub> B) h \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) h) 
                  else
                  if h<j then nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i-1\<mapsto>xi)) (Sp\<^bsub>j,aj\<^esub> f) 
                     else nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i-1\<mapsto>xi)) (Sp\<^bsub>j,aj\<^esub> f))"
        proof -
          fix xi assume i_gt_j:"i>j" and xi_car:"xi\<in>carrier (Ls !(i-1))" and Bi_undefined:"B i=None"
          show "(Pr\<^bsub>i\<^esub> f) (\<lambda>k\<in>{1..length Ls}. if k=i then xi else if k=j then aj else if B k\<noteq>None then the (B k) else nested Ls k (B(j\<mapsto>aj,i\<mapsto>xi)) f) = 
              (Pr\<^bsub>i-1\<^esub> (Sp\<^bsub>j,aj\<^esub> f)) (\<lambda>h\<in>{1..length Ls-1}. 
                if h=i-1 then xi else if (Sp\<^bsub>j\<^esub> B) h \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) h) 
                  else
                  if h<j then nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i-1\<mapsto>xi)) (Sp\<^bsub>j,aj\<^esub> f) 
                     else nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i-1\<mapsto>xi)) (Sp\<^bsub>j,aj\<^esub> f))"
            (is "?l=?r")
          proof -
            have b1:"(\<lambda>k\<in>{1..length Ls}. if k = i then xi else if k = j then aj else if B k \<noteq> None then the (B k) else nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f) j = aj"
              using a_j \<open>i>j\<close> by auto
            have b2:"(\<lambda>k\<in>{1..length Ls}. if k = i then xi else if k = j then aj else if B k \<noteq> None then the (B k) else nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f) \<in> carrier \<Otimes>Ls"
            proof (rule cart_carrier_criterion)
              fix k assume \<open>k \<in> {1..length Ls}\<close>
              show "(\<lambda>k\<in>{1..length Ls}. if k = i then xi else if k = j then aj else if B k \<noteq> None then the (B k) else nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f) k \<in> carrier (Ls ! (k-1))"
              proof (cases "k=i")
                case True
                then show ?thesis 
                  using \<open>i\<in>{1..length Ls}\<close> xi_car by auto
              next
                case False
                then show ?thesis
                proof (cases "k=j")
                  case True
                  then show ?thesis 
                    using a_j aj_car \<open>k\<noteq>i\<close> by auto
                next
                  case False
                  then show ?thesis 
                  proof (cases "B k\<noteq>None")
                    case True
                    then show ?thesis 
                      using Suc.prems(2)[of "k"] \<open>k \<in> {1..length Ls}\<close> \<open>k\<noteq>j\<close> Bi_undefined by auto
                  next
                    case False
                    then show ?thesis
                      using nested_closed[of "k" "B(j \<mapsto> aj, i \<mapsto> xi)" "f"] \<open>k\<noteq>i\<close> \<open>k\<noteq>j\<close> \<open>k \<in> {1..length Ls}\<close> by auto
                  qed
                qed
              qed
            next
              fix k assume "k \<notin> {1..length Ls}"
              then show "(\<lambda>k\<in>{1..length Ls}. if k = i then xi else if k = j then aj else if B k \<noteq> None then the (B k) else nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f) k = undefined"
                by auto
            qed
            have b3:"(fst (n_to_two j (\<lambda>k\<in>{1..length Ls}. if k = i then xi else if k = j then aj else if B k \<noteq> None then the (B k) else nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f)))
              = (\<lambda>h\<in>{1..length Ls - 1}.
                if h = i - 1 then xi 
                else if (Sp\<^bsub>j\<^esub> B) h \<noteq> None then the (Sp\<^bsub>j\<^esub> B h)
                else if h < j then nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) (Sp\<^bsub>j,aj\<^esub> f) else nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) (Sp\<^bsub>j,aj\<^esub> f))"
            proof (rule j_sub_locale.vect_eqI)
              show "fst (n_to_two j (\<lambda>k\<in>{1..length Ls}. if k = i then xi else if k = j then aj else if B k \<noteq> None then the (B k) else nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f)) \<in> carrier \<Otimes>SpLs\<^bsub>j\<^esub> Ls"
              proof (rule in_carrier_spl_I')
                show "j \<in> {1..length Ls}"
                  using a_j by auto
              next
                fix h assume \<open>h \<in> {1..length Ls - 1}\<close>
                show "\<And>h. h \<in> {1..length Ls - 1} \<Longrightarrow>
                      (h < j \<longrightarrow> fst (n_to_two j (\<lambda>k\<in>{1..length Ls}. if k = i then xi else if k = j then aj else if B k \<noteq> None then the (B k) else nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f)) h \<in> carrier (Ls ! (h-1))) \<and>
                      (j \<le> h \<longrightarrow> fst (n_to_two j (\<lambda>k\<in>{1..length Ls}. if k = i then xi else if k = j then aj else if B k \<noteq> None then the (B k) else nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f)) h \<in> carrier (Ls ! h))"
                  using a_j b2 cart_prod_lattice.carrier_spl_criterion cart_prod_lattice.n_to_two_in_carrier cart_prod_lattice_axioms by blast
              next
                fix y assume \<open>y\<notin>{1..length Ls - 1}\<close>
                show "fst (n_to_two j (\<lambda>k\<in>{1..length Ls}. if k = i then xi else if k = j then aj else if B k \<noteq> None then the (B k) else nested Ls k (B(j \<mapsto> aj, i \<mapsto>xi)) f)) y = undefined"
                  using \<open>y \<notin> {1..length Ls - 1}\<close> n_to_two_fst_ext by blast
              qed
            next
              show "(\<lambda>h\<in>{1..length Ls - 1}.
        if h = i - 1 then xi else if (Sp\<^bsub>j\<^esub> B) h \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) h) else if h < j then nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) (Sp\<^bsub>j,aj\<^esub> f) else nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) Sp\<^bsub>j,aj\<^esub> f)
                \<in> carrier \<Otimes>SpLs\<^bsub>j\<^esub> Ls"
              proof (rule in_carrier_spl_I')
                show "j \<in> {1..length Ls}"
                  using a_j by auto
              next
                fix h assume \<open>h \<in> {1..length Ls - 1}\<close>
                show "(h < j \<longrightarrow> 
         (\<lambda>h\<in>{1..length Ls - 1}.
              if h = i - 1 then xi else if (Sp\<^bsub>j\<^esub> B) h \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) h) else if h < j then nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) (Sp\<^bsub>j,aj\<^esub> f) else nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) Sp\<^bsub>j,aj\<^esub> f)
           h \<in> carrier (Ls ! (h-1))) \<and>
         (j \<le> h \<longrightarrow> (\<lambda>h\<in>{1..length Ls - 1}.
              if h = i - 1 then xi else if (Sp\<^bsub>j\<^esub> B) h \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) h) else if h < j then nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) (Sp\<^bsub>j,aj\<^esub> f) else nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) Sp\<^bsub>j,aj\<^esub> f)
           h \<in> carrier (Ls ! h))"
                proof -
                  have d1:"h<j \<Longrightarrow>
          (\<lambda>h\<in>{1..length Ls - 1}.
              if h = i - 1 then xi else if (Sp\<^bsub>j\<^esub> B) h \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) h) else if h < j then nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) (Sp\<^bsub>j,aj\<^esub> f) else nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) Sp\<^bsub>j,aj\<^esub> f)
           h \<in> carrier (Ls ! (h-1))"
                  proof -
                    assume \<open>h<j\<close>
                    then have \<open>h\<noteq>i-1\<close>
                      using \<open>j<i\<close> by linarith
                    have "h\<noteq>i-1 \<Longrightarrow> (Sp\<^bsub>j\<^esub> B) h = None \<Longrightarrow> nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) (Sp\<^bsub>j,aj\<^esub> f) \<in> carrier (SpLs\<^bsub>j\<^esub> Ls ! (h-1))"
                      using j_sub_locale.nested_closed[of "h" "(Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)" "Sp\<^bsub>j,aj\<^esub> f"] length_minus_1 \<open>h \<in> {1..length Ls - 1}\<close> unfolding Sp_Ls_def
                      by (metis a_j fun_upd_other)
                    then have b1:"h\<noteq>i-1 \<Longrightarrow> (Sp\<^bsub>j\<^esub> B) h = None \<Longrightarrow> nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) (Sp\<^bsub>j,aj\<^esub> f) \<in> carrier (Ls ! (h-1))"
                      unfolding Sp_Ls_def get_member_def using remove_at_nth_lt[of "j" "Ls" "h"] \<open>h<j\<close> \<open>h \<in> {1..length Ls - 1}\<close> a_j by auto
                    have b2:"Sp\<^bsub>j\<^esub> B h \<noteq> None \<Longrightarrow> the ((Sp\<^bsub>j\<^esub> B) h) \<in>carrier (Ls!(h-1))"
                      unfolding specialize_env_def using \<open>h<j\<close> Suc.prems(2)[of "h"] \<open>h \<in> {1..length Ls - 1}\<close> by auto
                    then show ?thesis
                      using b1 b2 \<open>h\<noteq>i-1\<close> \<open>h \<in> {1..length Ls - 1}\<close> \<open>h<j\<close> by auto
                  qed
                  have d2:"j \<le> h \<Longrightarrow>
    (\<lambda>h\<in>{1..length Ls - 1}.
        if h = i - 1 then xi else if (Sp\<^bsub>j\<^esub> B) h \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) h) else if h < j then nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) (Sp\<^bsub>j,aj\<^esub> f) else nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) Sp\<^bsub>j,aj\<^esub> f)
     h
    \<in> carrier (Ls ! h)"
                  proof -
                    assume \<open>j \<le> h\<close>
                    have "h\<noteq>i-1 \<Longrightarrow> (Sp\<^bsub>j\<^esub> B) h = None \<Longrightarrow> nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) (Sp\<^bsub>j,aj\<^esub> f) \<in> carrier (SpLs\<^bsub>j\<^esub> Ls ! (h-1))"
                      using j_sub_locale.nested_closed[of "h" "(Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)" "Sp\<^bsub>j,aj\<^esub> f"] length_minus_1 \<open>h \<in> {1..length Ls - 1}\<close> unfolding Sp_Ls_def
                      by (metis a_j fun_upd_other)
                    then have b1:"h\<noteq>i-1 \<Longrightarrow> (Sp\<^bsub>j\<^esub> B) h = None \<Longrightarrow> nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) (Sp\<^bsub>j,aj\<^esub> f) \<in> carrier (Ls ! h)"
                      unfolding Sp_Ls_def get_member_def using remove_at_nth_ge[of "j" "Ls" "h"] \<open>j \<le> h\<close> \<open>h \<in> {1..length Ls - 1}\<close> a_j by auto
                    have b2:"Sp\<^bsub>j\<^esub> B h \<noteq> None \<Longrightarrow> the (Sp\<^bsub>j\<^esub> B h) \<in>carrier (Ls!h)"
                      unfolding specialize_env_def using \<open>j \<le> h\<close> Suc.prems(2)[of "h+1"] \<open>h \<in> {1..length Ls - 1}\<close> by auto
                    then show ?thesis
                      using b1 b2 xi_car \<open>h \<in> {1..length Ls - 1}\<close> \<open>j \<le> h\<close> by auto
                  qed
                  show ?thesis 
                    using d1 d2 by auto
                qed
              next
                fix y assume \<open>y\<notin> {1..length Ls - 1}\<close>
                show "(\<lambda>h\<in>{1..length Ls - 1}.
             if h = i - 1 then xi else if (Sp\<^bsub>j\<^esub> B) h \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) h) else if h < j then nested SpLs\<^bsub>j\<^esub> Ls h ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) Sp\<^bsub>j,aj\<^esub> f else nested SpLs\<^bsub>j\<^esub> Ls h ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) Sp\<^bsub>j,aj\<^esub> f)
                  y = undefined"
                  by (meson FuncSet.restrict_apply \<open>y \<notin> {1..length Ls - 1}\<close>)
              qed
            next
              fix k assume a_k:"k \<in> {1..length SpLs\<^bsub>j\<^esub> Ls}"
              show "fst (n_to_two j (\<lambda>k\<in>{1..length Ls}. if k = i then xi else if k = j then aj else if B k \<noteq> None then the (B k) else nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f)) k =
         (\<lambda>h\<in>{1..length Ls - 1}.
             if h = i - 1 then xi else if (Sp\<^bsub>j\<^esub> B) h \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) h) else if h < j then nested SpLs\<^bsub>j\<^esub> Ls h ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) Sp\<^bsub>j,aj\<^esub> f else nested SpLs\<^bsub>j\<^esub> Ls h ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) Sp\<^bsub>j,aj\<^esub> f)
          k"
                (is "?l=?r1")
              proof -
                have b1:"?r1 = (\<lambda>h\<in>{1..length Ls - 1}. if h = i - 1 then xi else if (Sp\<^bsub>j\<^esub> B) h \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) h) else nested SpLs\<^bsub>j\<^esub> Ls h ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) Sp\<^bsub>j,aj\<^esub> f) k"
                  (is "_=?r2")
                  by auto
                have "?l =?r2"
                proof -
                  have \<open>i-1 \<ge>j\<close> 
                    using \<open>j<i\<close> by auto
                  then have \<open>i-1\<in>{1..length Ls-1}\<close>
                    using a_j \<open>i \<in> {1..length Ls}\<close> by auto
                  have b11:"k=i-1 \<Longrightarrow> ?l=xi" 
                    using n_to_two_simps_geq[of "i-1" "j"] \<open>i-1\<in>{1..length Ls-1}\<close> \<open>i-1 \<ge>j\<close> by auto
                  have b12:"k=i-1 \<Longrightarrow> ?r2=xi"
                    using a_k \<open>i - 1 \<in> {1..length Ls - 1}\<close> by auto
                  have b1:"k=i-1 \<Longrightarrow> ?l=?r2"
                    using b11 b12 by auto

                  have b21:"k<j \<Longrightarrow> B k \<noteq>None \<Longrightarrow> ?l=the (B k)"
                    using n_to_two_simps_lt[of "k" "j"] \<open>i-1 \<ge>j\<close> a_j a_k by auto
                  have b221:"k<j \<Longrightarrow> (Sp\<^bsub>j\<^esub> B) k = B k"
                    using specialize_env_simps a_k length_minus_1 a_j unfolding Sp_Ls_def by auto
                  have b222:"k<j \<Longrightarrow> B k \<noteq>None \<Longrightarrow> ?r2 = the (B k)"
                    using b221 a_k \<open>i-1 \<ge>j\<close> a_j by auto
                  have b2:"k<j \<Longrightarrow> B k \<noteq>None \<Longrightarrow> ?l=?r2"
                    using b21 b222 by auto

                  have b3:"k<j \<Longrightarrow> B k = None \<Longrightarrow> ?l=?r2"
                  proof -
                    assume \<open>k<j\<close> and \<open>B k = None\<close>
                    have b33:"?l = nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f"
                      using \<open>i-1 \<ge>j\<close> a_j a_k n_to_two_simps_lt[of "k" "j"] length_minus_1 \<open>B k = None\<close> \<open>k<j\<close> unfolding Sp_Ls_def by auto
                    have b34:"?r2 = nested (SpLs\<^bsub>j\<^esub> Ls) k ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) (Sp\<^bsub>j,aj\<^esub> f)"
                      using b221 \<open>B k = None\<close> a_k length_minus_1'[of "j" "Ls"] a_j \<open>i-1 \<ge>j\<close> a_j a_k \<open>k < j\<close> by auto
                    have b31:"\<And>j. j\<notin>{1..length Ls} \<Longrightarrow> (B(i \<mapsto>xi)) j = None"
                      using a_i Suc.prems by fastforce
                    have b32:"\<And>j. j \<in> {1..length Ls} \<Longrightarrow> (B(i \<mapsto>xi)) j \<noteq> None \<Longrightarrow> the ((B(i \<mapsto> xi)) j) \<in> carrier (Ls ! (j-1))"
                      using Suc.prems xi_car 
                      by (metis fun_upd_apply option.sel)
                    have "\<And>k. k \<in> {1..length Ls} \<Longrightarrow> k \<noteq> i \<Longrightarrow> k \<noteq> j \<Longrightarrow> (B(i \<mapsto> xi)) k = B k"
                      by auto
                    then have b35:"Sp\<^bsub>j\<^esub> (B(i \<mapsto> xi)) = (Sp\<^bsub>j\<^esub> B)(i-1\<mapsto>xi)"
                      using special_env_eq(2)[where B="B(i \<mapsto> xi)" and i="i-1" and xi="xi" and C="B" and j="j"] \<open>i-1 \<ge>j\<close> \<open>i-1\<in>{1..length Ls-1}\<close> a_j b31 Suc.prems(3) by auto
                    have "nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f = nested (SpLs\<^bsub>j\<^esub> Ls) k Sp\<^bsub>j\<^esub> B(i\<mapsto>xi) (Sp\<^bsub>j,aj\<^esub> f)"
                      using IH[of "k" "xi"] a_k \<open>k < j\<close> xi_car \<open>B k = None\<close> b31 b32 Bi_undefined a_j i_gt_j by auto
                    then show "?l=?r2"
                      using b33 b34 b35 by auto
                  qed
                  have a_k': "k\<in>{1..length Ls-1}"
                    using a_k length_minus_1' a_j by auto
                  have b4:"k\<ge>j \<Longrightarrow> k\<noteq>i-1 \<Longrightarrow> ?l = ?r2"
                  proof -
                    assume \<open>k\<ge>j\<close> and \<open>k\<noteq>i-1\<close>
                    then have "?l = (if k+1 = i then xi else if k+1 = j then aj else if B (k+1) \<noteq> None then the (B (k+1)) else nested Ls (k+1) (B(j \<mapsto>aj, i \<mapsto> xi)) f)"
                      using n_to_two_simps_geq[of "k" "j"] a_k' by auto
                    also have "... = (if B (k+1) \<noteq> None then the (B (k+1)) else nested Ls (k+1) (B(j \<mapsto> aj, i \<mapsto> xi)) f)"
                      (is "_=?l2")
                      using \<open>k\<noteq>i-1\<close> \<open>k\<ge>j\<close> by auto
                    finally have b47:"?l=?l2"
                      by simp
                    have b41:"\<And>j. j\<notin>{1..length Ls} \<Longrightarrow> (B(i \<mapsto>xi)) j = None"
                      using a_i Suc.prems by fastforce
                    have b42:"\<And>j. j \<in> {1..length Ls} \<Longrightarrow> (B(i \<mapsto> xi)) j \<noteq> None \<Longrightarrow> the ((B(i \<mapsto> xi)) j) \<in> carrier (Ls !(j-1))"
                      using Suc.prems xi_car 
                      by (metis fun_upd_apply option.sel)
                    have "Sp\<^bsub>j\<^esub> B k = B (k+1)"
                      using specialize_env_simps(2) \<open>k\<ge>j\<close> a_k' by auto
                    then have b48:"?r2 = (if B (k+1) \<noteq> None then the (B (k+1)) else nested SpLs\<^bsub>j\<^esub> Ls k ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) (Sp\<^bsub>j,aj\<^esub> f))"
                      (is "_=?r3")
                      using a_k' \<open>k\<noteq>i-1\<close> by auto
                    have b43:"k + 1 \<in> {1..length Ls}"
                      using a_k' by auto
                    have b44:"i\<noteq>j"
                      using i_gt_j by auto
                    have b45:"j<k+1"
                      using \<open>k\<ge>j\<close> by auto
                    then have b46:"Sp\<^bsub>j\<^esub> (B(i \<mapsto> xi)) = (Sp\<^bsub>j\<^esub> B)(i-1\<mapsto>xi)"
                      using special_env_eq(2)[where B="B(i \<mapsto> xi)" and i="i-1" and xi="xi" and C="B" and j="j"] \<open>i-1 \<ge>j\<close> \<open>i-1\<in>{1..length Ls-1}\<close> a_j b41 Suc.prems(3) by auto
                    have "nested Ls (k+1) (B(j \<mapsto> aj, i\<mapsto> xi)) f = nested (SpLs\<^bsub>j\<^esub> Ls) k (Sp\<^bsub>j\<^esub> (B(i \<mapsto> xi))) (Sp\<^bsub>j,aj\<^esub> f)"
                      using IH[of "k+1" "xi"] a_k' b45 Bi_undefined a_j b44 b41 b42 b43 by auto
                    then have "?l2=?r3"
                      using b46 by auto
                    then show "?l=?r2"
                      using b47 b48 by auto
                  qed
                  show "?l =?r2"
                    using b1 b2 b3 b4 \<open>i>j\<close> le_geq_cases by blast
                qed
                then show "?l=?r1"
                  using b1 by auto
              qed
            qed
            show "?l=?r"
              using specialize_proj_eq(2)[where j="j" and i="i" and f="f" and aj="aj"
                 and x="(\<lambda>k\<in>{1..length Ls}. if k = i then xi else if k = j then aj else if B k \<noteq> None then the (B k) else nested Ls k (B(j \<mapsto> aj, i \<mapsto> xi)) f)"]
              a_j \<open>i\<in>{1..length Ls}\<close> \<open>j < i\<close> b1 b2 b3 by auto
          qed
        qed
        then have lem2'_i_gt_j:"\<And>xi. xi\<in>carrier (Ls ! (i-1)) \<Longrightarrow> B i =None
          \<Longrightarrow> i>j
          \<Longrightarrow> (Pr\<^bsub>i\<^esub> f) (\<lambda>k\<in>{1..length Ls}. if k=i then xi else if k=j then aj else if B k\<noteq>None then the (B k) else nested Ls k (B(j\<mapsto>aj,i\<mapsto>xi)) f) = 
              (Pr\<^bsub>i-1\<^esub> (Sp\<^bsub>j,aj\<^esub> f)) (\<lambda>h\<in>{1..length Ls-1}. 
                if h=i-1 then xi else if (Sp\<^bsub>j\<^esub> B) h \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) h) 
                  else nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i-1\<mapsto>xi)) (Sp\<^bsub>j,aj\<^esub> f))"
          by presburger
        
        have claim'_i_gt_j:"j < i \<Longrightarrow> B i = None \<Longrightarrow> nested Ls i (B(j \<mapsto> aj)) f = nested SpLs\<^bsub>j\<^esub> Ls (i - 1) Sp\<^bsub>j\<^esub> B Sp\<^bsub>j,aj\<^esub> f"
        proof -
          assume \<open>j<i\<close> and \<open>B i = None\<close>
          have "nested Ls i (B(j \<mapsto> aj)) f = (
            LFP\<^bsub>(Ls ! (i-1))\<^esub> 
            (\<lambda>xi\<in>carrier (Ls ! (i-1)). 
                       (Pr\<^bsub>i\<^esub> f) (\<lambda>k\<in>{1..length Ls}. if k=i then xi else if k=j then aj else if B k\<noteq>None then the (B k) else nested Ls k (B(j\<mapsto>aj,i\<mapsto>xi)) f)))"
            using lem1 \<open>j<i\<close> \<open>B i = None\<close> by auto
          also have "... = LFP\<^bsub>(Ls ! (i-1))\<^esub> 
            (\<lambda>xi\<in>carrier (Ls ! (i-1)). (Pr\<^bsub>i-1\<^esub> (Sp\<^bsub>j,aj\<^esub> f)) (\<lambda>h\<in>{1..length Ls-1}. if h=i-1 then xi else if (Sp\<^bsub>j\<^esub> B) h \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) h) else nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i-1\<mapsto>xi)) (Sp\<^bsub>j,aj\<^esub> f)))"
            using lem2'_i_gt_j \<open>j<i\<close> \<open>B i = None\<close> by (smt (verit) restrict_ext)
          finally have l1:"nested Ls i (B(j \<mapsto> aj)) f = LFP\<^bsub>(Ls ! (i-1))\<^esub> 
            (\<lambda>xi\<in>carrier (Ls ! (i-1)). (Pr\<^bsub>i-1\<^esub> (Sp\<^bsub>j,aj\<^esub> f)) (\<lambda>h\<in>{1..length Ls-1}. if h=i-1 then xi else if (Sp\<^bsub>j\<^esub> B) h \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) h) else nested (SpLs\<^bsub>j\<^esub> Ls) h ((Sp\<^bsub>j\<^esub> B)(i-1\<mapsto>xi)) (Sp\<^bsub>j,aj\<^esub> f)))"
            by simp

          have b51:"i - 1 \<in> {1..length Ls}"
            using \<open>i \<in> {1..length Ls}\<close> a_j \<open>j<i\<close> by auto
          have b52:"j \<le> i - 1"
            using \<open>j<i\<close> by auto
          have "nested (SpLs\<^bsub>j\<^esub> Ls) (i - 1) (Sp\<^bsub>j\<^esub> B) (Sp\<^bsub>j,aj\<^esub> f) = (if i - 1 \<notin> {1..length (SpLs\<^bsub>j\<^esub> Ls)} then undefined
        else if (Sp\<^bsub>j\<^esub> B) (i - 1) \<noteq> None then undefined
        else LFP\<^bsub>((SpLs\<^bsub>j\<^esub> Ls) ! (i - 2))\<^esub>
              (\<lambda>xi\<in>carrier ((SpLs\<^bsub>j\<^esub> Ls) ! (i - 2)).
                  Pr\<^bsub>i - 1\<^esub> (Sp\<^bsub>j,aj\<^esub> f) (\<lambda>ja\<in>{1..length (SpLs\<^bsub>j\<^esub> Ls)}. if ja = i - 1 then xi else if (Sp\<^bsub>j\<^esub> B) ja \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) ja) else nested (SpLs\<^bsub>j\<^esub> Ls) ja ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) (Sp\<^bsub>j,aj\<^esub> f))))"
            using nested.simps[of "SpLs\<^bsub>j\<^esub> Ls" "i - 1" "Sp\<^bsub>j\<^esub> B" "Sp\<^bsub>j,aj\<^esub> f"] 
            by (metis (no_types, lifting) Suc_1 diff_Suc_eq_diff_pred)
          also have "... = (if (Sp\<^bsub>j\<^esub> B) (i - 1) \<noteq> None then undefined else
              LFP\<^bsub>SpLs\<^bsub>j\<^esub> Ls ! (i - 2)\<^esub>
              (\<lambda>xi\<in>carrier (SpLs\<^bsub>j\<^esub> Ls ! (i - 2)).
                 Pr\<^bsub>i - 1\<^esub> (Sp\<^bsub>j,aj\<^esub> f) (\<lambda>ja\<in>{1..length SpLs\<^bsub>j\<^esub> Ls}. if ja = i - 1 then xi else if (Sp\<^bsub>j\<^esub> B) ja \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) ja) else nested (SpLs\<^bsub>j\<^esub> Ls) ja ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) Sp\<^bsub>j,aj\<^esub> f)))"
            using \<open>i\<in>{1..length Ls}\<close> a_j \<open>i>j\<close> by auto
          also have "... = LFP\<^bsub>SpLs\<^bsub>j\<^esub> Ls ! (i - 2)\<^esub>
              (\<lambda>xi\<in>carrier (SpLs\<^bsub>j\<^esub> Ls ! (i - 2)).
                 Pr\<^bsub>i - 1\<^esub> (Sp\<^bsub>j,aj\<^esub> f) (\<lambda>ja\<in>{1..length SpLs\<^bsub>j\<^esub> Ls}. if ja = i - 1 then xi else if (Sp\<^bsub>j\<^esub> B) ja \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) ja) else nested (SpLs\<^bsub>j\<^esub> Ls) ja ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) Sp\<^bsub>j,aj\<^esub> f))"
            using \<open>B i=None\<close> specialize_env_simps(2)[of "i-1" "j" "B"] \<open>i>j\<close> \<open>i\<in>{1..length Ls}\<close> a_j by auto
          also have "... = LFP\<^bsub>Ls ! (i-1)\<^esub>
              (\<lambda>xi\<in>carrier (Ls ! (i-1)).
                 Pr\<^bsub>i - 1\<^esub> (Sp\<^bsub>j,aj\<^esub> f) (\<lambda>ja\<in>{1..length SpLs\<^bsub>j\<^esub> Ls}. if ja = i - 1 then xi else if (Sp\<^bsub>j\<^esub> B) ja \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) ja) else nested (SpLs\<^bsub>j\<^esub> Ls) ja ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) Sp\<^bsub>j,aj\<^esub> f))"
            using SpLs_nth_ge[of "j" "Ls" "i-1"] b51 b52 a_j 
            by (metis (no_types, lifting) diff_diff_left one_add_one)
          also have "... = LFP\<^bsub>(Ls ! (i-1))\<^esub>
              (\<lambda>xi\<in>carrier (Ls ! (i-1)).
                 Pr\<^bsub>i - 1\<^esub> (Sp\<^bsub>j,aj\<^esub> f) (\<lambda>ja\<in>{1..length Ls-1}. if ja = i - 1 then xi else if (Sp\<^bsub>j\<^esub> B) ja \<noteq> None then the ((Sp\<^bsub>j\<^esub> B) ja) else nested (SpLs\<^bsub>j\<^esub> Ls) ja ((Sp\<^bsub>j\<^esub> B)(i - 1 \<mapsto> xi)) Sp\<^bsub>j,aj\<^esub> f))"
            using length_minus_1' a_j by (metis (lifting))
          also have "... = nested Ls i (B(j \<mapsto> aj)) f"
            using l1 by auto
          finally show "nested Ls i (B(j \<mapsto> aj)) f = nested (SpLs\<^bsub>j\<^esub> Ls) (i - 1) (Sp\<^bsub>j\<^esub> B) (Sp\<^bsub>j,aj\<^esub> f)"
            by simp
        qed
        have claim_i_gt_j:"j < i \<longrightarrow> nested Ls i (B(j \<mapsto> aj)) f = nested SpLs\<^bsub>j\<^esub> Ls (i - 1) Sp\<^bsub>j\<^esub> B Sp\<^bsub>j,aj\<^esub> f"
        proof (cases "B i = None")
          case True
          then show ?thesis
            using claim'_i_gt_j by auto
        next
          case False
          then show ?thesis
            using nested_simps_defined[of "i" "B" "f"] specialize_env_simps(2)[of "i-1" "j" "B"]
            by (metis (lifting) a_j add_le_imp_le_diff bot_nat_0.extremum_strict le_add_diff_inverse2 le_geq_cases lem1 length_minus_1' less_iff_succ_less_eq less_one nat_less_le nested.simps)
        qed
        show ?thesis
          using claim_i_lt_j claim_i_gt_j by auto
      qed
    qed
  qed
qed

lemma (in cart_prod_lattice) nested_sp_compat:
  fixes i::"nat" and j::"nat" and f::"(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" and B::"nat \<Rightarrow> 'a option" and aj::"'a"
  assumes B_car:"\<And>i. i\<in>{1..length Ls} \<Longrightarrow> B i \<noteq> None \<Longrightarrow> the (B i) \<in> carrier (Ls ! (i-1))"
      and B_ext:"\<And>i. i\<notin>{1..length Ls} \<Longrightarrow> B i = None"
      and a_i:"i\<in>{1..length Ls}"
      and a_j:"j\<in>{1..length Ls}"
      and a_car:"f\<in>car_prod_carrier Ls \<rightarrow>\<^sub>E car_prod_carrier Ls" 
      and aj_car:"aj\<in>carrier (Ls!(j-1))"
    shows "(i<j \<Longrightarrow> nested Ls i (B(j\<mapsto>aj)) f = nested (SpLs\<^bsub>j\<^esub> Ls) i (Sp\<^bsub>j\<^esub> B) (Sp\<^bsub>j,aj\<^esub> f))"
          "(i>j \<Longrightarrow> nested Ls i (B(j\<mapsto>aj)) f = nested (SpLs\<^bsub>j\<^esub> Ls) (i-1) (Sp\<^bsub>j\<^esub> B) (Sp\<^bsub>j,aj\<^esub> f))"
  using nested_sp_compat' assms by auto

lemma (in complete_lattice) carrier_fpl_form: "carrier (fpl L f) = fps L f"
  by auto

lemma (in complete_lattice) fps_in_I:
  assumes "f v .= v"
  and "v\<in>carrier L"
  shows "v\<in>(fps L f)"
  unfolding fps_def using assms by auto

lemma (in complete_lattice) fpl_in_I:
  assumes "f v .= v"
  and "v\<in>carrier L"
  shows "v\<in>carrier (fpl L f)"
  apply (simp add:carrier_fpl_form)
  using fps_in_I assms by auto

lemma (in cart_prod_lattice) fps_in_coord_I:
  assumes a_cond:"\<And>i. i\<in>{1..length Ls} \<Longrightarrow> f v i = v i"
  and a_f:"f\<in>carrier (\<Otimes>Ls) \<rightarrow> carrier (\<Otimes>Ls)"
  and a_v:"v\<in>carrier (\<Otimes>Ls)"
shows "v\<in>(fps (\<Otimes>Ls) f)"
proof -
  have "f v = v"
  proof (rule vect_eqI)
    show "v\<in>carrier (\<Otimes>Ls)"
      using a_v by auto
  next
    show "f v \<in> carrier \<Otimes>Ls"
      using a_f a_v by auto
  next
    fix i assume \<open>i\<in>{1..length Ls}\<close>
    then show "f v i = v i"
      using a_cond by auto
  qed
  then show ?thesis
    using fps_in_I a_v by auto
qed

(* claim 6 of my arxiv article, used to prove one side of Bekic. *)
lemma general_Bekic_claim:
  fixes F::"(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)"
    and Ls:: "'a gorder list"
    and v::"nat \<Rightarrow> 'a"
    and i::"nat"
  assumes a_F:"F \<in> carrier (\<Otimes>Ls) \<rightarrow>\<^sub>E carrier (\<Otimes>Ls)"
      and cart_prod_lattice: "cart_prod_lattice Ls"
      and a_mono:"Mono\<^bsub>\<Otimes>Ls\<^esub> F"
      and v_fp: "v\<in>fps (\<Otimes>Ls) F"
      and a_i:"i \<in>{1..length Ls}"
    shows "(Pr\<^bsub>i\<^esub> F) (\<lambda>j\<in>{1..length Ls}. if j=i then (v i) else nested Ls j (Bot(i\<mapsto>v i)) F) \<sqsubseteq>\<^bsub>Ls!(i-1)\<^esub> v i"
  using assms
proof (induction "length Ls" arbitrary:Ls F i v rule:nat_induct_one)
  interpret base_locale: cart_prod_lattice "Ls"
    using cart_prod_lattice by auto
  case zero
  then show ?case using base_locale.Ls_len_pos by auto
next
  case one
  then show ?case
    (is "?l \<sqsubseteq>\<^bsub>Ls!(i-1)\<^esub> ?r")
  proof -
    interpret Ls: cart_prod_lattice "Ls"
      using \<open>cart_prod_lattice Ls\<close> by auto
    have "F v .=\<^bsub>\<Otimes>Ls\<^esub> v"
      using one.prems unfolding fps_def by auto
    then have b4:"F v = v"
      by (simp add: cart_prod_def)
    have "?l = F v 1"
      using one unfolding proj_def
      by (smt (verit, ccfv_SIG) PiE_restrict atLeastAtMost_iff car_prod_carrier_def car_prod_carrier_form diff_is_0_eq fps_def mem_Collect_eq nat_less_le restrict_ext zero_less_diff)
    then have "?l = ?r"
      using b4 one unfolding proj_def by auto
    then show ?thesis
      by (metis (no_types, lifting) Ls.cart_prod_lattice_axioms Ls.le_refl cart_prod_lattice.Ls_le_criterion fps_def mem_Collect_eq one.prems(4,5))
  qed
next
  case (suc n)
  then show ?case
  proof -
    have b_v:"v \<in> carrier (\<Otimes>Ls)"
      using suc.prems(4) unfolding fps_def by auto
    have b_v':"v i \<in> carrier (Ls!(i-1))"
      using b_v cart_carrier_iff[of "v"] suc.prems(5) by blast
    have b_v'': "\<And>j. j\<in>{1..length Ls} \<Longrightarrow> v j\<in>carrier (Ls!(j-1))"
      using b_v cart_carrier_iff[of "v" "Ls"] by auto
    have a_len:"length Ls > 1"
      using \<open>Suc n = length Ls\<close> \<open>1 \<le> n\<close> by auto
    interpret Ls: cart_prod_lattice "Ls"
      using \<open>cart_prod_lattice Ls\<close> by auto
    interpret hat_i_sub_locale: cart_prod_lattice "Sp_Ls i Ls"
      using hat_j_prod_locale_external[of "Ls" "i"] \<open>i \<in> {1..length Ls}\<close> \<open>cart_prod_lattice Ls\<close> suc.hyps(3) suc.hyps(1) by linarith

    have "fst (Ls.n_to_two i v) \<in> carrier (fpl (\<Otimes>(Sp_Ls i Ls)) (Ls.specialize_fn i (v i) F))"
    proof (rule hat_i_sub_locale.fpl_in_I)
      have "F \<in> carrier \<Otimes>Ls \<rightarrow> carrier \<Otimes>Ls"
        using suc.prems(1) by auto
      then have "F v .=\<^bsub>\<Otimes>Ls\<^esub> v"
        using suc.prems(4) unfolding fps_def by auto
      then have b4:"F v = v"
        by (simp add: Ls.eq_is_equal)
      then have b1:"fst (Ls.n_to_two i v) \<in> carrier_spl Ls i"
        using Ls.n_to_two_in_carrier[of "i"] b_v \<open>i\<in>{1..length Ls}\<close> by auto
      have "Ls.specialize_fn i (v i) F (fst (Ls.n_to_two i v)) 
        = fst (Ls.n_to_two i (F (Ls.two_to_n i (fst (Ls.n_to_two i v), v i))))"
        using Ls.specialize_fn_n_two[of "i" "fst (Ls.n_to_two i v)" "v i" "F"] \<open>i \<in> {1..length Ls}\<close> a_len b1 b_v'
              \<open>F \<in> carrier \<Otimes>Ls \<rightarrow>\<^sub>E carrier \<Otimes>Ls\<close>
        by auto
      also have "... = fst (Ls.n_to_two i (F v))"
        using Ls.two_n__n_two_id[of "v" "i"] Ls.n_to_two_simps_snd[of "i" "v"] b_v suc.prems(5) by auto
      also have "... = fst (Ls.n_to_two i v)"
        using b4 by auto
      finally show "Ls.specialize_fn i (v i) F (fst (Ls.n_to_two i v)) .=\<^bsub>\<Otimes>SpLs\<^bsub>i\<^esub> Ls\<^esub> fst (Ls.n_to_two i v)"
        by (simp add: hat_i_sub_locale.eq_is_equal)
    next
      show "fst (Ls.n_to_two i v) \<in> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
        using carrier_spl_simp Ls.n_two__carrier(1)[of "v" "i"] a_i b_v suc.prems(5) by auto
    qed
    have r0:"\<And>j. j\<in>{1..length Ls} \<Longrightarrow>
      ((j<i \<longrightarrow> ((Pr\<^bsub>j\<^esub> (Ls.specialize_fn i (v i) F)) (\<lambda>k\<in>{1..length Ls-1}. if k=j then v j else nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j\<mapsto>(v j))) (Ls.specialize_fn i (v i) F)) \<sqsubseteq>\<^bsub>Ls!(j-1)\<^esub> v j))
        \<and> (j>i \<longrightarrow> ((Pr\<^bsub>j-1\<^esub> (Ls.specialize_fn i (v i) F)) (\<lambda>k\<in>{1..length Ls-1}. if k=j-1 then v j else nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j-1\<mapsto>(v j))) (Ls.specialize_fn i (v i) F))) \<sqsubseteq>\<^bsub>Ls!(j-1)\<^esub> (v j)))"
    proof
      have r1:"\<And>j. j\<in>{1..length Ls} \<Longrightarrow> j<i \<Longrightarrow> ((Pr\<^bsub>j\<^esub> (Ls.specialize_fn i (v i) F)) (\<lambda>k\<in>{1..length Ls-1}. if k=j then v j else nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j\<mapsto>(v j))) (Ls.specialize_fn i (v i) F)) \<sqsubseteq>\<^bsub>Ls!(j-1)\<^esub> v j)"
      proof -
        fix j assume a_j':"j \<in> {1..length Ls}" and \<open>j<i\<close>
        have a_j:"j \<in> {1..length Ls-1}"
          using \<open>j<i\<close> suc.prems(5) a_j' by auto
        have c1:"n=length (SpLs\<^bsub>i\<^esub> Ls)"
          using \<open>Suc n =length Ls\<close> length_minus_1' a_i by (metis One_nat_def diff_Suc_1' suc.prems(5))
        have c2:"Ls.specialize_fn i (v i) F \<in> carrier (\<Otimes>SpLs\<^bsub>i\<^esub> Ls) \<rightarrow>\<^sub>E carrier (\<Otimes>SpLs\<^bsub>i\<^esub> Ls)"
          using Ls.specialize_fn_PiE[of "i" "v i" "F"] suc.prems(5) a_len b_v' suc.prems(1) by auto
        have c3:"cart_prod_lattice (SpLs\<^bsub>i\<^esub> Ls)"
          using hat_i_sub_locale.cart_prod_lattice_axioms by auto
        have c4:"Mono\<^bsub>\<Otimes>SpLs\<^bsub>i\<^esub> Ls\<^esub> (Ls.specialize_fn i (v i) F)"
          using Ls.mono_specialize_mono[of "F" "i" "v i"] suc.prems b_v' a_len by blast
        have c5:"j\<in>{1..length (SpLs\<^bsub>i\<^esub> Ls)}"
          using length_minus_1' suc.prems(5) a_j by auto
        have c6:"fst (Ls.n_to_two i v) \<in> fps (\<Otimes>(SpLs\<^bsub>i\<^esub> Ls)) (Ls.specialize_fn i (v i) F)"
          using suc.prems(4) \<open>fst (Ls.n_to_two i v) \<in> carrier (fpl \<Otimes>SpLs\<^bsub>i\<^esub> Ls (Ls.specialize_fn i (v i) F))\<close> by auto
        have c7:"fst (Ls.n_to_two i v) j = v j"
          using Ls.n_to_two_simps_lt[of "j" "i" "v"] \<open>j<i\<close> a_j by auto
        have conc:"(Pr\<^bsub>j\<^esub> (Ls.specialize_fn i (v i) F)) (\<lambda>ja\<in>{1..length SpLs\<^bsub>i\<^esub> Ls}. if ja = j then fst (Ls.n_to_two i v) j else nested (SpLs\<^bsub>i\<^esub> Ls) ja (Bot(j \<mapsto> fst (Ls.n_to_two i v) j)) (Ls.specialize_fn i (v i) F)) \<sqsubseteq>\<^bsub>(SpLs\<^bsub>i\<^esub> Ls) ! (j-1)\<^esub>
              fst (Ls.n_to_two i v) j"
          using suc.hyps(2)[of "SpLs\<^bsub>i\<^esub> Ls" "Ls.specialize_fn i (v i) F" "fst (Ls.n_to_two i v)" "j" ] c1 c2 c3 c4 c5 c6 by auto
        have c8:"(Pr\<^bsub>j\<^esub> (Ls.specialize_fn i (v i) F)) (\<lambda>ja\<in>{1..length SpLs\<^bsub>i\<^esub> Ls}. if ja = j then fst (Ls.n_to_two i v) j else nested (SpLs\<^bsub>i\<^esub> Ls) ja (Bot(j \<mapsto> fst (Ls.n_to_two i v) j)) (Ls.specialize_fn i (v i) F))
            = (Pr\<^bsub>j\<^esub> (Ls.specialize_fn i (v i) F)) (\<lambda>k\<in>{1..length SpLs\<^bsub>i\<^esub> Ls}. if k=j then v j else nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j\<mapsto>(v j))) (Ls.specialize_fn i (v i) F))"
          using c7 by presburger
        also have "... = (Pr\<^bsub>j\<^esub> (Ls.specialize_fn i (v i) F)) (\<lambda>k\<in>{1..length Ls-1}. if k=j then v j else nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j\<mapsto>(v j))) (Ls.specialize_fn i (v i) F))"
          using length_minus_1'[of "i" "Ls"] suc.prems(5) by presburger
        finally have "(Pr\<^bsub>j\<^esub> (Ls.specialize_fn i (v i) F)) (\<lambda>k\<in>{1..length Ls-1}. if k=j then v j else nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j\<mapsto>(v j))) (Ls.specialize_fn i (v i) F)) \<sqsubseteq>\<^bsub>SpLs\<^bsub>i\<^esub> Ls ! (j-1)\<^esub> v j"
          using conc c7 by auto
        then show "(Pr\<^bsub>j\<^esub> (Ls.specialize_fn i (v i) F)) (\<lambda>k\<in>{1..length Ls-1}. if k=j then v j else nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j\<mapsto>(v j))) (Ls.specialize_fn i (v i) F)) \<sqsubseteq>\<^bsub>Ls ! (j-1)\<^esub> v j"
          using SpLs_nth_lt[of "i" "Ls" "j"] suc.prems(5) a_j \<open>j<i\<close> by auto
      qed
      then show "\<And>j. j \<in> {1..length Ls} \<Longrightarrow> j < i \<longrightarrow> Pr\<^bsub>j\<^esub> Ls.specialize_fn i (v i) F (\<lambda>k\<in>{1..length Ls - 1}. if k = j then v j else nested SpLs\<^bsub>i\<^esub> Ls k (Bot(j \<mapsto> v j)) (Ls.specialize_fn i (v i) F)) \<sqsubseteq>\<^bsub>Ls ! (j-1)\<^esub> v j"
        by auto
    next
      have r2:"\<And>j. j\<in>{1..length Ls} \<Longrightarrow> i<j \<Longrightarrow> ((Pr\<^bsub>j-1\<^esub> (Ls.specialize_fn i (v i) F)) (\<lambda>k\<in>{1..length Ls-1}. if k=j-1 then v j else nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j-1\<mapsto>(v j))) (Ls.specialize_fn i (v i) F)) \<sqsubseteq>\<^bsub>Ls ! (j-1)\<^esub> v j)"
      proof -
        fix j assume a_j:"j \<in> {1..length Ls}" and \<open>i<j\<close>
        have a_j':"j-1\<in>{1..length Ls-1}"
          using \<open>i<j\<close> a_j suc.prems(5) by auto
        then have a_j'':"j-1\<in>{1..length SpLs\<^bsub>i\<^esub> Ls}"
          using length_minus_1' suc.prems(5) by auto
        have c1:"n=length (SpLs\<^bsub>i\<^esub> Ls)"
          using \<open>Suc n =length Ls\<close> length_minus_1' a_i by (metis One_nat_def diff_Suc_1' suc.prems(5))
        have c2:"Ls.specialize_fn i (v i) F \<in> carrier (\<Otimes>SpLs\<^bsub>i\<^esub> Ls) \<rightarrow>\<^sub>E carrier (\<Otimes>SpLs\<^bsub>i\<^esub> Ls)"
          using Ls.specialize_fn_PiE[of "i" "v i" "F"] suc.prems(5) a_len b_v' suc.prems(1) by auto
        have c3:"cart_prod_lattice (SpLs\<^bsub>i\<^esub> Ls)"
          using hat_i_sub_locale.cart_prod_lattice_axioms by auto
        have c4:"Mono\<^bsub>\<Otimes>SpLs\<^bsub>i\<^esub> Ls\<^esub> (Ls.specialize_fn i (v i) F)"
          using Ls.mono_specialize_mono[of "F" "i" "v i"] suc.prems b_v' a_len by blast
        have c6:"fst (Ls.n_to_two i v) \<in> fps (\<Otimes>(SpLs\<^bsub>i\<^esub> Ls)) (Ls.specialize_fn i (v i) F)"
          using suc.prems(4) \<open>fst (Ls.n_to_two i v) \<in> carrier (fpl \<Otimes>SpLs\<^bsub>i\<^esub> Ls (Ls.specialize_fn i (v i) F))\<close> by auto
        have c7:"fst (Ls.n_to_two i v) (j-1) = v j"
          using Ls.n_to_two_simps_geq[of "j-1" "i" "v"] \<open>i<j\<close> a_j' by auto
        have conc:"(Pr\<^bsub>j-1\<^esub> (Ls.specialize_fn i (v i) F)) (\<lambda>ja\<in>{1..length SpLs\<^bsub>i\<^esub> Ls}. if ja = j-1 then fst (Ls.n_to_two i v) (j-1) else nested (SpLs\<^bsub>i\<^esub> Ls) ja (Bot(j-1\<mapsto> fst (Ls.n_to_two i v) (j-1))) (Ls.specialize_fn i (v i) F)) \<sqsubseteq>\<^bsub>(SpLs\<^bsub>i\<^esub> Ls) ! (j-2)\<^esub>
              fst (Ls.n_to_two i v) (j-1)"
          using suc.hyps(2)[of "SpLs\<^bsub>i\<^esub> Ls" "Ls.specialize_fn i (v i) F" "fst (Ls.n_to_two i v)" "j-1" ] c1 c2 c3 c4 a_j'' c6 
          by (metis Suc_1 diff_diff_left plus_1_eq_Suc)
        have c8:"(Pr\<^bsub>j-1\<^esub> (Ls.specialize_fn i (v i) F)) (\<lambda>ja\<in>{1..length SpLs\<^bsub>i\<^esub> Ls}. if ja = j-1 then fst (Ls.n_to_two i v) (j-1) else nested (SpLs\<^bsub>i\<^esub> Ls) ja (Bot(j-1 \<mapsto> fst (Ls.n_to_two i v) (j-1))) (Ls.specialize_fn i (v i) F))
            = (Pr\<^bsub>j-1\<^esub> (Ls.specialize_fn i (v i) F)) (\<lambda>k\<in>{1..length SpLs\<^bsub>i\<^esub> Ls}. if k=j-1 then v j else nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j-1\<mapsto>(v j))) (Ls.specialize_fn i (v i) F))"
          using c7 by presburger
        also have "... = (Pr\<^bsub>j-1\<^esub> (Ls.specialize_fn i (v i) F)) (\<lambda>k\<in>{1..length Ls-1}. if k=j-1 then v j else nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j-1\<mapsto>(v j))) (Ls.specialize_fn i (v i) F))"
          using length_minus_1'[of "i" "Ls"] suc.prems(5) by presburger
        finally have "(Pr\<^bsub>j-1\<^esub> (Ls.specialize_fn i (v i) F)) (\<lambda>k\<in>{1..length Ls-1}. if k=j-1 then v j else nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j-1\<mapsto>(v j))) (Ls.specialize_fn i (v i) F)) \<sqsubseteq>\<^bsub>SpLs\<^bsub>i\<^esub> Ls ! (j-2)\<^esub> v j"
          using conc c7 by auto
        then show "(Pr\<^bsub>j-1\<^esub> (Ls.specialize_fn i (v i) F)) (\<lambda>k\<in>{1..length Ls-1}. if k=j-1 then v j else nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j-1\<mapsto>(v j))) (Ls.specialize_fn i (v i) F)) \<sqsubseteq>\<^bsub>Ls!(j-1)\<^esub> v j"
          using SpLs_nth_ge[of "i" "Ls" "j-1"] suc.prems(5) a_j \<open>i<j\<close>
          by (metis (no_types, lifting) Nat.diff_cancel Sp_Ls_def Suc_1 a_j' diff_Suc_eq_diff_pred diff_le_mono less_eq_Suc_le minus_nat.diff_0 plus_1_eq_Suc
            remove_at_nth_ge2)
      qed
      then show "\<And>j. j \<in> {1..length Ls} \<Longrightarrow> i < j \<longrightarrow> Pr\<^bsub>j - 1\<^esub> Ls.specialize_fn i (v i) F (\<lambda>k\<in>{1..length Ls - 1}. if k = j - 1 then v j else nested SpLs\<^bsub>i\<^esub> Ls k (Bot(j - 1\<mapsto>v j)) (Ls.specialize_fn i (v i) F)) \<sqsubseteq>\<^bsub>Ls ! (j-1)\<^esub> v j"
        by auto
    qed
    have ji__ki:"\<And>j k. j\<in>{1..length Ls} \<Longrightarrow> k\<in>{1..length Ls-1} \<Longrightarrow> j<i \<Longrightarrow>
            k<i \<Longrightarrow> nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j\<mapsto>v j)) (Ls.specialize_fn i (v i) F) = nested Ls k (Bot(j\<mapsto>v j,i\<mapsto>v i)) F"
    proof -
      fix j k assume a_j:"j\<in>{1..length Ls}" and a_k:"k\<in>{1..length Ls-1}" and \<open>k<i\<close> and \<open>j<i\<close>
      show "nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j\<mapsto>v j)) (Ls.specialize_fn i (v i) F) = nested Ls k (Bot(j\<mapsto>v j,i\<mapsto>v i)) F"
      proof -
        have a_k':"k\<in>{1..length Ls}"
          using a_k by auto
        have c1:"(\<And>i. i \<in> {1..length Ls} \<Longrightarrow> (Bot(j\<mapsto> v j)) i \<noteq> None \<Longrightarrow> the ((Bot(j \<mapsto> v j)) i) \<in> carrier (Ls ! (i-1)))"
          using b_v''[of "j"] a_j 
          by (metis Bot_defined fun_upd_same option.sel)
        have c2:"\<And>i. i\<notin>{1..length Ls} \<Longrightarrow> (Bot(j\<mapsto> v j)) i = None"
          by (metis Bot_ext' Suc_diff_le a_j atLeastAtMost_iff diff_Suc_1 diff_is_0_eq nat.distinct(1) nat_le_linear)
        have c4:"Ls.specialize_env i (Bot(j \<mapsto> v j)) = (Bot(j\<mapsto>v j))"
          using Ls.Bot_specialize(1)[of "j" "i" "v j"] \<open>j<i\<close> a_j suc.prems by auto
        have "nested Ls k (Bot(j \<mapsto> v j, i \<mapsto> v i)) F = nested SpLs\<^bsub>i\<^esub> Ls k (Ls.specialize_env i (Bot(j \<mapsto> v j))) (Ls.specialize_fn i (v i) F)"
          using Ls.nested_sp_compat(1)[of "Bot(j\<mapsto>v j)" "k" "i" "F" "v i"] c1 c2 a_k' suc.prems \<open>k<i\<close> b_v'
          by (metis car_prod_carrier_form)
        then show ?thesis
          using c4 by auto
      qed
    qed
    have ji__ik:"\<And>j k. j\<in>{1..length Ls} \<Longrightarrow> k\<in>{1..length Ls-1} \<Longrightarrow> j<i \<Longrightarrow>
            k\<ge>i \<Longrightarrow> nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j\<mapsto>v j)) (Ls.specialize_fn i (v i) F) = nested Ls (k+1) (Bot(j\<mapsto>v j,i\<mapsto>v i)) F"
    proof -
      fix j k assume a_j:"j\<in>{1..length Ls}" and a_k:"k\<in>{1..length Ls-1}" and \<open>k\<ge>i\<close> and \<open>j<i\<close>
      show "nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j\<mapsto>v j)) (Ls.specialize_fn i (v i) F) = nested Ls (k+1) (Bot(j\<mapsto>v j,i\<mapsto>v i)) F"
      proof -
        have a_k':"k+1\<in>{1..length Ls}"
          using a_k by auto
        have \<open>k+1>i\<close>
          using \<open>k\<ge>i\<close> by auto
        have c1:"(\<And>i. i \<in> {1..length Ls} \<Longrightarrow> (Bot(j \<mapsto> v j)) i \<noteq> None \<Longrightarrow> the ((Bot(j \<mapsto> v j)) i) \<in> carrier (Ls ! (i-1)))"
          using b_v''[of "j"] a_j 
          by (metis Bot_defined fun_upd_same option.sel)
        have c2:"\<And>i. i\<notin> {1..length Ls} \<Longrightarrow> (Bot(j \<mapsto> v j)) i = None"
          by (metis Bot_ext' Suc_diff_le a_j atLeastAtMost_iff diff_Suc_1 diff_is_0_eq nat.distinct(1) nat_le_linear)
        have c4:"Ls.specialize_env i (Bot(j \<mapsto> v j)) = (Bot(j\<mapsto>v j))"
          using Ls.Bot_specialize(1)[of "j" "i" "v j"] \<open>j<i\<close> a_j suc.prems by auto
        have "nested Ls (k+1) (Bot(j \<mapsto> v j, i \<mapsto> v i)) F = nested SpLs\<^bsub>i\<^esub> Ls k (Ls.specialize_env i (Bot(j \<mapsto> v j))) (Ls.specialize_fn i (v i) F)"
          using Ls.nested_sp_compat(2)[of "Bot(j\<mapsto>v j)" "k+1" "i" "F""v i"] c1 c2 a_k' suc.prems \<open>k+1>i\<close> b_v' car_prod_carrier_form
          by (metis Suc_eq_plus1 diff_Suc_1)
        then show ?thesis
          using c4 by auto
      qed
    qed
    have ij__ki:"\<And>j k. j\<in>{1..length Ls} \<Longrightarrow> k\<in>{1..length Ls-1} \<Longrightarrow> j>i \<Longrightarrow>
            k<i \<Longrightarrow> nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j-1\<mapsto>v j)) (Ls.specialize_fn i (v i) F) = nested Ls k (Bot(j\<mapsto>v j,i\<mapsto>v i)) F"
    proof -
      fix j k assume a_j:"j\<in>{1..length Ls}" and a_k:"k\<in>{1..length Ls-1}" and \<open>k<i\<close> and \<open>j>i\<close>
      show "nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j-1\<mapsto>v j)) (Ls.specialize_fn i (v i) F) = nested Ls k (Bot(j\<mapsto>v j,i\<mapsto>v i)) F"
      proof -
        have a_k':"k\<in>{1..length Ls}"
          using a_k by auto
        have c1:"(\<And>i. i \<in> {1..length Ls} \<Longrightarrow> (Bot(j \<mapsto> v j)) i \<noteq> None \<Longrightarrow> the ((Bot(j \<mapsto> v j)) i) \<in> carrier (Ls ! (i-1)))"
          using b_v''[of "j"] a_j
          by (metis Bot_defined fun_upd_same option.sel)
        have c2:"\<And>i. i\<notin> {1..length Ls} \<Longrightarrow> (Bot(j \<mapsto> v j)) i = None"
          by (metis Bot_ext' Suc_diff_le a_j atLeastAtMost_iff diff_Suc_1 diff_is_0_eq nat.distinct(1) nat_le_linear)
        have c4:"Ls.specialize_env i (Bot(j \<mapsto> v j)) = (Bot(j-1\<mapsto>v j))"
          using Ls.Bot_specialize(2)[of "j" "i" "v j"] \<open>j>i\<close> a_j suc.prems by auto
        have "nested Ls k (Bot(j \<mapsto> v j, i \<mapsto> v i)) F = nested SpLs\<^bsub>i\<^esub> Ls k (Ls.specialize_env i (Bot(j \<mapsto> v j))) (Ls.specialize_fn i (v i) F)"
          using Ls.nested_sp_compat(1)[of "Bot(j\<mapsto>v j)" "k" "i"  "F""v i"] c1 c2 a_k' suc.prems \<open>k<i\<close> b_v' car_prod_carrier_form
          by (metis Suc_eq_plus1 diff_Suc_1)
        then show ?thesis
          using c4 by auto
      qed
    qed
    have ij__ik:"\<And>j k. j\<in>{1..length Ls} \<Longrightarrow> k\<in>{1..length Ls-1} \<Longrightarrow> j>i \<Longrightarrow>
            k\<ge>i \<Longrightarrow> nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j-1\<mapsto>v j)) (Ls.specialize_fn i (v i) F) = nested Ls (k+1) (Bot(j\<mapsto>v j,i\<mapsto>v i)) F"
    proof -
      fix j k assume a_j:"j\<in>{1..length Ls}" and a_k:"k\<in>{1..length Ls-1}" and \<open>k\<ge>i\<close> and \<open>j>i\<close>
      show "nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j-1\<mapsto>v j)) (Ls.specialize_fn i (v i) F) = nested Ls (k+1) (Bot(j\<mapsto>v j,i\<mapsto>v i)) F"
      proof -
        have a_k':"k+1\<in>{1..length Ls}"
          using a_k by auto
        have \<open>k+1>i\<close>
          using \<open>k\<ge>i\<close> by auto
        have c1:"(\<And>i. i \<in> {1..length Ls} \<Longrightarrow> (Bot(j \<mapsto> v j)) i \<noteq> None \<Longrightarrow> the ((Bot(j \<mapsto> v j)) i) \<in> carrier (Ls ! (i-1)))"
          using b_v''[of "j"] a_j 
          by (metis Bot_defined fun_upd_same option.sel)
        have c2:"\<And>i. i\<notin> {1..length Ls} \<Longrightarrow> (Bot(j \<mapsto> v j)) i = None"
          by (metis Bot_ext' Suc_diff_le a_j atLeastAtMost_iff diff_Suc_1 diff_is_0_eq nat.distinct(1) nat_le_linear)
        have c4:"Ls.specialize_env i (Bot(j \<mapsto> v j)) = (Bot(j-1\<mapsto>v j))"
          using Ls.Bot_specialize(2)[of "j" "i" "v j"] \<open>j>i\<close> a_j suc.prems by auto
        have "nested Ls (k+1) (Bot(j \<mapsto> v j, i \<mapsto> v i)) F = nested SpLs\<^bsub>i\<^esub> Ls k (Ls.specialize_env i (Bot(j \<mapsto> v j))) (Ls.specialize_fn i (v i) F)"
          using Ls.nested_sp_compat(2)[of "Bot(j\<mapsto>v j)" "k+1" "i"  "F""v i"] c1 c2  a_k' suc.prems \<open>k+1>i\<close> b_v' car_prod_carrier_form
          by (metis Suc_eq_plus1 diff_Suc_1)
        then show ?thesis
          using c4 by auto
      qed
    qed

    have ij__lem:"\<And>j. j\<in>{1..length Ls} \<Longrightarrow> j>i \<Longrightarrow> ((Pr\<^bsub>j\<^esub> F) (\<lambda>h\<in>{1..length Ls}. if h=i then v i else if h=j then v j else nested Ls h (Bot(j\<mapsto>v j, i\<mapsto>v i)) F)
       \<sqsubseteq>\<^bsub>Ls!(j-1)\<^esub> v j)"
    proof -
      fix j assume a_j:"j\<in>{1..length Ls}" and \<open>j>i\<close>
      let ?w = "\<lambda>k\<in>{1..length Ls-1}. if k=j-1 then v j else nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j-1\<mapsto>(v j))) (Ls.specialize_fn i (v i) F)"
      have b1:"?w \<in> carrier_spl Ls i"
      proof (rule Ls.in_carrier_spl_I)
        show "i \<in> {1..length Ls}"
          using suc.prems by auto
      next
        show "\<And>y. y \<notin> {1..length Ls - 1} \<Longrightarrow>
          ?w y = undefined"
          by auto
      next
        fix h assume \<open>h\<in>{1..length Ls-1}\<close>
        have r1:"h < i \<Longrightarrow> 
            ?w h \<in> carrier (Ls ! (h-1))"
        proof - assume \<open>h<i\<close>
          have b1:"(\<lambda>k\<in>{1..length Ls - 1}. if k = j - 1 then v j else nested SpLs\<^bsub>i\<^esub> Ls k (Bot(j - 1\<mapsto> v j)) (Ls.specialize_fn i (v i) F)) h = 
            (if h = j - 1 then v j else nested SpLs\<^bsub>i\<^esub> Ls h (Bot(j - 1 \<mapsto> v j)) (Ls.specialize_fn i (v i) F))"
            using \<open>h\<in>{1..length Ls-1}\<close> by auto
          have \<open>h\<noteq>j-1\<close>
            using \<open>h<i\<close> \<open>i<j\<close> by auto
          have "nested (SpLs\<^bsub>i\<^esub> Ls) h (Bot(j - 1 \<mapsto> v j)) (Ls.specialize_fn i (v i) F) \<in> carrier (Ls!(h-1))"
          proof -
            have c1:"h \<in> {1..length SpLs\<^bsub>i\<^esub> Ls}"
              using \<open>h\<in>{1..length Ls-1}\<close> length_minus_1' suc.prems by auto
            have c2:"(Bot(j - 1\<mapsto> v j)) h = None"
              using \<open>h\<noteq>j-1\<close> unfolding Bot_def by auto
            show ?thesis
              using hat_i_sub_locale.nested_closed[of "h" "Bot(j - 1 \<mapsto> v j)"] c1 c2 SpLs_nth_lt \<open>h<i\<close> suc.prems \<open>h\<in>{1..length Ls-1}\<close>
              by (metis (no_types, lifting) atLeastAtMost_iff le_trans less_or_eq_imp_le)
          qed
          then show ?thesis
            using \<open>h\<noteq>j-1\<close> b1 by auto
        qed
        have r2:"i \<le> h \<Longrightarrow>
          ?w h \<in> carrier (Ls ! h)"
        proof - assume \<open>i\<le>h\<close>
          have b1:"h=j-1 \<Longrightarrow> v j \<in> carrier (Ls!h)"
            using b_v'' a_j by auto
          have "h\<noteq>j-1 \<Longrightarrow> nested (SpLs\<^bsub>i\<^esub> Ls) h (Bot(j - 1 \<mapsto> v j)) (Ls.specialize_fn i (v i) F) \<in> carrier (Ls ! h)"
          proof - assume \<open>h\<noteq>j-1\<close>
            have c3:"((SpLs\<^bsub>i\<^esub> Ls) ! (h-1)) = (Ls ! (h))"
              using SpLs_nth_ge[of "i" "Ls" "h"] suc.prems(5) \<open>h\<in>{1..length Ls-1}\<close> \<open>i\<le>h\<close> by auto
            have c2:"(Bot(j - 1 \<mapsto> v j)) h = None"
              using \<open>h\<noteq>j-1\<close> unfolding Bot_def by auto
            have c1:"h \<in> {1..length SpLs\<^bsub>i\<^esub> Ls}"
              using \<open>h\<in>{1..length Ls-1}\<close> length_minus_1' suc.prems by auto
            show ?thesis
              using hat_i_sub_locale.nested_closed[of "h" "Bot(j - 1 \<mapsto> v j)"] c1 c2 c3 by auto
          qed
          then show ?thesis
            using b1 \<open>h\<in>{1..length Ls-1}\<close> by auto
        qed
        show "(h < i \<longrightarrow> ?w h \<in> carrier (Ls ! (h-1))) \<and> (i \<le> h \<longrightarrow> ?w h \<in> carrier (Ls ! h))"
          using r1 r2 by auto
      qed
      then have b3:"?w = fst (Ls.n_to_two i (Ls.two_to_n i (?w, v i)))"
        using Ls.n_two__two_n_id[of "?w" "i" "v i"] b_v' suc.prems(5) by auto
      have b2:"Ls.two_to_n i (?w, v i) \<in> carrier \<Otimes>Ls"
        using b1 b_v' Ls.two_n__carrier[of "i" "?w" "v i"] suc.prems(5) by auto
      then have b5:"
        Pr\<^bsub>j - 1\<^esub> (Ls.specialize_fn i (v i) F) ?w 
      = (Pr\<^bsub>j\<^esub> F) (Ls.two_to_n i (?w, v i))"
        using Ls.specialize_proj_eq(2)[of "i" "j" "Ls.two_to_n i (?w, v i)" "v i" "F"] Ls.two_to_n_simps(1)
              suc.prems(5) \<open>i<j\<close> a_j b1 b3 
        by (metis (lifting) b_v')
      have b4:"Ls.two_to_n i (?w, v i) = (\<lambda>h\<in>{1..length Ls}. if h=i then v i else if h=j then v j
               else if h<i then nested Ls h (Bot(j\<mapsto>v j, i\<mapsto>v i)) F else nested Ls h (Bot(j\<mapsto>v j, i\<mapsto>v i)) F)"
        (is "?l=?r")
      proof (rule Ls.vect_eqI)
        show "Ls.two_to_n i (?w, v i) \<in> carrier (\<Otimes>Ls)"
          using b2 by auto
        show "?r\<in> carrier (\<Otimes>Ls)"
        proof (rule cart_carrier_criterion)
          show "\<And>i. i\<notin>{1..length Ls} \<Longrightarrow> ?r i = undefined"
            by auto
        next
          fix h assume \<open>h\<in>{1..length Ls}\<close>
          have "h\<noteq>i \<Longrightarrow> h\<noteq>j \<Longrightarrow> nested Ls h (Bot(j \<mapsto>v j, i \<mapsto> v i)) F \<in> carrier (Ls !(h-1))"
            using Ls.nested_closed[of "h" "Bot(j \<mapsto> v j, i \<mapsto> v i)" "F"] \<open>h \<in> {1..length Ls}\<close> suc.prems(5) unfolding Bot_def 
            by (metis  fun_upd_apply)
          then show "?r h \<in>carrier (Ls ! (h-1))"
            using b_v'' a_j suc.prems(5) \<open>h\<in>{1..length Ls}\<close> 
            by auto
        qed
      next
        fix h assume \<open>h\<in>{1..length Ls}\<close>
        show "?l h = ?r h"
        proof -
          have c1:"h<i \<Longrightarrow> ?l h = ?r h"
          proof - 
            assume \<open>h<i\<close>
            then have \<open>h\<noteq>j-1\<close>
              using \<open>i<j\<close> by auto
            have \<open>h\<in>{1..length Ls-1}\<close>
              using \<open>h\<in>{1..length Ls}\<close> \<open>h<i\<close> suc.prems(5) by auto
            have \<open>h<j\<close>
              using \<open>h<i\<close> \<open>i<j\<close> by auto
            from Ls.two_to_n_simps(2)[of "?w" "i" "v i" "h"] have "?l h = ?w h"
              using \<open>h<i\<close> \<open>h\<in>{1..length Ls}\<close> b_v' b1 suc.prems(5) by auto
            also have "... = nested (SpLs\<^bsub>i\<^esub> Ls) h (Bot(j - 1 \<mapsto> v j)) (Ls.specialize_fn i (v i) F)"
              using \<open>h\<noteq>j-1\<close> \<open>h\<in>{1..length Ls-1}\<close> by auto
            finally show "?l h = ?r h"
              using \<open>h<j\<close> \<open>h<i\<close> \<open>h\<in>{1..length Ls}\<close> ij__ki[of "j" "h"] \<open>h\<in>{1..length Ls-1}\<close> a_j \<open>i<j\<close> by auto
          qed
          have c2:"h=i \<Longrightarrow> ?l h = ?r h"
          proof - assume \<open>h=i\<close>
            from Ls.two_to_n_simps(1)[of "?w" "i" "v i"] 
            have b1:"?l h = v i"
              using \<open>h=i\<close> \<open>h\<in>{1..length Ls}\<close> b1 b_v' suc.prems(5) by auto
            have b2:"?r h = v i"
              using \<open>h\<in>{1..length Ls}\<close> \<open>h=i\<close> by auto
            then show ?thesis 
              using b1 b2 by auto
          qed
          have c3:"h=j \<Longrightarrow> ?l h = ?r h"
          proof - assume \<open>h=j\<close>
            have \<open>h-1\<in>{1..length Ls-1}\<close>
              using \<open>h=j\<close> \<open>i<j\<close> suc.prems(5) \<open>h\<in>{1..length Ls}\<close> by auto
            have b2:"?r h = v j"
              using \<open>h-1\<in>{1..length Ls-1}\<close> \<open>h=j\<close> by auto
            from Ls.two_to_n_simps(3)[of "?w" "i" "v i" "h"] 
            have b1:"?l h = ?w (h-1)"
              using \<open>h=j\<close> \<open>h\<in>{1..length Ls}\<close> b1 b_v' \<open>i<j\<close> suc.prems(5) by auto
            also have b3:"... = v j"
              using \<open>h-1\<in>{1..length Ls-1}\<close> \<open>h=j\<close> by auto
            finally show ?thesis 
              using b1 b2 by auto
          qed
          have c4:"h>i \<Longrightarrow> h\<noteq>j \<Longrightarrow> ?l h = ?r h"
          proof - assume \<open>h>i\<close> and \<open>h\<noteq>j\<close>
            have \<open>h-1\<in>{1..length Ls-1}\<close>
              using \<open>h>i\<close> \<open>i<j\<close> suc.prems(5) \<open>h\<in>{1..length Ls}\<close> by auto
            have b2:"?r h = nested Ls h (Bot(j \<mapsto> v j, i \<mapsto> v i)) F"
              using \<open>h-1\<in>{1..length Ls-1}\<close> \<open>h\<noteq>j\<close> \<open>h>i\<close> by auto
            from Ls.two_to_n_simps(3)[of "?w" "i" "v i" "h"] 
            have b1:"?l h = ?w (h-1)"
              using \<open>h\<noteq>j\<close> \<open>h>i\<close> \<open>h\<in>{1..length Ls}\<close> b1 b_v' \<open>i<j\<close> suc.prems(5) by auto
            also have b3:"... = nested SpLs\<^bsub>i\<^esub> Ls (h-1) (Bot(j - 1 \<mapsto> v j)) (Ls.specialize_fn i (v i) F)"
              using \<open>h-1\<in>{1..length Ls-1}\<close> \<open>h\<noteq>j\<close> by auto
            finally show ?thesis
              using b1 b2 ij__ik[of "j" "h-1"] a_j \<open>h-1\<in>{1..length Ls-1}\<close> \<open>h>i\<close> \<open>i<j\<close> by auto
          qed
          show ?thesis
            using c1 c2 c3 c4 \<open>h\<in>{1..length Ls}\<close> \<open>i<j\<close> by linarith
        qed
      qed
      then have "Ls.two_to_n i (?w, v i) = (\<lambda>h\<in>{1..length Ls}. if h=i then v i else if h=j then v j
                                           else nested Ls h (Bot(j\<mapsto>v j, i\<mapsto>v i)) F)"
        by auto
      then have "Pr\<^bsub>j - 1\<^esub> (Ls.specialize_fn i (v i) F) ?w 
      = (Pr\<^bsub>j\<^esub> F) (\<lambda>h\<in>{1..length Ls}. if h=i then v i else if h=j then v j else nested Ls h (Bot(j\<mapsto>v j, i\<mapsto>v i)) F)"
        using b5 by auto
      then show "Pr\<^bsub>j\<^esub> F (\<lambda>h\<in>{1..length Ls}. if h = i then v i else if h = j then v j else nested Ls h (Bot(j\<mapsto> v j, i\<mapsto>v i)) F) \<sqsubseteq>\<^bsub>Ls ! (j-1)\<^esub> v j"
        using r0[of "j"] a_j \<open>i<j\<close> by auto
    qed
    then have ij_aj_geq:"\<And>j. j\<in>{1..length Ls} \<Longrightarrow> j>i \<Longrightarrow>
      LFP\<^bsub>Ls ! (j-1)\<^esub> (\<lambda>xj\<in>carrier (Ls ! (j-1)). (Pr\<^bsub>j\<^esub> F) (\<lambda>h\<in>{1..length Ls}. if h = i then v i else if h = j then xj else nested Ls h (Bot(j \<mapsto> xj, i \<mapsto> v i)) F)) \<sqsubseteq>\<^bsub>Ls ! (j-1)\<^esub> v j"
    proof -
      fix j assume a_j:"j\<in>{1..length Ls}" and \<open>j>i\<close>
      interpret Ls_j: complete_lattice "Ls ! (j-1)"
        using Ls.Ls_comp_lat a_j by auto
      let ?f = "\<lambda>xj\<in>carrier (Ls ! (j-1)). (Pr\<^bsub>j\<^esub> F) (\<lambda>h\<in>{1..length Ls}. if h = i then v i else if h = j then xj else nested Ls h (Bot(j \<mapsto> xj, i \<mapsto> v i)) F)"
      show "LFP\<^bsub>Ls ! (j-1)\<^esub> (\<lambda>xj\<in>carrier (Ls ! (j-1)). (Pr\<^bsub>j\<^esub> F) (\<lambda>h\<in>{1..length Ls}. if h = i then v i else if h = j then xj else nested Ls h (Bot(j \<mapsto> xj, i \<mapsto> v i)) F)) \<sqsubseteq>\<^bsub>Ls ! (j-1)\<^esub> v j"
        using ij__lem[of "j"] Ls_j.LFP_lowerbound[of "v j" "?f"] b_v''[of "j"] \<open>i<j\<close> a_j by auto
    qed

    have ji__lem: "\<And>j. j\<in>{1..length Ls} \<Longrightarrow> j<i \<Longrightarrow> ((Pr\<^bsub>j\<^esub> F) (\<lambda>h\<in>{1..length Ls}. if h=i then v i else if h=j then v j else nested Ls h (Bot(j\<mapsto>v j, i\<mapsto>v i)) F)
       \<sqsubseteq>\<^bsub>Ls ! (j-1)\<^esub> v j)"
    proof -
      fix j assume a_j:"j\<in>{1..length Ls}" and \<open>j<i\<close>
      let ?w = "\<lambda>k\<in>{1..length Ls-1}. if k=j then v j else nested (SpLs\<^bsub>i\<^esub> Ls) k (Bot(j\<mapsto>(v j))) (Ls.specialize_fn i (v i) F)"
      have b1:"?w \<in> carrier_spl Ls i"
      proof (rule Ls.in_carrier_spl_I)
        show "i \<in> {1..length Ls}"
          using suc.prems by auto
      next
        show "\<And>y. y \<notin> {1..length Ls - 1} \<Longrightarrow>
          ?w y = undefined"
          by auto
      next
        fix h assume \<open>h\<in>{1..length Ls-1}\<close>
        have r1:"h \<ge> i \<Longrightarrow> 
            ?w h \<in> carrier (Ls ! h)"
        proof - 
          assume \<open>h\<ge>i\<close>
          have b1:"(\<lambda>k\<in>{1..length Ls - 1}. if k = j then v j else nested SpLs\<^bsub>i\<^esub> Ls k (Bot(j\<mapsto> v j)) (Ls.specialize_fn i (v i) F)) h = 
            (if h = j then v j else nested SpLs\<^bsub>i\<^esub> Ls h (Bot(j \<mapsto> v j)) (Ls.specialize_fn i (v i) F))"
            using \<open>h\<in>{1..length Ls-1}\<close> by auto
          have \<open>h\<noteq>j\<close>
            using \<open>h\<ge>i\<close> \<open>j<i\<close> by auto
          have "nested (SpLs\<^bsub>i\<^esub> Ls) h (Bot(j \<mapsto> v j)) (Ls.specialize_fn i (v i) F) \<in> carrier (Ls! h)"
          proof -
            have c1:"h \<in> {1..length SpLs\<^bsub>i\<^esub> Ls}"
              using \<open>h\<in>{1..length Ls-1}\<close> length_minus_1' suc.prems by auto
            have c2:"(Bot(j\<mapsto> v j)) h = None"
              using \<open>h\<noteq>j\<close> unfolding Bot_def by auto
            show ?thesis
              using hat_i_sub_locale.nested_closed[of "h" "Bot(j \<mapsto> v j)" "Ls.specialize_fn i (v i) F"] 
                    c1 c2 SpLs_nth_ge[of "i" "Ls" "h"] 
                    \<open>h\<ge>i\<close> suc.prems \<open>h\<in>{1..length Ls-1}\<close>
              by auto
          qed
          then show ?thesis
            using \<open>h\<noteq>j\<close> b1 by auto
        qed
        have r2:"i > h \<Longrightarrow>
          ?w h \<in> carrier (Ls ! (h-1))"
        proof - 
          assume \<open>i>h\<close>
          have b1:"h=j \<Longrightarrow> v j \<in> carrier (Ls ! (h-1))"
            using b_v'' a_j by auto
          have "h\<noteq>j \<Longrightarrow> nested (SpLs\<^bsub>i\<^esub> Ls) h (Bot(j \<mapsto> v j)) (Ls.specialize_fn i (v i) F) \<in> carrier (Ls ! (h-1))"
          proof - assume \<open>h\<noteq>j\<close>
            have c3:"((SpLs\<^bsub>i\<^esub> Ls) ! (h-1)) = (Ls ! (h-1))"
              using SpLs_nth_lt[of "i" "Ls" "h"] suc.prems(5) \<open>h\<in>{1..length Ls-1}\<close> \<open>i>h\<close> by auto
            have c2:"(Bot(j \<mapsto> v j)) h = None"
              using \<open>h\<noteq>j\<close> unfolding Bot_def by auto
            have c1:"h \<in> {1..length SpLs\<^bsub>i\<^esub> Ls}"
              using \<open>h\<in>{1..length Ls-1}\<close> length_minus_1' suc.prems by auto
            show ?thesis
              using hat_i_sub_locale.nested_closed[of "h" "Bot(j\<mapsto>v j)"] c1 c2 c3 by auto
          qed
          then show ?thesis
            using b1 \<open>h\<in>{1..length Ls-1}\<close> by auto
        qed
        show "(h < i \<longrightarrow> ?w h \<in> carrier (Ls ! (h-1))) \<and> (i \<le> h \<longrightarrow> ?w h \<in> carrier (Ls ! h))"
          using r1 r2 by auto
      qed
      then have b3:"?w = fst (Ls.n_to_two i (Ls.two_to_n i (?w, v i)))"
        using Ls.n_two__two_n_id[of "?w" "i" "v i"] b_v' suc.prems(5) by auto
      have b2:"Ls.two_to_n i (?w, v i) \<in> carrier \<Otimes>Ls"
        using b1 b_v' Ls.two_n__carrier[of "i" "?w" "v i"] suc.prems(5) by auto
      then have b5:"
        Pr\<^bsub>j\<^esub> (Ls.specialize_fn i (v i) F) ?w 
      = (Pr\<^bsub>j\<^esub> F) (Ls.two_to_n i (?w, v i))"
        using Ls.specialize_proj_eq(1)[of "i" "j" "Ls.two_to_n i (?w, v i)" "v i" "F"] Ls.two_to_n_simps(1)
              suc.prems(5) \<open>i>j\<close> a_j b1 b3 
        by (metis (lifting) b_v')
      have b4:"Ls.two_to_n i (?w, v i) = (\<lambda>h\<in>{1..length Ls}. if h=i then v i else if h=j then v j
               else if h<i then nested Ls h (Bot(j\<mapsto>v j, i\<mapsto>v i)) F else nested Ls h (Bot(j\<mapsto>v j, i\<mapsto>v i)) F)"
        (is "?l=?r")
      proof (rule Ls.vect_eqI)
        show "Ls.two_to_n i (?w, v i) \<in> carrier (\<Otimes>Ls)"
          using b2 by auto
        show "?r\<in> carrier (\<Otimes>Ls)"
        proof (rule cart_carrier_criterion)
          show "\<And>i. i\<notin>{1..length Ls} \<Longrightarrow> ?r i = undefined"
            by auto
        next
          fix h assume \<open>h\<in>{1..length Ls}\<close>
          have "h\<noteq>i \<Longrightarrow> h\<noteq>j \<Longrightarrow> nested Ls h (Bot(j\<mapsto>v j, i \<mapsto> v i)) F \<in> carrier (Ls!(h-1))"
            using Ls.nested_closed[of "h" "Bot(j \<mapsto> v j, i \<mapsto> v i)" "F"] \<open>h \<in> {1..length Ls}\<close> suc.prems(5) unfolding Bot_def 
            by (metis  fun_upd_apply)
          then show "?r h \<in>carrier (Ls ! (h-1))"
            using b_v'' a_j suc.prems(5) \<open>h\<in>{1..length Ls}\<close> 
            by auto
        qed
      next
        fix h assume \<open>h\<in>{1..length Ls}\<close>
        show "?l h = ?r h"
        proof -
          have c1:"h>i \<Longrightarrow> ?l h = ?r h"
          proof - 
            assume \<open>h>i\<close>
            then have \<open>h-1\<noteq>j\<close>
              using \<open>i>j\<close> by auto
            have "h-1 \<in> {1..length Ls-1}"
              using \<open>h>i\<close> suc.prems \<open>h\<in>{1..length Ls}\<close> by auto
            have \<open>h-1\<ge>i\<close>
              using \<open>h>i\<close> by auto
            from Ls.two_to_n_simps(3)[of "?w" "i" "v i" "h"] have "?l h = ?w (h-1)"
              using \<open>h>i\<close> \<open>h\<in>{1..length Ls}\<close> b_v' b1 suc.prems(5) by auto
            also have "... = nested (SpLs\<^bsub>i\<^esub> Ls) (h-1) (Bot(j \<mapsto> v j)) (Ls.specialize_fn i (v i) F)"
              using \<open>h-1\<noteq>j\<close> \<open>h-1\<in>{1..length Ls-1}\<close> by auto
            finally show "?l h = ?r h"
              using \<open>h>i\<close> \<open>h-1\<noteq>j\<close> \<open>h\<in>{1..length Ls}\<close> ji__ik[of "j" "h-1"] \<open>h-1\<in>{1..length Ls-1}\<close> a_j \<open>i>j\<close> \<open>i\<le>h-1\<close> by auto
          qed
          have c2:"h=i \<Longrightarrow> ?l h = ?r h"
          proof - assume \<open>h=i\<close>
            from Ls.two_to_n_simps(1)[of "?w" "i" "v i"] 
            have b1:"?l h = v i"
              using \<open>h=i\<close> \<open>h\<in>{1..length Ls}\<close> b1 b_v' suc.prems(5) by auto
            have b2:"?r h = v i"
              using \<open>h\<in>{1..length Ls}\<close> \<open>h=i\<close> by auto
            then show ?thesis 
              using b1 b2 by auto
          qed
          have c3:"h=j \<Longrightarrow> ?l h = ?r h"
          proof - assume \<open>h=j\<close>
            have b2:"?r h = v j"
              using \<open>h=j\<close> \<open>h\<in>{1..length Ls}\<close> by auto
            have \<open>h<i\<close>
              using \<open>h=j\<close> \<open>j<i\<close> by auto
            then have \<open>h\<in>{1..length Ls -1}\<close>
              using \<open>h\<in>{1..length Ls}\<close> suc.prems by auto
            from Ls.two_to_n_simps(2)[of "?w" "i" "v i" "h"] 
            have b1:"?l h = ?w h"
              using \<open>h=j\<close> \<open>h\<in>{1..length Ls}\<close> b1 b_v' \<open>j<i\<close> suc.prems(5) by auto
            also have b3:"... = v j"
              using \<open>h\<in>{1..length Ls-1}\<close> \<open>h=j\<close> by auto
            finally show ?thesis 
              using b1 b2 by auto
          qed
          have c4:"h<i \<Longrightarrow> h\<noteq>j \<Longrightarrow> ?l h = ?r h"
          proof - assume \<open>h<i\<close> and \<open>h\<noteq>j\<close>
            have \<open>h\<in>{1..length Ls-1}\<close>
              using \<open>h<i\<close> suc.prems \<open>h\<in>{1..length Ls}\<close> by auto
            have b2:"?r h = nested Ls h (Bot(j \<mapsto> v j, i \<mapsto> v i)) F"
              using \<open>h\<in>{1..length Ls}\<close> \<open>h\<noteq>j\<close> \<open>h<i\<close> by auto
            from Ls.two_to_n_simps(2)[of "?w" "i" "v i" "h"] 
            have b1:"?l h = ?w h"
              using \<open>h\<noteq>j\<close> \<open>h<i\<close> \<open>h\<in>{1..length Ls}\<close> b1 b_v' \<open>i>j\<close> suc.prems(5) by auto
            also have b3:"... = nested SpLs\<^bsub>i\<^esub> Ls h (Bot(j\<mapsto> v j)) (Ls.specialize_fn i (v i) F)"
              using \<open>h\<in>{1..length Ls-1}\<close> \<open>h\<noteq>j\<close> by auto
            finally show ?thesis
              using b1 b2 ji__ki[of "j" "h"] a_j \<open>h\<in>{1..length Ls-1}\<close> \<open>h<i\<close> \<open>i>j\<close> by auto
          qed
          show ?thesis
            using c1 c2 c3 c4 \<open>h\<in>{1..length Ls}\<close> \<open>i>j\<close> by linarith
        qed
      qed
      then have "Ls.two_to_n i (?w, v i) = (\<lambda>h\<in>{1..length Ls}. if h=i then v i else if h=j then v j
                                           else nested Ls h (Bot(j\<mapsto>v j, i\<mapsto>v i)) F)"
        by auto
      then have "Pr\<^bsub>j\<^esub> (Ls.specialize_fn i (v i) F) ?w 
      = (Pr\<^bsub>j\<^esub> F) (\<lambda>h\<in>{1..length Ls}. if h=i then v i else if h=j then v j else nested Ls h (Bot(j\<mapsto>v j, i\<mapsto>v i)) F)"
        using b5 by auto
      then show "Pr\<^bsub>j\<^esub> F (\<lambda>h\<in>{1..length Ls}. if h = i then v i else if h = j then v j else nested Ls h (Bot(j \<mapsto> v j, i \<mapsto> v i)) F) \<sqsubseteq>\<^bsub>Ls ! (j-1)\<^esub> v j"
        using r0[of "j"] a_j \<open>i>j\<close> by auto
    qed
    then have ji_aj_geq:"\<And>j. j\<in>{1..length Ls} \<Longrightarrow> j<i \<Longrightarrow>
      LFP\<^bsub>Ls ! (j-1)\<^esub> (\<lambda>xj\<in>carrier (Ls ! (j-1)). (Pr\<^bsub>j\<^esub> F) (\<lambda>h\<in>{1..length Ls}. if h = i then v i else if h = j then xj else nested Ls h (Bot(j \<mapsto> xj, i \<mapsto> v i)) F)) \<sqsubseteq>\<^bsub>Ls ! (j-1)\<^esub> v j"
    proof -
      fix j assume a_j:"j\<in>{1..length Ls}" and \<open>j<i\<close>
      interpret Ls_j: complete_lattice "Ls ! (j-1)"
        using Ls.Ls_comp_lat a_j by auto
      let ?f = "\<lambda>xj\<in>carrier (Ls ! (j-1)). (Pr\<^bsub>j\<^esub> F) (\<lambda>h\<in>{1..length Ls}. if h = i then v i else if h = j then xj else nested Ls h (Bot(j \<mapsto> xj, i \<mapsto> v i)) F)"
      show "LFP\<^bsub>Ls ! (j-1)\<^esub> (\<lambda>xj\<in>carrier (Ls ! (j-1)). (Pr\<^bsub>j\<^esub> F) (\<lambda>h\<in>{1..length Ls}. if h = i then v i else if h = j then xj else nested Ls h (Bot(j \<mapsto> xj, i \<mapsto> v i)) F)) \<sqsubseteq>\<^bsub>Ls ! (j-1)\<^esub> v j"
        using ji__lem[of "j"] Ls_j.LFP_lowerbound[of "v j" "?f"] b_v''[of "j"] \<open>i>j\<close> a_j by auto
    qed

    have i_neq_j__geq_nested_simpl:"\<And>j. j\<in>{1..length Ls} \<Longrightarrow> j\<noteq>i \<Longrightarrow> LFP\<^bsub>Ls ! (j-1)\<^esub>
     (\<lambda>xj\<in>carrier (Ls ! (j-1)). Pr\<^bsub>j\<^esub> F (\<lambda>h\<in>{1..length Ls}. if h = i then v i else if h = j then xj else nested Ls h (Bot(j\<mapsto>xj, i\<mapsto>v i)) F))
      = nested Ls j (Bot(i\<mapsto>v i)) F"
    proof -
      fix j assume \<open>j\<in>{1..length Ls}\<close> and \<open>j\<noteq>i\<close>
      have "nested Ls j (Bot(i\<mapsto>v i)) F = LFP\<^bsub>Ls ! (j-1)\<^esub>
                (\<lambda>xi\<in>carrier (Ls ! (j-1)). Pr\<^bsub>j\<^esub> F (\<lambda>ja\<in>{1..length Ls}. if ja = j then xi else if (Bot(i \<mapsto> v i)) ja \<noteq> None then the ((Bot(i \<mapsto> v i)) ja) else nested Ls ja (Bot(i \<mapsto> v i, j \<mapsto> xi)) F))"
        using nested.simps[where Ls ="Ls" and B="Bot(i\<mapsto>v i)" and i="j" and f="F"] \<open>j\<in>{1..length Ls}\<close> \<open>j\<noteq>i\<close> Bot_defined by metis
      also have "... = LFP\<^bsub>Ls ! (j-1)\<^esub>
                (\<lambda>xj\<in>carrier (Ls ! (j-1)). Pr\<^bsub>j\<^esub> F (\<lambda>h\<in>{1..length Ls}. if h = i then v i else if h = j then xj else nested Ls h (Bot(j\<mapsto>xj, i\<mapsto>v i)) F))"
      proof -
        have "\<And>xj. xj\<in>carrier (Ls ! (j-1)) \<Longrightarrow> (\<lambda>ja\<in>{1..length Ls}. if ja = j then xj else if (Bot(i \<mapsto> v i)) ja \<noteq> None then the ((Bot(i \<mapsto> v i)) ja) else nested Ls ja (Bot(i \<mapsto> v i, j \<mapsto> xj)) F)
              = (\<lambda>h\<in>{1..length Ls}. if h = i then v i else if h = j then xj else nested Ls h (Bot(j\<mapsto>xj, i\<mapsto>v i)) F)"
          using Bot_defined[of "i" "v i"] \<open>j\<noteq>i\<close> 
          by (smt (verit, ccfv_SIG) fun_upd_same fun_upd_twist option.sel restrict_ext)
        then show ?thesis
          by (metis (no_types, lifting) restrict_ext)
      qed
      finally show "LFP\<^bsub>Ls ! (j-1)\<^esub>
          (\<lambda>xj\<in>carrier (Ls ! (j-1)). Pr\<^bsub>j\<^esub> F (\<lambda>h\<in>{1..length Ls}. if h = i then v i else if h = j then xj else nested Ls h (Bot(j\<mapsto>xj, i\<mapsto>v i)) F))
            = nested Ls j (Bot(i\<mapsto>v i)) F"
        by auto
    qed
    from ji_aj_geq ij_aj_geq i_neq_j__geq_nested_simpl
    have i_neq_j__geq_nested: "\<And>j. j\<in>{1..length Ls} \<Longrightarrow> j\<noteq>i \<Longrightarrow> nested Ls j (Bot(i \<mapsto> v i)) F \<sqsubseteq>\<^bsub>Ls ! (j-1)\<^esub> v j"
      by (metis (no_types, lifting) ge_le_eq_cases)
    
    have v_i_form: "(\<lambda>j\<in>{1..length Ls}. if j = i then v i else v j) = v"
    proof (rule Ls.vect_eqI)
      show "v\<in>carrier (\<Otimes>Ls)"
        using b_v by simp
    next
      show "(\<lambda>j\<in>{1..length Ls}. if j = i then v i else v j) \<in> carrier \<Otimes>Ls"
        using cart_carrier_criterion b_v'' by auto
    next
      fix k assume \<open>k\<in>{1..length Ls}\<close>
      then show "(\<lambda>j\<in>{1..length Ls}. if j = i then v i else v j) k = v k"
        by auto
    qed

    have v_i_fp: "(Pr\<^bsub>i\<^esub> F) (\<lambda>j\<in>{1..length Ls}. if j = i then v i else v j) = v i"
    proof -
      from suc.prems(4) have \<open>F v = v\<close>
        unfolding fps_def by (simp add: Ls.eq_is_equal)
      show ?thesis 
        unfolding proj_def using \<open>F v = v\<close> v_i_form by auto
    qed
    then have "(Pr\<^bsub>i\<^esub> F) (\<lambda>j\<in>{1..length Ls}. if j = i then v i else nested Ls j (Bot(i\<mapsto> v i)) F) \<sqsubseteq>\<^bsub>Ls!(i-1)\<^esub> v i"
    proof -
      have prF_iso:"isotone (\<Otimes>Ls) (Ls!(i-1)) (Pr\<^bsub>i\<^esub> F)"
        using Ls.mono_proj_iso suc.prems by auto
      have "\<And>j. j\<in>{1..length Ls} \<Longrightarrow> j\<noteq>i \<Longrightarrow> nested Ls j (Bot(i\<mapsto> v i)) F \<sqsubseteq>\<^bsub>Ls!(j-1)\<^esub> v j"
        using i_neq_j__geq_nested suc.prems by auto
      then have "(Pr\<^bsub>i\<^esub> F) (\<lambda>j\<in>{1..length Ls}. if j = i then v i else nested Ls j (Bot(i\<mapsto> v i)) F) \<sqsubseteq>\<^bsub>Ls!(i-1)\<^esub> v i"
        using prF_iso use_iso2[of "(\<Otimes>Ls)" "Ls!(i-1)" "Pr\<^bsub>i\<^esub> F" 
                                  "\<lambda>j\<in>{1..length Ls}. if j = i then v i else nested Ls j (Bot(i\<mapsto> v i)) F" 
                                  "\<lambda>j\<in>{1..length Ls}. if j = i then v i else v j"
                                  ]
              v_i_form
              b_v b_v''
        unfolding proj_def
        by (smt (verit, ccfv_threshold) Bot_defined FuncSet.restrict_apply Locales.proj_def Ls.cart_prod_lattice_axioms Ls.le_refl Ls.nested_closed car_prod_carrierI car_prod_carrier_form
          cart_prod_lattice.Ls_le_criterion v_i_fp)
      then show ?thesis
        by auto
    qed
    then show ?thesis
      by auto
  qed
qed

lemma (in cart_prod_lattice) len_1_LFP:
  assumes F_wd: "F \<in> carrier (\<Otimes>Ls) \<rightarrow>\<^sub>E carrier (\<Otimes>Ls)"
      and a_len: "length Ls = 1"
  shows "LFP\<^bsub>\<Otimes>Ls\<^esub> F 1 = LFP\<^bsub>Ls ! 0\<^esub> (\<lambda>xi\<in>carrier (Ls!0). F (\<lambda>j\<in>{1..length Ls}. xi) 1)"
proof -
  interpret base: complete_lattice "\<Otimes>Ls"
    by (simp add: local.complete_lattice_axioms)
  interpret base_i: complete_lattice "(Ls!0)"
    using Ls_comp_lat a_len by auto
  interpret iso: complete_lattice_hom "\<Otimes>Ls" "(Ls!0)" "\<lambda>x\<in>carrier (\<Otimes>Ls). x 1" "\<lambda>xi\<in>carrier (Ls!0). (\<lambda>i\<in>{1..length Ls}. xi)"
    "F" "\<lambda>x\<in>carrier (Ls!0). (proj 1 F) (\<lambda>j\<in>{1..length Ls}. x)"
  proof (unfold_locales)
    show "(\<lambda>x\<in>carrier (\<Otimes>Ls). x 1) \<in> carrier (\<Otimes>Ls) \<rightarrow>\<^sub>E carrier (Ls!0)"
      using cart_carrier_iff[where Ls = "Ls"] a_len by auto
  next
    show "(\<lambda>xi\<in>carrier (Ls!0). \<lambda>i\<in>{1..length Ls}. xi) \<in> carrier (Ls!0) \<rightarrow>\<^sub>E carrier \<Otimes>Ls"
      using cart_carrier_iff[where Ls = "Ls"] a_len by auto
  next
    show "F \<in> carrier \<Otimes>Ls \<rightarrow>\<^sub>E carrier \<Otimes>Ls"
      using assms by auto
  next
    show "(\<lambda>x\<in>carrier (Ls!0). (proj 1 F) (\<lambda>j\<in>{1..length Ls}. x)) \<in> carrier (Ls!0) \<rightarrow>\<^sub>E carrier (Ls!0)"
    proof
      show "\<And>x. x \<notin> carrier (Ls!0) \<Longrightarrow> (\<lambda>x\<in>carrier (Ls!0). Pr\<^bsub>1\<^esub> F (\<lambda>j\<in>{1..length Ls}. x)) x = undefined"
        by auto
    next
      fix x assume a_x:"x\<in> carrier (Ls!0)"
      have eq:"(\<lambda>x\<in>carrier (Ls!0). Pr\<^bsub>1\<^esub> F (\<lambda>j\<in>{1..length Ls}. x)) x = F (\<lambda>j\<in>{1..length Ls}. x) 1"
        unfolding proj_def using a_x by auto
      have "(\<lambda>j\<in>{1..length Ls}. x) \<in> carrier (\<Otimes>Ls)"
        using a_x cart_carrier_iff[of "\<lambda>j\<in>{1..length Ls}. x" "Ls"] a_len by auto
      then have "F (\<lambda>j\<in>{1..length Ls}. x) \<in> carrier (\<Otimes>Ls)"
        using assms by auto
      then have "F (\<lambda>j\<in>{1..length Ls}. x) 1 \<in> carrier (Ls!0)"
        using cart_carrier_iff[of "F (\<lambda>j\<in>{1..length Ls}. x)" "Ls"] a_len by auto
      then show "(\<lambda>x\<in>carrier (Ls!0). Pr\<^bsub>1\<^esub> F (\<lambda>j\<in>{1..length Ls}. x)) x \<in> carrier (Ls!0)"
        using eq by auto
    qed
  next
    fix x y assume a_x:"x \<in> carrier \<Otimes>Ls" and a_y:"y\<in>carrier (\<Otimes>Ls)" and a_xy:"x \<sqsubseteq>\<^bsub>\<Otimes>Ls\<^esub> y"
    from Ls_le_criterion[of "x" "y"]
    have "(x 1) \<sqsubseteq>\<^bsub>(Ls!0)\<^esub> (y 1)"
      using a_xy by (simp add: a_len)
    then show "(\<lambda>x\<in>carrier \<Otimes>Ls. x 1) x \<sqsubseteq>\<^bsub>(Ls!0)\<^esub> (\<lambda>x\<in>carrier \<Otimes>Ls. x 1) y"
      using a_x a_y by auto
  next
    fix x y assume a_x:"x \<in> carrier (Ls!0)" and a_y:"y \<in> carrier (Ls!0)" and a_xy:"x \<sqsubseteq>\<^bsub>(Ls!0)\<^esub> y"
    have a_x':"(\<lambda>xi\<in>carrier (Ls!0). \<lambda>i\<in>{1..length Ls}. xi) x = (\<lambda>i\<in>{1..length Ls}. x)"
      using a_x by auto
    have a_y':"(\<lambda>xi\<in>carrier (Ls!0). \<lambda>i\<in>{1..length Ls}. xi) y = (\<lambda>i\<in>{1..length Ls}. y)"
      using a_y by auto
    have b_x:"(\<lambda>i\<in>{1..length Ls}. x) 1 = x"
      using a_len by auto
    have b_y:"(\<lambda>i\<in>{1..length Ls}. y) 1 = y"
      using a_len by auto
    have b_xy:"(\<lambda>i\<in>{1..length Ls}. x) 1 \<sqsubseteq>\<^bsub>(Ls!0)\<^esub> (\<lambda>i\<in>{1..length Ls}. y) 1"
      using b_x b_y a_xy by auto
    then have "\<forall>i\<in>{1..length Ls}. (\<lambda>i\<in>{1..length Ls}. x) i \<sqsubseteq>\<^bsub>Ls ! (i-1)\<^esub> (\<lambda>i\<in>{1..length Ls}. y) i"
      using a_len by auto
    then have "(\<lambda>i\<in>{1..length Ls}. x)\<sqsubseteq>\<^bsub>\<Otimes>Ls\<^esub> (\<lambda>i\<in>{1..length Ls}. y)"
      using Ls_le_criterion by auto
    then show "(\<lambda>xi\<in>carrier (Ls!0). \<lambda>i\<in>{1..length Ls}. xi) x \<sqsubseteq>\<^bsub>\<Otimes>Ls\<^esub> (\<lambda>xi\<in>carrier (Ls!0). \<lambda>i\<in>{1..length Ls}. xi) y"
      using a_x' a_y' by auto
  next
    fix x assume a_x:"x\<in>carrier (\<Otimes>Ls)"
    have a_x':"x 1 \<in> carrier (Ls!0)"
      using cart_carrier_iff 
      by (metis (mono_tags, lifting) a_len a_x atLeastAtMost_iff diff_self_eq_0 eq_imp_le)
    have "(\<lambda>xi\<in>carrier (Ls!0). \<lambda>i\<in>{1..length Ls}. xi) ((\<lambda>x\<in>carrier \<Otimes>Ls. x 1) x) = (\<lambda>xi\<in>carrier (Ls!0). \<lambda>i\<in>{1..length Ls}. xi) (x 1)"
      using a_x by auto
    also have "... = (\<lambda>i\<in>{1..length Ls}. x 1)"
      using a_x cart_carrier_iff[of "x" "Ls"] a_len by auto
    also have "... = x"
    proof 
      show "(\<lambda>i\<in>{1..length Ls}. x 1) \<in> carrier \<Otimes>Ls"
        using cart_carrier_criterion[of "Ls" "\<lambda>i\<in>{1..length Ls}. x 1"] a_x' a_len by auto
      show "x\<in>carrier (\<Otimes>Ls)"
        using a_x by auto
      fix i assume a_i:"i\<in>{1..length Ls}"
      then have \<open>i=1\<close> 
        using a_len by auto
      then show "(\<lambda>i\<in>{1..length Ls}. x 1) i = x i"
        using a_len by auto
    qed
    finally show "(\<lambda>xi\<in>carrier (Ls!0). \<lambda>i\<in>{1..length Ls}. xi) ((\<lambda>x\<in>carrier \<Otimes>Ls. x 1) x) = x"
      by auto
  next
    fix x assume a_x:"x\<in>carrier (Ls!0)"
    have b1:"(\<lambda>i\<in>{1..length Ls}. x) \<in> carrier (\<Otimes>Ls)"
      using cart_carrier_criterion[of "Ls" "(\<lambda>i\<in>{1..length Ls}. x)"] a_len a_x by auto
    have eq1:"(\<lambda>x\<in>carrier \<Otimes>Ls. x 1) ((\<lambda>xi\<in>carrier (Ls!0). \<lambda>i\<in>{1..length Ls}. xi) x) = (\<lambda>x\<in>carrier \<Otimes>Ls. x 1) (\<lambda>i\<in>{1..length Ls}. x)"
      using a_x by auto
    have eq2:"(\<lambda>x\<in>carrier \<Otimes>Ls. x 1) (\<lambda>i\<in>{1..length Ls}. x) = (\<lambda>i\<in>{1..length Ls}. x) 1"
      using b1 by auto
    have eq3:"(\<lambda>i\<in>{1..length Ls}. x) 1 = x"
      using a_len by auto
    show "(\<lambda>x\<in>carrier \<Otimes>Ls. x 1) ((\<lambda>xi\<in>carrier (Ls!0). \<lambda>i\<in>{1..length Ls}. xi) x) = x"
      using eq1 eq2 eq3 by auto
  next
    fix x assume a_x:"x\<in>carrier (\<Otimes>Ls)"
    have b1:"x 1 \<in> carrier (Ls!0)"
      using a_x cart_carrier_iff[of "x" "Ls"] a_len by auto
    have b2:"(\<lambda>j\<in>{1..length Ls}. (x 1)) = x"
    proof
      show "x \<in> carrier \<Otimes>Ls"
        using a_x by simp
      show "(\<lambda>j\<in>{1..length Ls}. x 1) \<in> carrier \<Otimes>Ls"
        using b1 cart_carrier_criterion[of "Ls"] a_len by auto
      show "\<And>i. i \<in> {1..length Ls} \<Longrightarrow> (\<lambda>j\<in>{1..length Ls}. x 1) i = x i"
        using a_len by auto
    qed
    have eq1:"((\<lambda>x\<in>carrier \<Otimes>Ls. x 1) \<circ> F) x = (\<lambda>x\<in>carrier \<Otimes>Ls. x 1) (F x)"
      using a_x by auto
    have "F x \<in> carrier (\<Otimes>Ls)"
      using assms a_x by auto
    then have eq2:"(\<lambda>x\<in>carrier \<Otimes>Ls. x 1) (F x) = F x 1"
      by auto
    have "((\<lambda>x\<in>carrier (Ls!0). (proj 1 F) (\<lambda>j\<in>{1..length Ls}. x)) \<circ> (\<lambda>x\<in>carrier \<Otimes>Ls. x 1)) x = ((\<lambda>x\<in>carrier (Ls!0). (proj 1 F) (\<lambda>j\<in>{1..length Ls}. x))) (x 1)"
      using a_x by auto
    also have "... = (Pr\<^bsub>1\<^esub> F) (\<lambda>j\<in>{1..length Ls}. (x 1))"
      using b1 by auto
    finally have eq3:"((\<lambda>x\<in>carrier (Ls!0). (proj 1 F) (\<lambda>j\<in>{1..length Ls}. x)) \<circ> (\<lambda>x\<in>carrier \<Otimes>Ls. x 1)) x = F x 1"
      using b1 b2 unfolding proj_def by auto
    show "((\<lambda>x\<in>carrier \<Otimes>Ls. x 1) \<circ> F) x = ((\<lambda>x\<in>carrier (Ls!0). Pr\<^bsub>1\<^esub> F (\<lambda>j\<in>{1..length Ls}. x)) \<circ> (\<lambda>x\<in>carrier \<Otimes>Ls. x 1)) x"
      using eq1 eq2 eq3 by auto
  qed
  from iso.LFP_compat_forward 
  show ?thesis
    using LFP_closed[of "F"] unfolding proj_def by auto
qed

lemma (in cart_prod_lattice) len_1_GFP:
  assumes F_wd: "F \<in> carrier (\<Otimes>Ls) \<rightarrow>\<^sub>E carrier (\<Otimes>Ls)"
      and a_len: "length Ls = 1"
    shows "GFP\<^bsub>\<Otimes>Ls\<^esub> F 1 = GFP\<^bsub>Ls ! 0\<^esub> (\<lambda>xi\<in>carrier (Ls!0). F (\<lambda>j\<in>{1..length Ls}. xi) 1)"
proof -
  interpret Lat: cart_prod_lattice "invert_Ls Ls"
    using cart_prod_lattice_axioms invert_cart_prod_lattice by auto
  have "GFP\<^bsub>\<Otimes>Ls\<^esub> F 1 = LFP\<^bsub>inv_gorder \<Otimes>Ls\<^esub> F 1"
    using LFP_dual[of "\<Otimes>Ls" "F"] by auto
  also have "... = LFP\<^bsub>\<Otimes>(invert_Ls Ls)\<^esub> F 1"
    using inv_cart_prod_is_cart_prod_inv[of "Ls"] by auto
  also have "... = LFP\<^bsub>(invert_Ls Ls) ! 0\<^esub> (\<lambda>xi\<in>carrier ((invert_Ls Ls)!0). F (\<lambda>j\<in>{1..length (invert_Ls Ls)}. xi) 1)"
    using Lat.len_1_LFP invert_preserve_funcset F_wd a_len by auto
  also have "... = LFP\<^bsub>inv_gorder (Ls ! 0)\<^esub> (\<lambda>xi\<in>carrier (inv_gorder (Ls ! 0)). F (\<lambda>j\<in>{1..length (invert_Ls Ls)}. xi) 1)"
    using invert_Ls_member[of "1" "Ls"] a_len by auto
  also have "... = LFP\<^bsub>inv_gorder (Ls ! 0)\<^esub> (\<lambda>xi\<in>carrier (Ls ! 0). F (\<lambda>j\<in>{1..length Ls}. xi) 1)"
    by simp
  also have "... = GFP\<^bsub>(Ls ! 0)\<^esub> (\<lambda>xi\<in>carrier (Ls ! 0). F (\<lambda>j\<in>{1..length Ls}. xi) 1)"
    using LFP_dual[of "Ls!0" "(\<lambda>xi\<in>carrier (Ls ! 0). F (\<lambda>j\<in>{1..length Ls}. xi) 1)"]
    by auto
  finally show ?thesis
    by simp
qed

(*Applications: 
  Inlining (mutual) recursive functions in a compiler?
*)
theorem general_Bekic:
  fixes F::"(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)"
  assumes a_car:"F \<in> carrier (\<Otimes>Ls) \<rightarrow>\<^sub>E carrier (\<Otimes>Ls)"
      and a_mono:"Mono\<^bsub>\<Otimes>Ls\<^esub> F"
      and cart_prod_lattice: "cart_prod_lattice Ls"
    shows "LFP\<^bsub>\<Otimes>Ls\<^esub> F = (\<lambda>i\<in>{1..length Ls}. nested Ls i Bot F)"
proof -
  interpret Ls: cart_prod_lattice Ls
    using cart_prod_lattice by auto
  (* The claim of Bekic is here. *)
  show "LFP\<^bsub>\<Otimes>Ls\<^esub> F = (\<lambda>i\<in>{1..length Ls}. nested Ls i Bot F)"
  proof (rule Ls.vect_eqI)
  (* For proof, we use a criterion testing equality of vectors. The criterion is:
    1) both sides are in the appropriate carrier
    2) every coordinate is equal
    The first two subgoal deal with 1). The last subgoal deals with 2).  
  *)
  (* 1st subgoal *)
    show "LFP\<^bsub>\<Otimes>Ls\<^esub> F \<in> carrier \<Otimes>Ls"
      using Ls.LFP_closed by auto
  next
  (* 2nd subgoal *)
    show "(\<lambda>i\<in>{1..length Ls}. nested Ls i Bot F) \<in> carrier \<Otimes>Ls"
    proof (rule cart_carrier_criterion)
      fix i assume \<open>i\<in>{1..length Ls}\<close>
      then show "(\<lambda>i\<in>{1..length Ls}. nested Ls i Bot F) i \<in> carrier (Ls ! (i-1))"
        using Ls.nested_closed[where B="Bot" and f="F"] Bot_undefined 
        by (metis restrict_apply')
    next
      fix i assume \<open>i\<notin>{1..length Ls}\<close>
      then show "(\<lambda>i\<in>{1..length Ls}. nested Ls i Bot F) i = undefined"
        by auto
    qed
  next
  (* 3rd subgoal *)
    fix i assume \<open>i\<in>{1..length Ls}\<close>
    show "LFP\<^bsub>\<Otimes>Ls\<^esub> F i = (\<lambda>i\<in>{1..length Ls}. nested Ls i Bot F) i"
      (is "?ai = ?bi")
      using assms \<open>i\<in>{1..length Ls}\<close>
    proof (induction "length Ls" arbitrary:Ls F i rule:nat_induct_one)
    (* We induct on the number of coordinates = length of Ls. *)
      case zero
      then show ?case (*in cart_prod_lattice, Ls must have positive length. Contradiction arises. *)
      proof -
        assume \<open>0=length Ls\<close>
        interpret Ls_zero: cart_prod_lattice "Ls"
          using zero by auto
        show ?case
          using \<open>0=length Ls\<close> Ls_zero.Ls_len_pos by auto
      qed
    next
      case one
      then show ?case (* n=1 case is mathematically trivial, but we handle it rather carefully. *)
        (is "?l = ?r")
      proof -
        interpret Ls_one: cart_prod_lattice "Ls"
          using one by auto
        have \<open>i=1\<close> 
          using \<open>i \<in> {1..length Ls}\<close> one by auto
        have "?r = nested Ls 1 Bot F"
          using \<open>i=1\<close> by auto
        then have r1:"?r = LFP\<^bsub>(Ls!0)\<^esub> (\<lambda>xi\<in>carrier (Ls!0). (proj 1 F) (\<lambda>(j::nat)\<in>{1..length Ls}. if j=1 then xi else 
          (if Bot j \<noteq> None then (the (Bot j)) else nested Ls j (Bot(1 \<mapsto> xi)) F)))"
          (is "?l1 = ?r1")
          using nested.simps[of "Ls" "1" "Bot" "F"] \<open>i = 1\<close> one unfolding Bot_def 
          by (metis diff_self_eq_0)
  
        have "\<And>xi. xi\<in>carrier (Ls!0) \<Longrightarrow> (\<lambda>j\<in>{1..length Ls}. if j=1 then xi else (if Bot j \<noteq> None then (the (Bot j)) else nested Ls j (Bot(1 \<mapsto> xi)) F))
              = (\<lambda>j\<in>{1..length Ls}. xi)"
        proof (rule restrict_eq)
          fix xi j assume \<open>xi\<in>carrier (Ls!0)\<close> and \<open>j\<in>{1..length Ls}\<close>
          have \<open>j=1\<close> 
            using one \<open>j\<in>{1..length Ls}\<close> by auto
          then show "(if j = 1 then xi else if Bot j \<noteq> None then the (Bot j) else nested Ls j (Bot(1 \<mapsto> xi)) F) = xi"
            by auto
        qed
        then have r2:"LFP\<^bsub>(Ls!0)\<^esub> (\<lambda>xi\<in>carrier (Ls!0). (proj 1 F) (\<lambda>j\<in>{1..length Ls}. if j=1 then xi else
                                      (if Bot j \<noteq> None then (the (Bot j)) else nested Ls j (Bot(1 \<mapsto> xi)) F))) 
            = LFP\<^bsub>(Ls!0)\<^esub> (\<lambda>xi\<in>carrier (Ls!0). (proj 1 F) (\<lambda>j\<in>{1..length Ls}. xi))"
          by (metis (no_types, lifting) restrict_ext)
        then have r3:"?r = LFP\<^bsub>(Ls!0)\<^esub> (\<lambda>xi\<in>carrier (Ls!0). F (\<lambda>j\<in>{1..length Ls}. xi) 1)"
          using r1 
          by (metis (no_types, lifting) ext Locales.proj_def)
        have l1:"?l = LFP\<^bsub>(Ls!0)\<^esub> (\<lambda>xi\<in>carrier (Ls!0). F (\<lambda>j\<in>{1..length Ls}. xi) 1)"
          using Ls_one.len_1_LFP[of "F"] one \<open>i=1\<close> by auto
        show ?thesis
          using l1 r3 by auto
      qed
    next
      (* We prove n>1 Bekic here. We follow proof on Xu's Arxiv article. *)
      case (suc n)
      then show ?case
      proof -
        (* we set up some background here. Particularly the variables
          ?aj = j-th coordinate of LFP of F
          ?aj' = nested j-th
          ?new_fp_hat_j = a vector containing (with j-th coord fixed to ?aj') nested h for each h
        *)
        interpret Ls_suc: cart_prod_lattice "Ls"
          using suc by auto      
        have a_len:"length Ls > 1"
          using \<open>Suc n = length Ls\<close> \<open>n\<ge>1\<close> by auto
        interpret Ls_i_sub: cart_prod_lattice "Sp_Ls i Ls"
          using hat_j_prod_locale_external[of "Ls" "i"] a_len 
                Ls_suc.cart_prod_lattice_axioms \<open>i \<in> {1..length Ls}\<close> by blast
        interpret Ls_i_coord: complete_lattice "Ls!(i-1)"
          using Ls_suc.Ls_comp_lat \<open>i \<in> {1..length Ls}\<close> by blast
        have a_i:"i\<in>{1..length Ls}"
          using suc by auto
        let ?ai="LFP\<^bsub>\<Otimes>Ls\<^esub> F i"
        have ai_car:"?ai \<in> carrier (Ls!(i-1))"
          using Ls_suc.LFP_closed[of "F"] cart_carrier_iff[of "LFP\<^bsub>\<Otimes>Ls\<^esub> F" "Ls"] a_i by blast
        let ?ai' = "nested Ls i Bot F"
        have ai'_car:"?ai' \<in> carrier (Ls!(i-1))"
          using Ls_suc.nested_closed[of "i" "Bot" "F"] Bot_undefined[of "i"] a_i by metis
        have eq1:"?ai' = (LFP\<^bsub>(Ls!(i-1))\<^esub> (\<lambda>xi\<in>carrier (Ls!(i-1)). (proj i F) (\<lambda>ja\<in>{1..length Ls}. (if ja = i then xi else if (Bot ja) \<noteq> None then the (Bot ja) else (nested Ls ja (Bot(i \<mapsto> xi)) F)))))"
          using Ls_suc.nested_simps_undefined[of "i" "Bot" "F"] a_i Bot_undefined[of "i"] 
          by (smt (verit, best) Bot_ext restrict_ext)
        have eq2:"(LFP\<^bsub>(Ls!(i-1))\<^esub> (\<lambda>xi\<in>carrier (Ls!(i-1)). (Pr\<^bsub>i\<^esub> F) (\<lambda>ja\<in>{1..length Ls}. (if ja = i then xi else if (Bot ja) \<noteq> None then the (Bot ja) else (nested Ls ja (Bot(i \<mapsto> xi)) F))))) 
            = (LFP\<^bsub>(Ls!(i-1))\<^esub> (\<lambda>xj\<in>carrier (Ls!(i-1)). (Pr\<^bsub>i\<^esub> F) (\<lambda>ja\<in>{1..length Ls}. if ja = i then xj else nested Ls ja (Bot(i \<mapsto> xj)) F)))"
          using Bot_undefined by (smt (verit, ccfv_SIG) restrict_ext)
        have ai'_eq3:"?ai' = (LFP\<^bsub>(Ls!(i-1))\<^esub> (\<lambda>xj\<in>carrier (Ls!(i-1)). (Pr\<^bsub>i\<^esub> F) (\<lambda>ja\<in>{1..length Ls}. if ja = i then xj else nested Ls ja (Bot(i \<mapsto> xj)) F)))"
          using eq1 eq2 by metis
        let ?new_fp_hat_i = "(\<lambda>h\<in>{1..length Ls-1}. if h<i then nested Ls h (Bot(i\<mapsto>?ai')) F else nested Ls (h+1) (Bot(i\<mapsto>?ai')) F)"
        have new_fp_hat_i_car:"?new_fp_hat_i \<in> carrier (\<Otimes>(SpLs\<^bsub>i\<^esub> Ls))"
        proof (rule Ls_suc.in_carrier_spl_I')
          show "i\<in>{1..length Ls}"
            using a_i by auto
        next
          show "\<And>y. y \<notin> {1..length Ls - 1} \<Longrightarrow> ?new_fp_hat_i y = undefined"
            by auto
        next
          fix h assume a_h:"h\<in>{1..length Ls-1}"
          have a_hi: "h < i \<Longrightarrow> ?new_fp_hat_i h \<in> carrier (Ls ! (h-1))"
          proof -
            have a_h':"h\<in>{1..length Ls}"
              using a_h by auto
            assume \<open>h<i\<close>
            then have eq:"?new_fp_hat_i h = nested Ls h (Bot(i \<mapsto> ?ai')) F"
              using \<open>h\<in>{1..length Ls-1}\<close> by auto
            have "nested Ls h (Bot(i \<mapsto> ?ai')) F \<in> carrier (Ls ! (h-1))"
              using Ls_suc.nested_closed[of "h" "Bot(i \<mapsto>?ai)"] \<open>h<i\<close> a_h' 
              by (metis Bot_defined Ls_suc.nested_closed nat_less_le)
            then show ?thesis
              using eq by auto
          qed
          have a_ih: "i\<le>h \<Longrightarrow> ?new_fp_hat_i h \<in> carrier (Ls ! h)"
          proof -
            have a_h':"h+1\<in>{1..length Ls}"
              using a_h by auto
            assume \<open>h\<ge>i\<close>
            then have eq:"?new_fp_hat_i h = nested Ls (h+1) (Bot(i \<mapsto> ?ai')) F"
              using \<open>h\<in>{1..length Ls-1}\<close> by auto
            have "nested Ls (h+1) (Bot(i \<mapsto> ?ai')) F \<in> carrier (Ls ! h)"
              using Ls_suc.nested_closed[of "h+1" "Bot(i \<mapsto>?ai')"] \<open>h\<ge>i\<close> a_h'
              by (metis Bot_defined Suc_eq_plus1 Suc_n_not_le_n diff_Suc_1)
            then show ?thesis
              using eq by auto
          qed
          show "(h < i \<longrightarrow> ?new_fp_hat_i h \<in> carrier (Ls ! (h-1))) \<and> (i \<le> h \<longrightarrow> ?new_fp_hat_i h \<in> carrier (Ls ! h))"
            using a_hi a_ih by auto
        qed
        have new_fp_hat_i_car':"?new_fp_hat_i \<in> carrier_spl Ls i"
          using new_fp_hat_i_car unfolding carrier_spl_simp by auto

        have b1:"n = length SpLs\<^bsub>i\<^esub> Ls"
          using length_minus_1'[of "i" "Ls"] \<open>Suc n = length Ls\<close> a_i by auto
        have b21:"Ls_suc.specialize_fn i ?ai' F \<in> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls \<rightarrow> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
          using Ls_suc.specialize_fn_funcset[of "i" "?ai'" "F"]
                a_i a_len ai'_car suc.prems(1)
          by blast
        have b22:"Ls_suc.specialize_fn i ?ai' F \<in> extensional (carrier (\<Otimes>SpLs\<^bsub>i\<^esub> Ls))"
          using Ls_suc.specialize_fn_ext[of "i" "?ai'" "F"]
                a_i a_len ai'_car
          by auto
        have b2:"Ls_suc.specialize_fn i ?ai' F \<in> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls \<rightarrow>\<^sub>E carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
          using b21 b22 PiE_iff by (smt (verit, best) Pi_iff)
        have b3:"Mono\<^bsub>\<Otimes>SpLs\<^bsub>i\<^esub> Ls\<^esub> (Ls_suc.specialize_fn i ?ai' F)"
          using Ls_suc.mono_specialize_mono[of "F" "i" "?ai'"] a_i ai'_car a_len suc by blast
  
        (* we apply IH here. *)
        from suc.hyps(2)[OF b1 b2 b3 Ls_i_sub.cart_prod_lattice_axioms]
             length_minus_1'[of "i" "Ls"]
        have lem_LFP_spF:"\<And>h. h \<in> {1..length Ls-1}
            \<Longrightarrow> LFP\<^bsub>\<Otimes>(SpLs\<^bsub>i\<^esub> Ls)\<^esub> (Ls_suc.specialize_fn i ?ai' F) h = (\<lambda>h\<in>{1..length SpLs\<^bsub>i\<^esub> Ls}. nested (SpLs\<^bsub>i\<^esub> Ls) h Bot (Ls_suc.specialize_fn i ?ai' F)) h"
          using a_i by auto

        (* we use lemma 5 here*)
        have ij_lem:"\<And>h. h\<in>{1..length Ls} \<Longrightarrow> 
                    h<i \<Longrightarrow> nested (SpLs\<^bsub>i\<^esub> Ls) h Bot (Ls_suc.specialize_fn i ?ai' F) = nested Ls h (Bot(i\<mapsto>?ai')) F"
          using Ls_suc.nested_sp_compat[where B="Bot" and j="i" and f="F" and aj="?ai'"]
                \<open>i \<in> {1..length Ls}\<close> suc.prems(1) ai'_car Bot_undefined car_prod_carrier_form
                Ls_suc.Bot_specialize_Bot
          by metis
        have ji_lem:"\<And>h. h\<in>{1..length Ls} \<Longrightarrow> 
                    h>i \<Longrightarrow> nested (SpLs\<^bsub>i\<^esub> Ls) (h-1) Bot (Ls_suc.specialize_fn i ?ai' F) = nested Ls h (Bot(i\<mapsto>?ai')) F"
          using Ls_suc.nested_sp_compat[where B="Bot" and j="i" and f="F" and aj="?ai'"]
                \<open>i \<in> {1..length Ls}\<close> suc.prems(1) ai'_car Bot_undefined car_prod_carrier_form
                Ls_suc.Bot_specialize_Bot
          by metis

        have hi_lem:"\<And>h. h\<in>{1..length Ls-1} \<Longrightarrow>
          (h<i \<Longrightarrow> nested (SpLs\<^bsub>i\<^esub> Ls) h Bot (Ls_suc.specialize_fn i ?ai' F) = nested Ls h (Bot(i\<mapsto>?ai')) F)"
          using ij_lem
          by (metis \<open>i \<in> {1..length Ls} \<Longrightarrow> length SpLs\<^bsub>i\<^esub> Ls = length Ls - 1\<close> \<open>i \<in> {1..length Ls}\<close> atLeastAtMost_iff b1 le_SucI suc.hyps(3))
        have ih_lem:"\<And>h. h\<in>{1..length Ls-1} \<Longrightarrow>
          (h\<ge>i \<Longrightarrow> nested (SpLs\<^bsub>i\<^esub> Ls) h Bot (Ls_suc.specialize_fn i ?ai' F) = nested Ls (h+1) (Bot(i\<mapsto>?ai')) F)"
          using ji_lem
          by (smt (verit) Suc_leI Suc_n_not_le_n add.commute atLeastAtMost_iff diff_add_inverse le_add1 le_trans not_less_eq plus_1_eq_Suc suc.hyps(3))

        (* we convert LFP of (Sp i,ai F) to equations of F *)
        have "(\<lambda>h\<in>{1..length SpLs\<^bsub>i\<^esub> Ls}. nested (SpLs\<^bsub>i\<^esub> Ls) h Bot (Ls_suc.specialize_fn i ?ai' F)) = (\<lambda>h\<in>{1..length Ls-1}. if h<i then nested Ls h (Bot(i\<mapsto>?ai')) F else nested Ls (h+1) (Bot(i\<mapsto>?ai')) F)"
          using length_minus_1'[of "i" "Ls"] a_i hi_lem ih_lem restrict_ext 
          by (smt (verit, ccfv_threshold) le_geq_cases)
        then have spF_LFP_coord_eq:"\<And>h. h \<in> {1..length Ls-1}
            \<Longrightarrow> LFP\<^bsub>\<Otimes>(SpLs\<^bsub>i\<^esub> Ls)\<^esub> (Ls_suc.specialize_fn i ?ai' F) h = ?new_fp_hat_i h"
          using lem_LFP_spF by auto
        have spF_LFP_eq: "LFP\<^bsub>\<Otimes>(SpLs\<^bsub>i\<^esub> Ls)\<^esub> (Ls_suc.specialize_fn i ?ai' F) = ?new_fp_hat_i"
        proof (rule Ls_i_sub.vect_eqI)
          show "LFP\<^bsub>\<Otimes>SpLs\<^bsub>i\<^esub> Ls\<^esub> (Ls_suc.specialize_fn i ?ai' F) \<in> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
            using Ls_i_sub.LFP_closed by auto
          show "?new_fp_hat_i \<in> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
            using new_fp_hat_i_car by auto
          fix h assume a_h:"h \<in> {1..length SpLs\<^bsub>i\<^esub> Ls}"
          show "LFP\<^bsub>\<Otimes>SpLs\<^bsub>i\<^esub> Ls\<^esub> (Ls_suc.specialize_fn i ?ai' F) h = ?new_fp_hat_i h"
            using spF_LFP_coord_eq length_minus_1'[of "i" "Ls"] a_i a_h by presburger
        qed
        then have spF_LFP_eq_unfold: "(Ls_suc.specialize_fn i ?ai' F) ?new_fp_hat_i = ?new_fp_hat_i"
          using Ls_i_sub.LFP_unfold[of "Ls_suc.specialize_fn i ?ai' F"] b3 by (metis b21)
        have spF_LFP_convert_F_hj: "\<And>h. h\<in>{1..length Ls-1} \<Longrightarrow> h < i \<Longrightarrow> (Ls_suc.specialize_fn i ?ai' F) ?new_fp_hat_i h = (Pr\<^bsub>h\<^esub> F) (Ls_suc.two_to_n i (?new_fp_hat_i, ?ai'))"
          using new_fp_hat_i_car carrier_spl_simp Ls_suc.specialize_fn_simps[where i="i"] by blast
        have spF_LFP_convert_F_jh:"\<And>h. h\<in>{1..length Ls-1} \<Longrightarrow> h \<ge> i \<Longrightarrow> (Ls_suc.specialize_fn i ?ai' F) ?new_fp_hat_i h = (Pr\<^bsub>h+1\<^esub> F) (Ls_suc.two_to_n i (?new_fp_hat_i, ?ai'))"
          using new_fp_hat_i_car carrier_spl_simp Ls_suc.specialize_fn_simps(2) by blast

        (* The equalities for Fi(a1'',...,aj',...,an'') = ai'' when i\<noteq>j *)
        have new_fp_hat_proj_F_eq_hj: "\<And>h. h\<in>{1..length Ls-1} \<Longrightarrow> h < i \<Longrightarrow> ?new_fp_hat_i h = (Pr\<^bsub>h\<^esub> F) (Ls_suc.two_to_n i (?new_fp_hat_i, ?ai'))"
          using spF_LFP_convert_F_hj spF_LFP_eq_unfold by auto
        have new_fp_hat_proj_F_eq_jh: "\<And>h. h\<in>{1..length Ls-1} \<Longrightarrow> h \<ge> i \<Longrightarrow> ?new_fp_hat_i h = (Pr\<^bsub>h+1\<^esub> F) (Ls_suc.two_to_n i (?new_fp_hat_i, ?ai'))"
          using spF_LFP_convert_F_jh spF_LFP_eq_unfold by auto

        (* we can now declare our new fixed point ah'' aj' (cf Arxiv) *)
        have f_wd:"F \<in> carrier \<Otimes>Ls \<rightarrow> carrier \<Otimes>Ls"
          using \<open>F \<in> carrier \<Otimes>Ls \<rightarrow>\<^sub>E carrier \<Otimes>Ls\<close> by auto
        have new_fp:"Ls_suc.two_to_n i (?new_fp_hat_i, ?ai') \<in> fps (\<Otimes>Ls) F"
        proof (* we prove our new fixed point is indeed a fixed point. *)
          (rule Ls_suc.fps_in_coord_I)
          show "F \<in> carrier \<Otimes>Ls \<rightarrow> carrier \<Otimes>Ls"
            using suc by auto
        next
          show "Ls_suc.two_to_n i (?new_fp_hat_i, ?ai') \<in> carrier (\<Otimes>Ls)"
            using Ls_suc.two_n__carrier[of "i" "?new_fp_hat_i" "?ai'"] a_i new_fp_hat_i_car ai'_car
            unfolding carrier_spl_simp by auto
        next
          fix h assume a_h:"h\<in>{1..length Ls}"
          show "F (Ls_suc.two_to_n i (?new_fp_hat_i, ?ai')) h = Ls_suc.two_to_n i (?new_fp_hat_i, ?ai') h"
          proof (cases "h=i")
            case True
            then show ?thesis
            proof -
              have "(Ls_suc.two_to_n i (?new_fp_hat_i, ?ai')) = (\<lambda>ja\<in>{1..length Ls}. if ja = i then ?ai' else if ja<i then ?new_fp_hat_i ja else ?new_fp_hat_i (ja-1))"
                (is "?l = ?r")                
              proof -
                have b1:"?new_fp_hat_i \<in> carrier_spl Ls i"
                  using new_fp_hat_i_car unfolding carrier_spl_simp by simp
                have b2:"?ai' \<in> carrier (Ls ! (i-1))"
                  using ai'_car by simp
                show ?thesis 
                  using Ls_suc.two_to_n_eq[OF b1 b2 a_i] by auto
              qed
              also have "... = (\<lambda>ja\<in>{1..length Ls}. if ja = i then ?ai' else if ja<i then nested Ls ja (Bot(i \<mapsto> ?ai')) F else nested Ls ja (Bot(i \<mapsto> ?ai')) F)"
                (is "?l = ?r")
              proof (rule restrict_eq)
                fix ja assume a_ja:"ja\<in>{1..length Ls}"
                have b1:"ja=i \<Longrightarrow> ?l ja = ?r ja"
                  by auto
                have "ja<i \<Longrightarrow> ?l ja = (\<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> ?ai')) F else nested Ls (h + 1) (Bot(i \<mapsto> ?ai')) F) ja"
                  using a_ja a_i by auto
                then have eq1:"ja<i \<Longrightarrow> ?l ja = nested Ls ja (Bot(i \<mapsto> ?ai')) F"
                  using a_ja a_i by auto
                have "ja<i \<Longrightarrow> ?r ja = nested Ls ja (Bot(i \<mapsto> ?ai')) F"
                  by auto
                then have b2:"ja<i \<Longrightarrow> ?l ja = ?r ja"
                  using eq1 by auto
                have "ja>i \<Longrightarrow> ?l ja = (\<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> nested Ls i Bot F)) F else nested Ls (h + 1) (Bot(i \<mapsto> nested Ls i Bot F)) F) (ja - 1)"
                  by auto
                then have eq2:"ja>i \<Longrightarrow> ?l ja = nested Ls ja (Bot(i \<mapsto> ?ai')) F"
                  using a_ja a_i 
                  by (metis (no_types, lifting) FuncSet.restrict_apply nested.simps
                      \<open>(\<lambda>h\<in>{1..length SpLs\<^bsub>i\<^esub> Ls}. nested SpLs\<^bsub>i\<^esub> Ls h Bot (Ls_suc.specialize_fn i (nested Ls i Bot F) F)) = (\<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> nested Ls i Bot F)) F else nested Ls (h + 1) (Bot(i \<mapsto> nested Ls i Bot F)) F)\<close>
                      ji_lem)
                have "ja>i \<Longrightarrow> ?r ja = nested Ls ja (Bot(i \<mapsto> ?ai')) F"
                  by auto
                then have b3:"ja>i \<Longrightarrow> ?l ja = ?r ja"
                  using eq2 by auto
                show "(if ja = i then nested Ls i Bot F
           else if ja < i then (\<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> nested Ls i Bot F)) F else nested Ls (h + 1) (Bot(i \<mapsto> nested Ls i Bot F)) F) ja
                else (\<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> nested Ls i Bot F)) F else nested Ls (h + 1) (Bot(i \<mapsto> nested Ls i Bot F)) F) (ja - 1)) =
          (if ja = i then nested Ls i Bot F else if ja < i then nested Ls ja (Bot(i \<mapsto> nested Ls i Bot F)) F else nested Ls ja (Bot(i \<mapsto> nested Ls i Bot F)) F)"
                  using b1 b2 b3 a_ja 
                  by (smt (verit, best) eq2 ge_le_eq_cases restrict_apply')
              qed
              also have "... = (\<lambda>ja\<in>{1..length Ls}. if ja = i then ?ai' else nested Ls ja (Bot(i \<mapsto> ?ai')) F)"
                by auto
              finally have two_to_n_nested_eq: "Ls_suc.two_to_n i (?new_fp_hat_i, ?ai') 
                                                = (\<lambda>ja\<in>{1..length Ls}. if ja = i then ?ai' else nested Ls ja (Bot(i \<mapsto> ?ai')) F)"
                by auto
              let ?v = "\<lambda>x\<in>carrier (Ls!(i-1)). \<lambda>h\<in>{1..length Ls-1}. if h<i then nested Ls h (Bot(i\<mapsto>x)) F else nested Ls (h+1) (Bot(i\<mapsto>x)) F"
              have vx_car_spl:"\<And>a. a\<in>carrier (Ls!(i-1)) \<Longrightarrow> ?v a \<in> carrier_spl Ls i"
              proof -
                fix x assume a_x:"x\<in>carrier (Ls!(i-1))"
                show vx_car_spl:"?v x \<in> carrier_spl Ls i"
                proof -
                  have eq:"?v x = (\<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> x)) F else nested Ls (h + 1) (Bot(i \<mapsto> x)) F)"
                    using a_x by auto
                  have "(\<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> x)) F else nested Ls (h + 1) (Bot(i \<mapsto> x)) F) \<in> carrier_spl Ls i"
                  proof (rule Ls_suc.in_carrier_spl_I)
                    show "i\<in>{1..length Ls}"
                      using a_i by simp
                    fix h assume \<open>h\<notin> {1..length Ls - 1}\<close>
                    then show "(\<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> x)) F else nested Ls (h + 1) (Bot(i \<mapsto> x)) F) h = undefined"
                      by auto
                  next
                    fix h assume a_h:"h\<in>{1..length Ls-1}"
                    have hj_lem:"h < i 
                      \<Longrightarrow> (\<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> x)) F else nested Ls (h + 1) (Bot(i \<mapsto> x)) F) h \<in> carrier (Ls ! (h-1))"
                    proof -
                      assume \<open>h<i\<close>
                      have \<open>h\<in>{1..length Ls}\<close>
                        using a_h by auto
                      have \<open>(Bot(i \<mapsto> x)) h = None\<close>
                        using Bot_undefined \<open>h<i\<close> by auto
                      from Ls_suc.nested_closed[OF \<open>h\<in>{1..length Ls}\<close>] \<open>(Bot(i \<mapsto> x)) h = None\<close> a_h \<open>h<i\<close>
                      show ?thesis
                        by auto
                    qed
                    have jh_lem:"h\<ge>i
                      \<Longrightarrow>(\<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> x)) F else nested Ls (h + 1) (Bot(i \<mapsto> x)) F) h \<in> carrier (Ls ! h)"
                    proof -
                      assume \<open>h\<ge>i\<close>
                      have \<open>h+1\<in>{1..length Ls}\<close>
                        using a_h by auto
                      have \<open>(Bot(i \<mapsto> x)) (h+1)= None\<close>
                        using Bot_undefined \<open>h\<ge>i\<close> by auto
                      from Ls_suc.nested_closed[OF \<open>h+1\<in>{1..length Ls}\<close>] \<open>(Bot(i \<mapsto> x)) (h+1)= None\<close> a_h \<open>h\<ge>i\<close>
                      show ?thesis
                        by auto
                    qed
                    show "(h < i \<longrightarrow> (\<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> x)) F else nested Ls (h + 1) (Bot(i \<mapsto> x)) F) h \<in> carrier (Ls ! (h-1))) \<and>
       (i \<le> h \<longrightarrow> (\<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> x)) F else nested Ls (h + 1) (Bot(i \<mapsto> x)) F) h \<in> carrier (Ls ! h)) "
                      using hj_lem jh_lem by auto
                  qed
                  then show ?thesis 
                    using eq by auto
                qed
              qed
              have v_mono:"\<And>x y. x \<in> carrier (Ls !(i-1)) \<Longrightarrow> y \<in> carrier (Ls !(i-1)) \<Longrightarrow> x \<sqsubseteq>\<^bsub>(Ls !(i-1))\<^esub> y \<Longrightarrow> ?v x \<sqsubseteq>\<^bsub>\<Otimes>SpLs\<^bsub>i\<^esub> Ls\<^esub> ?v y"
              proof -
                fix x y assume a_x:"x\<in>carrier (Ls !(i-1))" and a_y:"y\<in>carrier (Ls !(i-1))" and a_xy:"x \<sqsubseteq>\<^bsub>(Ls !(i-1))\<^esub> y"
                show "?v x \<sqsubseteq>\<^bsub>\<Otimes>SpLs\<^bsub>i\<^esub> Ls\<^esub> ?v y"
                proof (rule Ls_suc.SpLs_le_criterion)
                  show "?v x \<in> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
                    using vx_car_spl[OF a_x] unfolding carrier_spl_simp by auto
                  show "?v y \<in> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
                    using vx_car_spl[OF a_y] unfolding carrier_spl_simp by auto
                  show "i\<in>{1..length Ls}"
                    using a_i by auto
                next
                  fix h assume a_h:"h\<in>{1..length Ls-1}"
                  have hj_lem:"h<i \<Longrightarrow> ?v x h \<sqsubseteq>\<^bsub>Ls ! (h-1)\<^esub> ?v y h"
                  proof -
                    assume \<open>h<i\<close>
                    then have a_h':\<open>h\<in>{1..length Ls-1}\<close>
                      using a_h a_i by auto
                    have \<open>h\<in>{1..length Ls}\<close>
                      using a_h by auto
                    have \<open>h\<noteq>i\<close>
                      using \<open>h<i\<close> by auto
                    have b1:"?v x h = nested Ls h (Bot(i\<mapsto>x)) F"
                      using a_x a_h' \<open>h<i\<close> by auto
                    have b2:"?v y h = nested Ls h (Bot(i\<mapsto>y)) F"
                      using a_y a_h' \<open>h<i\<close> by auto
                    have b3:"nested Ls h (Bot(i\<mapsto>x)) F \<sqsubseteq>\<^bsub>Ls ! (h-1)\<^esub> nested Ls h (Bot(i\<mapsto>y)) F"
                      using Ls_suc.nested_subst_mono_Bot[OF f_wd \<open>h\<in>{1..length Ls}\<close> a_i a_x a_y a_xy \<open>h\<noteq>i\<close> \<open>Mono\<^bsub>\<Otimes>Ls\<^esub> F\<close>]
                      by auto
                    show ?thesis using b1 b2 b3 by auto
                  qed
                  have jh_lem:"h\<ge>i \<Longrightarrow> ?v x h \<sqsubseteq>\<^bsub>Ls ! h\<^esub> ?v y h"
                  proof -
                    assume \<open>h\<ge>i\<close>
                    then have a_h':\<open>h\<in>{1..length Ls-1}\<close>
                      using a_h a_i by auto
                    have \<open>h+1\<in>{1..length Ls}\<close>
                      using a_h by auto
                    have \<open>h+1\<noteq>i\<close>
                      using \<open>h\<ge>i\<close> by auto
                    have b1:"?v x h = nested Ls (h+1) (Bot(i\<mapsto>x)) F"
                      using a_x a_h' \<open>h\<ge>i\<close> by auto
                    have b2:"?v y h = nested Ls (h+1) (Bot(i\<mapsto>y)) F"
                      using a_y a_h' \<open>h\<ge>i\<close> by auto
                    have b3:"nested Ls (h+1) (Bot(i\<mapsto>x)) F \<sqsubseteq>\<^bsub>Ls ! h\<^esub> nested Ls (h+1) (Bot(i\<mapsto>y)) F"
                      using Ls_suc.nested_subst_mono_Bot[OF f_wd \<open>h+1\<in>{1..length Ls}\<close> a_i a_x a_y a_xy \<open>h+1\<noteq>i\<close> \<open>Mono\<^bsub>\<Otimes>Ls\<^esub> F\<close>]
                      by auto
                    show ?thesis using b1 b2 b3 by auto
                  qed
                  show "(h < i \<longrightarrow>
           (\<lambda>x\<in>carrier (Ls ! (i-1)). \<lambda>h\<in>{1..length Ls - 1}. if h <i then nested Ls h (Bot(i \<mapsto> x)) F else nested Ls (h + 1) (Bot(i \<mapsto> x)) F) x h \<sqsubseteq>\<^bsub>Ls ! (h-1)\<^esub>
           (\<lambda>x\<in>carrier (Ls ! (i-1)). \<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> x)) F else nested Ls (h + 1) (Bot(i \<mapsto> x)) F) y h) \<and>
          (i \<le> h \<longrightarrow>
           (\<lambda>x\<in>carrier (Ls ! (i-1)). \<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> x)) F else nested Ls (h + 1) (Bot(i \<mapsto> x)) F) x h \<sqsubseteq>\<^bsub>Ls ! h \<^esub>
           (\<lambda>x\<in>carrier (Ls ! (i-1)). \<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> x)) F else nested Ls (h + 1) (Bot(i \<mapsto> x)) F) y h)"
                    using hj_lem jh_lem by auto
                qed
              qed
              have two_to_n_nested_eq_univ:"\<And>x. x\<in>carrier (Ls ! (i-1)) \<Longrightarrow> Ls_suc.two_to_n i (?v x, x)
                                          = (\<lambda>ja\<in>{1..length Ls}. if ja = i then x else if ja<i then ?v x ja else ?v x (ja-1))"
              proof -
                fix x assume a_x:"x\<in>carrier (Ls ! (i-1))"
                show "Ls_suc.two_to_n i (?v x, x) = (\<lambda>ja\<in>{1..length Ls}. if ja = i then x else if ja<i then ?v x ja else ?v x (ja-1))"
                proof (rule Ls_suc.two_to_n_eq')
                  show "?v x \<in> carrier_spl Ls i"
                    using vx_car_spl a_x by auto
                  show "?v x \<in> carrier_spl Ls i"
                    using vx_car_spl a_x by auto
                  show "x\<in>carrier (Ls ! (i-1))"
                    using a_x by auto
                  show "i\<in>{1..length Ls}"
                    using a_i by auto
                next
                  fix h assume a_h:"h\<in>{1..length Ls-1}"
                  show "?v x h = ?v x h"
                    by auto
                qed
              qed
                  
              let ?proj_func = "\<lambda>xj\<in>carrier (Ls ! (i-1)). (Pr\<^bsub>i\<^esub> F) (\<lambda>ja\<in>{1..length Ls}. if ja = i then xj else nested Ls ja (Bot(i \<mapsto> xj)) F)"
              have proj_func_eq:"?proj_func = (\<lambda>x\<in>carrier (Ls ! (i-1)). (Pr\<^bsub>i\<^esub> F) (Ls_suc.two_to_n i (?v x ,x)))"
              proof (rule restrict_eq)
                fix a assume a1:"a\<in>carrier (Ls ! (i-1))"
                from two_to_n_nested_eq_univ[OF a1]
                have "Ls_suc.two_to_n i (?v a,a) = (\<lambda>h\<in>{1..length Ls}. if h = i then a else if h<i then ?v a h else ?v a (h-1))"
                  by auto
                also have "... = (\<lambda>h\<in>{1..length Ls}. if h = i then a else nested Ls h (Bot(i \<mapsto> a)) F)"
                  (is "?l = ?r")
                proof (rule restrict_eq)
                  fix h assume a_h:"h\<in>{1..length Ls}"
                  have b1:"h=i \<Longrightarrow> ?l h = ?r h"
                    by auto
                  have b2:"h<i \<Longrightarrow> ?l h = nested Ls h (Bot(i \<mapsto> a)) F"
                  proof -
                    assume \<open>h<i\<close>
                    have a_h':"h\<in>{1..length Ls-1}"
                      using a_h a_i \<open>h<i\<close> by auto
                    then have "?l h = (\<lambda>x\<in>carrier (Ls ! (i-1)). \<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> x)) F else nested Ls (h + 1) (Bot(i \<mapsto> x)) F) a h"
                      using a_h \<open>h<i\<close> by auto
                    also have "... = (\<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> a)) F else nested Ls (h + 1) (Bot(i \<mapsto> a)) F) h"
                      using a1 by auto
                    also have "... = nested Ls h (Bot(i \<mapsto> a)) F"
                      using a_h' \<open>h<i\<close> by auto
                    finally show ?thesis by auto
                  qed
                  have b3:"h>i \<Longrightarrow> ?l h = nested Ls h (Bot(i \<mapsto> a)) F"
                  proof -
                    assume \<open>h>i\<close>
                    have a_h':"h-1\<in>{1..length Ls-1}"
                      using a_h a_i \<open>h>i\<close> by auto
                    then have "?l h = (\<lambda>x\<in>carrier (Ls ! (i-1)). \<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> x)) F else nested Ls (h + 1) (Bot(i \<mapsto> x)) F) a (h-1)"
                      using a_h \<open>h>i\<close> by auto
                    also have "... = (\<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> a)) F else nested Ls (h + 1) (Bot(i \<mapsto> a)) F) (h-1)"
                      using a1 by auto
                    also have "... = nested Ls h (Bot(i \<mapsto> a)) F"
                      using a_h' \<open>h>i\<close> by auto
                    finally show ?thesis by auto
                  qed
                  have b4:"h\<noteq>i \<Longrightarrow> ?r h = nested Ls h (Bot(i \<mapsto> a)) F"
                    using a_h by auto
                  then show "(if h = i then a
      else if h < i then (\<lambda>x\<in>carrier (Ls ! (i-1)). \<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> x)) F else nested Ls (h + 1) (Bot(i \<mapsto> x)) F) a h
           else (\<lambda>x\<in>carrier (Ls ! (i-1)). \<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> x)) F else nested Ls (h + 1) (Bot(i \<mapsto> x)) F) a (h - 1)) =
     (if h = i then a else nested Ls h (Bot(i \<mapsto> a)) F)"
                    using a_h b2 b3 by fastforce
                qed
                finally show "Pr\<^bsub>i\<^esub> F (\<lambda>ja\<in>{1..length Ls}. if ja = i then a else nested Ls ja (Bot(i \<mapsto> a)) F) = Pr\<^bsub>i\<^esub> F (Ls_suc.two_to_n i
                  ((\<lambda>x\<in>carrier (Ls ! (i-1)). \<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> x)) F else nested Ls (h + 1) (Bot(i \<mapsto> x)) F) a, a))"
                  by auto
              qed
              have proj_func_eq_app:"\<And>x. x\<in>carrier (Ls ! (i-1)) \<Longrightarrow>
                (Pr\<^bsub>i\<^esub> F) (Ls_suc.two_to_n i (?v x ,x)) = (Pr\<^bsub>i\<^esub> F) (\<lambda>ja\<in>{1..length Ls}. if ja =i then x else nested Ls ja (Bot(i \<mapsto> x)) F)"
              proof -
                fix x assume a_x:"x\<in>carrier (Ls ! (i-1))"
                show "(Pr\<^bsub>i\<^esub> F) (Ls_suc.two_to_n i (?v x ,x)) = (Pr\<^bsub>i\<^esub> F) (\<lambda>ja\<in>{1..length Ls}. if ja = i then x else nested Ls ja (Bot(i \<mapsto> x)) F)"
                (is "?l = ?r")
                proof -
                  have eq_l:"?l = (\<lambda>x\<in>carrier (Ls ! (i-1)). (Pr\<^bsub>i\<^esub> F) (Ls_suc.two_to_n i (?v x ,x))) x"
                    using a_x by auto
                  have eq_r:"?r = (\<lambda>x\<in>carrier (Ls ! (i-1)). (Pr\<^bsub>i\<^esub> F) (\<lambda>ja\<in>{1..length Ls}. if ja = i then x else nested Ls ja (Bot(i \<mapsto> x)) F)) x"
                    using a_x by auto
                  show ?thesis
                    using eq_l eq_r proj_func_eq by argo
                qed
              qed

              (* The equality aj' = F_j(a1'', ..., aj', ..., an''), where ai'' = nested(n,i,[j:=aj'],F) for i\<noteq>j. *)
              then have i_coord_eq:"?ai' = (Pr\<^bsub>i\<^esub> F) (\<lambda>ja\<in>{1..length Ls}. if ja = i then ?ai' else nested Ls ja (Bot(i \<mapsto> ?ai')) F)"
              proof -
                have b1:"Mono\<^bsub>(Ls ! (i-1))\<^esub> ?proj_func"
                proof -
                  have v_car: "?v \<in> carrier (Ls ! (i-1)) \<rightarrow> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
                  proof
                    fix x assume a_x:"x\<in>carrier (Ls ! (i-1))"
                    show "(\<lambda>h\<in>{1..length Ls - 1}. if h < i then nested Ls h (Bot(i \<mapsto> x)) F else nested Ls (h + 1) (Bot(i \<mapsto> x)) F) \<in> carrier \<Otimes>SpLs\<^bsub>i\<^esub> Ls"
                      using vx_car_spl[OF a_x] a_x unfolding carrier_spl_simp by auto
                  qed
                  show ?thesis
                    using Ls_suc.mono_proj_lam_mono_app[OF f_wd a_i \<open>Mono\<^bsub>\<Otimes>Ls\<^esub> F\<close> v_car v_mono] proj_func_eq by auto
                qed
                have b2:"?proj_func \<in> carrier (Ls ! (i-1)) \<rightarrow> carrier (Ls ! (i-1))"
                proof
                  fix x assume a_x:\<open>x\<in>carrier (Ls ! (i-1))\<close>
                  have a_vx:"?v x \<in> carrier_spl Ls i"
                    using vx_car_spl a_x by auto
                  have vx_x_car: \<open>Ls_suc.two_to_n i (?v x ,x) \<in> carrier (\<Otimes>Ls)\<close>
                    using Ls_suc.two_n__carrier[OF a_i a_vx a_x] by auto
                  have Fv_car: "F (Ls_suc.two_to_n i (?v x ,x)) \<in> carrier (\<Otimes>Ls)"
                    using f_wd vx_x_car by auto
                  have proj_func_app_car:"(Pr\<^bsub>i\<^esub> F) (Ls_suc.two_to_n i (?v x ,x)) \<in> carrier (Ls ! (i-1))"
                    using cart_carrier_iff[of "F (Ls_suc.two_to_n i (?v x ,x))" "Ls"] Fv_car a_i unfolding proj_def by auto
                  show "(Pr\<^bsub>i\<^esub> F) (\<lambda>ja\<in>{1..length Ls}. if ja = i then x else nested Ls ja (Bot(i \<mapsto> x)) F) \<in> carrier (Ls ! (i-1))"
                    using proj_func_app_car proj_func_eq_app[OF a_x] by auto
                qed
                from Ls_i_coord.LFP_unfold[OF b1 b2] ai'_eq3
                have "?ai' = (\<lambda>xj\<in>carrier (Ls ! (i-1)). Pr\<^bsub>i\<^esub> F (\<lambda>ja\<in>{1..length Ls}. if ja = i then xj else nested Ls ja (Bot(i \<mapsto> xj)) F)) ?ai'"
                  by auto
                then show ?thesis
                  using ai'_car 
                  by (metis (no_types, lifting) ext restrict_apply')
              qed
              then have b1:"F (Ls_suc.two_to_n i (?new_fp_hat_i, ?ai')) h = ?ai'"
                using proj_func_eq_app[OF ai'_car] ai'_car True two_to_n_nested_eq unfolding proj_def by argo
              have b2: "Ls_suc.two_to_n i (?new_fp_hat_i, ?ai') h = ?ai'"
                using \<open>h=i\<close> Ls_suc.two_to_n_simps(1) new_fp_hat_i_car a_i \<open>h\<in>{1..length Ls}\<close> ai'_car unfolding carrier_spl_simp
                by auto
              show ?thesis
                using b1 b2 by auto
            qed
          next
            case False
            then show ?thesis
            proof (cases "h<i")
              case True
              then show ?thesis
              proof -
                have \<open>h\<in>{1..length Ls-1}\<close>
                  using a_h a_i \<open>h<i\<close> by auto
                from new_fp_hat_proj_F_eq_hj[OF \<open>h\<in>{1..length Ls-1}\<close> \<open>h<i\<close>]
                show ?thesis 
                  unfolding proj_def using Ls_suc.two_to_n_simps(2)[OF new_fp_hat_i_car' ai'_car a_i a_h \<open>h<i\<close>] by auto
              qed
            next
              case False
              then show ?thesis
              proof -
                have \<open>h>i\<close>
                  using \<open>h\<noteq>i\<close> \<open>\<not>h<i\<close> by auto
                then have \<open>h-1\<ge>i\<close>
                  by auto
                have \<open>h-1\<in>{1..length Ls-1}\<close>
                  using a_h a_i \<open>h>i\<close> by auto
                from new_fp_hat_proj_F_eq_jh[OF \<open>h-1\<in>{1..length Ls-1}\<close> \<open>h-1\<ge>i\<close>]
                show ?thesis
                  unfolding proj_def using Ls_suc.two_to_n_simps(3)[OF new_fp_hat_i_car' ai'_car a_i a_h \<open>h>i\<close>] a_h by auto
              qed
            qed
          qed
        qed
        have LFP_F_le:"LFP\<^bsub>\<Otimes>Ls\<^esub> F \<sqsubseteq>\<^bsub>\<Otimes>Ls\<^esub> Ls_suc.two_to_n i (?new_fp_hat_i, ?ai')"
          using Ls_suc.LFP_least_fixed_point[OF \<open>Mono\<^bsub>\<Otimes>Ls\<^esub> F\<close> f_wd new_fp] by simp
        then have "LFP\<^bsub>\<Otimes>Ls\<^esub> F i \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> Ls_suc.two_to_n i (?new_fp_hat_i, ?ai') i"
          using Ls_suc.Ls_le_criterion LFP_F_le a_i by auto
        then have lemma_ai_le_ai':"?ai \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> ?ai'"
          using Ls_suc.two_to_n_simps(1)[OF new_fp_hat_i_car' ai'_car a_i a_i] by auto
        have lemma_ai_ge_ai':"?ai' \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> ?ai"
        proof -
          let ?f= "(\<lambda>x\<in>carrier (Ls ! (i-1)). Pr\<^bsub>i\<^esub> F (\<lambda>ja\<in>{1..length Ls}. if ja = i then x else nested Ls ja (Bot(i \<mapsto> x)) F))"
          have LFP_is_fp:"LFP\<^bsub>\<Otimes>Ls\<^esub> F \<in> fps (\<Otimes>Ls) F"
            using Ls_suc.LFP_fixed_point[OF \<open>Mono\<^bsub>\<Otimes>Ls\<^esub> F\<close> f_wd] by simp
          from general_Bekic_claim[OF \<open>F \<in> carrier \<Otimes>Ls \<rightarrow>\<^sub>E carrier \<Otimes>Ls\<close> \<open>cart_prod_lattice Ls\<close> \<open>Mono\<^bsub>\<Otimes>Ls\<^esub> F\<close> LFP_is_fp a_i]
          have b1:"Pr\<^bsub>i\<^esub> F (\<lambda>j\<in>{1..length Ls}. if j = i then ?ai else nested Ls j (Bot(i \<mapsto> ?ai)) F) \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> ?ai"
            by simp
          then have b2:"?f ?ai \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> ?ai"
            using ai_car by auto
          have b3:"LFP\<^bsub>(Ls ! (i-1))\<^esub> (\<lambda>x\<in>carrier (Ls ! (i-1)). Pr\<^bsub>i\<^esub> F (\<lambda>ja\<in>{1..length Ls}. if ja = i then x else nested Ls ja (Bot(i \<mapsto> x)) F)) \<sqsubseteq>\<^bsub>(Ls ! (i-1))\<^esub> ?ai"
            using Ls_i_coord.LFP_lowerbound[OF ai_car] b2 by auto
          then show ?thesis
            using ai'_eq3 by auto
        qed
        show "LFP\<^bsub>\<Otimes>Ls\<^esub> F i = (\<lambda>i\<in>{1..length Ls}. nested Ls i Bot F) i"
          using lemma_ai_ge_ai' lemma_ai_le_ai' a_i 
          by (metis FuncSet.restrict_apply Ls_i_coord.le_antisym ai'_car ai_car)
      qed
    qed
  qed
qed

(* The GFP version of general Bekic is obtained from the LFP version by dualizing the order. 
   Correspondingly in the nested expression on RHS, replaced all \<mu> by \<nu>.
*)
theorem general_Bekic_gfp:
  fixes F::"(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)"
  assumes a_car:"F \<in> carrier (\<Otimes>Ls) \<rightarrow>\<^sub>E carrier (\<Otimes>Ls)"
      and a_mono:"Mono\<^bsub>\<Otimes>Ls\<^esub> F"
      and cart_prod_lattice: "cart_prod_lattice Ls"
    shows "GFP\<^bsub>\<Otimes>Ls\<^esub> F = (\<lambda>i\<in>{1..length Ls}. nested_gfp Ls i Bot F)"
proof -
  have "GFP\<^bsub>\<Otimes>Ls\<^esub> F = LFP\<^bsub>inv_gorder \<Otimes>Ls\<^esub> F"
    using LFP_dual[of "\<Otimes>Ls" "F"] by auto
  also have "... = LFP\<^bsub>\<Otimes>(invert_Ls Ls)\<^esub> F"
    using inv_cart_prod_is_cart_prod_inv[of "Ls"] by auto
  also have "... = (\<lambda>i\<in>{1..length Ls}. nested (invert_Ls Ls) i Bot F)"
  proof -
    from invert_preserve_funcset[of "F" "Ls"] assms
    have b1_1:"F \<in> carrier \<Otimes>invert_Ls Ls \<rightarrow>\<^sub>E carrier \<Otimes>invert_Ls Ls" by auto
    from invert_preserve_mono[OF cart_prod_lattice] assms
    have b1_2:"Mono\<^bsub>\<Otimes>(invert_Ls Ls)\<^esub> F" by auto
    from invert_cart_prod_lattice[OF cart_prod_lattice]
    have b1_3:"cart_prod_lattice (invert_Ls Ls)" by auto
    from general_Bekic[OF b1_1 b1_2 b1_3]
    show ?thesis by auto
  qed 
  also have "... = (\<lambda>i\<in>{1..length Ls}. nested_gfp Ls i Bot F)"
    using nested_invert_is_nested_gfp cart_prod_lattice unfolding Bot_def
    by (metis (no_types, lifting) restrict_ext)
  finally show ?thesis
    by simp
qed

end