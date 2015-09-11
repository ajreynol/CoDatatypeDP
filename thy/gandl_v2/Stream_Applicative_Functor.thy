theory Stream_Applicative_Functor imports
  "~~/src/HOL/Library/Stream"
  Applicative_Functor
begin

section {* Streams *}

text {* We re-use the stream library (typ @{typ "'a stream"}) from the distribution *}

lemma siterate_unique:
  assumes "xs = x ## smap f xs"
  shows "xs = siterate f x"
using assms
proof(coinduction arbitrary: xs x)
  case (Eq_stream xs x)
  have "smap f xs = f x ## smap f (smap f xs)"
    by(subst Eq_stream) simp
  then show ?case
    by(subst (1 2) Eq_stream) auto
qed

subsection{* Applicative Functor machinery *}

definition pure_stream :: "'a \<Rightarrow> 'a stream"
where "pure_stream = sconst"

adhoc_overloading pure pure_stream

lemma pure_stream_sel [simp]:
  shows shd_pure_stream: "shd (pure x) = x"
  and stl_pure_stream: "stl (pure x) = pure x"
by(simp_all add: pure_stream_def)

primcorec ap_stream :: "('a \<Rightarrow> 'b) stream \<Rightarrow> 'a stream \<Rightarrow> 'b stream"
where
  "shd (ap_stream f x) = shd f (shd x)"
| "stl (ap_stream f x) = ap_stream (stl f) (stl x)"

adhoc_overloading Applicative_Functor.ap ap_stream

lemma ap_stream_identity:
  "pure id \<diamond> t = t"
by(coinduction arbitrary: t) simp_all

lemma ap_stream_identity':
  "pure (%x. x) \<diamond> t = t"
by(coinduction arbitrary: t) simp_all

lemma ap_stream_composition:
  "pure (op \<circ>) \<diamond> r1 \<diamond> r2 \<diamond> r3 = r1 \<diamond> (r2 \<diamond> r3)"
by(coinduction arbitrary: r1 r2 r3) auto

lemma ap_stream_homomorphism:
  "pure f \<diamond> pure x = pure (f x)"
by(coinduction) simp_all

lemma ap_stream_interchange:
  "t \<diamond> pure x = pure (\<lambda>f. f x) \<diamond> t"
by(coinduction arbitrary: t) auto

(* FIXME: Replace with NO_MATCH in repository version *)
simproc_setup ap_tree_interchange ("x \<diamond> pure y") = {*
  fn phi => fn ctxt => fn redex => case Thm.term_of redex of
      Const (@{const_name ap_stream}, _) $ Const (@{const_name pure}, _) $ _ => NONE
    | _ => SOME @{thm ap_stream_interchange[folded atomize_eq]}
*}

lemma ap_stream_strong_extensional:
  "(\<And>x. f \<diamond> pure x = g \<diamond> pure x) \<Longrightarrow> f = g"
proof(coinduction arbitrary: f g)
  case [rule_format]: (Eq_stream f g)
  have "shd f = shd g"
  proof
    fix x
    show "shd f x = shd g x"
      using Eq_stream[of x] by(subst (asm) (1 2) ap_stream.ctr) simp
  qed
  moreover {
    fix x
    have "stl f \<diamond> pure x = stl g \<diamond> pure x"
      using Eq_stream[of x] by(subst (asm) (1 2) ap_stream.ctr) simp
  } ultimately show ?case by simp
qed

lemma ap_stream_extensional:
  "(\<And>x. f \<diamond> x = g \<diamond> x) \<Longrightarrow> f = g"
by(rule ap_stream_strong_extensional) simp

subsubsection {* Combinatory model *}

definition K_stream :: "('a \<Rightarrow> 'b \<Rightarrow> 'a) stream"
where "K_stream = pure (\<lambda>x _. x)"

adhoc_overloading Applicative_Functor.K K_stream

definition S_stream :: "(('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c) stream"
where "S_stream = pure (\<lambda>f g x. f x (g x))"

adhoc_overloading Applicative_Functor.S S_stream

definition I_stream :: "('a \<Rightarrow> 'a) stream"
where "I_stream = pure id"

adhoc_overloading Applicative_Functor.I I_stream

lemma I_stream_conv_SKK: "\<^bold>I = \<^bold>S \<diamond> \<^bold>K \<diamond> \<^bold>K"
by(simp only: S_stream_def K_stream_def I_stream_def id_def ap_stream_homomorphism)

lemma ap_stream_K_stream: "\<^bold>K \<diamond> u \<diamond> v = u"
by(coinduction arbitrary: u v)(auto simp add: K_stream_def)

lemma ap_stream_S_stream: "\<^bold>S \<diamond> u \<diamond> v \<diamond> w = (u \<diamond> w) \<diamond> (v \<diamond> w)"
by(coinduction arbitrary: u v w)(auto simp add: S_stream_def)

lemma ap_stream_I_stream: "\<^bold>I \<diamond> x = x"
by(subst I_stream_conv_SKK)(simp add: ap_stream_S_stream ap_stream_K_stream)

lemma pure_const: "pure (\<lambda>_. c) = \<^bold>K \<diamond> pure c"
by(simp only: K_stream_def ap_stream_homomorphism)

lemma pure_id: "pure (\<lambda>x. x) = \<^bold>I"
by(simp add: I_stream_def id_def)

lemma pure_ap_streamp: "pure (\<lambda>x. (f x) (g x)) = \<^bold>S \<diamond> pure f \<diamond> pure g"
by(simp only: S_stream_def ap_stream_homomorphism)

lemma pure_K_stream_apply [simp]:
  "pure (\<lambda>_. c) \<diamond> x = pure c"
by(simp only: ap_stream_K_stream pure_const)

lemma same_K_apply [simp]:
  "pure (\<lambda>_. c) \<diamond> x = pure c"
by(coinduction arbitrary: x) auto

lemma ap_stream_same2: 
  fixes f :: "('b \<Rightarrow> 'b \<Rightarrow> 'a) stream"
  shows "f \<diamond> x \<diamond> x = pure (\<lambda>f x. f x x) \<diamond> f \<diamond> x"
using ap_stream_S_stream[of "f" "pure (id :: 'b \<Rightarrow> 'b)" x, symmetric]
by(simp add: ap_stream_identity S_stream_def ap_stream_homomorphism o_def ap_stream_composition[symmetric])

lemma ap_stream_pure_same [simp]: "pure f \<diamond> a \<diamond> a = pure (\<lambda>x. f x x) \<diamond> a"
by(coinduction arbitrary: a) auto

lemma pure_stream_K2_apply:
  "pure (\<lambda>x _. f x) \<diamond> x \<diamond> y = pure f \<diamond> x"
by(coinduction arbitrary: x y)(auto)

definition C_stream :: "(('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c) stream"
where "C_stream = pure (\<lambda>f x y. f y x)"

adhoc_overloading Applicative_Functor.C C_stream

lemma ap_stream_C_stream: "\<^bold>C \<diamond> u \<diamond> v \<diamond> w = u \<diamond> w \<diamond> v"
by(coinduction arbitrary: u v w)(auto simp add: C_stream_def)

lemma stream_eq_conv_pure:
  notes [simp] = ap_stream_composition[symmetric] o_def ap_stream_homomorphism
  shows "pure op = \<diamond> t \<diamond> t' = pure True \<longleftrightarrow> t = t'" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  have "pure op = \<diamond> t \<diamond> (\<^bold>I \<diamond> t) = \<^bold>K \<diamond> pure True \<diamond> t"
    by(subst ap_stream_S_stream[symmetric])(simp add: S_stream_def I_stream_def K_stream_def)
  thus ?lhs using \<open>?rhs\<close> unfolding ap_stream_K_stream by(simp add: I_stream_def)
next
  assume ?lhs

  have "t = \<^bold>K \<diamond> t \<diamond> t'" by(simp add: ap_stream_K_stream)
  also have "\<dots> = pure (\<lambda>x y. if x = y then y else x) \<diamond> t \<diamond> t'" by(simp add: K_stream_def)
  also have "\<dots> = \<^bold>S \<diamond> (pure (\<lambda>x y1 y2. if x = y1 then y2 else x) \<diamond> t) \<diamond> \<^bold>I \<diamond> t'"
    unfolding S_stream_def I_stream_def by(simp cong: if_cong del: if_eq_cancel)
  also have "\<dots> = (pure (\<lambda>x y1 y2. if x = y1 then y2 else x) \<diamond> t) \<diamond> t' \<diamond> t'"
    unfolding ap_stream_S_stream by(simp add: ap_stream_identity ap_stream_I_stream)
  also have "\<dots> = (S_stream \<diamond> (pure (\<lambda>x1 x2 y1 y2. if x1 = y1 then y2 else x2)) \<diamond> \<^bold>I \<diamond> t) \<diamond> t' \<diamond> t'"
    unfolding S_stream_def I_stream_def by(simp cong: if_cong)
  also have "\<dots> = pure (\<lambda>x1 x2 y1 y2. if x1 = y1 then y2 else x2) \<diamond> t \<diamond> t \<diamond> t' \<diamond> t'"
    unfolding ap_stream_S_stream by(simp add: ap_stream_identity ap_stream_I_stream)
  also have "\<dots> = \<^bold>C \<diamond> (pure (\<lambda>x1 x2 y1 y2. if x1 = y1 then y2 else x2) \<diamond> t) \<diamond> t' \<diamond> t \<diamond> t'"
    unfolding ap_stream_C_stream ..
  also have "\<dots> = pure (\<lambda>b x2 y2. if b then y2 else x2) \<diamond> (pure op = \<diamond> t \<diamond> t') \<diamond> t \<diamond> t'"
    by(simp add: C_stream_def)
  also have "\<dots> = pure (\<lambda>b x2 y2. if b then y2 else x2) \<diamond> pure True \<diamond> t \<diamond> t'"
    unfolding \<open>?lhs\<close> ..
  also have "\<dots> = \<^bold>C \<diamond> \<^bold>K \<diamond> t \<diamond> t'" by(simp add: C_stream_def K_stream_def)
  also have "\<dots> = t'" by(simp add: ap_stream_C_stream ap_stream_K_stream)
  finally show ?rhs .
qed


lemma ap_stream_pure_SCons: "pure f \<diamond> (x ## xs) = f x ## (pure f \<diamond> xs)"
by(rule stream.expand) simp

end
