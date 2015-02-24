(*<*)
theory Stern_Brocot_Basis
imports
  Main
  "~~/src/HOL/Rat"
  "~~/src/HOL/Library/Sublist"
begin

(*>*)
section{* Auxiliary definitions and lemmas *}

text{*

Later we will need to reason about how two paths (lists of directions)
can be distinct. The following lemma asserts that either one is a
proper prefix of the other, or they share a common prefix and then
diverge.

*}

lemma lists_not_eq:
  assumes "xs \<noteq> ys"
  obtains
    (c1) "prefix xs ys"
  | (c2) "prefix ys xs"
  | (c3) ps x y xs' ys'
          where "xs = ps @ x # xs'" and "ys = ps @ y # ys'" and "x \<noteq> y"
using assms
by (cases xs ys rule: prefixeq_cases)
   (blast dest: parallel_decomp prefix_order.neq_le_trans)+

text{*

The @{const "Fract"} constructor is injective under certain
conditions:

*}

lemma rat_inv_eq:
  assumes "Fract a b = Fract c d"
  assumes "b > 0"
  assumes "d > 0"
  assumes "coprime a b"
  assumes "coprime c d"
  shows "a = c \<and> b = d"
proof -
  from `b > 0` `d > 0` `Fract a b = Fract c d`
  have "a * d = c * b" by (simp add: eq_rat)
  moreover
  from arg_cong[where f=sgn, OF this] `b > 0` `d > 0`
  have "sgn a = sgn c" by (simp add: sgn_times)
  moreover note `b > 0` `d > 0`
  ultimately show ?thesis
    using coprime_crossproduct_int[OF `coprime a b` `coprime c d`]
    by (simp add: abs_sgn)
qed
(*<*)

end
(*>*)
