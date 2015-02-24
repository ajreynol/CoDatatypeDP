header{* The Stern-Brocot Tree as a codatatype *}

theory SternBrocotBNF
imports
  Stern_Brocot_Basis
  "~~/src/HOL/Library/Stream"
begin

subsection {* A codatatype of infinite binary trees *}

codatatype 'a tree = Node (root: 'a) (left: "'a tree") (right: "'a tree")

lemma map_tree_sels [simp]:
  "root (map_tree f t) = f (root t)"
  "left (map_tree f t) = map_tree f (left t)"
  "right (map_tree f t) = map_tree f (right t)"
by (case_tac [!] t) simp_all

primcorec unfold_tree :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b tree" where
  "unfold_tree g1 g22 g32 a =
   Node (g1 a) (unfold_tree g1 g22 g32 (g22 a)) (unfold_tree g1 g22 g32 (g32 a))"

lemma map_tree_unfold_tree:
  "map_tree f (unfold_tree out l r x) = unfold_tree (f \<circ> out) l r x"
by(coinduction arbitrary: x) auto

lemma rel_treeD:
  assumes "rel_tree A x y"
  shows rel_tree_rootD: "A (root x) (root y)"
  and rel_tree_leftD: "rel_tree A (left x) (left y)"
  and rel_tree_rightD: "rel_tree A (right x) (right y)"
using assms
by(cases x y rule: tree.exhaust[case_product tree.exhaust], simp_all)+
 
lemma set_tree_induct[consumes 1, case_names root left right]:
  assumes x: "x \<in> set_tree t"
  and root: "\<And>t. P (root t) t"
  and left: "\<And>x t. \<lbrakk> x \<in> set_tree (left t); P x (left t) \<rbrakk> \<Longrightarrow> P x t"
  and right: "\<And>x t. \<lbrakk> x \<in> set_tree (right t); P x (right t) \<rbrakk> \<Longrightarrow> P x t"
  shows "P x t" 
apply (rule tree.set_induct[of x t P])
   apply (rule x)
  apply (metis root tree.sel(1))
 apply (simp add: left)
apply (simp add: right)
done

subsubsection {* Applicative Functor machinery for trees *}

primcorec tree_pure :: "'a \<Rightarrow> 'a tree"
where "tree_pure x = Node x (tree_pure x) (tree_pure x)"

lemmas tree_pure_unfold = tree_pure.ctr
   and tree_pure_simps = tree_pure.simps

lemma map_tree_pure [simp]: "map_tree f (tree_pure x) = tree_pure (f x)"
by(coinduction arbitrary: x) auto

primcorec tree_ap :: "('a \<Rightarrow> 'b) tree \<Rightarrow> 'a tree \<Rightarrow> 'b tree" (infixl "\<diamond>" 70)
where
  "root (f \<diamond> x) = root f (root x)"
| "left (f \<diamond> x) = left f \<diamond> left x"
| "right (f \<diamond> x) = right f \<diamond> right x"

lemma map_tree_tree_ap_tree_pure:
  "tree_pure f \<diamond> u = map_tree f u"
by(coinduction arbitrary: u) auto

lemma root_in_set_tree: "root y \<in> set_tree y"
by(cases y) simp

lemma in_set_tree_left: "x \<in> set_tree (left y) \<Longrightarrow> x \<in> set_tree y"
by(cases y) simp

lemma right_in_set_tree: "x \<in> set_tree (right y) \<Longrightarrow> x \<in> set_tree y"
by(cases y) simp

lemma tree_ap_pure_Node [simp]:
  "tree_pure f \<diamond> Node x l r = Node (f x) (tree_pure f \<diamond> l) (tree_pure f \<diamond> r)"
by(rule tree.expand) auto

lemma tree_ap_Node_Node [simp]:
  "Node f fl fr \<diamond> Node x l r = Node (f x) (fl \<diamond> l) (fr \<diamond> r)"
by(rule tree.expand) auto

text {* Applicative functor laws *}

lemma tree_ap_identity: "tree_pure id \<diamond> t = t"
by(simp add: map_tree_tree_ap_tree_pure tree.map_id)

lemma tree_ap_composition:
  "tree_pure (op \<circ>) \<diamond> r1 \<diamond> r2 \<diamond> r3 = r1 \<diamond> (r2 \<diamond> r3)"
by(coinduction arbitrary: r1 r2 r3) auto

lemma tree_ap_homomorphism:
  "tree_pure f \<diamond> tree_pure x = tree_pure (f x)"
by(simp add: map_tree_tree_ap_tree_pure)

lemma tree_ap_interchange:
  "t \<diamond> tree_pure x = tree_pure (\<lambda>f. f x) \<diamond> t"
by(coinduction arbitrary: t) auto

simproc_setup tree_ap_interchange ("x \<diamond> tree_pure y") = {*
  fn phi => fn ctxt => fn redex => case term_of redex of
      Const (@{const_name tree_ap}, _) $ Const (@{const_name tree_pure}, _) $ _ => NONE
    | _ => SOME @{thm tree_ap_interchange[folded atomize_eq]}
*}

lemma tree_ap_strong_extensional:
  "(\<And>x. f \<diamond> tree_pure x = g \<diamond> tree_pure x) \<Longrightarrow> f = g"
proof(coinduction arbitrary: f g)
  case (Eq_tree f g)[rule_format]
  have "root f = root g"
  proof
    fix x
    show "root f x = root g x"
      using Eq_tree[of x] by(subst (asm) (1 2) tree_ap.ctr) simp
  qed
  moreover {
    fix x
    have "left f \<diamond> tree_pure x = left g \<diamond> tree_pure x"
      using Eq_tree[of x] by(subst (asm) (1 2) tree_ap.ctr) simp
  } moreover {
    fix x
    have "right f \<diamond> tree_pure x = right g \<diamond> tree_pure x"
      using Eq_tree[of x] by(subst (asm) (1 2) tree_ap.ctr) simp
  } ultimately show ?case by simp
qed

lemma tree_ap_extensional:
  "(\<And>x. f \<diamond> x = g \<diamond> x) \<Longrightarrow> f = g"
by(rule tree_ap_strong_extensional) simp

text {* Combinatory model *}

definition tree_K :: "('a \<Rightarrow> 'b \<Rightarrow> 'a) tree"
where "tree_K = tree_pure (\<lambda>x _. x)"

definition tree_S :: "(('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c) tree"
where "tree_S = tree_pure (\<lambda>f g x. f x (g x))"

definition tree_I :: "('a \<Rightarrow> 'a) tree"
where "tree_I = tree_pure id"

lemma tree_I_conv_SKK: "tree_I = tree_S \<diamond> tree_K \<diamond> tree_K"
by(simp only: tree_S_def tree_K_def tree_I_def id_def tree_ap_homomorphism)

lemma tree_ap_tree_K: "tree_K \<diamond> u \<diamond> v = u"
by(coinduction arbitrary: u v)(auto simp add: tree_K_def)

lemma tree_ap_tree_S: "tree_S \<diamond> u \<diamond> v \<diamond> w = (u \<diamond> w) \<diamond> (v \<diamond> w)"
by(coinduction arbitrary: u v w)(auto simp add: tree_S_def)

lemma tree_pure_const: "tree_pure (\<lambda>_. c) = tree_K \<diamond> tree_pure c"
by(simp only: tree_K_def tree_ap_homomorphism)

lemma tree_pure_id: "tree_pure (\<lambda>x. x) = tree_I"
by(simp add: tree_I_def id_def)

lemma tree_pure_app: "tree_pure (\<lambda>x. (f x) (g x)) = tree_S \<diamond> tree_pure f \<diamond> tree_pure g"
by(simp only: tree_S_def tree_ap_homomorphism)

definition tree_C :: "(('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c) tree"
where "tree_C = tree_pure (\<lambda>f x y. f y x)"

lemma tree_ap_tree_C: "tree_C \<diamond> u \<diamond> v \<diamond> w = u \<diamond> w \<diamond> v"
by(coinduction arbitrary: u v w)(auto simp add: tree_C_def)


subsection {* Arithmetic using type classes *}

text{*
FIXME Unlike HOLCF we can instantiate Isabelle/HOL's
algebraic/arithmetic hierarchy.
*}

instantiation tree :: (zero) zero begin
definition "0 = tree_pure 0"
instance ..
end

instantiation tree :: (one) one begin
definition "1 = tree_pure 1"
instance ..
end

instantiation tree :: (plus) plus begin
definition "plus x y = tree_pure op + \<diamond> x \<diamond> y"
instance ..
end

instantiation tree :: (minus) minus begin
definition "minus x y = tree_pure op - \<diamond> x \<diamond> y"
instance ..
end

instantiation tree :: (uminus) uminus begin
definition "uminus = op \<diamond> (tree_pure uminus)"
instance ..
end

instantiation tree :: (times) times begin
definition "times x y = tree_pure op * \<diamond> x \<diamond> y"
instance ..
end

instance tree :: (Rings.dvd) Rings.dvd ..

instantiation tree :: ("Divides.div") "Divides.div" begin
definition "x div y = tree_pure op div \<diamond> x \<diamond> y"
definition "x mod y = tree_pure op mod \<diamond> x \<diamond> y"
instance ..
end

lemmas arith_tree_defs =
  zero_tree_def
  one_tree_def
  plus_tree_def
  minus_tree_def
  uminus_tree_def
  times_tree_def
  div_tree_def
  mod_tree_def

(* FIXME discard
lemma zero_tree_simps [simp]:
  "root 0 = 0"
  "left 0 = 0"
  "right 0 = 0"
by simp_all
*)

(* FIXME discard
lemma one_tree_simps [simp]:
  "root 1 = 1"
  "left 1 = 1"
  "right 1 = 1"
by simp_all
*)

lemma plus_tree_simps [simp]:
  "root (t + t') = root t + root t'"
  "left (t + t') = left t + left t'"
  "right (t + t') = right t + right t'"
by(simp_all add: arith_tree_defs)

lemma minus_tree_simps [simp]:
  "root (t - t') = root t - root t'"
  "left (t - t') = left t - left t'"
  "right (t - t') = right t - right t'"
by(simp_all add: arith_tree_defs)

(* FIXME discard
lemma uminus_tree_simps [simp]:
  "root (- t) = - root t"
  "left (- t) = - left t"
  "right (- t) = - right t"
by simp_all
*)

lemma times_tree_simps [simp]:
  "root (t * t') = root t * root t'"
  "left (t * t') = left t * left t'"
  "right (t * t') = right t * right t'"
by(simp_all add: arith_tree_defs)

(* FIXME discard
lemma div_tree_simps [simp]:
  "root (t div t') = root t div root t'"
  "left (t div t') = left t div left t'"
  "right (t div t') = right t div right t'"
by simp_all
*)

lemma mod_tree_simps [simp]:
  "root (t mod t') = root t mod root t'"
  "left (t mod t') = left t mod left t'"
  "right (t mod t') = right t mod right t'"
by(simp_all add: arith_tree_defs)

lemmas [simp] =
  tree_ap_composition[symmetric]
  o_def

lemmas [simp] =
  tree_ap_homomorphism
  tree_ap_identity[unfolded id_def]


lemma tree_pure_K_apply:
  "tree_pure (\<lambda>_. c) \<diamond> x = tree_pure c"
by(coinduction arbitrary: x) auto


lemma tree_ap_same2: "f \<diamond> x \<diamond> x = tree_pure (\<lambda>f x. f x x) \<diamond> f \<diamond> x"
by(coinduction arbitrary: f x) auto



lemma tree_pure_inject: "tree_pure x = tree_pure y \<longleftrightarrow> x = y"
by(subst (1 2) tree_pure_unfold)(auto)


instance tree :: (semigroup_add) semigroup_add
by(intro_classes)(simp add: add.assoc[abs_def] arith_tree_defs)

instance tree :: (ab_semigroup_add) ab_semigroup_add
proof(intro_classes)
  fix t t' :: "'a tree"
  show "t + t' = t' + t"
    unfolding arith_tree_defs
    by(subst tree_ap_tree_C[symmetric])(simp add: tree_C_def add.commute)
qed

instance tree :: (semigroup_mult) semigroup_mult
by(intro_classes)(simp add: arith_tree_defs mult.assoc[abs_def])

instance tree :: (ab_semigroup_mult) ab_semigroup_mult
proof(intro_classes)
  fix t t' :: "'a tree"
  show "t * t' = t' * t"
    unfolding arith_tree_defs
    by(subst tree_ap_tree_C[symmetric])(simp add: tree_C_def mult.commute)
qed

instance tree :: (monoid_add) monoid_add
by(intro_classes)(simp_all add: add_0_left[abs_def] arith_tree_defs)

instance tree :: (comm_monoid_add) comm_monoid_add
by(intro_classes)(simp add: add_0[abs_def])

instance tree :: (comm_monoid_diff) comm_monoid_diff
proof
  fix t t' t'' :: "'a tree"
  show "t + t' - (t + t'') = t' - t''"
    unfolding arith_tree_defs
    apply(subst tree_ap_composition[symmetric])
    apply(subst tree_ap_homomorphism)
    apply(subst tree_ap_composition[symmetric])
    apply(subst tree_ap_homomorphism)
    apply(subst (1) tree_ap_tree_C[symmetric])
    apply(subst (5) tree_ap_tree_C[symmetric])
    apply(subst (2) tree_ap_tree_C[symmetric])
    apply(subst (3) tree_ap_tree_C[symmetric])
    apply(subst tree_ap_tree_S[symmetric])
    apply(subst (25) tree_ap_tree_K[symmetric, where v=t])
    apply(simp add: tree_K_def tree_S_def tree_C_def)
    done
    (* by(coinduction arbitrary: t t' t'') auto *)
next
  fix t :: "'a tree"
  show "0 - t = 0"
    unfolding arith_tree_defs
    by(subst (6) tree_ap_tree_K[symmetric, where v=t])(simp add: tree_K_def zero_diff[abs_def])
qed(simp_all add: add_0[abs_def] diff_diff_add[abs_def] arith_tree_defs)

instance tree :: (monoid_mult) monoid_mult
by(intro_classes)(simp_all add: mult_1_left[abs_def] arith_tree_defs)

instance tree :: (comm_monoid_mult) comm_monoid_mult
by(intro_classes)(simp_all add: mult_1[abs_def])

lemma eq_tree_pureD: "t = tree_pure x \<Longrightarrow> root t = x \<and> left t = tree_pure x \<and> right t = tree_pure x"
by simp

lemma tree_eq_conv_pure: "(t = t') \<longleftrightarrow> tree_pure op = \<diamond> t \<diamond> t' = tree_pure True"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  have "tree_pure op = \<diamond> t \<diamond> (tree_I \<diamond> t) = tree_K \<diamond> tree_pure True \<diamond> t"
    by(subst tree_ap_tree_S[symmetric])(simp add: tree_S_def tree_I_def tree_K_def)
  thus ?rhs using `?lhs` unfolding tree_ap_tree_K by(simp add: tree_I_def)
next
  assume ?rhs
  thus ?lhs -- {* FIXME: Does this direction somehow follow from combinatorial structure? *}
    by(coinduction arbitrary: t t')(auto dest: eq_tree_pureD)
qed

instance tree :: (cancel_semigroup_add) cancel_semigroup_add
proof(intro_classes)
  fix a b c :: "'a tree"
  assume "a + b = a + c"
  hence "tree_pure op = \<diamond> (a + b) \<diamond> (a + c) = tree_pure True"
    by(simp add: tree_eq_conv_pure[symmetric])
  thus "b = c"
    unfolding arith_tree_defs
    apply(subst tree_eq_conv_pure)
    apply(subst (4) tree_ap_tree_K[symmetric, where v=a])
    apply(subst (asm) tree_ap_composition[symmetric])
    apply(subst (asm) tree_ap_composition[symmetric])
    apply(subst (asm) (5) tree_ap_tree_C[symmetric])
    apply(subst (asm) (3) tree_ap_tree_C[symmetric])
    apply(subst (asm) tree_ap_tree_S[symmetric])
    apply(simp add: tree_S_def tree_C_def tree_K_def)
    done
(*
  proof(coinduction arbitrary: a b c)
    case (Eq_tree a b c)
    thus ?case
      by(cases a b c rule: tree.exhaust[case_product tree.exhaust[case_product tree.exhaust]])(auto simp add: arith_tree_defs)
  qed*)
next
  fix a b c :: "'a tree"
  assume "b + a = c + a"
  thus "b = c"
  proof(coinduction arbitrary: a b c)
    case (Eq_tree a b c)
    thus ?case
      by(cases a b c rule: tree.exhaust[case_product tree.exhaust[case_product tree.exhaust]])(auto simp add: arith_tree_defs)
  qed
qed

instance tree :: (cancel_ab_semigroup_add) cancel_ab_semigroup_add
proof(intro_classes)
  fix a b c :: "'a tree"
  assume "a + b = a + c"
  thus "b = c"
  proof(coinduction arbitrary: a b c)
    case (Eq_tree a b c)
    thus ?case
      by(cases a b c rule: tree.exhaust[case_product tree.exhaust[case_product tree.exhaust]])(auto simp add: arith_tree_defs)
  qed
qed

instance tree :: (cancel_comm_monoid_add) cancel_comm_monoid_add ..

instance tree :: (group_add) group_add
by intro_classes(simp_all add: arith_tree_defs tree_ap_same2 tree_pure_K_apply)

instance tree :: (ab_group_add) ab_group_add
by intro_classes(simp_all add: arith_tree_defs tree_ap_same2 tree_pure_K_apply)

instance tree :: (semiring) semiring
proof intro_classes
  fix a b c :: "'a tree"
  show "(a + b) * c = a * c + b * c"
    by(coinduction arbitrary: a b c)(auto simp add: distrib_right)
  show "a * (b + c) = a * b + a * c"
    by(coinduction arbitrary: a b c)(auto simp add: distrib_left)
qed

instance tree :: (mult_zero) mult_zero
by intro_classes(simp_all add: mult_zero_left[abs_def] arith_tree_defs tree_pure_K_apply)

instance tree :: (semiring_0) semiring_0 ..

instance tree :: (semiring_0_cancel) semiring_0_cancel ..

instance tree :: (comm_semiring) comm_semiring
by intro_classes(rule distrib_right)

instance tree :: (comm_semiring_0) comm_semiring_0 ..

instance tree :: (comm_semiring_0_cancel) comm_semiring_0_cancel ..

instance tree :: (zero_neq_one) zero_neq_one
by intro_classes(simp add: arith_tree_defs tree_pure_inject)

instance tree :: (semiring_1) semiring_1 ..

instance tree :: (comm_semiring_1) comm_semiring_1 ..

instance tree :: (semiring_1_cancel) semiring_1_cancel ..

instance tree :: (comm_semiring_1_cancel) comm_semiring_1_cancel ..

instance tree :: (ring) ring ..

instance tree :: (comm_ring) comm_ring ..

instance tree :: (ring_1) ring_1 ..

instance tree :: (comm_ring_1) comm_ring_1 ..

instance tree :: (numeral) numeral ..

instance tree :: (neg_numeral) neg_numeral ..

instance tree :: (semiring_numeral) semiring_numeral ..

lemma of_nat_Tree: "of_nat n = tree_pure (of_nat n)"
by(induct n)(simp_all add: arith_tree_defs)

instance tree :: (semiring_char_0) semiring_char_0
by intro_classes(simp add: inj_on_def of_nat_Tree tree_pure_inject)

instance tree :: (ring_char_0) ring_char_0 ..

lemma numeral_tree_simps [simp]:
  "root (numeral n) = numeral n"
  "left (numeral n) = numeral n"
  "right (numeral n) = numeral n"
by(induct n)(auto simp add: numeral.simps arith_tree_defs)

lemmas [simp del] =
  tree_ap_composition[symmetric]
  o_def


subsubsection{* Formal fractions. *}

type_synonym fraction = "nat \<times> nat"

abbreviation succ :: "fraction \<Rightarrow> fraction" where
  "succ \<equiv> \<lambda>(m, n). (m + n, n)"

abbreviation inverse' :: "fraction \<Rightarrow> fraction" where
  "inverse' \<equiv> \<lambda>(m, n). (n, m)"

abbreviation tree_succ :: "(fraction \<Rightarrow> fraction) tree" where
  "tree_succ \<equiv> tree_pure succ"

abbreviation tree_inverse :: "(fraction \<Rightarrow> fraction) tree" where
  "tree_inverse \<equiv> tree_pure inverse'"


subsubsection{* Rationals *}

abbreviation toRat :: "fraction \<Rightarrow> rat" where
  "toRat \<equiv> \<lambda>(x, y). Fract (int x) (int y)"

abbreviation tree_toRat :: "(fraction \<Rightarrow> rat) tree" where
  "tree_toRat \<equiv> tree_pure toRat"

subsubsection{* Standard tree combinators *}

text{*

recurse combinator. This is critical: this is how we define our trees
recursively.

uniqueness for this gives us the unique fixed-point theorem for
guarded recursive definitions.

*}

lemma map_unfold_tree [simp]: fixes l r x
 defines "unf \<equiv> unfold_tree (\<lambda>f. f x) (\<lambda>f. f \<circ> l) (\<lambda>f. f \<circ> r)"
 shows "map_tree G (unf F) = unf (G \<circ> F)"
by(coinduction arbitrary: F G)(auto 4 3 simp add: unf_def o_assoc)

definition tree_recurse :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a tree"
where
  "tree_recurse l r x \<equiv> unfold_tree (\<lambda>f. f x) (\<lambda>f. f \<circ> l) (\<lambda>f. f \<circ> r) id"

lemma tree_recurse_ap:
  "tree_recurse l r x = unfold_tree id (\<lambda>f. f \<circ> l) (\<lambda>f. f \<circ> r) id \<diamond> tree_pure x"
by(simp add: tree_ap_interchange map_tree_tree_ap_tree_pure map_tree_unfold_tree tree_recurse_def)

lemma tree_recurse_unfold:
  "tree_recurse l r x = Node x (map_tree l (tree_recurse l r x)) (map_tree r (tree_recurse l r x))"
unfolding tree_recurse_def by (subst unfold_tree.ctr) simp

lemma tree_recurse_unique':
  assumes A: "t = Node x (map_tree l t) (map_tree r t)"
  shows "map_tree H t = unfold_tree (\<lambda>f. f x) (\<lambda>f. f \<circ> l) (\<lambda>f. f \<circ> r) H"
sorry

lemma tree_recurse_unique:
  assumes "t = Node x (map_tree l t) (map_tree r t)"
  shows "t = tree_recurse l r x"
using assms unfolding tree_recurse_def
by (rule tree_recurse_unique'[where H=id, unfolded tree.map_id])

lemma tree_recurse_fusion:
  assumes "h \<circ> l = l' \<circ> h"
  assumes "h \<circ> r = r' \<circ> h"
  shows "map_tree h (tree_recurse l r x) = tree_recurse l' r' (h x)"
apply (rule tree_recurse_unique)
apply (simp add: tree.map_comp)
apply (subst tree_recurse_unfold)
apply (simp add: tree.map_comp assms)
done

text{*

FIXME iteration

*}

primcorec tree_iterate :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a tree"
where
  "root (tree_iterate l r s) = s"
| "left (tree_iterate l r s) = tree_iterate l r (l s)"
| "right (tree_iterate l r s) = tree_iterate l r (r s)"

lemma tree_iterate_unfold:
  "tree_iterate l r s = Node s (tree_iterate l r (l s)) (tree_iterate l r (r s))"
by (rule tree.expand) simp
(*
lemma unfold_tree_tree_iterate:
  "unfold_tree out l r = map_tree out \<circ> tree_iterate l r"
apply(clarsimp simp: fun_eq_iff tree_iterate_def)
apply coinduction
apply auto
done
*)
lemma tree_iterate_fusion:
  assumes "h \<circ> l = l' \<circ> h"
  assumes "h \<circ> r = r' \<circ> h"
  shows "map_tree h (tree_iterate l r x) = tree_iterate l' r' (h x)"
apply(coinduction arbitrary: x)
using assms by (force simp: tree_iterate_def fun_eq_iff)

text{*

\citeauthor{DBLP:journals/jfp/Hinze09} shows that if the tree
construction function is suitably monoidal then recursion and
iteration define the same tree.

*}

lemma tree_recursion_iteration:
  assumes monoid:
    "\<And>x y z. f (f x y) z = f x (f y z)"
    "\<And>x. f x \<epsilon> = x"
    "\<And>x. f \<epsilon> x = x"
  shows "tree_recurse (f l) (f r) \<epsilon> = tree_iterate (\<lambda>x. f x l) (\<lambda>x. f x r) \<epsilon>"
apply (rule tree_recurse_unique[symmetric])
apply (subst tree_iterate_unfold)
apply (simp add: tree_iterate_fusion[where r'="\<lambda>x. f x r" and l'="\<lambda>x. f x l"] fun_eq_iff monoid)
done

subsubsection{* Tree traversal *}

datatype dir = L | R
type_synonym path = "dir list"

definition traverse_tree :: "path \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "traverse_tree path \<equiv> foldr (\<lambda>d f. f \<circ> case_dir left right d) path id"

lemma traverse_tree_simps[simp]:
  "traverse_tree [] = id"
  "traverse_tree (d # path) = traverse_tree path \<circ> (case d of L \<Rightarrow> left | R \<Rightarrow> right)"
by (simp_all add: traverse_tree_def)

lemma traverse_tree_map_tree:
  "traverse_tree path (map_tree f t) = map_tree f (traverse_tree path t)"
by (induct path arbitrary: t) (simp_all split: dir.splits)

text{* @{const "traverse_tree"} is an applicative-functor homomorphism. *}

lemma traverse_tree_tree_pure:
  "traverse_tree path (tree_pure x) = tree_pure x"
by (induct path arbitrary: f x) (simp_all split: dir.splits)

lemma traverse_tree_ap:
  "traverse_tree path (f \<diamond> x) = traverse_tree path f \<diamond> traverse_tree path x"
by (induct path arbitrary: f x) (simp_all split: dir.splits)

lemma traverse_tree_append:
  "traverse_tree (path @ ext) t = traverse_tree ext (traverse_tree path t)"
by (induct path arbitrary: t) simp_all

lemmas traverse_tree_pure_ap_simps [simp] =
  traverse_tree_map_tree
  traverse_tree_tree_pure
  traverse_tree_ap

context fixes l r :: "'a \<Rightarrow> 'a" begin

primrec traverse_dir :: "dir \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "traverse_dir L = l"
| "traverse_dir R = r"

abbreviation traverse_path :: "path \<Rightarrow> 'a \<Rightarrow> 'a"
where "traverse_path \<equiv> fold traverse_dir"

end

lemma traverse_tree_tree_iterate:
  "traverse_tree path (tree_iterate l r s) =
   tree_iterate l r (traverse_path l r path s)"
by (induct path arbitrary: s) (simp_all split: dir.splits)

subsection{* The Stern-Brocot Tree *}

text{*

With all the boilerplate in hand we can give a nice rendition of the
Stern-Brocot tree. See \S\ref{sec:holcf-stern-brocot} for details.

Standard account of the Stern-Brocot tree in terms of mediants.

*}

definition mediant :: "fraction \<times> fraction \<Rightarrow> fraction" where
  "mediant \<equiv> \<lambda>((a, c), (b, d)). (a + b, c + d)"

definition stern_brocot_standard :: "fraction tree" where
  "stern_brocot_standard \<equiv>
     unfold_tree (\<lambda>(lb, ub). mediant (lb, ub))
                 (\<lambda>(lb, ub). (lb, mediant (lb, ub)))
                 (\<lambda>(lb, ub). (mediant (lb, ub), ub))
                 ((0, 1), (1, 0))"

text{*

FIXME As a recursion equation. Write the equation, or point to the
HOLCF version.

*}

definition stern_brocot :: "fraction tree" where
  "stern_brocot \<equiv> tree_recurse (inverse' \<circ> succ \<circ> inverse') succ (1, 1)"

text{*

FIXME in terms of applicative functors:

*}

lemma stern_brocot_unfold:
  "stern_brocot =
       Node (1, 1)
            (tree_inverse \<diamond> (tree_succ \<diamond> (tree_inverse \<diamond> stern_brocot)))
            (tree_succ \<diamond> stern_brocot)"
unfolding stern_brocot_def
by (rule tree_recurse_unique[symmetric])(subst tree_recurse_unfold, simp add: map_tree_tree_ap_tree_pure tree.map_comp o_def)+

lemma stern_brocot_simps:
  "root stern_brocot = (1, 1)"
  "left stern_brocot = tree_inverse \<diamond> (tree_succ \<diamond> (tree_inverse \<diamond> stern_brocot))"
  "right stern_brocot = tree_succ \<diamond> stern_brocot"
by (subst stern_brocot_unfold, simp)+

text{*

FIXME basic properties:

*}

lemma stern_brocot_denominator_non_zero:
  "case root (traverse_tree path stern_brocot) of (m, n) \<Rightarrow> m > 0 \<and> n > 0"
by (induct path)
   (auto simp: stern_brocot_simps id_def[symmetric]
        split: dir.splits)

lemma stern_brocot_coprime:
  "case root (traverse_tree path stern_brocot) of (m, n) \<Rightarrow> coprime m n"
by(induct path)(clarsimp simp: stern_brocot_simps field_simps id_def[symmetric] split: dir.splits)+

subsubsection{* All the rationals *}

text{*

Relatively easy to show that it contains all the
rationals. Computation path taken by Euclid's GCD algorithm gives us
the path in the Stern-Brocot tree.

*}

function mkPath :: "nat \<Rightarrow> nat \<Rightarrow> path" where
  "mkPath 0 _ = []"
| "mkPath _ 0 = []"
| "m = n \<Longrightarrow> mkPath (Suc m) (Suc n) = []"
| "m < n \<Longrightarrow> mkPath (Suc m) (Suc n) = L # mkPath (Suc m) (n - m)"
| "m > n \<Longrightarrow> mkPath (Suc m) (Suc n) = R # mkPath (m - n) (Suc n)"
by atomize_elim(auto, arith)
termination mkPath by lexicographic_order

lemmas mkPath_induct[case_names zero_left zero_right equal less greater] = mkPath.induct

theorem stern_brocot_rationals:
  "\<lbrakk> m > 0; n > 0 \<rbrakk> \<Longrightarrow>
  root (traverse_tree (mkPath m n) (tree_toRat \<diamond> stern_brocot)) = Fract (int m) (int n)"
proof(induction m n rule: mkPath_induct)
  case (less m n)
  with stern_brocot_denominator_non_zero[where path="mkPath (Suc m) (n - m)"]
  show ?case
    by (simp add: stern_brocot_simps eq_rat field_simps zdiff_int[symmetric] split: prod.split_asm)
next
  case (greater m n)
  with stern_brocot_denominator_non_zero[where path="mkPath (m - n) (Suc n)"]
  show ?case
    by (simp add: stern_brocot_simps eq_rat field_simps zdiff_int[symmetric] split: prod.split_asm)
qed (simp_all add: stern_brocot_simps eq_rat)

subsubsection{* No repetitions *}

text{*

FIXME no repetitions takes more doing.

Follows \citet{DBLP:conf/mpc/BackhouseF08}.

*}

type_synonym Mat = "fraction \<times> fraction"
type_synonym Vec = fraction

definition Mulmat :: "Mat \<Rightarrow> Mat \<Rightarrow> Mat" where
  "Mulmat \<equiv> \<lambda>((a, c), (b, d)) ((a', c'), (b', d')).
                   ((a * a' + b * c', c * a' + d * c'),
                   (a * b' + b * d', c * b' + d * d'))"

definition Mulvec :: "Mat \<Rightarrow> Vec \<Rightarrow> Vec" where
  "Mulvec \<equiv> \<lambda>((a, c), (b, d)) (a', c').
                   (a * a' + b * c', c * a' + d * c')"

definition Fmat :: Mat where "Fmat \<equiv> ((0, 1), (1, 0))"
definition Imat :: Mat where "Imat \<equiv> ((1, 0), (0, 1))"
definition LLmat :: Mat where "LLmat \<equiv> ((1, 1), (0, 1))"
definition URmat :: Mat where "URmat \<equiv> ((1, 0), (1, 1))"

definition Det :: "Mat \<Rightarrow> nat" where
  "Det \<equiv> \<lambda>((a, c), (b, d)). a * d - b * c"

lemma Dets [iff]:
  "Det Imat = 1"
  "Det LLmat = 1"
  "Det URmat = 1"
unfolding Det_def Imat_def LLmat_def URmat_def by simp_all

lemma LLmat_URmat_Det:
  "Det m = 1 \<Longrightarrow> Det (Mulmat m LLmat) = 1"
  "Det m = 1 \<Longrightarrow> Det (Mulmat LLmat m) = 1"
  "Det m = 1 \<Longrightarrow> Det (Mulmat m URmat) = 1"
  "Det m = 1 \<Longrightarrow> Det (Mulmat URmat m) = 1"
by (cases m, simp add: Det_def LLmat_def URmat_def Mulmat_def split_def field_simps)+

lemma mediant_Imat_Fmat [simp]:
  "mediant Fmat = (1, 1)"
  "mediant Imat = (1, 1)"
by (simp_all add: Fmat_def Imat_def mediant_def)

lemma Mulmat_Imat [simp]:
  "Mulmat Imat x = x"
  "Mulmat x Imat = x"
by (simp_all add: Mulmat_def Imat_def split_def)

lemma Mulmat_assoc [simp]:
  "Mulmat (Mulmat x y) z = Mulmat x (Mulmat y z)"
by (simp add: Mulmat_def field_simps split_def)

lemma LLmat_URmat_pos:
  "0 < snd (mediant m) \<Longrightarrow> 0 < snd (mediant (Mulmat m LLmat))"
  "0 < snd (mediant m) \<Longrightarrow> 0 < snd (mediant (Mulmat m URmat))"
by (cases m) (simp_all add: LLmat_def URmat_def Mulmat_def split_def field_simps mediant_def)

lemma inverse'_succ_inverse':
  "inverse' \<circ> succ \<circ> inverse' = (\<lambda>(x, y). (x, x + y))"
by (clarsimp simp: fun_eq_iff)

definition stern_brocot_iterate_aux :: "Mat \<Rightarrow> Mat tree" where
  "stern_brocot_iterate_aux \<equiv> tree_iterate (\<lambda>s. Mulmat s LLmat) (\<lambda>s. Mulmat s URmat)"

definition stern_brocot_iterate :: "fraction tree" where
  "stern_brocot_iterate \<equiv> map_tree mediant (stern_brocot_iterate_aux Imat)"

lemma stern_brocot_iterate: "stern_brocot = stern_brocot_iterate" (is "?lhs = ?rhs")
proof -
  have "?rhs = map_tree mediant (tree_recurse (Mulmat LLmat) (Mulmat URmat) Imat)"
    using tree_recursion_iteration[where f="Mulmat" and l="LLmat" and r="URmat" and \<epsilon>="Imat"]
    by (simp add: stern_brocot_iterate_def stern_brocot_iterate_aux_def)
 also have "\<dots> = tree_recurse (Mulvec LLmat) (Mulvec URmat) (1, 1)"
   unfolding mediant_Imat_Fmat(2)[symmetric]
   by (rule tree_recurse_fusion)(simp_all add: fun_eq_iff mediant_def Mulmat_def Mulvec_def LLmat_def URmat_def)[2]
 also have "\<dots> = ?lhs"
   by (simp add: stern_brocot_def inverse'_succ_inverse' Mulvec_def LLmat_def URmat_def)
 finally show ?thesis by simp
qed

lemma tree_ordering_left:
  assumes DX: "Det X = 1"
  assumes DY: "Det Y = 1"
  assumes MX: "0 < snd (mediant X)"
  shows "toRat (mediant (Mulmat (Mulmat X LLmat) Y)) < toRat (mediant X)"
proof -
  from DX DY have F: "0 < snd (mediant (Mulmat (Mulmat X LLmat) Y))"
    by (auto simp: Det_def Mulmat_def LLmat_def split_def mediant_def)
  with DX DY MX show ?thesis
    apply (cases X)
    apply (cases Y)
    apply (simp add: split_def zmult_int)
    apply (clarsimp simp: Det_def Mulmat_def LLmat_def URmat_def mediant_def split_def)
    apply (subgoal_tac "(b * ba) * (bb + ca) < (a * c) * (bb + ca)")
     apply (simp add: field_simps)
    apply simp
    apply (case_tac bb)
    apply (simp add: field_simps)+
    done
qed

lemma tree_ordering_right:
  assumes DX: "Det X = 1"
  assumes DY: "Det Y = 1"
  assumes MX: "0 < snd (mediant X)"
  shows "toRat (mediant X) < toRat (mediant (Mulmat (Mulmat X URmat) Y))"
proof -
  from DX DY have F: "0 < snd (mediant (Mulmat (Mulmat X URmat) Y))"
    by (auto simp: Det_def Mulmat_def URmat_def split_def mediant_def)
  then show ?thesis using DX DY MX
    apply (cases X)
    apply (cases Y)
    apply (clarsimp simp add: split_def zmult_int)
    apply (clarsimp simp add: Det_def Mulmat_def LLmat_def URmat_def mediant_def split_def algebra_simps)
    apply (simp add: add_mult_distrib2[symmetric] mult.assoc[symmetric])
    apply (case_tac aa)
    apply (simp_all)
    done
qed

lemma stern_brocot_iterate_aux_Det:
  assumes "Det m = 1" "0 < snd (mediant m)"
  shows "case root (traverse_tree path (stern_brocot_iterate_aux m)) of m' \<Rightarrow> Det m' = 1 \<and> 0 < snd (mediant m')"
using assms
by (induct path arbitrary: m)
   (simp_all add: stern_brocot_iterate_aux_def LLmat_URmat_Det LLmat_URmat_pos split: dir.splits)

lemma stern_brocot_iterate_aux_decompose:
  "case root (traverse_tree path (stern_brocot_iterate_aux m)) of m' \<Rightarrow> (\<exists>m''. Mulmat m m'' = m' \<and> Det m'' = 1)"
proof(induction path arbitrary: m)
  case Nil show ?case
    by (auto simp add: stern_brocot_iterate_aux_def intro: exI[where x=Imat] simp del: split_paired_Ex)
next
  case (Cons d ds m)
  from Cons.IH[where m="Mulmat m URmat"] Cons.IH[where m="Mulmat m LLmat"] show ?case
    by(simp add: stern_brocot_iterate_aux_def split: dir.splits del: split_paired_Ex)(fastforce simp: LLmat_URmat_Det)
qed

lemma stern_brocot_fractions_not_repeated_prefix:
  assumes "root (traverse_tree path stern_brocot_iterate) = root (traverse_tree path' stern_brocot_iterate)"
  assumes pp': "prefix path path'"
  shows False
proof -
  from pp' obtain d ds where pp': "path' = path @ [d] @ ds"
    by (auto elim!: prefixE')
  def m \<equiv> "root (traverse_tree path (stern_brocot_iterate_aux Imat))"
  then have Dm: "Det m = 1" and Pm: "0 < snd (mediant m)"
    using stern_brocot_iterate_aux_Det[where path="path" and m="Imat"] by simp_all
  def m' \<equiv> "root (traverse_tree path' (stern_brocot_iterate_aux Imat))"
  then have Dm': "Det m' = 1"
    using stern_brocot_iterate_aux_Det[where path=path' and m="Imat"] by simp
  let ?M = "case d of L \<Rightarrow> Mulmat m LLmat | R \<Rightarrow> Mulmat m URmat"
  from pp'
  have "root (traverse_tree ds (stern_brocot_iterate_aux ?M)) = m'"
    by(simp add: m_def m'_def traverse_tree_append stern_brocot_iterate_aux_def traverse_tree_tree_iterate split: dir.splits)
  then obtain m''
    where mm'm'': "Mulmat ?M m''= m'" and Dm'': "Det m'' = 1"
    using stern_brocot_iterate_aux_decompose[where path="ds" and m="?M"] by clarsimp
  hence "case d of L \<Rightarrow> toRat (mediant m') < toRat (mediant m) | R \<Rightarrow> toRat (mediant m) < toRat (mediant m')"
    using tree_ordering_left[OF Dm Dm'' Pm, unfolded mm'm'']
          tree_ordering_right[OF Dm Dm'' Pm, unfolded mm'm'']
    by (simp split: dir.splits)
  with assms show False
    by (simp add: stern_brocot_iterate_def m_def m'_def split: dir.splits)
qed

lemma stern_brocot_fractions_not_repeated_parallel:
  assumes "root (traverse_tree path stern_brocot_iterate) = root (traverse_tree path' stern_brocot_iterate)"
  assumes p: "path = pref @ d # ds"
  assumes p': "path' = pref @ d' # ds'"
  assumes dd': "d \<noteq> d'"
  shows False
proof -
  def m \<equiv> "root (traverse_tree pref (stern_brocot_iterate_aux Imat))"
  then have Dm: "Det m = 1" and Pm: "0 < snd (mediant m)"
    using stern_brocot_iterate_aux_Det[where path="pref" and m="Imat"] by simp_all
  def pm \<equiv> "root (traverse_tree path (stern_brocot_iterate_aux Imat))"
  then have Dpm: "Det pm = 1"
    using stern_brocot_iterate_aux_Det[where path=path and m="Imat"] by simp
  let ?M = "case d of L \<Rightarrow> Mulmat m LLmat | R \<Rightarrow> Mulmat m URmat"
  from p
  have "root (traverse_tree ds (stern_brocot_iterate_aux ?M)) = pm"
    by(simp add: traverse_tree_append stern_brocot_iterate_aux_def m_def pm_def traverse_tree_tree_iterate split: dir.splits)
  then obtain pm'
    where pm': "Mulmat ?M pm'= pm" and Dpm': "Det pm' = 1"
    using stern_brocot_iterate_aux_decompose[where path="ds" and m="?M"] by clarsimp
  hence "case d of L \<Rightarrow> toRat (mediant pm) < toRat (mediant m) | R \<Rightarrow> toRat (mediant m) < toRat (mediant pm)"
    using tree_ordering_left[OF Dm Dpm' Pm, unfolded pm']
          tree_ordering_right[OF Dm Dpm' Pm, unfolded pm']
    by (simp split: dir.splits)
  moreover
  def p'm \<equiv> "root (traverse_tree path' (stern_brocot_iterate_aux Imat))"
  then have Dp'm: "Det p'm = 1"
    using stern_brocot_iterate_aux_Det[where path=path' and m="Imat"] by simp
  let ?M' = "case d' of L \<Rightarrow> Mulmat m LLmat | R \<Rightarrow> Mulmat m URmat"
  from p'
  have "root (traverse_tree ds' (stern_brocot_iterate_aux ?M')) = p'm"
    by(simp add: traverse_tree_append stern_brocot_iterate_aux_def m_def p'm_def traverse_tree_tree_iterate split: dir.splits)
  then obtain p'm'
    where p'm': "Mulmat ?M' p'm' = p'm" and Dp'm': "Det p'm' = 1"
    using stern_brocot_iterate_aux_decompose[where path="ds'" and m="?M'"] by clarsimp
  hence "case d' of L \<Rightarrow> toRat (mediant p'm) < toRat (mediant m) | R \<Rightarrow> toRat (mediant m) < toRat (mediant p'm)"
    using tree_ordering_left[OF Dm Dp'm' Pm, unfolded pm']
          tree_ordering_right[OF Dm Dp'm' Pm, unfolded pm']
    by (simp split: dir.splits)
  ultimately show False using pm' p'm' assms
    by(simp add: traverse_tree_append m_def pm_def p'm_def stern_brocot_iterate_def split: dir.splits)
qed

lemma stern_brocot_fractions_not_repeated:
  assumes "root (traverse_tree path stern_brocot_iterate) = root (traverse_tree path' stern_brocot_iterate)"
  shows "path = path'"
proof(rule ccontr)
  assume "path \<noteq> path'"
  then show False using assms
    by (cases path path' rule: lists_not_eq)
       (blast intro: stern_brocot_fractions_not_repeated_prefix sym
                     stern_brocot_fractions_not_repeated_parallel)+
qed

theorem stern_brocot_rationals_not_repeated:
  assumes "root (traverse_tree path (tree_toRat \<diamond> stern_brocot))
         = root (traverse_tree path' (tree_toRat \<diamond> stern_brocot))"
  shows "path = path'"
using assms
using stern_brocot_coprime[where path=path]
      stern_brocot_coprime[where path=path']
      stern_brocot_denominator_non_zero[where path=path]
      stern_brocot_denominator_non_zero[where path=path']
by(auto simp: transfer_int_nat_gcd dest!: rat_inv_eq intro: stern_brocot_fractions_not_repeated simp add: stern_brocot_iterate[symmetric] split: prod.splits)


subsection{* Linearising the Stern-Brocot Tree *}

subsubsection {* Streams *}

text{*

We use the standard BNF @{typ "'a stream"} type.

*}

notation SCons (infixr "\<prec>" 65)

context fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" begin

primcorec szip_with :: "'a stream \<Rightarrow> 'b stream \<Rightarrow> 'c stream"
where
  "shd (szip_with s t) = f (shd s) (shd t)"
| "stl (szip_with s t) = szip_with (stl s) (stl t)"

end
lemma smap_siterate: "smap f (siterate f a) = siterate f (f a)"
by(coinduction arbitrary: a) auto

lemma siterate_unique:
  assumes "xs = x \<prec> smap f xs"
  shows "xs = siterate f x"
using assms
proof(coinduction arbitrary: xs x)
  case (Eq_stream xs x)
  have "smap f xs = f x \<prec> smap f (smap f xs)"
    by(subst Eq_stream) simp
  then show ?case
    by(subst (1 2) Eq_stream) auto
qed

subsubsection{* Applicative Functor machinery *}

abbreviation st_pure :: "'a \<Rightarrow> 'a stream" where
  "st_pure \<equiv> sconst"

primcorec st_ap :: "('a \<Rightarrow> 'b) stream \<Rightarrow> 'a stream \<Rightarrow> 'b stream" (infixl "\<box>" 70)
where
  "shd (f \<box> x) = shd f (shd x)"
| "stl (f \<box> x) = stl f \<box> stl x"

lemma st_ap_identity:
  "st_pure id \<box> t = t"
by(coinduction arbitrary: t) simp_all

lemma st_ap_identity':
  "st_pure (%x. x) \<box> t = t"
by(coinduction arbitrary: t) simp_all

lemma st_ap_composition:
  "st_pure (op \<circ>) \<box> r1 \<box> r2 \<box> r3 = r1 \<box> (r2 \<box> r3)"
by(coinduction arbitrary: r1 r2 r3) auto

lemma st_ap_homomorphism:
  "st_pure f \<box> st_pure x = st_pure (f x)"
by(coinduction) simp_all

lemma st_ap_interchange:
  "t \<box> st_pure x = st_pure (\<lambda>f. f x) \<box> t"
by(coinduction arbitrary: t) auto

lemma same_K_apply [simp]:
  "st_pure (\<lambda>_. c) \<box> x = st_pure c"
by(coinduction arbitrary: x) auto

lemma st_pure_K2_apply:
  "st_pure (\<lambda>x _. f x) \<box> x \<box> y = st_pure f \<box> x"
by(coinduction arbitrary: x y)(auto)

text{*

FIXME note here and elsewhere that this is not a property of all
applicative functors.

*}

lemma st_ap_pure_same [simp]: "st_pure f \<box> a \<box> a = st_pure (\<lambda>x. f x x) \<box> a"
by(coinduction arbitrary: a) auto

lemma st_ap_pure_SCons [simp]: "st_pure f \<box> (x \<prec> xs) = f x \<prec> (st_pure f \<box> xs)"
by(rule stream.expand) simp

lemma st_ap_SCons_SCons [simp]: "(f \<prec> fs) \<box> (x \<prec> xs) = f x \<prec> (fs \<box> xs)"
by(rule stream.expand) simp


subsection{* FIXME pointwise arithmetic on streams *}

(* Isabelle arithmetic type class madness *)

instantiation stream :: (zero) zero begin
definition "0 = st_pure 0"
instance ..
end

instantiation stream :: (one) one begin
definition "1 = st_pure 1"
instance ..
end

instantiation stream :: (plus) plus begin
definition "x + y = st_pure op + \<box> x \<box> y"
instance ..
end

instantiation stream :: (minus) minus begin
definition "x - y = st_pure op - \<box> x \<box> y"
instance ..
end

instantiation stream :: (uminus) uminus begin
definition "uminus = op \<box> (st_pure uminus)"
instance ..
end

instantiation stream :: (times) times begin
definition "x * y = st_pure op * \<box> x \<box> y"
instance ..
end

instance stream :: (Rings.dvd) Rings.dvd ..

instantiation stream :: ("Divides.div") "Divides.div" begin
definition "x div y = st_pure op div \<box> x \<box> y"
definition "x mod y = st_pure op mod \<box> x \<box> y"
instance ..
end

simproc_setup st_ap_interchange ("x \<box> st_pure y") = {*
  fn phi => fn ctxt => fn redex => case term_of redex of
      Const (@{const_name st_ap}, _) $ (Const (@{const_name siterate}, _) $ Const (@{const_name id}, _)) $ _ => NONE
    | _ => SOME @{thm st_ap_interchange[folded atomize_eq]}
*}

lemmas arith_stream_defs =
  zero_stream_def
  one_stream_def
  plus_stream_def
  minus_stream_def
  uminus_stream_def
  times_stream_def
  div_stream_def
  mod_stream_def

lemma plus_stream_simps [simp]:
  "shd (t + t') = shd t + shd t'"
  "stl (t + t') = stl t + stl t'"
by(simp_all add: arith_stream_defs)

lemma minus_stream_simps [simp]:
  "shd (t - t') = shd t - shd t'"
  "stl (t - t') = stl t - stl t'"
by(simp_all add: arith_stream_defs)

lemma times_stream_simps [simp]:
  "shd (t * t') = shd t * shd t'"
  "stl (t * t') = stl t * stl t'"
by(simp_all add: arith_stream_defs)

lemma mod_stream_simps [simp]:
  "shd (t mod t') = shd t mod shd t'"
  "stl (t mod t') = stl t mod stl t'"
by(simp_all add: arith_stream_defs)

lemmas [simp] =
  st_ap_identity'
  st_ap_homomorphism
  st_ap_composition[symmetric]
  o_def

instance stream :: (semigroup_add) semigroup_add
by(intro_classes)(simp add: add.assoc[abs_def] arith_stream_defs)

instance stream :: (ab_semigroup_add) ab_semigroup_add
proof(intro_classes)
  fix a b :: "'a stream"
  show "a + b = b + a"
    by(coinduction arbitrary: a b)(auto simp add: add.commute)
qed

instance stream :: (semigroup_mult) semigroup_mult
by(intro_classes)(simp add: mult.assoc[abs_def] arith_stream_defs)

instance stream :: (ab_semigroup_mult) ab_semigroup_mult
proof(intro_classes)
  fix a b :: "'a stream"
  show "a * b = b * a"
    by(coinduction arbitrary: a b)(auto simp add: mult.commute)
qed

instance stream :: (monoid_add) monoid_add
by(intro_classes)(simp_all add: add_0_left[abs_def] arith_stream_defs)

instance stream :: (comm_monoid_add) comm_monoid_add
by(intro_classes)(simp add: add_0[abs_def] arith_stream_defs)

instance stream :: (comm_monoid_diff) comm_monoid_diff
proof(intro_classes)
  fix a b c :: "'a stream"
  show "a + b - (a + c) = b - c"
    by(coinduction arbitrary: a b c)(fastforce simp add: diff_diff_add)
qed(simp_all add: add_0[abs_def] zero_diff[abs_def] diff_diff_add[abs_def] arith_stream_defs)

instance stream :: (monoid_mult) monoid_mult
by(intro_classes)(simp_all add: mult_1_left[abs_def] arith_stream_defs)

instance stream :: (comm_monoid_mult) comm_monoid_mult
by(intro_classes)(simp_all add: mult_1[abs_def])

instance stream :: (cancel_semigroup_add) cancel_semigroup_add
proof(intro_classes)
  fix a b c :: "'a stream"
  assume "a + b = a + c"
  thus "b = c"
  proof(coinduction arbitrary: a b c)
    case (Eq_stream a b c)
    then show ?case
      by(cases a b c rule: stream.exhaust[case_product stream.exhaust[case_product stream.exhaust]])(auto simp add: arith_stream_defs)
  qed
next
  fix a b c :: "'a stream"
  assume "b + a = c + a"
  thus "b = c"
  proof(coinduction arbitrary: a b c)
    case (Eq_stream a b c)
    then show ?case
      by(cases a b c rule: stream.exhaust[case_product stream.exhaust[case_product stream.exhaust]])(auto simp add: arith_stream_defs)
  qed
qed

instance stream :: (cancel_ab_semigroup_add) cancel_ab_semigroup_add
by(intro_classes)(erule add_left_imp_eq)

instance stream :: (cancel_comm_monoid_add) cancel_comm_monoid_add ..

instance stream :: (group_add) group_add
by intro_classes(simp_all add: arith_stream_defs)

instance stream :: (ab_group_add) ab_group_add
by intro_classes(simp_all)

instance stream :: (semiring) semiring
proof intro_classes
  fix a b c :: "'a stream"
  show "(a + b) * c = a * c + b * c"
    by(coinduction arbitrary: a b c)(auto simp add: distrib_right)
  show "a * (b + c) = a * b + a * c"
    by(coinduction arbitrary: a b c)(auto simp add: distrib_left)
qed

instance stream :: (mult_zero) mult_zero
by intro_classes(simp_all add: mult_zero_left[abs_def] arith_stream_defs)

instance stream :: (semiring_0) semiring_0 ..

instance stream :: (semiring_0_cancel) semiring_0_cancel ..

instance stream :: (comm_semiring) comm_semiring
by intro_classes(rule distrib_right)

instance stream :: (comm_semiring_0) comm_semiring_0 ..

instance stream :: (comm_semiring_0_cancel) comm_semiring_0_cancel ..

lemma same_inject [simp]: "st_pure x = st_pure y \<longleftrightarrow> x = y"
by(subst (1 2) siterate.ctr)(auto)

instance stream :: (zero_neq_one) zero_neq_one
by intro_classes(simp add: arith_stream_defs)

instance stream :: (semiring_1) semiring_1 ..

instance stream :: (comm_semiring_1) comm_semiring_1 ..

instance stream :: (semiring_1_cancel) semiring_1_cancel ..

instance stream :: (comm_semiring_1_cancel) comm_semiring_1_cancel ..

instance stream :: (ring) ring ..

instance stream :: (comm_ring) comm_ring ..

instance stream :: (ring_1) ring_1 ..

instance stream :: (comm_ring_1) comm_ring_1 ..

instance stream :: (numeral) numeral ..

instance stream :: (neg_numeral) neg_numeral ..

instance stream :: (semiring_numeral) semiring_numeral ..

lemma of_nat_stream: "of_nat n = st_pure (of_nat n)"
apply(induct n)
apply(simp add: arith_stream_defs id_def)
by (metis of_nat_Suc one_stream_def plus_stream_def st_ap_homomorphism)

instance stream :: (semiring_char_0) semiring_char_0
by intro_classes(simp add: inj_on_def of_nat_stream)

instance stream :: (ring_char_0) ring_char_0 ..

lemma numeral_stream_simps [simp]:
  "shd (numeral n) = numeral n"
  "stl (numeral n) = numeral n"
by(induct n)(auto simp add: numeral.simps arith_stream_defs)

lemmas [simp del] =
  st_ap_composition[symmetric]
  o_def

text{*

FIXME turn a tree into a stream.

*}

primcorec tree_chop :: "'a tree \<Rightarrow> 'a tree"
where
  "root (tree_chop t) = root (left t)"
| "left (tree_chop t) = right t"
| "right (tree_chop t) = tree_chop (left t)"

lemma tree_chop_tree_pure [simp]:
  "tree_chop (tree_pure x) = tree_pure x"
by(coinduction rule: tree.coinduct_strong) auto

lemma tree_chop_tree_ap [simp]:
  "tree_chop (f \<diamond> x) = tree_chop f \<diamond> tree_chop x"
by(coinduction arbitrary: f x rule: tree.coinduct_strong) auto

lemma map_tree_chop:
  "map_tree f (tree_chop t) = tree_chop (map_tree f t)"
by(coinduction arbitrary: t rule: tree.coinduct_strong) auto

primcorec stream :: "'a tree \<Rightarrow> 'a stream"
where
  "shd (stream t) = root t"
| "stl (stream t) = stream (tree_chop t)"

text{*

@{text "stream"} is an idiom homomorphism.

*}

lemma stream_pure [simp]:
  "stream (tree_pure x) = st_pure x"
by coinduction auto

lemma stream_ap [simp]:
  "stream (f \<diamond> x) = stream f \<box> stream x"
by(coinduction arbitrary: f x) auto

lemma stream_plus: "stream (t + t') = stream t + stream t'"
by(simp add: plus_stream_def plus_tree_def)

lemma stream_minus: "stream (t - t') = stream t - stream t'"
by(simp add: minus_stream_def minus_tree_def)

lemma stream_times: "stream (t * t') = stream t * stream t'"
by(simp add: times_stream_def times_tree_def)

lemma stream_mod: "stream (t mod t') = stream t mod stream t'"
by(simp add: mod_stream_def mod_tree_def)

lemma stream_1 [simp]: "stream 1 = 1"
by(simp add: one_tree_def one_stream_def)

lemma stream_numeral [simp]: "stream (numeral n) = numeral n"
by(induct n)(simp_all only: numeral.simps stream_plus stream_1)

(* FIXME may as well just use the defs directly. Proofs not polished. *)

definition num :: "nat tree" where
  "num \<equiv> tree_pure fst \<diamond> stern_brocot"

definition den :: "nat tree" where
  "den \<equiv> tree_pure snd \<diamond> stern_brocot"

lemma num_unfold: "num = Node 1 num (num + den)"
unfolding num_def den_def plus_tree_def
by(subst stern_brocot_unfold)(simp add: tree_ap_composition[symmetric] o_def split_beta tree_ap_same2)

lemma den_unfold: "den = Node 1 (num + den) den"
unfolding num_def den_def plus_tree_def
by(subst stern_brocot_unfold)(simp add: tree_ap_composition[symmetric] o_def split_beta add_ac tree_ap_same2)

lemma num_simps [simp]:
  "root num = 1"
  "left num = num"
  "right num = num + den"
by(subst num_unfold, simp)+

lemma den_simps [simp]:
  "root den = 1"
  "left den = num + den"
  "right den = den"
by (subst den_unfold, simp)+

lemma den_eq_chop_num: "den = tree_chop num"
by(coinduction rule: tree.coinduct_strong) simp


lemma stern_brocot_num_div:
  "tree_pure Pair \<diamond> num \<diamond> den = stern_brocot"
unfolding stern_brocot_def
apply (rule tree_recurse_unique)
apply (subst den_unfold)
apply (subst num_unfold)
apply(simp add: map_tree_tree_ap_tree_pure[symmetric] plus_tree_def tree_ap_same2 tree_ap_composition[symmetric] o_def add_ac)
done

lemma map_tree_plus:
  assumes "\<And>x y. f (x + y) = f x + f y"
  shows "map_tree f (t + t') = map_tree f t + map_tree f t'"
by(simp add: map_tree_tree_ap_tree_pure[symmetric] plus_tree_def tree_ap_composition[symmetric] o_def assms)

text{* FIXME would it be better to work over int everywhere? IIRC there is some matrix arithmetic that relies on non-negativity. *}

definition den' :: "int tree" where "den' = map_tree int den"
definition num' :: "int tree" where "num' = map_tree int num"

lemma num'_simps [simp]:
  "root num' = 1"
  "left num' = num'"
  "right num' = num' + den'"
by(simp_all add: den'_def num'_def map_tree_tree_ap_tree_pure[symmetric] plus_tree_def tree_ap_composition[symmetric] o_def)

(* FIXME discard
lemma den'_simps [simp]:
  "root den' = 1"
  "left den' = num' + den'"
  "right den' = den'"
by(simp_all add: den'_def num'_def map_tree_plus)
*)

lemma den'_eq_chop_num':
  "den' = tree_chop num'"
by(simp add: den'_def num'_def den_eq_chop_num map_tree_chop)

(* FIXME discard
lemma map_nat_num': "map_tree nat num' = num"
by(simp add: num'_def tree.map_comp o_def id_def[symmetric] tree.map_id)
*)

lemma map_nat_den': "map_tree nat den' = den"
by(simp add: den'_def tree.map_comp o_def id_def[symmetric] tree.map_id)

text{*

\citet[p502]{DBLP:journals/jfp/Hinze09} gets a bit oblique here.

He's also a bit sloppy in his treatment of partial operations
 - x mod (x + y) = x only if y > 0, which is non-trivial for trees.

Perhaps he has an answer here:

\url{http://www.cs.ox.ac.uk/ralf.hinze/Lifting.pdf}

chop den
 = Node 2 den (chop (num + den))
 = Node 2 den (chop num + chop den)
 = Node 2 den (den + chop den)

num + den - chop den
 = (Node 1 num (num + den) + Node 1 (num + den) den) - chop den
 = Node 2 (2num + den) (num + 2den) - chop den
 = Node 2 (2num + den) (num + 2den) - Node 2 den (den + chop den)
 = Node 0 2num (num + 2den - (den + chop den))
 = Node 0 2num (num + den - chop den)

The arithmetic facts we need. FIXME could attempt to use the transfer package for these.

*}

text{*

Hinze's identities

*}

lemma tree_chop_plus: "tree_chop (t + t') = tree_chop t + tree_chop t'"
by(simp add: plus_tree_def)

primcorec FIXME_x :: "nat tree"
where "FIXME_x = Node 0 num FIXME_x"

lemma FIXME_x_unique: "x = Node 0 num x \<Longrightarrow> x = FIXME_x"
proof(coinduction arbitrary: x rule: tree.coinduct_strong)
  case (Eq_tree x)
  show ?case
    by(subst (1 2 3 4) Eq_tree)(simp add: eqTrueI[OF Eq_tree])
qed

(* FIXME how does Hinze propose to prove this? *)

lemma mod_tree_lemma1:
  fixes x :: "nat tree"
  shows "\<forall>n\<in>set_tree y. 0 < n \<Longrightarrow> x mod (x + y) = x"
by(coinduction arbitrary: x y)(auto dest: spec intro: root_in_set_tree intro: in_set_tree_left right_in_set_tree)

lemma mod_tree_lemma2:
  fixes x y :: "'a :: semiring_div tree"
  shows "(x + y) mod y = x mod y"
by(coinduction arbitrary: x y)(auto)

lemma set_tree_pathD:
  "x \<in> set_tree t \<Longrightarrow> \<exists>p. x = root (traverse_tree p t)"
apply(induct rule: set_tree_induct)
apply(auto intro: exI[where x="[]"] exI[where x="L # p" for L p] exI[where x="R # p" for R p])
 apply (metis comp_apply dir.case(1) traverse_tree_simps(2))
by (metis comp_apply dir.case(2) traverse_tree_simps(2))

lemma den_ge_1: "\<forall>x\<in>set_tree den. 0 < x"
apply(clarsimp simp add: tree.set_map den_def)
apply(drule set_tree_pathD)
apply clarify
apply(cut_tac path="p" in stern_brocot_denominator_non_zero)
apply auto
done

lemma FIXME_FIXME_x:
  "num mod den = FIXME_x"
apply (rule FIXME_x_unique)
apply(rule tree.expand)
apply(simp add: mod_tree_lemma1 den_ge_1 mod_tree_lemma2)
done

definition FIXME_x' :: "int tree" where "FIXME_x' = map_tree int FIXME_x"

lemma FIXME_x'_simps [simp]:
  "root FIXME_x' = 0"
  "left FIXME_x' = num'"
  "right FIXME_x' = FIXME_x'"
by(simp_all add: FIXME_x'_def num'_def)

lemma FIXME_x'2_unique: "x = Node 0 (2 * num') x \<Longrightarrow> x = 2 * FIXME_x'"
proof(coinduction arbitrary: x rule: tree.coinduct_strong)
  case (Eq_tree x)
  show ?case
    by(subst (1 2 3 4) Eq_tree)(simp add: eqTrueI[OF Eq_tree])
qed

lemma num'_plus_den'_minus_chop_den': "num' + den' - tree_chop den' = 2 * FIXME_x'"
apply(rule FIXME_x'2_unique)
apply(rule tree.expand)
apply(simp add: tree_chop_plus den'_eq_chop_num')
done

lemma map_tree_mod:
  assumes "\<And>x y. f (x mod y) = f x mod f y"
  shows "map_tree f (t mod t') = map_tree f t mod map_tree f t'"
by(simp add: mod_tree_def map_tree_tree_ap_tree_pure[symmetric] tree_ap_composition[symmetric] o_def assms)

lemma foo: fixes x :: nat shows "0 < y \<Longrightarrow> 2 * (x mod y) \<le> x + y"
by (metis Divides.mod_less_eq_dividend add_le_mono mod_le_divisor mult_2)

lemma FIXME_conversion:
  assumes "\<forall>x\<in>set_tree t'. 0 < x"
  shows "tree_pure (\<lambda>x y. int (x - y) = int x - int y) \<diamond> (t + t') \<diamond> (2 * (t mod t')) = tree_pure True"
using assms
apply(coinduction arbitrary: t t')
apply(auto dest: right_in_set_tree in_set_tree_left simp add: zdiff_int[symmetric] foo root_in_set_tree)
done

lemma tree_ap_cong:
  assumes *: "x = y"
  and rel: "tree_pure (\<lambda>f g x. f x = g x) \<diamond> f \<diamond> g \<diamond> y = tree_pure True"
  shows "f \<diamond> x = g \<diamond> y"
unfolding * using rel
proof(coinduction arbitrary: f g y)
  case (Eq_tree f g y)
  hence "tree_pure (\<lambda>f g x. f x = g x) \<diamond> f \<diamond> g \<diamond> y = Node True (tree_pure True) (tree_pure True)"
    by(simp add: tree_pure.ctr[symmetric])
  thus ?case
    by(cases f g y rule: tree.exhaust[case_product tree.exhaust[case_product tree.exhaust]])(auto)
qed

lemma map_tree_diff:
  assumes "tree_pure (\<lambda>x xa. f (x - xa) = f x - f xa) \<diamond> t \<diamond> t' = tree_pure True"
  shows "map_tree f (t - t') = map_tree f t - map_tree f t'"
by(auto simp add: minus_tree_def map_tree_tree_ap_tree_pure[symmetric] tree_ap_composition[symmetric] o_def tree_ap_same2 assms intro: tree_ap_cong[OF refl])

lemma map_tree_times:
  assumes "\<And>x y. f (x * y) = f x * f y"
  shows "map_tree f (t * t') = map_tree f t * map_tree f t'"
by(simp add: times_tree_def map_tree_tree_ap_tree_pure[symmetric] tree_ap_composition[symmetric] o_def assms)
(*
lemma map_tree_int_1 [simp]: "map_tree int 1 = 1"
by(simp add: one_tree_def)
*)
lemma map_tree_int_numeral [simp]:
  "map_tree int (numeral n) = numeral n"
by(induct n)(simp_all only: numeral.simps map_tree_plus one_tree_def map_tree_pure int_1)

lemma FIXME_perhaps_the_result:
  "tree_chop den = num + den - 2 * (num mod den)"
proof -
  have "tree_chop den = map_tree nat (tree_chop den')"
    by(simp add: map_tree_chop map_nat_den')
  also have "tree_chop den' = num' + den' - tree_chop den' + tree_chop den' - 2 * FIXME_x'"
    by(subst num'_plus_den'_minus_chop_den') simp
  also have "\<dots> = num' + den' - 2 * (num' mod den')"
    by(simp add: FIXME_x'_def num'_def den'_def FIXME_FIXME_x[symmetric])
      (simp add: map_tree_tree_ap_tree_pure[symmetric] arith_tree_defs tree_ap_composition[symmetric] o_def zmod_int)
  also have "\<dots> = map_tree int (num + den - 2 * (num mod den))"
    by(simp add: num'_def den'_def map_tree_plus map_tree_diff[OF FIXME_conversion] den_ge_1 map_tree_times map_tree_mod int_mult zmod_int)
  finally show ?thesis
    by(simp add: tree.map_comp o_def id_def[symmetric] tree.map_id)
qed

subsection{* FIXME loopless linearisation of the Stern-Brocot tree. *}

text{*

FIXME commentary. Loopless?

Dijkstra's fusc function. EWD 570, 578

FIXME how clearly related are they?

FIXME point to the HOLCF rendition.

FIXME again may as well export the def.

*}

definition step :: "nat \<times> nat \<Rightarrow> nat \<times> nat"
where "step = (\<lambda>(n, d). (d, n + d - 2 * (n mod d)))"

definition stern_brocot_loopless :: "fraction stream"
where "stern_brocot_loopless \<equiv> siterate step (1, 1)"

lemma stern_brocot_loopless_rec:
  "stern_brocot_loopless = (1, 1) \<prec> smap step stern_brocot_loopless"
by(rule stream.expand) (simp add: stern_brocot_loopless_def smap_siterate)

definition fusc :: "nat stream"
where "fusc \<equiv> smap fst stern_brocot_loopless"

definition fusc' :: "nat stream"
where "fusc' \<equiv> smap snd stern_brocot_loopless"

lemma fusc_unfold: "fusc = 1 \<prec> fusc'"
unfolding fusc_def fusc'_def
by (subst stern_brocot_loopless_rec) (simp add: stream.map_comp o_def split_def step_def)

lemma smap_conv_st_ap_st_pure: "smap f xs = st_pure f \<box> xs"
by(coinduction arbitrary: xs)(auto)

lemma st_pure_numeral [symmetric]: "numeral n = st_pure (numeral n)"
by(induction n)(simp_all only: numeral.simps plus_stream_def st_ap_composition st_ap_homomorphism one_stream_def)

lemma fusc'_unfold: "fusc' = 1 \<prec> (fusc + fusc' - 2 * (fusc mod fusc'))"
unfolding fusc_def fusc'_def
by(subst stern_brocot_loopless_rec)(simp add: arith_stream_defs st_ap_composition[symmetric] o_def smap_conv_st_ap_st_pure step_def split_def st_pure_numeral[symmetric])

lemma fusc_simps [simp]:
  "shd fusc = 1"
  "stl fusc = fusc'"
by(simp_all add: fusc_unfold)

lemma fusc'_simps [simp]:
  "shd fusc' = 1"
  "stl fusc' = fusc + fusc' - 2 * (fusc mod fusc')"
by(subst fusc'_unfold, simp)+

text{*

FIXME Equivalence of streaming the Stern-Brocot Tree with ...

*}

lemma FIXME_lift_step: "st_pure Pair \<box> ys \<box> (xs + ys - 2 * (xs mod ys)) = st_pure (\<lambda>x y. (y, x + y - 2 * (x mod y))) \<box> xs \<box> ys"
by(coinduction arbitrary: xs ys) auto

lemma fusc_fusc'_iterate: "st_pure Pair \<box> fusc \<box> fusc' = siterate (\<lambda>(n, d). (d, n + d - 2 * (n mod d))) (1, 1)"
apply(rule siterate_unique)
apply(rule stream.expand)
apply(simp add: smap_conv_st_ap_st_pure st_ap_composition[symmetric] o_def FIXME_lift_step)
done

lemma fusc_fusc'_unique:
  assumes xs: "xs = 1 \<prec> xs'"
  and xs': "xs' = 1 \<prec> (xs + xs' - 2 * (xs mod xs'))"
  shows "xs = fusc \<and> xs' = fusc'"
proof -
  have [simp]: "shd xs = 1" "stl xs = xs'"
    "shd xs' = 1" "stl xs' = xs + xs' - 2 * (xs mod xs')"
    using assms by (metis Stream.stream.sel)+
  have eq: "st_pure Pair \<box> xs \<box> xs' = st_pure Pair \<box> fusc \<box> fusc'"
    unfolding fusc_fusc'_iterate
    apply(rule siterate_unique)
    apply(rule stream.expand)
    apply(simp add: FIXME_lift_step st_ap_composition[symmetric] smap_conv_st_ap_st_pure o_def)
    done
  have "smap fst (st_pure Pair \<box> xs \<box> xs') = fusc"
       "smap snd (st_pure Pair \<box> xs \<box> xs') = fusc'"
    unfolding eq smap_conv_st_ap_st_pure
    by (simp_all add: st_ap_composition[symmetric] o_def st_pure_K2_apply)
  then show ?thesis
    by(simp add: smap_conv_st_ap_st_pure st_ap_composition[symmetric] o_def st_pure_K2_apply)
qed

lemma fusc_num: "fusc = stream num"
  and fusc'_den: "fusc' = stream den"
proof -
  have "stream num = fusc \<and> stream den = fusc'"
  proof(rule fusc_fusc'_unique)
    show "stream num = 1 \<prec> stream den"
      by (rule stream.expand) (simp add: den_eq_chop_num)
    show "stream den = 1 \<prec> (stream num + stream den - 2 * (stream num mod stream den))"
      by (rule stream.expand)
         (simp add: FIXME_perhaps_the_result stream_plus stream_minus stream_times stream_mod)
  qed
  then show "fusc = stream num" "fusc' = stream den" by simp_all
qed

theorem stern_brocot_loopless:
  "stream stern_brocot = stern_brocot_loopless" (is "?lhs = ?rhs")
proof -
  have "?lhs = stream (tree_pure Pair \<diamond> num \<diamond> den)" by (simp only: stern_brocot_num_div)
  also have "\<dots> = st_pure Pair \<box> fusc \<box> fusc'" by (simp add: fusc_num fusc'_den)
  also have "\<dots> = ?rhs" by (simp add: stern_brocot_loopless_def step_def fusc_fusc'_iterate)
  finally show ?thesis .
qed

end
