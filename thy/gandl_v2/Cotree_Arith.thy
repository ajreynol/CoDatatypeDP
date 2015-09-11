theory Cotree_Arith imports Cotree begin

subsection {* Arithmetic on @{typ "'a tree"} *}

text{*
  We instantiate the algebraic arithmetic hierarchy via the applicative functor machinery.
*}

instantiation tree :: (zero) zero begin
definition "0 = pure_tree 0"
instance ..
end

instantiation tree :: (one) one begin
definition "1 = pure_tree 1"
instance ..
end

instantiation tree :: (plus) plus begin
definition "plus x y = pure op + \<diamond> x \<diamond> (y :: 'a tree)"
(* \<diamond> :: ('a \<Rightarrow> 'a \<Rightarrow> 'a) tree \<Rightarrow> 'a tree \<Rightarrow> ('a \<Rightarrow> 'a) tree *)
(* \<diamond> :: ('a \<Rightarrow> 'a) tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree *)
instance ..
end

instantiation tree :: (minus) minus begin
definition "minus x y = pure op - \<diamond> x \<diamond> (y :: 'a tree)"
instance ..
end

instantiation tree :: (uminus) uminus begin
definition "uminus = (op \<diamond> (pure uminus) :: 'a tree \<Rightarrow> 'a tree)"
instance ..
end

instantiation tree :: (times) times begin
definition "times x y = pure op * \<diamond> x \<diamond> (y :: 'a tree)"
instance ..
end

instance tree :: (Rings.dvd) Rings.dvd ..

instantiation tree :: (Divides.div) Divides.div begin
definition "x div y = pure_tree op div \<diamond> x \<diamond> (y :: 'a tree)"
definition "x mod y = pure_tree op mod \<diamond> x \<diamond> (y :: 'a tree)"
instance ..
end

lemmas arith_tree_defs =
  zero_tree_def
  one_tree_def
  plus_tree_def
  minus_tree_def
  uminus_tree_def
  times_tree_def
  divide_tree_def
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
  ap_tree_composition[symmetric]
  o_def
  ap_tree_homomorphism
  ap_tree_identity[unfolded id_def]

lemma pure_tree_inject: "pure x = pure y \<longleftrightarrow> x = y"
by(subst (1 2) pure_tree_unfold)(auto)

instance tree :: (semigroup_add) semigroup_add
by(intro_classes)(simp add: add.assoc[abs_def] arith_tree_defs)

instance tree :: (ab_semigroup_add) ab_semigroup_add
proof(intro_classes)
  fix t t' :: "'a tree"
  show "t + t' = t' + t"
    unfolding arith_tree_defs
    by(subst ap_tree_C_tree[symmetric])(simp add: C_tree_def add.commute)
qed

instance tree :: (semigroup_mult) semigroup_mult
by(intro_classes)(simp add: arith_tree_defs mult.assoc[abs_def])

instance tree :: (ab_semigroup_mult) ab_semigroup_mult
proof(intro_classes)
  fix t t' :: "'a tree"
  show "t * t' = t' * t"
    unfolding arith_tree_defs
    by(subst ap_tree_C_tree[symmetric])(simp add: C_tree_def mult.commute)
qed

instance tree :: (monoid_add) monoid_add
by(intro_classes)(simp_all add: add_0_left[abs_def] arith_tree_defs)

instance tree :: (comm_monoid_add) comm_monoid_add
by(intro_classes)(simp add: add_0[abs_def])

instance tree :: (cancel_ab_semigroup_add) cancel_ab_semigroup_add
proof
  fix t t' :: "'a tree"
  have "t + t' - t = \<^bold>S \<diamond> (pure op \<circ> \<diamond> \<^bold>C \<diamond> (pure ((op \<circ> op -) \<circ> op +))) \<diamond> \<^bold>I \<diamond> t \<diamond> t'"
    unfolding ap_tree_S_tree ap_tree_composition ap_tree_C_tree arith_tree_defs ap_tree_I_tree
    by simp
  also have "\<dots> = \<^bold>C \<diamond> \<^bold>K \<diamond> t \<diamond> t'"
    by(simp add: K_tree_def S_tree_def C_tree_def I_tree_def)
  also have "\<dots> = t'" unfolding ap_tree_C_tree ap_tree_K_tree by simp
  finally show "t + t' - t = t'" .
qed(simp add: add_0[abs_def] diff_diff_add[abs_def] zero_diff[abs_def] arith_tree_defs)

instance tree :: (cancel_semigroup_add) cancel_semigroup_add
proof(intro_classes)
  fix a b c :: "'a tree"
  assume "a + b = a + c"
  hence "pure op = \<diamond> (a + b) \<diamond> (a + c) = pure True"
    by(simp add: tree_eq_conv_pure)
  hence "\<^bold>S \<diamond> (\<^bold>C \<diamond> (pure op \<circ> \<diamond> (pure op \<circ> \<diamond> pure op =) \<diamond> pure op +) \<diamond> b) \<diamond> (\<^bold>C \<diamond> pure op + \<diamond> c) \<diamond> a = pure True"
    unfolding ap_tree_S_tree ap_tree_C_tree by(simp add: arith_tree_defs)
  hence "\<^bold>K \<diamond> (pure op = \<diamond> b \<diamond> c) \<diamond> a = pure True"
    by(simp add: S_tree_def C_tree_def K_tree_def)
  thus "b = c" unfolding ap_tree_K_tree
    by(simp add: tree_eq_conv_pure)
next
  fix a b c :: "'a tree"
  assume "b + a = c + a"
  hence "pure op = \<diamond> (b + a) \<diamond> (c + a) = pure True"
    by(simp add: tree_eq_conv_pure)
  hence "\<^bold>S \<diamond> (pure op \<circ> \<diamond> (pure op \<circ> \<diamond> pure op =) \<diamond> pure op + \<diamond> b) \<diamond> (pure op + \<diamond> c) \<diamond> a = pure True"
    unfolding ap_tree_S_tree arith_tree_defs by simp
  hence "\<^bold>K \<diamond> (pure op = \<diamond> b \<diamond> c) \<diamond> a = pure True"
    by(simp add: S_tree_def C_tree_def K_tree_def)
  thus "b = c" unfolding ap_tree_K_tree
    by(simp add: tree_eq_conv_pure)
qed

instance tree :: (cancel_comm_monoid_add) cancel_comm_monoid_add ..

instance tree :: (comm_monoid_diff) comm_monoid_diff
by intro_classes(simp add: add_0[abs_def] diff_diff_add[abs_def] zero_diff[abs_def] pure_K_tree_apply arith_tree_defs)

instance tree :: (monoid_mult) monoid_mult
by(intro_classes)(simp_all add: mult_1_left[abs_def] arith_tree_defs)

instance tree :: (comm_monoid_mult) comm_monoid_mult
by(intro_classes)(simp_all add: mult_1[abs_def])

instance tree :: (group_add) group_add
by intro_classes(simp_all add: arith_tree_defs ap_tree_same2 pure_K_tree_apply)

instance tree :: (ab_group_add) ab_group_add
by intro_classes(simp_all add: arith_tree_defs ap_tree_same2 pure_K_tree_apply)

instance tree :: (semiring) semiring
proof intro_classes
  fix a b c :: "'a tree"
  have "(a + b) * c = \<^bold>S \<diamond> (pure op \<circ> \<diamond> pure op + \<diamond> (pure op * \<diamond> a)) \<diamond> (pure op * \<diamond> b) \<diamond> c"
    unfolding arith_tree_defs by(simp add: S_tree_def distrib_right[abs_def])
  also have "\<dots> = a * c + b * c"
    unfolding arith_tree_defs ap_tree_S_tree by simp
  finally show "(a + b) * c = a * c + b * c" .

  have "a * (b + c) = \<^bold>C \<diamond> \<^bold>C \<diamond> a \<diamond> (\<^bold>S \<diamond> (pure op \<circ> \<diamond> pure op + \<diamond> (\<^bold>C \<diamond> pure op * \<diamond> b))) \<diamond> (\<^bold>C \<diamond> pure op * \<diamond> c)"
    unfolding arith_tree_defs C_tree_def S_tree_def by(simp add: distrib_left) 
  also have "\<dots> = a * b + a * c"
    unfolding arith_tree_defs ap_tree_C_tree ap_tree_S_tree ap_tree_composition by simp
  finally show "a * (b + c) = a * b + a * c" .
qed

instance tree :: (mult_zero) mult_zero
by intro_classes(simp_all add: mult_zero_left[abs_def] arith_tree_defs pure_K_tree_apply)

instance tree :: (semiring_0) semiring_0 ..

instance tree :: (semiring_0_cancel) semiring_0_cancel ..

instance tree :: (comm_semiring) comm_semiring
by intro_classes(rule distrib_right)

instance tree :: (comm_semiring_0) comm_semiring_0 ..

instance tree :: (comm_semiring_0_cancel) comm_semiring_0_cancel ..

instance tree :: (zero_neq_one) zero_neq_one
by intro_classes(simp add: arith_tree_defs pure_tree_inject)

instance tree :: (semiring_1) semiring_1 ..

instance tree :: (comm_semiring_1) comm_semiring_1 ..

instance tree :: (semiring_1_cancel) semiring_1_cancel ..

instance tree :: (comm_semiring_1_cancel) comm_semiring_1_cancel
proof
  fix a b c :: "'a tree"
  have "a * (b - c) = \<^bold>S \<diamond> (pure op \<circ> \<diamond> \<^bold>C \<diamond> (pure op \<circ> \<diamond> (pure op \<circ> \<diamond> pure op \<circ>) \<diamond> (pure op \<circ> \<diamond> (pure op \<circ> \<diamond> pure op -) \<diamond> pure op *))) \<diamond> pure op * \<diamond> a \<diamond> b \<diamond> c"
    unfolding S_tree_def C_tree_def by(simp add: arith_tree_defs right_diff_distrib')
  also have "\<dots> = a * b - a * c"
    unfolding ap_tree_S_tree ap_tree_composition ap_tree_C_tree
    by(simp add: arith_tree_defs)
  finally show "a * (b - c) = a * b - a * c" .
qed

instance tree :: (ring) ring ..

instance tree :: (comm_ring) comm_ring ..

instance tree :: (ring_1) ring_1 ..

instance tree :: (comm_ring_1) comm_ring_1 ..

instance tree :: (numeral) numeral ..

lemma numeral_tree_def: "(numeral t :: _ tree) = pure (numeral t)" (* move to cotree_arith *)
by(induction t)(simp_all only: numeral.simps plus_tree_def ap_tree_homomorphism one_tree_def)

instance tree :: (neg_numeral) neg_numeral ..

instance tree :: (semiring_numeral) semiring_numeral ..

lemma of_nat_Tree: "of_nat n = pure_tree (of_nat n)"
by(induct n)(simp_all add: arith_tree_defs)

instance tree :: (semiring_char_0) semiring_char_0
by intro_classes(simp add: inj_on_def of_nat_Tree pure_tree_inject)

instance tree :: (ring_char_0) ring_char_0 ..

lemma numeral_tree_simps [simp]:
  "root (numeral n) = numeral n"
  "left (numeral n) = numeral n"
  "right (numeral n) = numeral n"
by(induct n)(auto simp add: numeral.simps arith_tree_defs)

lemmas [simp del] =
  ap_tree_composition[symmetric]
  o_def

end
