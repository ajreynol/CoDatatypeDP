theory Stream_Arith imports Stream_Applicative_Functor begin

subsection {* Pointwise arithmetic on streams *}

instantiation stream :: (zero) zero begin
definition "0 = pure_stream 0"
instance ..
end

instantiation stream :: (one) one begin
definition "1 = pure_stream 1"
instance ..
end

instantiation stream :: (plus) plus begin
definition "x + y = pure op + \<diamond> x \<diamond> (y :: 'a stream)"
instance ..
end

instantiation stream :: (minus) minus begin
definition "x - y = pure_stream op - \<diamond> x \<diamond> (y :: 'a stream)"
instance ..
end

instantiation stream :: (uminus) uminus begin
definition "uminus = (op \<diamond> (pure uminus) :: 'a stream \<Rightarrow> 'a stream)"
instance ..
end

instantiation stream :: (times) times begin
definition "x * y = pure_stream op * \<diamond> x \<diamond> (y :: 'a stream)"
instance ..
end

instance stream :: (Rings.dvd) Rings.dvd ..

instantiation stream :: ("Divides.div") "Divides.div" begin
definition "x div y = pure_stream op div \<diamond> x \<diamond> (y :: 'a stream)"
definition "x mod y = pure_stream op mod \<diamond> x \<diamond> (y :: 'a stream)"
instance ..
end

lemmas arith_stream_defs =
  zero_stream_def
  one_stream_def
  plus_stream_def
  minus_stream_def
  uminus_stream_def
  times_stream_def
  divide_stream_def
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
  ap_stream_identity'
  ap_stream_homomorphism
  ap_stream_composition[symmetric]
  o_def

instance stream :: (semigroup_add) semigroup_add
by(intro_classes)(simp add: add.assoc[abs_def] arith_stream_defs)

instance stream :: (ab_semigroup_add) ab_semigroup_add
proof(intro_classes)
  fix a b :: "'a stream"
  show "a + b = b + a"
    unfolding arith_stream_defs
    by(subst ap_stream_C_stream[symmetric])(simp add: C_stream_def add.commute)
qed

instance stream :: (semigroup_mult) semigroup_mult
by(intro_classes)(simp add: mult.assoc[abs_def] arith_stream_defs)

instance stream :: (ab_semigroup_mult) ab_semigroup_mult
proof(intro_classes)
  fix a b :: "'a stream"
  show "a * b = b * a"
    unfolding arith_stream_defs
    by(subst ap_stream_C_stream[symmetric])(simp add: C_stream_def mult.commute)
qed

instance stream :: (monoid_add) monoid_add
by(intro_classes)(simp_all add: add_0_left[abs_def] arith_stream_defs)

instance stream :: (comm_monoid_add) comm_monoid_add
by(intro_classes)(simp add: add_0[abs_def] arith_stream_defs)

instance stream :: (cancel_ab_semigroup_add) cancel_ab_semigroup_add
proof
  fix a b :: "'a stream"
  have "a + b - a = \<^bold>S \<diamond> (pure op \<circ> \<diamond> \<^bold>C \<diamond> (pure ((op \<circ> op -) \<circ> op +))) \<diamond> \<^bold>I \<diamond> a \<diamond> b"
    unfolding ap_stream_S_stream ap_stream_composition ap_stream_C_stream arith_stream_defs ap_stream_I_stream
    by simp
  also have "\<dots> = \<^bold>C \<diamond> \<^bold>K \<diamond> a \<diamond> b"
    by(simp add: K_stream_def S_stream_def C_stream_def I_stream_def)
  also have "\<dots> = b" unfolding ap_stream_C_stream ap_stream_K_stream by simp
  finally show "a + b - a = b" .
qed(simp add: add_0[abs_def] diff_diff_add[abs_def] zero_diff[abs_def] arith_stream_defs)

instance stream :: (cancel_semigroup_add) cancel_semigroup_add
proof(intro_classes)
  fix a b c :: "'a stream"
  assume "a + b = a + c"
  hence "pure op = \<diamond> (a + b) \<diamond> (a + c) = pure True"
    by(simp add: stream_eq_conv_pure)
  hence "\<^bold>S \<diamond> (\<^bold>C \<diamond> (pure op \<circ> \<diamond> (pure op \<circ> \<diamond> pure op =) \<diamond> pure op +) \<diamond> b) \<diamond> (\<^bold>C \<diamond> pure op + \<diamond> c) \<diamond> a = pure True"
    unfolding ap_stream_S_stream ap_stream_C_stream by(simp add: arith_stream_defs)
  hence "\<^bold>K \<diamond> (pure op = \<diamond> b \<diamond> c) \<diamond> a = pure True"
    by(simp add: S_stream_def C_stream_def K_stream_def)
  thus "b = c" unfolding ap_stream_K_stream
    by(simp add: stream_eq_conv_pure)
next
  fix a b c :: "'a stream"
  assume "b + a = c + a"
  hence "pure op = \<diamond> (b + a) \<diamond> (c + a) = pure True"
    by(simp add: stream_eq_conv_pure)
  hence "\<^bold>S \<diamond> (pure op \<circ> \<diamond> (pure op \<circ> \<diamond> pure op =) \<diamond> pure op + \<diamond> b) \<diamond> (pure op + \<diamond> c) \<diamond> a = pure True"
    unfolding ap_stream_S_stream arith_stream_defs by simp
  hence "\<^bold>K \<diamond> (pure op = \<diamond> b \<diamond> c) \<diamond> a = pure True"
    by(simp add: S_stream_def C_stream_def K_stream_def)
  thus "b = c" unfolding ap_stream_K_stream
    by(simp add: stream_eq_conv_pure)
qed

instance stream :: (cancel_comm_monoid_add) cancel_comm_monoid_add ..

instance stream :: (comm_monoid_diff) comm_monoid_diff
by intro_classes(simp add: add_0[abs_def] diff_diff_add[abs_def] zero_diff[abs_def] pure_K_stream_apply arith_stream_defs)

instance stream :: (monoid_mult) monoid_mult
by(intro_classes)(simp_all add: mult_1_left[abs_def] arith_stream_defs)

instance stream :: (comm_monoid_mult) comm_monoid_mult
by(intro_classes)(simp_all add: mult_1[abs_def])

instance stream :: (group_add) group_add
by intro_classes(simp_all add: arith_stream_defs)

instance stream :: (ab_group_add) ab_group_add
by intro_classes(simp_all)

instance stream :: (semiring) semiring
proof intro_classes
  fix a b c :: "'a stream"
  have "(a + b) * c = \<^bold>S \<diamond> (pure op \<circ> \<diamond> pure op + \<diamond> (pure op * \<diamond> a)) \<diamond> (pure op * \<diamond> b) \<diamond> c"
    unfolding arith_stream_defs by(simp add: S_stream_def distrib_right[abs_def])
  also have "\<dots> = a * c + b * c"
    unfolding arith_stream_defs ap_stream_S_stream by simp
  finally show "(a + b) * c = a * c + b * c" .

  have "a * (b + c) = \<^bold>C \<diamond> \<^bold>C \<diamond> a \<diamond> (\<^bold>S \<diamond> (pure op \<circ> \<diamond> pure op + \<diamond> (\<^bold>C \<diamond> pure op * \<diamond> b))) \<diamond> (\<^bold>C \<diamond> pure op * \<diamond> c)"
    unfolding arith_stream_defs C_stream_def S_stream_def by(simp add: distrib_left) 
  also have "\<dots> = a * b + a * c"
    unfolding arith_stream_defs ap_stream_C_stream ap_stream_S_stream ap_stream_composition by simp
  finally show "a * (b + c) = a * b + a * c" .
qed

instance stream :: (mult_zero) mult_zero
by intro_classes(simp_all add: mult_zero_left[abs_def] arith_stream_defs)

instance stream :: (semiring_0) semiring_0 ..

instance stream :: (semiring_0_cancel) semiring_0_cancel ..

instance stream :: (comm_semiring) comm_semiring
by intro_classes(rule distrib_right)

instance stream :: (comm_semiring_0) comm_semiring_0 ..

instance stream :: (comm_semiring_0_cancel) comm_semiring_0_cancel ..

lemma pure_stream_inject [simp]: "pure_stream x = pure_stream y \<longleftrightarrow> x = y"
by(subst (15 17) shd_pure_stream[symmetric])(auto simp del: shd_pure_stream, simp)

instance stream :: (zero_neq_one) zero_neq_one
by intro_classes(simp add: arith_stream_defs)

instance stream :: (semiring_1) semiring_1 ..

instance stream :: (comm_semiring_1) comm_semiring_1 ..

instance stream :: (semiring_1_cancel) semiring_1_cancel ..

instance stream :: (comm_semiring_1_cancel) comm_semiring_1_cancel
proof
  fix a b c :: "'a stream"
  have "a * (b - c) = \<^bold>S \<diamond> (pure op \<circ> \<diamond> \<^bold>C \<diamond> (pure op \<circ> \<diamond> (pure op \<circ> \<diamond> pure op \<circ>) \<diamond> (pure op \<circ> \<diamond> (pure op \<circ> \<diamond> pure op -) \<diamond> pure op *))) \<diamond> pure op * \<diamond> a \<diamond> b \<diamond> c"
    unfolding S_stream_def C_stream_def by(simp add: arith_stream_defs right_diff_distrib')
  also have "\<dots> = a * b - a * c"
    unfolding ap_stream_S_stream ap_stream_composition ap_stream_C_stream
    by(simp add: arith_stream_defs)
  finally show "a * (b - c) = a * b - a * c" .
qed

instance stream :: (ring) ring ..

instance stream :: (comm_ring) comm_ring ..

instance stream :: (ring_1) ring_1 ..

instance stream :: (comm_ring_1) comm_ring_1 ..

instance stream :: (numeral) numeral ..

instance stream :: (neg_numeral) neg_numeral ..

instance stream :: (semiring_numeral) semiring_numeral ..

lemma of_nat_stream: "of_nat n = pure_stream (of_nat n)"
apply(induct n)
apply(simp add: arith_stream_defs id_def)
by (metis of_nat_Suc one_stream_def plus_stream_def ap_stream_homomorphism)

instance stream :: (semiring_char_0) semiring_char_0
by intro_classes(simp add: inj_on_def of_nat_stream)

instance stream :: (ring_char_0) ring_char_0 ..

lemma numeral_stream_simps [simp]:
  "shd (numeral n) = numeral n"
  "stl (numeral n) = numeral n"
by(induct n)(auto simp add: numeral.simps arith_stream_defs)

lemmas [simp del] =
  ap_stream_composition[symmetric]
  o_def

end
