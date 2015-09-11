theory Cotree imports 
  Main
  Applicative_Functor
begin

section {* A codatatype of infinite binary trees *}

context notes [[bnf_note_all]] begin
codatatype 'a tree = Node (root: 'a) (left: "'a tree") (right: "'a tree")
end

lemma rel_treeD:
  assumes "rel_tree A x y"
  shows rel_tree_rootD: "A (root x) (root y)"
  and rel_tree_leftD: "rel_tree A (left x) (left y)"
  and rel_tree_rightD: "rel_tree A (right x) (right y)"
using assms
by(cases x y rule: tree.exhaust[case_product tree.exhaust], simp_all)+

lemmas map_tree_sels [simp] = tree.map_sel

lemma root_in_set_tree: "root y \<in> set_tree y"
by(fact tree.set_sel)

lemma in_set_tree_left: "x \<in> set_tree (left y) \<Longrightarrow> x \<in> set_tree y"
by(fact tree.set_sel)

lemma right_in_set_tree: "x \<in> set_tree (right y) \<Longrightarrow> x \<in> set_tree y"
by(fact tree.set_sel)

lemma set_tree_induct[consumes 1, case_names root left right]:
  assumes x: "x \<in> set_tree t"
  and root: "\<And>t. P (root t) t"
  and left: "\<And>x t. \<lbrakk> x \<in> set_tree (left t); P x (left t) \<rbrakk> \<Longrightarrow> P x t"
  and right: "\<And>x t. \<lbrakk> x \<in> set_tree (right t); P x (right t) \<rbrakk> \<Longrightarrow> P x t"
  shows "P x t"
using x
proof(rule tree.set_induct)
  fix l x r
  from root[of "Node x l r"] show "P x (Node x l r)" by simp
qed(auto intro: left right)

context 
  fixes g1 :: "'a \<Rightarrow> 'b"
  and g22 :: "'a \<Rightarrow> 'a"
  and g32 :: "'a \<Rightarrow> 'a"
begin

primcorec unfold_tree :: "'a \<Rightarrow> 'b tree"
where "unfold_tree a = Node (g1 a) (unfold_tree (g22 a)) (unfold_tree (g32 a))"

end

lemma map_tree_unfold_tree:
  "map_tree f (unfold_tree out l r x) = unfold_tree (f \<circ> out) l r x"
by(coinduction arbitrary: x) auto


subsection {* Applicative functor for @{typ "'a tree"} *}

primcorec pure_tree :: "'a \<Rightarrow> 'a tree"
where "pure_tree x = Node x (pure_tree x) (pure_tree x)"

lemmas pure_tree_unfold = pure_tree.ctr
   and pure_tree_simps = pure_tree.simps

adhoc_overloading pure pure_tree

lemma map_pure_tree [simp]: "map_tree f (pure x) = pure (f x)"
by(coinduction arbitrary: x) auto

primcorec ap_tree :: "('a \<Rightarrow> 'b) tree \<Rightarrow> 'a tree \<Rightarrow> 'b tree"
where
  "root (ap_tree f x) = root f (root x)"
| "left (ap_tree f x) = ap_tree (left f) (left x)"
| "right (ap_tree f x) = ap_tree (right f) (right x)"

adhoc_overloading Applicative_Functor.ap ap_tree

lemma map_tree_ap_tree_pure_tree:
  "pure f \<diamond> u = map_tree f u"
by(coinduction arbitrary: u) auto

lemma ap_tree_pure_Node [simp]:
  "pure f \<diamond> Node x l r = Node (f x) (pure f \<diamond> l) (pure f \<diamond> r)"
by(rule tree.expand) auto

lemma ap_tree_Node_Node [simp]:
  "Node f fl fr \<diamond> Node x l r = Node (f x) (fl \<diamond> l) (fr \<diamond> r)"
by(rule tree.expand) auto

text {* Applicative functor laws *}

lemma ap_tree_identity: "pure id \<diamond> t = t"
by(simp add: map_tree_ap_tree_pure_tree tree.map_id)

lemma ap_tree_composition:
  "pure (op \<circ>) \<diamond> r1 \<diamond> r2 \<diamond> r3 = r1 \<diamond> (r2 \<diamond> r3)"
by(coinduction arbitrary: r1 r2 r3) auto

lemma ap_tree_homomorphism:
  "pure f \<diamond> pure x = pure (f x)"
by(simp add: map_tree_ap_tree_pure_tree)

lemma ap_tree_interchange:
  "t \<diamond> pure x = pure (\<lambda>f. f x) \<diamond> t"
by(coinduction arbitrary: t) auto

(* FIXME: Replace with NO_MATCH in repository version *)
simproc_setup ap_tree_interchange ("x \<diamond> pure y") = {*
  fn phi => fn ctxt => fn redex => case Thm.term_of redex of
      Const (@{const_name ap_tree}, _) $ Const (@{const_name pure}, _) $ _ => NONE
    | _ => SOME @{thm ap_tree_interchange[folded atomize_eq]}
*}

lemma ap_tree_strong_extensional:
  "(\<And>x. f \<diamond> pure x = g \<diamond> pure x) \<Longrightarrow> f = g"
proof(coinduction arbitrary: f g)
  case [rule_format]: (Eq_tree f g)
  have "root f = root g"
  proof
    fix x
    show "root f x = root g x"
      using Eq_tree[of x] by(subst (asm) (1 2) ap_tree.ctr) simp
  qed
  moreover {
    fix x
    have "left f \<diamond> pure x = left g \<diamond> pure x"
      using Eq_tree[of x] by(subst (asm) (1 2) ap_tree.ctr) simp
  } moreover {
    fix x
    have "right f \<diamond> pure x = right g \<diamond> pure x"
      using Eq_tree[of x] by(subst (asm) (1 2) ap_tree.ctr) simp
  } ultimately show ?case by simp
qed

lemma ap_tree_extensional:
  "(\<And>x. f \<diamond> x = g \<diamond> x) \<Longrightarrow> f = g"
by(rule ap_tree_strong_extensional) simp

subsubsection {* Combinatory model *}

definition K_tree :: "('a \<Rightarrow> 'b \<Rightarrow> 'a) tree"
where "K_tree = pure (\<lambda>x _. x)"

adhoc_overloading Applicative_Functor.K K_tree

definition S_tree :: "(('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c) tree"
where "S_tree = pure (\<lambda>f g x. f x (g x))"

adhoc_overloading Applicative_Functor.S S_tree

definition I_tree :: "('a \<Rightarrow> 'a) tree"
where "I_tree = pure id"

adhoc_overloading Applicative_Functor.I I_tree

lemma I_tree_conv_SKK: "\<^bold>I = \<^bold>S \<diamond> \<^bold>K \<diamond> \<^bold>K"
by(simp only: S_tree_def K_tree_def I_tree_def id_def ap_tree_homomorphism)

lemma ap_tree_K_tree: "\<^bold>K \<diamond> u \<diamond> v = u"
by(coinduction arbitrary: u v)(auto simp add: K_tree_def)

lemma ap_tree_S_tree: "\<^bold>S \<diamond> u \<diamond> v \<diamond> w = (u \<diamond> w) \<diamond> (v \<diamond> w)"
by(coinduction arbitrary: u v w)(auto simp add: S_tree_def)

lemma ap_tree_I_tree: "\<^bold>I \<diamond> x = x"
by(subst I_tree_conv_SKK)(simp add: ap_tree_S_tree ap_tree_K_tree)

lemma pure_const: "pure (\<lambda>_. c) = \<^bold>K \<diamond> pure c"
by(simp only: K_tree_def ap_tree_homomorphism)

lemma pure_id: "pure (\<lambda>x. x) = \<^bold>I"
by(simp add: I_tree_def id_def)

lemma pure_ap_treep: "pure (\<lambda>x. (f x) (g x)) = \<^bold>S \<diamond> pure f \<diamond> pure g"
by(simp only: S_tree_def ap_tree_homomorphism)

lemma pure_K_tree_apply:
  "pure (\<lambda>_. c) \<diamond> x = pure c"
by(simp only: ap_tree_K_tree pure_const)

lemma ap_tree_same2: 
  fixes f :: "('b \<Rightarrow> 'b \<Rightarrow> 'a) tree"
  shows "f \<diamond> x \<diamond> x = pure (\<lambda>f x. f x x) \<diamond> f \<diamond> x"
using ap_tree_S_tree[of "f" "pure (id :: 'b \<Rightarrow> 'b)" x, symmetric]
by(simp add: ap_tree_identity S_tree_def ap_tree_homomorphism o_def ap_tree_composition[symmetric])

definition C_tree :: "(('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c) tree"
where "C_tree = pure (\<lambda>f x y. f y x)"

adhoc_overloading Applicative_Functor.C C_tree

lemma ap_tree_C_tree: "\<^bold>C \<diamond> u \<diamond> v \<diamond> w = u \<diamond> w \<diamond> v"
by(coinduction arbitrary: u v w)(auto simp add: C_tree_def)

text {*
  With combinators, we get that logical equality of trees can be expressed in terms of
  point-wise equality of the trees. Note that we need all combinators K, S and C.
  This allows the combinators to operate on both sides of the equality simultaneously. 
*}

lemma tree_eq_conv_pure:
  notes [simp] = ap_tree_composition[symmetric] o_def ap_tree_homomorphism
  shows "pure op = \<diamond> t \<diamond> t' = pure True \<longleftrightarrow> t = t'" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  have "pure op = \<diamond> t \<diamond> (\<^bold>I \<diamond> t) = \<^bold>K \<diamond> pure True \<diamond> t"
    by(subst ap_tree_S_tree[symmetric])(simp add: S_tree_def I_tree_def K_tree_def)
  thus ?lhs using \<open>?rhs\<close> unfolding ap_tree_K_tree by(simp add: I_tree_def)
next
  assume ?lhs

  have "t = \<^bold>K \<diamond> t \<diamond> t'" by(simp add: ap_tree_K_tree)
  also have "\<dots> = pure (\<lambda>x y. if x = y then y else x) \<diamond> t \<diamond> t'" by(simp add: K_tree_def)
  also have "\<dots> = \<^bold>S \<diamond> (pure (\<lambda>x y1 y2. if x = y1 then y2 else x) \<diamond> t) \<diamond> \<^bold>I \<diamond> t'"
    unfolding S_tree_def I_tree_def by(simp cong: if_cong)
  also have "\<dots> = (pure (\<lambda>x y1 y2. if x = y1 then y2 else x) \<diamond> t) \<diamond> t' \<diamond> t'"
    unfolding ap_tree_S_tree by(simp add: ap_tree_identity ap_tree_I_tree)
  also have "\<dots> = (S_tree \<diamond> (pure (\<lambda>x1 x2 y1 y2. if x1 = y1 then y2 else x2)) \<diamond> \<^bold>I \<diamond> t) \<diamond> t' \<diamond> t'"
    unfolding S_tree_def I_tree_def by(simp cong: if_cong)
  also have "\<dots> = pure (\<lambda>x1 x2 y1 y2. if x1 = y1 then y2 else x2) \<diamond> t \<diamond> t \<diamond> t' \<diamond> t'"
    unfolding ap_tree_S_tree by(simp add: ap_tree_identity ap_tree_I_tree)
  also have "\<dots> = \<^bold>C \<diamond> (pure (\<lambda>x1 x2 y1 y2. if x1 = y1 then y2 else x2) \<diamond> t) \<diamond> t' \<diamond> t \<diamond> t'"
    unfolding ap_tree_C_tree ..
  also have "\<dots> = pure (\<lambda>b x2 y2. if b then y2 else x2) \<diamond> (pure op = \<diamond> t \<diamond> t') \<diamond> t \<diamond> t'"
    by(simp add: C_tree_def)
  also have "\<dots> = pure (\<lambda>b x2 y2. if b then y2 else x2) \<diamond> pure True \<diamond> t \<diamond> t'"
    unfolding \<open>?lhs\<close> ..
  also have "\<dots> = \<^bold>C \<diamond> \<^bold>K \<diamond> t \<diamond> t'" by(simp add: C_tree_def K_tree_def)
  also have "\<dots> = t'" by(simp add: ap_tree_C_tree ap_tree_K_tree)
  finally show ?rhs .
qed

subsection {* Standard tree combinators *}

subsubsection {* Recurse combinator *}

text {*
  This will be the main combinator to define trees recursively

  Uniqueness for this gives us the unique fixed-point theorem for guarded recursive definitions.
*}
lemma map_unfold_tree [simp]: fixes l r x
 defines "unf \<equiv> unfold_tree (\<lambda>f. f x) (\<lambda>f. f \<circ> l) (\<lambda>f. f \<circ> r)"
 shows "map_tree G (unf F) = unf (G \<circ> F)"
by(coinduction arbitrary: F G)(auto 4 3 simp add: unf_def o_assoc)

definition tree_recurse :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a tree"
where "tree_recurse l r x \<equiv> unfold_tree (\<lambda>f. f x) (\<lambda>f. f \<circ> l) (\<lambda>f. f \<circ> r) id"

lemma tree_recurse_ap:
  "tree_recurse l r x = unfold_tree id (\<lambda>f. f \<circ> l) (\<lambda>f. f \<circ> r) id \<diamond> pure x"
by(simp add: ap_tree_interchange map_tree_ap_tree_pure_tree map_tree_unfold_tree tree_recurse_def)

lemma tree_recurse_simps:
  "root (tree_recurse l r x) = x"
  "left (tree_recurse l r x) = map_tree l (tree_recurse l r x)"
  "right (tree_recurse l r x) = map_tree r (tree_recurse l r x)"
unfolding tree_recurse_def by simp_all

lemma tree_recurse_unfold:
  "tree_recurse l r x = Node x (map_tree l (tree_recurse l r x)) (map_tree r (tree_recurse l r x))"
by(rule tree.expand)(simp add: tree_recurse_simps)

lemma tree_recurse_unique':
  assumes A: "t = Node x (map_tree l t) (map_tree r t)"
  shows "map_tree H t = unfold_tree (\<lambda>f. f x) (\<lambda>f. f \<circ> l) (\<lambda>f. f \<circ> r) H"
unfolding unfold_tree_def corec_tree_def
apply(subst tree.dtor_corec_unique[where fc="\<lambda>f. map_tree f t", symmetric])
 apply(simp add: fun_eq_iff map_pre_tree_def)
 apply(subst (3) A)
 apply(clarsimp simp add: BNF_Composition.id_bnf_def)
 apply(simp_all add: Node_def tree.dtor_ctor tree.map_comp BNF_Composition.id_bnf_def)
done

(*
tree_recurse l r x = Node x (map_tree l (tree_recurse l r x)) (map_tree r (tree_recurse l r x))
*)

lemma tree_recurse_unique:
  "t = Node x (map_tree l t) (map_tree r t) 
  \<Longrightarrow> t = tree_recurse l r x"
unfolding tree_recurse_def
by (rule tree_recurse_unique'[where H=id, unfolded tree.map_id])

lemma tree_recurse_fusion:
  assumes "h \<circ> l = l' \<circ> h" and "h \<circ> r = r' \<circ> h"
  shows "map_tree h (tree_recurse l r x) = tree_recurse l' r' (h x)"
by(rule tree_recurse_unique)(simp add: tree.expand tree_recurse_simps tree.map_comp assms)

subsubsection {* Tree iteration *}

primcorec tree_iterate :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a tree"
where
  "root (tree_iterate l r s) = s"
| "left (tree_iterate l r s) = tree_iterate l r (l s)"
| "right (tree_iterate l r s) = tree_iterate l r (r s)"

lemma tree_iterate_unfold:
  "tree_iterate l r s = Node s (tree_iterate l r (l s)) (tree_iterate l r (r s))"
by(fact tree_iterate.code)

lemma unfold_tree_tree_iterate:
  "unfold_tree out l r = map_tree out \<circ> tree_iterate l r"
apply(clarsimp simp: fun_eq_iff tree_iterate_def)
apply coinduction
apply auto
done

lemma tree_iterate_fusion:
  assumes "h \<circ> l = l' \<circ> h"
  assumes "h \<circ> r = r' \<circ> h"
  shows "map_tree h (tree_iterate l r x) = tree_iterate l' r' (h x)"
apply(coinduction arbitrary: x)
using assms by(auto simp add: fun_eq_iff)

subsubsection {* Tree traversal *}

datatype dir = L | R
type_synonym path = "dir list"

definition traverse_tree :: "path \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
where "traverse_tree path \<equiv> foldr (\<lambda>d f. f \<circ> case_dir left right d) path id"

lemma traverse_tree_simps[simp]:
  "traverse_tree [] = id"
  "traverse_tree (d # path) = traverse_tree path \<circ> (case d of L \<Rightarrow> left | R \<Rightarrow> right)"
by (simp_all add: traverse_tree_def)

lemma traverse_tree_map_tree:
  "traverse_tree path (map_tree f t) = map_tree f (traverse_tree path t)"
by (induct path arbitrary: t) (simp_all split: dir.splits)

text{* @{const "traverse_tree"} is an applicative-functor homomorphism. *}

lemma traverse_tree_pure_tree:
  "traverse_tree path (pure x) = pure x"
by (induct path arbitrary: x) (simp_all split: dir.splits)

lemma traverse_tree_ap:
  "traverse_tree path (f \<diamond> x) = traverse_tree path f \<diamond> traverse_tree path x"
by (induct path arbitrary: f x) (simp_all split: dir.splits)

lemma traverse_tree_append:
  "traverse_tree (path @ ext) t = traverse_tree ext (traverse_tree path t)"
by (induct path arbitrary: t) simp_all

lemmas traverse_pure_ap_tree_simps [simp] =
  traverse_tree_map_tree
  traverse_tree_pure_tree
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
apply(rule tree_recurse_unique[symmetric])
apply(rule tree.expand)
apply(simp add: tree_iterate_fusion[where r'="\<lambda>x. f x r" and l'="\<lambda>x. f x l"] fun_eq_iff monoid)
done

subsection {* Mirroring *}

primcorec mirror :: "'a tree \<Rightarrow> 'a tree"
where
  "root (mirror t) = root t"
| "left (mirror t) = mirror (right t)"
| "right (mirror t) = mirror (left t)"

lemma mirror_unfold: "mirror (Node x l r) = Node x (mirror r) (mirror l)"
by(rule tree.expand) simp

lemma mirror_pure: "mirror (pure x) = pure x"
by(coinduction rule: tree.coinduct) simp

lemma mirror_ap_tree: "mirror (f \<diamond> x) = mirror f \<diamond> mirror x"
by(coinduction arbitrary: f x) auto

end
