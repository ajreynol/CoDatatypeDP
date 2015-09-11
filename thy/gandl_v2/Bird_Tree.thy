theory Bird_Tree imports Stern_Brocot_Tree begin

definition bird :: "fraction tree"
where "bird = tree_recurse (inverse' o succ) (succ o inverse') (1, 1)"

lemma bird_unfold:
  "bird = Node (1, 1) (pure inverse' \<diamond> (pure succ \<diamond> bird)) (pure succ \<diamond> (pure inverse' \<diamond> bird))"
by(auto simp add: bird_def tree_recurse_def map_tree_ap_tree_pure_tree intro: tree.expand)

lemma bird_simps:
  "root bird = (1, 1)"
  "left bird = pure inverse' \<diamond> (pure succ \<diamond> bird)"
  "right bird = pure succ \<diamond> (pure inverse' \<diamond> bird)"
by(subst bird_unfold, simp)+

lemma inverse'_inverse': "inverse' \<circ> inverse' = id"
by(simp add: fun_eq_iff)

lemma "mirror bird = pure inverse' \<diamond> bird" (is "?lhs = ?rhs")
proof -
  let ?R = "\<lambda>t. Node (1, 1) (pure succ \<diamond> (pure inverse' \<diamond> t)) (pure inverse' \<diamond> (pure succ \<diamond> t))"
  have "mirror bird = ?R (mirror bird)"
    by(rule tree.expand)(simp add: bird_simps mirror_ap_tree mirror_pure)
  note tree_recurse_unique[OF this[unfolded map_tree_ap_tree_pure_tree tree.map_comp]]
  moreover
  def t \<equiv> "pure inverse' \<diamond> bird"
  have "t = ?R t"
    by(rule tree.expand)(simp add: t_def bird_simps ap_tree_composition[symmetric] o_assoc inverse'_inverse')
  note tree_recurse_unique[OF this[unfolded map_tree_ap_tree_pure_tree tree.map_comp]]
  ultimately show ?thesis by(simp add: t_def)
qed

primcorec even_odd_mirror :: "bool \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
where
  "\<And>even. root (even_odd_mirror even t) = root t"
| "\<And>even. left (even_odd_mirror even t) = even_odd_mirror (\<not> even) (if even then right t else left t)"
| "\<And>even. right (even_odd_mirror even t) = even_odd_mirror (\<not> even) (if even then left t else right t)"

definition even_mirror :: "'a tree \<Rightarrow> 'a tree"
where "even_mirror = even_odd_mirror True"

definition odd_mirror :: "'a tree \<Rightarrow> 'a tree"
where "odd_mirror = even_odd_mirror False"

lemma even_mirror_simps:
  "root (even_mirror t) = root t"
  "left (even_mirror t) = odd_mirror (right t)"
  "right (even_mirror t) = odd_mirror (left t)"
  and odd_mirror_simps:
  "root (odd_mirror t) = root t"
  "left (odd_mirror t) = even_mirror (left t)"
  "right (odd_mirror t) = even_mirror (right t)"
by(simp_all add: even_mirror_def odd_mirror_def)
  
lemma map_tree_even_odd_mirror: fixes even shows
  "map_tree f (even_odd_mirror even t) = even_odd_mirror even (map_tree f t)"
by(coinduction arbitrary: t even)(auto)

lemma map_tree_even_mirror: "map_tree f (even_mirror t) = even_mirror (map_tree f t)"
  and map_tree_odd_mirror: "map_tree f (odd_mirror t) = odd_mirror (map_tree f t)"
by(simp_all add: even_mirror_def odd_mirror_def map_tree_even_odd_mirror)

lemma even_odd_mirror_pure: fixes even shows
  "even_odd_mirror even (pure_tree x) = pure_tree x"
by(coinduction arbitrary: even) auto

lemma even_mirror_pure: "even_mirror (pure_tree x) = pure_tree x"
  and odd_mirror_pure: "odd_mirror (pure_tree x) = pure_tree x"
by(simp_all add: even_mirror_def odd_mirror_def even_odd_mirror_pure)

lemma even_odd_mirror_ap_tree: fixes even shows
  "even_odd_mirror even (f \<diamond> x) = even_odd_mirror even f \<diamond> even_odd_mirror even x"
by(coinduction arbitrary: even f x) auto

lemma even_mirror_ap_tree: "even_mirror (f \<diamond> x) = even_mirror f \<diamond> even_mirror x"
  and odd_mirror_ap_tree: "odd_mirror (f \<diamond> x) = odd_mirror f \<diamond> odd_mirror x"
by(simp_all add: even_mirror_def odd_mirror_def even_odd_mirror_ap_tree)

fun even_mirror_path :: "path \<Rightarrow> path"
  and odd_mirror_path :: "path \<Rightarrow> path"
where
  "even_mirror_path [] = []"
| "even_mirror_path (d # ds) = (case d of L \<Rightarrow> R | R \<Rightarrow> L) # odd_mirror_path ds"
| "odd_mirror_path [] = []"
| "odd_mirror_path (d # ds) = d # even_mirror_path ds"

lemma even_mirror_traverse_tree: 
  "root (traverse_tree path (even_mirror t)) = root (traverse_tree (even_mirror_path path) t)"
  and odd_mirror_traverse_tree:
  "root (traverse_tree path (odd_mirror t)) = root (traverse_tree (odd_mirror_path path) t)"
by (induct path arbitrary: t) (simp_all add: even_mirror_simps odd_mirror_simps split: dir.splits)

lemma even_odd_mirror_path_involution:
  "even_mirror_path (even_mirror_path path) = path"
  "odd_mirror_path (odd_mirror_path path) = path"
by (induct path) (simp_all split: dir.splits)

lemma even_odd_mirror_path_injective:
  "even_mirror_path path = even_mirror_path path' \<longleftrightarrow> path = path'"
  "odd_mirror_path path = odd_mirror_path path' \<longleftrightarrow> path = path'"
by (induct path arbitrary: path') (case_tac path', simp_all split: dir.splits)+

lemmas even_odd_mirror_simps =
  map_tree_even_mirror map_tree_odd_mirror
  even_mirror_pure odd_mirror_pure
  even_mirror_ap_tree odd_mirror_ap_tree
  even_mirror_traverse_tree odd_mirror_traverse_tree
  even_odd_mirror_path_involution
  even_odd_mirror_path_injective

abbreviation (input) "rs \<equiv> map_tree (inverse' \<circ> succ)"
abbreviation (input) "sr \<equiv> map_tree (succ \<circ> inverse')"
abbreviation (input) "rsr \<equiv> map_tree (inverse' \<circ> succ \<circ> inverse')"
abbreviation (input) "rsrs \<equiv> map_tree (inverse' \<circ> succ \<circ> inverse' \<circ> succ)"
abbreviation (input) "rssr \<equiv> map_tree (inverse' \<circ> succ \<circ> succ \<circ> inverse')"
abbreviation (input) "rsrrsr \<equiv> map_tree (inverse' \<circ> succ \<circ> inverse' \<circ> inverse' \<circ> succ \<circ> inverse')"
abbreviation (input) "srrs \<equiv> map_tree (succ \<circ> inverse' \<circ> inverse' \<circ> succ)"
abbreviation (input) "srsr \<equiv> map_tree (succ \<circ> inverse' \<circ> succ \<circ> inverse')"

lemma rssrsr_rssr:
  "inverse' \<circ> succ \<circ> inverse' \<circ> inverse' \<circ> succ \<circ> inverse' = inverse' \<circ> succ \<circ> succ \<circ> inverse'"
by (metis (lifting, no_types) comp_id fun.map_comp inverse'_inverse')

lemma srrs_ss: "succ \<circ> inverse' \<circ> inverse' \<circ> succ = succ \<circ> succ"
by (metis (lifting, no_types) comp_id fun.map_comp inverse'_inverse')

(* FIXME use corec to get the uniqueness rule *)
lemma bird_rec_unique':
  fixes ROOT LEFT RIGHT
  defines [simp]: "ROOT \<equiv> None" and [simp]: "LEFT \<equiv> Some True" and [simp]: "RIGHT \<equiv> Some False"
  assumes A: "t = Node x (Node y (map_tree ll t) (map_tree lr t)) (Node z (map_tree rl t) (map_tree rr t))"
  shows "map_tree H t =
   unfold_tree
     (\<lambda>(f, s). f (case s of None \<Rightarrow> x | Some True \<Rightarrow> y | Some False \<Rightarrow> z)) 
     (\<lambda>(f, s). case s of None \<Rightarrow> (f, LEFT) | Some True \<Rightarrow> (f \<circ> ll, ROOT) | Some False \<Rightarrow> (f \<circ> rl, ROOT))
     (\<lambda>(f, s). case s of None \<Rightarrow> (f, RIGHT) | Some True \<Rightarrow> (f \<circ> lr, ROOT) | Some False => (f \<circ> rr, ROOT))
     (H, ROOT)"
   (is "?lhs H = ?rhs (H, ROOT)")
proof -
  have [simp]: "root t = x" "root (left t) = y" "root (right t) = z"
    "left (left t) = map_tree ll t" "left (right t) = map_tree rl t"
    "right (left t) = map_tree lr t" "right (right t) = map_tree rr t"
    by(subst A, simp)+
  let ?R = "\<lambda>l r. \<exists>H. 
    l = ?lhs H \<and> r = ?rhs (H, ROOT) \<or>
    l = left (?lhs H) \<and> r = ?rhs (H, LEFT) \<or>
    l = right (?lhs H) \<and> r = ?rhs (H, RIGHT)"
  have "?R (?lhs H) (?rhs (H, ROOT))" by blast
  thus ?thesis by(rule tree.coinduct[where ?R="?R"])(auto simp add: tree.map_comp)
qed

lemmas bird_rec_unique = bird_rec_unique'[where H=id, simplified tree.map_id]
 
lemma odd_mirror_bird_stern_brocot:
  "odd_mirror bird = stern_brocot"
proof -
  let ?R = "\<lambda>t. Node (1, 1) (Node (1, 2) (rssr t) (rsrs t)) (Node (2, 1) (srsr t) (srrs t))"
  have "odd_mirror bird = ?R (odd_mirror bird)"
    by(auto 4 3 intro: tree.expand simp add: even_mirror_simps odd_mirror_simps bird_simps even_odd_mirror_simps ap_tree_composition[symmetric] o_assoc map_tree_ap_tree_pure_tree tree.map_comp)
  note bird_rec_unique[OF this]
  moreover
  have "stern_brocot = ?R stern_brocot"
    by(rule tree.expand)(auto intro: tree.expand simp add: stern_brocot_simps ap_tree_composition[symmetric] o_assoc map_tree_ap_tree_pure_tree tree.map_comp rssrsr_rssr srrs_ss)
  note bird_rec_unique[OF this]
  ultimately show ?thesis by simp
qed

theorem bird_rationals:
  assumes "m > 0" "n > 0"
  shows "root (traverse_tree (odd_mirror_path (mk_path m n)) (pure toRat \<diamond> bird)) = Fract (int m) (int n)"
using stern_brocot_rationals[OF assms]
by (simp add: odd_mirror_bird_stern_brocot[symmetric] even_odd_mirror_simps)

theorem bird_rationals_not_repeated:
  "root (traverse_tree path (pure toRat \<diamond> bird)) = root (traverse_tree path' (pure toRat \<diamond> bird))
  \<Longrightarrow> path = path'"
using stern_brocot_rationals_not_repeated[where path="odd_mirror_path path" and path'="odd_mirror_path path'"]
by (simp add: odd_mirror_bird_stern_brocot[symmetric] even_odd_mirror_simps)

end

