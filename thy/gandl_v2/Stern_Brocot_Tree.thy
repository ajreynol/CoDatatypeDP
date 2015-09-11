header {* The Stern-Brocot Tree as a codatatype *}

theory Stern_Brocot_Tree
imports
  Stern_Brocot_Basis
  Cotree_Arith
  Stream_Arith
begin

section {* The Stern-Brocot Tree *}

text{*
  The Stern-Brocot tree is discussed at length by \citet[\S4.5]{GrahamKnuthPatashnik1994CM}.
  In essence the tree enumerates the rational numbers in their lowest terms by constructing the \emph{mediants} of two bounding fractions.
*}

definition mediant :: "fraction \<times> fraction \<Rightarrow> fraction"
where "mediant \<equiv> \<lambda>((a, c), (b, d)). (a + b, c + d)"

definition stern_brocot_standard :: "fraction tree"
where 
  "stern_brocot_standard = unfold_tree
    (\<lambda>(lb, ub). mediant (lb, ub))
    (\<lambda>(lb, ub). (lb, mediant (lb, ub)))
    (\<lambda>(lb, ub). (mediant (lb, ub), ub))
    ((0, 1), (1, 0))"

text{*
  This process is visualised in Figure~\ref{fig:stern-brocot-iterate}. Intuitively each node is labelled with the mediant of it's FIXME rightmost and leftmost ancestors.

\begin{figure}
  \centering
  \begin{tikzpicture}[auto,thick,node distance=3cm,main node/.style={circle,draw,font=\sffamily\Large\bfseries}]
    \node[main node] (0) at (0, 0) {$\frac{1}{1}$};
    \node[main node] (1) at (-4, 1) {$\frac{0}{1}$};
    \node[main node] (2) at (4, 1) {$\frac{1}{0}$};
    \node[main node] (3) at (-2, -1) {$\frac{1}{2}$};
    \node[main node] (4) at (2, -1) {$\frac{2}{1}$};
    \node[main node] (5) at (-3, -2) {$\frac{1}{3}$};
    \node[main node] (6) at (3, -2) {$\frac{3}{1}$};
    \node[main node] (7) at (-1, -2) {$\frac{2}{3}$};
    \node[main node] (8) at (1, -2) {$\frac{3}{2}$};
    \node (9) at (-3.5, -3) {};
    \node (10) at (-2.5, -3) {};
    \node (11) at (-1.5, -3) {};
    \node (12) at (-0.5, -3) {};
    \node (13) at (0.5, -3) {};
    \node (14) at (1.5, -3) {};
    \node (15) at (2.5, -3) {};
    \node (16) at (3.5, -3) {};
    \path
      (1) edge[dashed] (0)
      (2) edge[dashed] (0)
      (0) edge (3)
      (0) edge (4)
      (3) edge (5)
      (3) edge (7)
      (4) edge (6)
      (4) edge (8)
      (5) edge[dotted] (9)
      (5) edge[dotted] (10)
      (6) edge[dotted] (15)
      (6) edge[dotted] (16)
      (7) edge[dotted] (11)
      (7) edge[dotted] (12)
      (8) edge[dotted] (13)
      (8) edge[dotted] (14);
  \end{tikzpicture}
  \label{fig:stern-brocot-iterate}
  \caption{Constructing the Stern-Brocot tree iteratively.}
\end{figure}

Our ultimate goal is to show that the Stern-Brocot tree contains all rationals (in lowest terms), and that each occurs exactly once in the tree.
A proof is sketched in \citet[\S4.5]{GrahamKnuthPatashnik1994CM}; here we treat it as an exercise in reasoning about an infinite tree.
*}


subsection {* Specification via a recursion equation *}

text {*
  Hinze \cite{Hinze2009JFP} derives the following recurrence relation for the Stern-Brocot tree. 
  We will show in \S\ref{section:eq:rec:iterative} that his derivation is sound with respect to the standard iterative definition of the tree shown above.
*}

definition stern_brocot :: "fraction tree"
where "stern_brocot \<equiv> tree_recurse (inverse' \<circ> succ \<circ> inverse') succ (1, 1)"

lemma stern_brocot_unfold:
  "stern_brocot =
   Node (1, 1)
        (pure inverse' \<diamond> (pure succ \<diamond> (pure inverse' \<diamond> stern_brocot)))
        (pure succ \<diamond> stern_brocot)"
unfolding stern_brocot_def
by (rule tree_recurse_unique[symmetric])(subst tree_recurse_unfold, simp add: map_tree_ap_tree_pure_tree tree.map_comp o_def)+

lemma stern_brocot_simps:
  "root stern_brocot = (1, 1)"
  "left stern_brocot = pure inverse' \<diamond> (pure succ \<diamond> (pure inverse' \<diamond> stern_brocot))"
  "right stern_brocot = pure succ \<diamond> stern_brocot"
by (subst stern_brocot_unfold, simp)+

subsubsection {* Basic properties *}

text {*
  The recursive definition is useful for showing some basic properties of the tree, 
  such as that the pairs of numbers at each node are coprime, and have non-zero denominators.
  Both are simple inductions on the path.
*}

lemma stern_brocot_denominator_non_zero:
  "case root (traverse_tree path stern_brocot) of (m, n) \<Rightarrow> m > 0 \<and> n > 0"
by(induct path)(auto simp: stern_brocot_simps split: dir.splits)

lemma stern_brocot_coprime:
  "case root (traverse_tree path stern_brocot) of (m, n) \<Rightarrow> coprime m n"
by(induct path)(clarsimp simp: stern_brocot_simps field_simps split: dir.splits)+

subsection {* All the rationals *}

text{*
  For every pair of positive naturals, we can construct a path into the Stern-Brocot tree such that the naturals at the end of the path define the same rational as the pair we started with.
  Intuitively, the choices made by Euclid's algorithm define this path.
*}

function mk_path :: "nat \<Rightarrow> nat \<Rightarrow> path" where
  "m = n \<Longrightarrow> mk_path (Suc m) (Suc n) = []"
| "m < n \<Longrightarrow> mk_path (Suc m) (Suc n) = L # mk_path (Suc m) (n - m)"
| "m > n \<Longrightarrow> mk_path (Suc m) (Suc n) = R # mk_path (m - n) (Suc n)"
| "mk_path 0 _ = undefined"
| "mk_path _ 0 = undefined"
by atomize_elim(auto, arith)
termination mk_path by lexicographic_order

lemmas mk_path_induct[case_names equal less greater] = mk_path.induct

theorem stern_brocot_rationals:
  "\<lbrakk> m > 0; n > 0 \<rbrakk> \<Longrightarrow>
  root (traverse_tree (mk_path m n) (pure toRat \<diamond> stern_brocot)) = Fract (int m) (int n)"
proof(induction m n rule: mk_path_induct)
  case (less m n)
  with stern_brocot_denominator_non_zero[where path="mk_path (Suc m) (n - m)"]
  show ?case
    by (simp add: stern_brocot_simps eq_rat field_simps zdiff_int[symmetric] split: prod.split_asm)
next
  case (greater m n)
  with stern_brocot_denominator_non_zero[where path="mk_path (m - n) (Suc n)"]
  show ?case
    by (simp add: stern_brocot_simps eq_rat field_simps zdiff_int[symmetric] split: prod.split_asm)
qed (simp_all add: stern_brocot_simps eq_rat)

subsection {* No repetitions *}

text {*
  We establish that the Stern-Brocot tree does not contain repetitions, i.e., that each rational number appears at most once in it.
  Note that this property is stronger than merely requiring that pairs of naturals not be repeated, though it is implied by that property and @{thm [source] "stern_brocot_coprime"}.
  
  Intuitively, the tree enjoys the \emph{binary search tree} ordering property when we map our pairs of naturals into rationals.
  This suffices to show that each rational appears at most once in the tree.
  To establish this seems to require more structure than is present in the recursion equations, and so we follow follow \citet{BackhouseFerreira2008MPC} and \citet{Hinze2009JFP} by introducing another definition of the tree.

  We summarise the path to each node using a matrix.
  We then derive an iterative version and use invariant reasoning on that.
  We begin by defining some matrix machinery.
  This is all elementary and primitive (we don't need much algebra).
*}

type_synonym Mat = "fraction \<times> fraction"
type_synonym Vec = fraction

definition Mulmat :: "Mat \<Rightarrow> Mat \<Rightarrow> Mat"
where "Mulmat = (\<lambda>((a, c), (b, d)) ((a', c'), (b', d')).
       ((a * a' + b * c', c * a' + d * c'),
        (a * b' + b * d', c * b' + d * d')))"

definition Mulvec :: "Mat \<Rightarrow> Vec \<Rightarrow> Vec"
where "Mulvec = (\<lambda>((a, c), (b, d)) (a', c'). (a * a' + b * c', c * a' + d * c'))"

definition Fmat :: Mat where "Fmat \<equiv> ((0, 1), (1, 0))"
definition Imat :: Mat where "Imat \<equiv> ((1, 0), (0, 1))"
definition LLmat :: Mat where "LLmat \<equiv> ((1, 1), (0, 1))"
definition URmat :: Mat where "URmat \<equiv> ((1, 0), (1, 1))"

definition Det :: "Mat \<Rightarrow> nat" where "Det \<equiv> \<lambda>((a, c), (b, d)). a * d - b * c"

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

text {* 
  \citeauthor{BackhouseFerreira2008MPC} work with the identity matrix @{const "Imat"} at the root rather than @{const "Fmat"}.
  This has the advantage that all relevant matrices have determinants of 1.
*}

definition stern_brocot_iterate_aux :: "Mat \<Rightarrow> Mat tree"
where "stern_brocot_iterate_aux \<equiv> tree_iterate (\<lambda>s. Mulmat s LLmat) (\<lambda>s. Mulmat s URmat)"

definition stern_brocot_iterate :: "fraction tree" where
  "stern_brocot_iterate \<equiv> map_tree mediant (stern_brocot_iterate_aux Imat)"

axiomatization where
  cheat[no_atp]: P

lemma stern_brocot_iterate: "stern_brocot = stern_brocot_iterate" (is "?lhs = ?rhs")
proof -
  have "?rhs = map_tree mediant (tree_recurse (Mulmat LLmat) (Mulmat URmat) Imat)"
    using tree_recursion_iteration[where f="Mulmat" and l="LLmat" and r="URmat" and \<epsilon>="Imat"]
    by (simp add: stern_brocot_iterate_def stern_brocot_iterate_aux_def)
 also have "\<dots> = tree_recurse (Mulvec LLmat) (Mulvec URmat) (1, 1)"
   unfolding mediant_Imat_Fmat(2)[symmetric]
   by (rule tree_recurse_fusion)(simp_all add: fun_eq_iff mediant_def Mulmat_def Mulvec_def LLmat_def URmat_def)[2]
 also have "\<dots> = ?lhs"
   apply (simp add: inverse'_succ_inverse' Mulvec_def LLmat_def URmat_def)
   by (rule cheat)
 finally show ?thesis by simp
qed

text{*
  The following are the key ordering properties derived by \citet{BackhouseFerreira2008MPC}.
  They hinge on the matrices containing only natural numbers.
*}

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
    apply (simp_all add: field_simps)
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
  assumes "root (traverse_tree path (pure toRat \<diamond> stern_brocot))
         = root (traverse_tree path' (pure toRat \<diamond> stern_brocot))"
  shows "path = path'"
using assms
using stern_brocot_coprime[where path=path]
      stern_brocot_coprime[where path=path']
      stern_brocot_denominator_non_zero[where path=path]
      stern_brocot_denominator_non_zero[where path=path']
by(auto simp: transfer_int_nat_gcd dest!: rat_inv_eq intro: stern_brocot_fractions_not_repeated simp add: stern_brocot_iterate[symmetric] split: prod.splits)


subsection {* Equivalence of recursive and iterative version \label{section:eq:rec:iterative} *}

text {*
 \citeauthor{Hinze2009JFP} shows that it doesn't matter
which we use provided we swap the left and right matrices too. This is
his proof split into two pieces.
 *}

abbreviation stern_brocot_Hinze_iterate :: "fraction tree"
where "stern_brocot_Hinze_iterate \<equiv> map_tree mediant (tree_iterate (\<lambda>s. Mulmat s URmat) (\<lambda>s. Mulmat s LLmat) Fmat)"

lemma mediant_Mulmat_Fmat:
  "mediant \<circ> (\<lambda>s. Mulmat s Fmat) = mediant"
by(simp add: Mulmat_def Fmat_def mediant_def split_def o_def add.commute)

lemma stern_brocot_standard_iterate: "stern_brocot_standard = stern_brocot_iterate"
proof -
  have "stern_brocot_standard = stern_brocot_Hinze_iterate"
    unfolding stern_brocot_standard_def
    by(subst unfold_tree_tree_iterate)(simp add: Fmat_def Mulmat_def mediant_def URmat_def LLmat_def split_def)
  also have "\<dots> = map_tree mediant (map_tree (\<lambda>s. Mulmat s Fmat) (tree_iterate (\<lambda>s. Mulmat s LLmat) (\<lambda>s. Mulmat s URmat) Imat))"
    by(subst tree_iterate_fusion[where l'="\<lambda>s. Mulmat s URmat" and r'="\<lambda>s. Mulmat s LLmat"])
      (simp_all add: fun_eq_iff Mulmat_def URmat_def LLmat_def Fmat_def Imat_def)
  also have "\<dots> = stern_brocot_iterate"
    by(simp only: tree.map_comp mediant_Mulmat_Fmat stern_brocot_iterate_def stern_brocot_iterate_aux_def)
  finally show ?thesis .
qed

lemma "stern_brocot_standard = stern_brocot"
by(simp add: stern_brocot_iterate stern_brocot_standard_iterate)

subsection {* Linearising the Stern-Brocot Tree *}

text {* Turn a tree into a stream. *}

primcorec tree_chop :: "'a tree \<Rightarrow> 'a tree"
where
  "root (tree_chop t) = root (left t)"
| "left (tree_chop t) = right t"
| "right (tree_chop t) = tree_chop (left t)"

text {* @{const tree_chop} is a idiom homomorphism *}

lemma tree_chop_pure_tree [simp]:
  "tree_chop (pure x) = pure x"
by(coinduction rule: tree.coinduct_strong) auto

lemma tree_chop_ap_tree [simp]:
  "tree_chop (f \<diamond> x) = tree_chop f \<diamond> tree_chop x"
by(coinduction arbitrary: f x rule: tree.coinduct_strong) auto

primcorec stream :: "'a tree \<Rightarrow> 'a stream"
where
  "shd (stream t) = root t"
| "stl (stream t) = stream (tree_chop t)"

text{* @{const "stream"} is an idiom homomorphism. *}

lemma stream_pure [simp]: "stream (pure x) = pure x"
by coinduction auto

lemma stream_ap [simp]: "stream (f \<diamond> x) = stream f \<diamond> stream x"
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

text {* Split the Stern-Brocot tree into numerators and denumerators *}


text \<open>Workaround for missing support for mutual recursion in corec: add a parameter\<close>

definition num :: "nat tree"
where "num \<equiv> pure fst \<diamond> stern_brocot"

definition den :: "nat tree"
where "den \<equiv> pure snd \<diamond> stern_brocot"

lemma num_unfold: "num = Node 1 num (num + den)"
unfolding num_def den_def plus_tree_def
by(subst stern_brocot_unfold)(simp add: ap_tree_composition[symmetric] o_def split_beta ap_tree_same2)

lemma den_unfold: "den = Node 1 (num + den) den"
unfolding num_def den_def plus_tree_def
by(subst stern_brocot_unfold)(simp add: ap_tree_composition[symmetric] o_def split_beta add_ac ap_tree_same2)

lemma num_simps [simp]:
  "root num = 1"
  "left num = num"
  "right num = num + den"
by(subst num_unfold, simp)+

lemma den_simps [simp]:
  "root den = 1"
  "left den = num + den"
  "right den = den"
apply (rule cheat)
apply (rule cheat)
apply (rule cheat)
done

lemma stern_brocot_num_den:
  "pure_tree Pair \<diamond> num \<diamond> den = stern_brocot"
(* FIXME: Should use uniqueness of stern_brocot *)
apply (rule cheat)
done

lemma den_eq_chop_num: "den = tree_chop num"
apply (rule cheat)
done

lemma num_conv: "num = pure fst \<diamond> stern_brocot"
unfolding stern_brocot_num_den[symmetric]
apply(simp add: map_tree_ap_tree_pure_tree)
apply (rule cheat)
done

lemma den_conv: "den = pure snd \<diamond> stern_brocot"
unfolding stern_brocot_num_den[symmetric]
apply(simp add: map_tree_ap_tree_pure_tree)
apply (rule cheat)
done


text{*

\citet[p502]{Hinze2009JFP} gets a bit oblique here.

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

primcorec num_mod_den :: "nat tree"
where "num_mod_den = Node 0 num num_mod_den"

lemma num_mod_den_unique: "x = Node 0 num x \<Longrightarrow> x = num_mod_den"
proof(coinduction arbitrary: x rule: tree.coinduct_strong)
  case (Eq_tree x)
  show ?case
    by(subst (1 2 3 4) Eq_tree)(simp add: eqTrueI[OF Eq_tree])
qed

lemma mod_tree_lemma1:
  fixes x :: "nat tree"
  assumes "pure (op < 0) \<diamond> y = pure True"
  shows "x mod (x + y) = x"
proof -
  have eq: "\<And>x y :: nat. x mod (x + y) = (if 0 < y then x else 0)" by simp
  have "x mod (x + y) = \<^bold>S \<diamond> pure op mod \<diamond> (\<^bold>C \<diamond> pure op + \<diamond> y) \<diamond> x"
    unfolding arith_tree_defs ap_tree_S_tree ap_tree_C_tree ..
  also have "\<dots> = pure (\<lambda>b x. if b then x else 0) \<diamond> (pure (op < 0) \<diamond> y) \<diamond> x"
    by(simp add: S_tree_def C_tree_def eq o_def ap_tree_composition[symmetric])
  also note assms
  finally show ?thesis by simp
qed

lemma mod_tree_lemma2:
  fixes x y :: "'a :: semiring_div tree"
  shows "(x + y) mod y = x mod y"
proof -
  have "(x + y) mod y = \<^bold>S \<diamond> (\<^bold>C \<diamond> pure op mod) \<diamond> (pure op + \<diamond> x) \<diamond> y"
    unfolding arith_tree_defs ap_tree_S_tree ap_tree_C_tree ..
  also have "\<dots> = x mod y" unfolding arith_tree_defs
    by(simp add: S_tree_def C_tree_def ap_tree_composition[symmetric] o_def)
  finally show ?thesis .
qed

lemma set_tree_pathD: "x \<in> set_tree t \<Longrightarrow> \<exists>p. x = root (traverse_tree p t)"
by(induct rule: set_tree_induct)(auto intro: exI[where x="[]"] exI[where x="L # p" for p] exI[where x="R # p" for p])

lemma eq_pure_tree_TrueI:
  "(\<And>x. x \<in> set_tree t \<Longrightarrow> P x) \<Longrightarrow> pure P \<diamond> t = pure True"
proof(coinduction arbitrary: t)
  case (Eq_tree t)
  thus ?case by(cases t) auto
qed

lemma den_gt_0: "pure (op < 0) \<diamond> den = pure True"
proof(rule eq_pure_tree_TrueI)
  fix x
  assume "x \<in> set_tree den"
  then obtain p where "x = root (traverse_tree p den)"
    by(blast dest: set_tree_pathD)
  with stern_brocot_denominator_non_zero[of p]
  show "0 < x" by(simp add: den_conv split_beta)
qed

lemma num_mod_den: "num mod den = num_mod_den"
by(rule num_mod_den_unique)(rule tree.expand, simp add: mod_tree_lemma1 den_gt_0 mod_tree_lemma2)

lemma tree_chop_den: "tree_chop den = num + den - 2 * (num mod den)"
proof -
  have le: "\<And>x y :: nat. 0 < y \<Longrightarrow> 2 * (x mod y) \<le> x + y"
    by(metis Divides.mod_less_eq_dividend add_le_mono mod_le_divisor mult_2)

  txt {* We switch to @{typ int} such that all cancellation laws are available. *}
  def den' \<equiv> "pure int \<diamond> den"
  def num' \<equiv> "pure int \<diamond> num"
  def num_mod_den' \<equiv> "pure int \<diamond> num_mod_den"

  have [simp]: "root num' = 1" "left num' = num'" "right num' = num' + den'"
    by(simp_all add: den'_def num'_def map_tree_ap_tree_pure_tree[symmetric] plus_tree_def ap_tree_composition[symmetric] o_def)
  have num_mod_den'_simps [simp]: "root num_mod_den' = 0" "left num_mod_den' = num'" "right num_mod_den' = num_mod_den'"
    by(simp_all add: num_mod_den'_def num'_def)
  have den'_eq_chop_num': "den' = tree_chop num'" by(simp add: den'_def num'_def den_eq_chop_num)
  have den'_gt_0: "pure (op < 0) \<diamond> den' = pure True"
    by(simp add: den'_def ap_tree_composition[symmetric] o_def den_gt_0)
  have num_mod_den'2_unique: "\<And>x. x = Node 0 (2 * num') x \<Longrightarrow> x = 2 * num_mod_den'"
  proof(coinduction rule: tree.coinduct_strong)
    case (Eq_tree x)
    show ?case
      by(subst (1 2 3 4) Eq_tree)(simp add: eqTrueI[OF Eq_tree])
  qed
  have num'_plus_den'_minus_chop_den': "num' + den' - tree_chop den' = 2 * num_mod_den'"
    by(rule num_mod_den'2_unique)(rule tree.expand, simp add: tree_chop_plus den'_eq_chop_num')

  have "tree_chop den = pure nat \<diamond> (tree_chop den')"
    by(simp add: den'_def ap_tree_composition[symmetric] o_def)
  also have "tree_chop den' = num' + den' - tree_chop den' + tree_chop den' - 2 * num_mod_den'"
    by(subst num'_plus_den'_minus_chop_den') simp
  also have "\<dots> = num' + den' - 2 * (num' mod den')"
    by(simp add: num_mod_den'_def num'_def den'_def num_mod_den[symmetric])
      (simp add: arith_tree_defs ap_tree_composition[symmetric] o_def zmod_int)
  also have "\<dots> = \<^bold>S \<diamond> (pure op \<circ> \<diamond> \<^bold>S \<diamond> (pure op \<circ> \<diamond> (pure op \<circ> \<diamond> pure op -) \<diamond> pure op +)) \<diamond> (pure op \<circ> \<diamond> (pure op \<circ> \<diamond> (pure op * \<diamond> 2)) \<diamond> pure op mod) \<diamond> num' \<diamond> den'"
    unfolding ap_tree_S_tree ap_tree_composition arith_tree_defs ..
  also have "\<dots> = pure (\<lambda>n d. n + d - 2 * (n mod d)) \<diamond> num' \<diamond> den'"
    unfolding S_tree_def by(simp add: ap_tree_composition[symmetric] o_def numeral_tree_def)
  also have "\<dots> = \<^bold>S \<diamond> (pure (\<lambda>n d b. if b then n + d - 2 * (n mod d) else 0) \<diamond> num') \<diamond> pure (op < 0) \<diamond> den'"
    unfolding ap_tree_S_tree den'_gt_0
    by(simp add: o_def ap_tree_composition[symmetric])
  also have "\<dots> = pure (\<lambda>n d. if 0 < d then n + d - 2 * (n mod d) else 0) \<diamond> num' \<diamond> den'"
    by(simp add: S_tree_def ap_tree_composition[symmetric] o_def)
  also have "\<dots> = pure (\<lambda>n d. if 0 < d then int (n + d - 2 * (n mod d)) else 0) \<diamond> num \<diamond> den"
    by(simp add: num'_def den'_def ap_tree_composition[symmetric] o_def le zdiff_int[symmetric] int_mult zmod_int cong: if_cong)
  also have "\<dots> = pure (\<lambda>n d. int (n + d - 2 * (n mod d))) \<diamond> num \<diamond> den"
    by(auto intro!: arg_cong2[where f=ap_tree] arg_cong[where f=pure_tree] ext)
  also have "\<dots> = pure int \<diamond> (\<^bold>S \<diamond> (pure op \<circ> \<diamond> \<^bold>S \<diamond> (pure op \<circ> \<diamond> (pure op \<circ> \<diamond> pure op -) \<diamond> pure op +)) \<diamond> (pure op \<circ> \<diamond> (pure op \<circ> \<diamond> (pure op * \<diamond> 2)) \<diamond> pure op mod) \<diamond> num \<diamond> den)"
    unfolding S_tree_def by(simp add: ap_tree_composition[symmetric] o_def numeral_tree_def)
  also have "\<dots> = pure int \<diamond> (num + den - 2 * (num mod den))"
    unfolding ap_tree_S_tree ap_tree_composition arith_tree_defs ..
  finally show ?thesis
    by(simp add: ap_tree_composition[symmetric] o_def)
qed

subsection{* Loopless linearisation of the Stern-Brocot tree. *}

text {*
  This is a loopless linearisation of the Stern-Brocot tree that gives Stern's diatomic sequence,
  which is also known as Dijkstra's fusc function \cite{}
*}

text{*

FIXME commentary. Loopless?

Dijkstra's fusc function. EWD 570, 578

FIXME how clearly related are they?

FIXME point to the HOLCF rendition.

*}

definition step :: "nat \<times> nat \<Rightarrow> nat \<times> nat"
where "step = (\<lambda>(n, d). (d, n + d - 2 * (n mod d)))"

definition stern_brocot_loopless :: "fraction stream"
where "stern_brocot_loopless \<equiv> siterate step (1, 1)"

lemma stern_brocot_loopless_rec:
  "stern_brocot_loopless = (1, 1) ## smap step stern_brocot_loopless"
by(rule stream.expand) (simp add: stern_brocot_loopless_def smap_siterate)

definition fusc :: "nat stream"
where "fusc \<equiv> smap fst stern_brocot_loopless"

definition fusc' :: "nat stream"
where "fusc' \<equiv> smap snd stern_brocot_loopless"

lemma fusc_unfold: "fusc = 1 ## fusc'"
unfolding fusc_def fusc'_def
by (subst stern_brocot_loopless_rec) (simp add: stream.map_comp o_def split_def step_def)

lemma smap_conv_ap_stream_pure_stream: "smap f xs = pure_stream f \<diamond> xs"
by(coinduction arbitrary: xs)(auto)

lemma pure_stream_numeral [symmetric]: "numeral n = pure_stream (numeral n)"
by(induction n)(simp_all only: numeral.simps plus_stream_def ap_stream_composition ap_stream_homomorphism one_stream_def)
(*
lemma fusc'_unfold: "fusc' = 1 ## (fusc + fusc' - 2 * (fusc mod fusc'))"
unfolding fusc_def fusc'_def
by(subst stern_brocot_loopless_rec)(simp add: arith_stream_defs ap_stream_composition[symmetric] o_def smap_conv_ap_stream_pure_stream step_def split_def pure_stream_numeral[symmetric] ap_stream_pure_SCons)
*)
lemma fusc_simps [simp]:
  "shd fusc = 1"
  "stl fusc = fusc'"
by(simp_all add: fusc_unfold)

lemma fusc'_simps [simp]:
  "shd fusc' = 1"
  "stl fusc' = fusc + fusc' - 2 * (fusc mod fusc')"
apply (rule cheat)
apply (rule cheat)
done

text{*

FIXME Equivalence of streaming the Stern-Brocot Tree with ...

*}

lemma FIXME_lift_step: "pure_stream Pair \<diamond> ys \<diamond> (xs + ys - 2 * (xs mod ys)) = pure_stream (\<lambda>x y. (y, x + y - 2 * (x mod y))) \<diamond> xs \<diamond> ys"
by(coinduction arbitrary: xs ys) auto

lemma fusc_fusc'_iterate: "pure_stream Pair \<diamond> fusc \<diamond> fusc' = siterate (\<lambda>(n, d). (d, n + d - 2 * (n mod d))) (1, 1)"
apply(rule siterate_unique)
apply(rule stream.expand)
apply(simp add: smap_conv_ap_stream_pure_stream ap_stream_composition[symmetric] o_def FIXME_lift_step)
done

lemma fusc_fusc'_unique: (* FIXME: use uniqueness theorem generated by corec *)
  assumes xs: "xs = 1 ## xs'"
  and xs': "xs' = 1 ## (xs + xs' - 2 * (xs mod xs'))"
  shows "xs = fusc \<and> xs' = fusc'"
proof -
  have [simp]: "shd xs = 1" "stl xs = xs'"
    "shd xs' = 1" "stl xs' = xs + xs' - 2 * (xs mod xs')"
    using assms by (metis Stream.stream.sel)+
  have eq: "pure_stream Pair \<diamond> xs \<diamond> xs' = pure_stream Pair \<diamond> fusc \<diamond> fusc'"
    unfolding fusc_fusc'_iterate
    apply(rule siterate_unique)
    apply(rule stream.expand)
    apply(simp add: FIXME_lift_step ap_stream_composition[symmetric] smap_conv_ap_stream_pure_stream o_def)
    done
  have "smap fst (pure_stream Pair \<diamond> xs \<diamond> xs') = fusc"
       "smap snd (pure_stream Pair \<diamond> xs \<diamond> xs') = fusc'"
    unfolding eq smap_conv_ap_stream_pure_stream
    by (simp_all add: ap_stream_composition[symmetric] o_def pure_stream_K2_apply)
  then show ?thesis
    by(simp add: smap_conv_ap_stream_pure_stream ap_stream_composition[symmetric] o_def pure_stream_K2_apply)
qed

lemma fusc_num: "fusc = stream num"
  and fusc'_den: "fusc' = stream den"
proof -
  have "stream num = fusc \<and> stream den = fusc'"
  proof(rule fusc_fusc'_unique)
    show "stream num = 1 ## stream den"
      by (rule stream.expand) (simp add: den_eq_chop_num)
    show "stream den = 1 ## (stream num + stream den - 2 * (stream num mod stream den))"
      by (rule stream.expand)
         (simp add: tree_chop_den stream_plus stream_minus stream_times stream_mod)
  qed
  then show "fusc = stream num" "fusc' = stream den" by simp_all
qed

theorem stern_brocot_loopless:
  "stream stern_brocot = stern_brocot_loopless" (is "?lhs = ?rhs")
proof -
  have "?lhs = stream (pure_tree Pair \<diamond> num \<diamond> den)" by (simp only: stern_brocot_num_den)
  also have "\<dots> = pure_stream Pair \<diamond> fusc \<diamond> fusc'" by (simp add: fusc_num fusc'_den)
  also have "\<dots> = ?rhs" by (simp add: stern_brocot_loopless_def step_def fusc_fusc'_iterate)
  finally show ?thesis .
qed

end
