theory Applicative_Functor imports
  Main
  "~~/src/Tools/Adhoc_Overloading"
begin

subsection {* The basic operations of applicative functors *}

consts pure :: "'a \<Rightarrow> 'b"

consts ap :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<diamond>" 70)

text {*
  The applicative functor requires the following laws about @{const pure} and @{const ap}:
  \begin{gather}
    @{term "pure id \<diamond> u = u"}
    \tag{\mbox{identity}}
    \\
    @{term "pure op \<circ> \<diamond> u \<diamond> v \<diamond> w = u \<diamond> (v \<diamond> w)"}
    \tag{\mbox{composition}}
    \\
    @{term "pure f \<diamond> pure x = pure (f x)"}
    \tag{\mbox{homomorphism}}
    \\
    @{term "u \<diamond> pure x = pure (\<lambda>f. f x) \<diamond> u"}
    \tag{\mbox{interchange}}
  \end{gather}
*}

hide_const (open) ap

subsection {* Applicative functors with combinatorial structure *}

consts S :: "'a" ("\<^bold>S")
consts K :: "'a" ("\<^bold>K")
consts I :: "'a" ("\<^bold>I")
consts C :: "'a" ("\<^bold>C")

text {*
  The combinators must satisfy the following specification:
  \begin{center}
    \begin{tabular}{@ {}l@ {\qquad}l@ {}}
      @{term "\<^bold>S = pure (\<lambda>f g x. f x (g x))"}
      &
      @{term "\<^bold>S x y z = x \<diamond> z \<diamond> (y \<diamond> z)"}
      \\
      @{term "\<^bold>I = pure id"}
      &
      @{term "\<^bold>I \<diamond> x = x"}
      \\
      @{term "\<^bold>K = pure (\<lambda>x y. x)"}
      &
      @{term "\<^bold>K \<diamond> x \<diamond> y = x"}
      \\
      @{term "\<^bold>C = pure (\<lambda>f x y. f y x)"}
      &
      @{term "\<^bold>C \<diamond> f \<diamond> x \<diamond> y = f \<diamond> y \<diamond> x"}
    \end{gather}
  \end{center}
*}

hide_const (open) S K I C

end
