// ! external
#import "../typst/notes.typ": *
#import "../typst/shortcuts.typ": *

// ! configuration
#show: doc => conf(
  course_code: "MATH457",
  course_title: "Algebra 4",
  subtitle: "Representation Theory; Galois Theory",
  semester: "Winter 2025",
  professor: "Prof. Henri Darmon",
  doc
)

#import "@preview/commute:0.2.0": node, arr, commutative-diagram

#set align(left)

= Representation Theory

== Introduction
#definition("Linear Representation")[
  A _linear representation_ of a group $G$ is a vector space $V$ over a field $FF$ equipped with a map $G times V -> V$ that makes $V$ a $G$-set in such a way that for each $g in G$, the map $v |-> g v$ is a linear homomorphism of $V$.

  This induces a homomorphism $
  rho : G -> "Aut"_FF (V),
  $ or, in particular, when $n = dim_FF V < infinity$, a homomorphism $
  rho : G -> "GL"_n (FF).
  $
  Alternatively, a linear representation $V$ can be viewed as a module over the group ring $FF[G] = {sum_(g in G) : lambda_g g : lambda_g in FF}$ (where we require all but finitely many scalars $lambda_g$ to be zero).
]

#definition("Irreducible Representation")[
  A linear representation $V$ of a group $G$ is called _irreducible_ if there exists no proper, nontrivial _subspace_ $W subset.neq V$ such that $W$ is $G$-stable. 
]

#example[
  1. Consider $G = ZZ\/2 = {1, tau}$. If $V$ a linear representation of $G$ and $rho : G -> "Aut"(V)$. Then, $V$ uniquely determined by $rho (tau)$. Let $p(x)$ be the minimal polynomial of $rho(tau)$. Then, $p(x) | x^2 - 1$. Suppose $FF$ is a field in which $2 eq.not 0$. Then, $p(x) | (x - 1)(x+1)$ and so $p(x)$ has either $1, -1$, or both as eigenvalues and thus we may write $
  V = V_+ plus.circle V_-,
  $ where $V_plus.minus := {v | tau v = plus.minus v}$. Hence, $V$ is irreducible only if one of $V_+, V_-$ all of $V$ and the other is trivial, or in other words $tau$ acts only as multiplication by $1$ or $-1$.

  2. Let $G = {g_1, dots, g_N}$ be a finite abelian group, and suppose $FF$ an algebraically closed field of characeristic 0 (such as $CC$). Let $rho : G -> "Aut" (V)$ and denote $T_j := rho (g_j)$ for $j = 1, dots, N$. Then, ${T_1, dots, T_N}$ is a set of mutually commuting linear transformations. Then, there exists a simultaneous eigenvector, say $v$, for ${T_1, dots, T_N}$, and so $"span" (v)$ a $G$-stable subspace of $V$. Thus, if $V$ irreducible, it must be that $dim_FF V = 1$.
]

#theorem[If $G$ a finite abelian group and $V$ an irreducible finite dimensional representation over an algebraically closed field of characeristic 0, then $dim V = 1$.]

#proof[
  Let $rho : G -> "Aut"(V)$, label $G = {g_1, dots, g_N}$ and put $T_j := rho (g_j)$ for $j = 1, dots, N$. Then, ${T_1, dots, T_N}$ a family of mutually commuting linear transformations on $V$. Then, there is a simultaneous eigenvector $v$ for ${T_1, dots, T_N}$  and thus $"span"(v)$ is $T_1, dots, T_N$-stable and so $V = "span"(v)$.
]
#lemma[
  Let $V$ be a finite dimensional vector space over $CC$ and let $T_1, dots, T_N : V -> V$ be a family of mutually commuting linear automorphisms on $V$. Then, there is a simultaneous eigenvector for $T_1, dots, T_N$.
]

#proposition[Let $FF$ a field where $2 eq.not 0$ and $V$ an irreducible representation of $S_3$. Then, there are three distinct (i.e., up to homomorphism) possibilities for $V$.]

#proof[
Let $rho : G -> "Aut"(V)$ and let $T = rho ((23))$. Then, notice that $p_T (x) | (x^2 - 1)$ so $T$ has eigenvalues in ${-1, 1}$. 

If the only eigenvalue of $T$ is $-1$, we claim that $V$ one-dimensional.

If $T$ has $1$ as an eigenvalue.
]