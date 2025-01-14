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

% ! 01-06
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

//  ! 01-08

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

#proposition[
  $D_8$ has a unique faithful irreducible representation, of dimension 2 over a field $F$ in which $0 eq.not 2$.
]

#proof[
  Write $G = D_8 = {1, r, r^2, r^3, v, h, d_1, d_2}$ as standard. Let $rho$ be our irreducible, faithful representation and let $T = rho(r^2)$. Then, $p_T (x) | x^2 - 1 = (x-1)(x+1)$ and so $V = V_+ plus.circle V_-$, the respective eigenspaces for $lambda = +1, - 1$ respectively for $T$. Then, notice that since $r^2$ in the center of $G$, both $V_+$ and $V_-$ are preserved by the action of $G$, hence one must be trivial and the other the entirety of $V$. $V$ can't equal $V_+$, else $T = I$ on all of $V$ hence $rho$ not faithful so $V = V_-$.

  Next, it must be that $rho(h)$ has both eigenvalues $1$ and $-1$. Let $v_1 in V$ be such that $h v_1 = v_1$ and $v_2 = r v_1$. We claim that $W := "span" {v_1, v_2}$, namely $V = W$ 2-dimensional.

  We simply check each element. $r v_1 = v_2$ and $r v_2 = r^2 v_1 = - v_1$ which are both in $W$ hence $r$ and thus $angle.l r angle.r$ fixes $W$. Next, $h v_1 = v_1$ and $v v_2 = v r v_1 = r h v_1 = r v_1 = v_2$ (since $r h r^(-1) = v$) and so $h v_2 = - v_2$ and $v v_1 = - v_1$ and so $W$ $G$-stable. Finally, $d_1$ and $d_2$ are just products of these elements and so $W$ $G$-stable.
]

//  ! 01-13

#theorem("Maschke's")[
  Any representation of a finite group $G$ over $CC$ can be written as a direct sum of irreducible representations, i.e. $
  V = V_1 plus.circle dots.c plus.circle V_t,
  $ where $V_j$ irreducible.
]

#remark[
  $|G| < infinity$ essential. For instance, consider $G = (ZZ,+)$ and 2-dimensional representation given by $n |-> mat(1, n; 0, 1)$. Then, $n dot e_1 = e_1$ and $n dot e_2 = n e_1 + e_2$. We have that $CC e_1$ irreducible then. But if $v = a e_1 + e_2 in W:= V \\ CC e_1$, then $G v = (a + 1) e_1 + e_2$ so $G v - v = e_1 in W$, contradiction.
]

#remark[
  $|CC|$ essential. Suppose $F = ZZ\/3 ZZ$ and $V = F e_1 plus.circle F e_2 plus.circle F e_3$, and $G = S_3$ acts on $V$ by permuting the basis vectors $e_i$. Then notice that $F (e_1 + e_2 + e_3)$ an irreducible subspace in $V$. Let $W = F (w)$ with $w := a e_1 + b e_2 + c e_3$ be any other $G$-stable subspace. Then, by applying $(123)$ repeatedly to $w$ and adding the result, we find that $(a + b + c) (e_1 + e_2 + e_3) in W$. Similarly, by applying $(12), (23), (13)$ to $w$, we find $(a - b) (e_1 - e_2), (b - c) (e_2 - e_3), (a - c) (e_1 - e_3)$ all in $W$. It must be that at least one of $a - b, a - c, b - c$ nonzero, else we'd have $w in F (e_1 + e_2 + e_3)$. Assume wlog $a - b eq.not 0$. Then, we may apply $(a - b)^(-1)$ and find $e_1 - e_2 in W$. By applying $(23), (13)$ to this vector and scaling, we find further $e_2 - e_3$ and $e_1 - e_3 in W$. But then, $
  2 (e_1 - e_2) + 2 (e_1 - e_3) = e_1 + e_2 + e_3 in W,
  $ so $F (e_1 + e_2 + e_3)$ a subspace of $W$, a contradiction. 
]

#proposition[
  Let $V$ be a representation of $|G| < infinity$ over $CC$ and let $W subset.eq V$ a sub-representation. Then, $W$ has a $G$-stable complement $W'$, such that $V = W plus.circle W'$.
]

#proof[
  Denote by $rho$ the homomorphism induced by the representation. Let $W_0'$ be any complementary subspace of $W$ and let $
  pi : V -> W
  $ be a projection onto $W$ along $W_0'$, i.e. $pi^2 = pi, pi (V) = W$, and $ker (pi) = W_0'$. Let us "replace"  $pi$ by the "average" $
  tilde(pi) := 1/(hash G) sum_(g in G) rho(g) pi rho(g)^(-1).
  $ Then the following hold: 

(1) $tilde(pi)$ $G$-equivariant, that is $tilde(pi) (g v) = g tilde(pi) (v)$ for every $g in G, v in V$.

(2) $tilde(pi)$ a projection onto $W$. 

Let $W' = ker(tilde(pi))$. Then, $W'$ $G$-stable, and $V = W plus.circle W'$.
]