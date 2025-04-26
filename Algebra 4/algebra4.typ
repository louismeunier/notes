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

// % ! 01-06
= Representation Theory

Recall that in studying group theory, we studied the notation of a group "acting" on a set. Representation theory studies group actions on vector spaces, which takes the notion of a group action on a set, and makes it compatible with the vector space structure. 
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

  2. Let $G = {g_1, dots, g_N}$ be a finite abelian group, and suppose $FF$ an algebraically closed field of characteristic 0 (such as $CC$). Let $rho : G -> "Aut" (V)$ and denote $T_j := rho (g_j)$ for $j = 1, dots, N$. Then, ${T_1, dots, T_N}$ is a set of mutually commuting linear transformations. Then, there exists a simultaneous eigenvector, say $v$, for ${T_1, dots, T_N}$, and so $"span" (v)$ a $G$-stable subspace of $V$. Thus, if $V$ irreducible, it must be that $dim_FF V = 1$.
]


#theorem[If $G$ a finite abelian group and $V$ an irreducible finite dimensional representation over an algebraically closed field of characteristic 0, then $dim V = 1$.]

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

#definition("Isomorphism of Representations")[
  Given a group $G$ and two representations $rho_i : G -> "Aut"_FF (V_i)$, $i = 1, 2$ an isomorphism of representations is a vector space isomorphism $phi: V_1 -> V_2$ that respects the group action, namely $
  phi(g v) = g phi(v)
  $ for every $g in G, v in V_1$.
]

//  ! 01-13

== Maschke's Theorem
#theorem("Maschke's")[
  Any representation of a finite group $G$ over $CC$ can be written as a direct sum of irreducible representations, i.e. $
  V = V_1 plus.circle dots.c plus.circle V_t,
  $ where $V_j$ irreducible.
]<thm:maschkes>

#remark[
  $|G| < infinity$ essential. For instance, consider $G = (ZZ,+)$ and 2-dimensional representation given by $n |-> mat(1, n; 0, 1)$. Then, $n dot e_1 = e_1$ and $n dot e_2 = n e_1 + e_2$. We have that $CC e_1$ irreducible then. But if $v = a e_1 + e_2 in W:= V \\ CC e_1$, then $G v = (a + 1) e_1 + e_2$ so $G v - v = e_1 in W$, contradiction.
]

#remark[
  $CC$ essential. Suppose $F = ZZ\/3 ZZ$ and $V = F e_1 plus.circle F e_2 plus.circle F e_3$, and $G = S_3$ acts on $V$ by permuting the basis vectors $e_i$. Then notice that $F (e_1 + e_2 + e_3)$ an irreducible subspace in $V$. Let $W = F (w)$ with $w := a e_1 + b e_2 + c e_3$ be any other $G$-stable subspace. Then, by applying $(123)$ repeatedly to $w$ and adding the result, we find that $(a + b + c) (e_1 + e_2 + e_3) in W$. Similarly, by applying $(12), (23), (13)$ to $w$, we find $(a - b) (e_1 - e_2), (b - c) (e_2 - e_3), (a - c) (e_1 - e_3)$ all in $W$. It must be that at least one of $a - b, a - c, b - c$ nonzero, else we'd have $w in F (e_1 + e_2 + e_3)$. Assume wlog $a - b eq.not 0$. Then, we may apply $(a - b)^(-1)$ and find $e_1 - e_2 in W$. By applying $(23), (13)$ to this vector and scaling, we find further $e_2 - e_3$ and $e_1 - e_3 in W$. But then, $
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

// ! 01-15
We present an alternative proof to the previous proposition by appealing to the existence of a certain inner product on complex representations of finite groups.

#definition[
  Given a vector space $V$ over $CC$, a _Hermitian pairing/inner product_ is a hermitian-bilinear map $V times V -> CC$, $(v, w) |-> angle.l v, w angle.r$ such that 
  - linear in the first coordinate;
  - conjugate-linear in the second coordinate;
  - $angle.l v, v angle.r in RR^(>= 0)$ and equal to zero iff $v = 0$.
 ]

 #theorem[Let $V$ be a finite dimensional complex representation of a finite group $G$. Then, there is a hermitian inner product $angle.l dot, dot angle.r$ such that $angle.l g v , g w angle.r = angle.l v, w angle.r$ for every $g in G$ and $v, w in V$.]

 #proof[
  Let $angle.l dot, dot angle.r_0$ be any inner product on $V$ (which exists by defining $angle.l e_i, e_j angle.r_0 = delta_i^j$ and extending by conjugate linearity). We apply "averaging": $
  angle.l v, w angle.r := 1/(hash G) sum_(g in G) angle.l g v, g w angle.r.
  $ Then, one can check that $angle.l dot, dot angle.r$ is hermitian linear, positive, and in particular $G$-equivariant.
 ]

 From this, the previous proposition follows quickly by taking $W' = W^perp$, the orthogonal complement to $W$ with respect to the $G$-invariant inner product that the previous theorem provides.

 From this proposition, Maschke's follows by repeatedly applying this logic. Since at each stage $V$ is split in two, eventually the dimension of the resulting dimensions will become zero since $V$ finite dimensional. Hence, the remaining vector spaces $V_1, dots, V_t$ left will necessarily be irreducible, since if they weren't, we could apply the proposition further.

// % ! 01-17
#theorem("Schur's Lemma")[
  Let $V, W$ be irreducible representations of a group $G$. Then, $
  Hom_G (V, W) = cases(0 "if" V tilde.eq.not_G W, CC "if" V tilde.eq_G W),
$ where $Hom_G (V, W) = {T : V -> W | T "linear and" G-"equivariant"}$.
]

#proof[
  Suppose $V tilde.eq.not_G W$ and let $T in Hom_G (V, W)$. Then, notice that $ker(T)$ a subrepresentation of $V$ (a subspace that is a representation in its own right), but by assumption $V$ irreducible hence either $ker(T) = V$ or ${0}$.

  If $ker(T) = V$, then $T$ trivial, and if $ker(T) = {0}$, then this implies $T : V-> im(T) subset W$ a representation isomorphism, namely $im(T)$ a irreducible subrepresentation of $W$. This implies that, since $W$ irreducible, $im(T) = W$, contradicting the original assumption.

  Suppose now $V tilde.eq_G W$. Let $T in Hom_G (V, W) = "End"_G (V)$. Since $CC$ algebraically closed, $T$ has an eigenvalue, $lambda$. Then, notice that $T - lambda I in "End"_G (V)$ and so $ker(T - lambda I) subset V$ a, necessarily trivial because $V$ irreducible, subrepresentation of $V$. Hence, $T - lambda I = 0 => T = lambda I$ on $V$. It follows that $Hom_G (V, W)$ a one-dimensional vector space over $CC$, so namely $CC$ itself.
]

#corollary[
  Given a general representation $V = plus.circle.big_(j=1)^t V_j^(m_j)$, $
  m_j = dim_CC Hom_G (V_j, V).
  $
]

#definition("Trace")[The trace of an endomorphism $T : V-> V$ is the trace of any matrix defining $T$. Since the trace is conjugation-invariant, this is well-defined regardless of basis.]

#proposition[
  Let $W subset.eq V$ a subspace and $pi : V -> W$ a projection. Then, $tr(pi) = dim(W)$.
]
#theorem[If $rho : G -> "Aut"_FF (V)$ a complex representation of $G$, then $
dim (V^G) = 1/(hash G) sum_(g in G) tr(rho(g)),
$  where $V^G = {v in V : g v = v forall g in G}$.
]

#proof[
  Let $pi = 1/(hash G) sum_(g in G) rho(g)$. Then, $
  pi^2 = (1/(hash G))^2 sum_(g in G) sum_(h in G) rho (g h) \ 
  = (1/(hash G))^2 hash G sum_(g in G) rho(g) = pi.
  $ We show $V^G = im(pi)$. If $v in im(pi)$, then $v = pi (w)$, so for every $h in G$, $
  rho(h) v &= 1/(hash G) sum_(g in G) rho(h g) w \ 
  &= 1/(hash G) sum_(h g in G) rho(h g) w \ 
  &=  pi (w) = v,
  $ so $v in V^G$. Conversely, if $v in V^G$, then $
  pi (v) &= 1/(hash G) sum_(g in G) rho(g) v = 1/(hash G) sum_(g in G) v = v,
  $ so $v in im(pi)$. Hence, $pi$ a projection with image $V^G$, so we conclude $
  dim(V^G) = tr(pi) = 1/(hash G) sum_(g in G) tr(rho(g)).
  $
]

== Characters, Orthogonality, Number of Irreducible Representations

#definition[
  Let $dim (V) < infinity$ and $G$ a group. The _character_ of $V$ is the function $
  chi_V : G -> CC, wide chi_V (g) := tr(rho(g)).
  $
]

#proposition[Characters are class functions, namely constant on conjugacy classes.]

#proof[
  Follows from the fact that the trace of a matrix is conjugation invariant.
]

// #theorem[If $V_1, V_2$ are 2 representations of $G$, then $V_1 tilde.eq_G V_2 <=> chi_(V_1) = chi_(V_2)$.]

#proposition[
  Given two representations $V, W$ of $G$, there is a natural action of $G$ on $Hom(V, W)$ given by $g ast T = g compose T compose g^(-1)$. Then, 
  $
  Hom(V, W)^G = {T : V -> W | g ast T = T},
  $ so $
  Hom(V, W)^G = Hom_G (V, W).
  $
]

#proposition[
  Suppose $V = V_1^(m_1) plus.circle dots.c plus.circle V_t^(m_t)$ a representation of $G$ written in irreducible form. Then,
  $
  Hom_G (V_j, V) = CC^(m_j).
  $
]

#proof[
By Maschke's Theorem and Schur's Lemma combined, $
"Hom"_G (V_j, V) &= "Hom"_G (V_j, V_1^m_1 plus.circle dots.c plus.circle V_t^(m_t)) \ 
&= plus.circle.big_(i=1)^t "Hom"_G (V_j, V_i)^(m_i) \ 
&= CC^(m_j)
$
]

#proposition[
  If $V, W$ are two representations, then so is $V plus.circle W$ with point-wise action, and $chi_(V plus.circle W) = chi_V + chi_W$.
]

#proof[
  We may pick an appropriate basis for $g in G$ such that $g$ acts on $V plus.circle W$ as $
  g = mat([rho_V (g)], 0; 0, [rho_W (g)]),
  $ where $rho_V, rho_W$ are the matrix representations of $g$ acting on $V, W$ respectively. From this, it is immediate that $tr(g) = tr(rho_V (g)) + tr(rho_W (g)) = chi_V + chi_W$.
]

#theorem[
  $chi_(Hom(V, W)) = overline(chi_V) chi_W$.
]
#proof[
  Let $g in G$ and $e_1, dots, e_n$ an eigenbasis for $V$ such that $g e_i = lambda_i e_i$ and $f_1, dots, f_m$ an eigenbasis for $W$ such that $g f_j = mu_j f_j$. Then, $
  {phi_(i)^j : V -> W | phi_(i)^j (e_ell) = f_j dot delta_(i)^ell, thin 1 <= i <= n, 1 <= j <= m}
  $ is a basis for $"Hom"(V, W)$, upon which $g$ acts by $
  g phi_(i)^j (g^(-1) e_ell) &= g phi_i^j (lambda_ell^(-1) e_ell) \
  &= lambda_ell^(-1) g f_j delta_(i)^ell \ 
  &= lambda_ell^(-1) mu_j delta_(i)^ell,
  $ hence $
  tr(g) = (sum_(i=1)^n lambda_ell^(-1)) (sum_(j=1)^m mu_j) = (sum_(i=1)^n overline(lambda_i)) (sum_(j=1)^m mu_j) = (overline(sum_(i=1)^n lambda_i)) (sum_(j=1)^m mu_j) = overline(chi_V (g)) chi_W (g)
  $ where we use the fact that $lambda^(-1) = overline(lambda)$ being a root of unity, and complex conjugation is linear.
]

#theorem("Orthogonality of Irreducible Group Characters")[
  Suppose $V_1, dots, V_t$ is a list of irreducible representations of $G$ and $chi_1, dots, chi_t$ are their corresponding characters. Then, the $chi_j$'s naturally live in the space $L^2 (G) tilde.eq CC^(hash G)$, which we can equip with the inner product $
  angle.l f_1, f_2 angle.r : 1/(hash G) sum_(g in G) overline(f_1 (g)) f_2 (g).
  $ Then, $
  angle.l chi_i, chi_j angle.r = delta_i^j.
  $
]

#proof[
$
angle.l chi_i, chi_j angle.r &= 1/(hash G) sum_(g in G) overline(chi_i (g)) chi_j (g) \ 
&= 1/(hash G) sum_(g in G) chi_(Hom(V_i, V_j)) (g) \ 
&= dim_CC (Hom (V_i, V_j)^G) \ 
&= cases(
  dim_CC (CC) i =j\
  dim_CC (0) i eq.not j
) = delta_i^j.
$
]

#corollary[
  $chi_1, dots, chi_t$ orthonormal vectors in $L^2 (G)$.
]

#corollary[
  $chi_1, dots, chi_t$ linearly independent, so in particular $t <= hash G = dim L^2 (G).$
]

#corollary[
  $t <= h(G) := hash$ conjugacy classes.
]

#proof[
  We have that $L_c^2 (G) subset.eq L^2 (G)$, where $L_c^2 (G)$ is the space of $CC$-valued functions on $G$ that are constant on conjugacy classes. It's easy to see that $dim_CC (L_c^2 (G)) = h(G)$. Then, since $chi_1, dots, chi_t$ are class functions, the live naturally in $L_c^2 (G)$ and hence since they are linearly independent, there are at most $h(G)$ of them.
]

#remark[
  We'll show this inequality is actually equality soon.
]

#theorem("Characterization of Representation by Characters")[
  If $V, W$ are two complex representations, they are isomorphic as representations $<=>$ $chi_V = chi_W$.
]

#proof[
  By Maschke's, $V = V_1^m_1 plus.circle dots.c plus.circle V_t^m_t$ and hence $chi_V = m_1 chi_1 + dots.c + m_t chi_t$. By orthogonality, $m_j = angle.l chi_V, chi_j angle.r$ for each $j = 1, dots, t$, hence $V$ completely determined by $chi_V$. 
  
  #qedhere
]

#definition("Regular Representation")[
  Define $
  V_"reg" &:=  CC[G] "with left mult."\ 
  &tilde.eq L^2 (G) "with" (g ast f)(x) := f(g^(-1) x),
  $ the "regular representation" of $G$.
]

#proposition[
  $chi_"reg" (g) = cases(hash G & "if" g = id \ 0 "else" )$.
]
#proof[
  If $g = id$, then $g$ simply acts as the identity on $V_"reg"$ and so has trace equal to the dimension of $V_"reg"$, which has as basis just the elements of $G$ hence dimension equal to $hash G$. If $g eq.not id$, then $g$ cannot fix any basis vector, i.e. any other element $h in G$, since $g h = h <=> g = id$. Hence, $g$ permutes every element in $G$ with no fixed points, hence its matrix representation in the standard basis would have no 1s on the diagonal hence trace equal to zero.
]

#theorem[
  Every irreducible representation of $V$, $V_j$, appears in $V_"reg"$ at least once, specifically, with multiplicity $dim _CC (V_j)$. Specifically, $
  V_"reg" = V_1^(d_1) plus.circle dots.c plus.circle V_t^(d_t),
  $ where $d_j := dim_CC (V_j)$.

  In particular, $
  hash G = d_1^2 + dots.c + d_t^2.
  $
]
#proof[
Write $V_"reg" = V_1^(m_1) plus.circle dots.c plus.circle V_t^m_t$. We'll show $m_j = d_j$ for each $j = 1, dots, t$. We find $
m_j &= angle.l chi_"reg", chi_j angle.r \ 
&= 1/(hash G)  sum_(g in G) overline(chi_"reg" (g)) chi_j (g) \ 
&= 1/(hash G) hash G dot chi_j (id) = chi_j (id) = d_j,
$ since the trace of the identity element acting on a vector space is always the dimension of the space. In particular, then $
hash G = dim_CC (V_"reg") &= dim_CC (V_1^d_1 plus.circle dots.c plus.circle V_t^(d_t)) \ 
&= d_1 dot dim_CC (V_1) + dots.c + d_t dot dim_CC (V_t) \ 
&= d_1^2 + dots.c + d_t^2.
$
]

#theorem[$t = h(G)$.]

#proof[
  Remark that $CC[G]$ has a natural ring structure, combining multiplication of coefficients in $CC$ and internal multiplication in $G$. Define a group homomorphism $
  underline(rho)  = (rho_1, dots, rho_t) : G -> "Aut"(V_1) times dots.c times "Aut"(V_t),
  $ collecting all the irreducible representation homomorphisms into a single vector. Then, this extends naturally by ($CC$-)linearity to a ring homomorphism $
  underline(rho) : CC[G] -> "End"_CC (V_1) plus.circle dots.c plus.circle "End"_CC (V_t).
  $ By picking bases for each $"End"_CC (V_j)$, we find that $dim_CC ("End"_CC (V_j)) = d_j^2$ hence $dim_CC ("End"_CC (V_1) plus.circle dots.c plus.circle "End"_CC (V_t)) = d_1^2 + dots.c + d_t^2 = hash G$, as we saw in the previous theorem. On the other hand, $dim_CC (CC[G]) = hash G$ hence the dimensions of the two sides are equal. We claim that $underline(rho)$ an isomorphism of rings. By dimensionality as $CC$-vector spaces, it suffices to show $underline(rho)$ injective.

  Let $theta in ker(underline(rho))$. Then, $rho_j (theta) = 0$ for each $j = 1, dots, t$, i.e. $theta$ acts as 0 on each of the irreducibles $V_1, dots, V_t$. Applying Maschke's, it follows that $theta$ must act as zero on every representation, in particular on $CC[G]$. Then, for every $sum beta_g g in CC[G]$, $theta dot (sum beta_g g) = 0$ so in particular $theta dot 1 = 0$ hence $theta = 0$ in $CC[G]$. Thus, $underline(rho)$ has trivial kernel as we wanted to show and thus $CC[G]$ and $"End"_CC (V_1) plus.circle dots.c plus.circle "End"_CC (V_t)$ are isomorphic as rings (moreover, as $CC$-algebras).

  We look now at the centers of the two rings, since they are (in general) noncommutative. Namely, $
  Z(CC[G]) = {sum lambda_g g | (sum lambda_g g) theta = theta (sum lambda_g g) forall theta in CC[G]}.
  $ Since multiplication in $CC$ is commutative and "factors through" internal multiplication, it follows that $sum lambda_g g in Z(CC[G])$ iff it commutes with every group element, i.e. $
  (sum lambda_g g) h = h (sum lambda_g g) & <=> sum_g (lambda_g h^(-1) g h) = sum_g lambda_g g \
  & <=> sum_g lambda_(h^(-1) g h) g = sum_g lambda_g g \ 
  & <=> lambda_(h^(-1) g h) = lambda_g forall g in G.
  $ Hence, $sum lambda_g g in Z(CC[G])$ iff $lambda_(h^(-1) g h) = lambda_g$ for every $g, h in G$. It follows, then, that the induced map $g |-> lambda_g$ a class function, and thus $dim_CC (Z(CC[G])) = h(G)$.

  On the other hand, $dim_CC (Z("End"_CC (V_j))) = 1$ (by representing as matrices, for instance, one can see that only scalar matrices will commute with all other matrices), hence $dim_CC (Z("End"_CC (V_1) plus.circle dots.c plus.circle "End"_CC (V_t))) = t$. $underline(rho)$ naturally restricts to an isomorphism of these centers, hence we conclude justly $t = h(G)$.
]

#remark[
  By picking bases for each irreducible representation $V_1, dots, V_t$, we can realize more concretely that $
  CC[G] tilde.eq M_d_1 (CC) plus.circle dots.c plus.circle M_(d_t) (CC),
  $ where $d_j := dim(V_j)$; in short, then, $CC[G]$ completely determined, as a group-ring, by 
  - the number of conjugacy classes in $G$, $t$; and
  - the dimension of each irreducible representation, $d_1, dots, d_t$.
  In particular, then, there may exist two non-isomorphic groups with isomorphic group rings.
]

== Fourier Analysis on Finite Abelian Groups

#definition[
  For a finite group $G$, let $
  L^2 (G) = {"square integrable functions" G -> CC},
  $ equipped with the $L^2$-norm, $||f||^2 = 1/(hash G) sum_(g in G) |f(g)|^2$. This is a vector space isomorphic to $CC^(hash G)$. We make the space a Hilbert space by defining $
  angle.l f_1, f_2 angle.r = 1/(hash G) sum_(g in G) overline(f_1 (g)) f_2 (g).
  $
]
#definition[
  Denote by $hat(G) = {chi_1, dots, chi_N}$ the set of irreducible characters of $G$. Then, $hat(G)$ an orthonormal family of functions in $L^2 (G)$.
]

We suppose for now $G$ abelian. In this case, $hash hat(G) = hash G$ so $hat(G)$ is an orthonormal basis for $L^2 (G)$ (comparing dimensions). In particular, one can prove that $hat(G)$ is abstractly isomorphic to $G$ as a group.

#definition[
  Given $f in L^2 (G)$, the function $hat(f) : hat(G) -> CC$ is defined by $
  hat(f)(chi) = 1/(hash G) sum_(g in G) overline(chi)(g) f(g),
  $ called the _Fourier transform_ of $f$ over $G$. Then, $
  f = sum_(chi in hat(G)) hat(f)(chi) chi,
  $ is called the _Fourier inversion formula_.
]

#example[
  Consider $G = RR\/ZZ$. $L^2 (G)$ space of $CC$-valued periodic functions on $RR$ which are square integrable on $[0, 1]$. Then, $hat(G)$ abstractly isomorphic to $ZZ$. Write $hat(G) = {chi_n | n in ZZ}$. Then, remark that $
  chi_n : RR\/ZZ -> CC^times, wide chi_n (x) = e^(2 pi i n x)
  $ gives the characteristic function for any integer $n$. More precisely, its not hard to see that the map $RR -> CC^times, x |-> e^(2 pi i n x)$ factors through (is constant on integer multiples) $ZZ$. 

  To speak about orthogonality of members of $hat(G)$, we must define a norm. We can identity $RR\/ZZ$ with $[0, 1]$, and so write $
  angle.l f_1, f_2 angle.r := integral_(0)^1 overline(f_1 (x)) f_2 (x) dif x. 
  $ Then, its not hard to see $
  angle.l chi_n, chi_m angle.r = integral_(0)^1 e^(-2 pi i (m - n) x) dif x = delta_m^n.
  $
]

#example[
  Let $G = ZZ\/N ZZ$ under addition. Note that $G$ then a subgroup of $RR\/ZZ$, and in particular, $
  hat(G) = {chi_0, chi_1, dots, chi_(N-1)}, wide chi_j (k) := e^(2 pi i j k\/N) .
  $ Then, one notices $
  chi_j_1 dot chi_j_2 = chi_(j_1 + j_2),
  $ so there is indeed a natural group structure on $hat(G)$. Then, the Fourier transform in this case gives, for $f in L^2 (ZZ\/N ZZ)$, $
  hat(f) (n) = 1/N sum_(k=0)^(N-1) e^(-2 pi i n k\/N) f(k).
  $
]
=== Application to Computing Particular Infinite Series

We consider an application of the theory we've developed on $G = ZZ\/N ZZ$ to study particular infinite summations. Its well know that the harmonic series $1 + 1/2 + 1/3 + dots.c$ diverges. A natural extension is to study modified such series, for instance $1 - 1/3 + 1/5 - 1/7 + dots.c$ and to ask if this series converges, and if it does, to what?

To approach this question, we more generally consider, for $f in L^2 (ZZ\/N ZZ)$ (i.e. a complex-valued $N$-periodic function defined on the integers), the series $
S(f) := sum_(n=1)^infinity f(n)/n,
$ when the summation exists. Remark then that $f |-> S(f)$ is linear. So, it suffices to consider the value of $S(f)$ on a basis of $L^2 (ZZ\/N ZZ)$, which we've derived in the previous example, namely $hat(G) = {chi_j : j = 0, dots, N-1}$. We can explicitly compute $S(chi_j)$: $
S(chi_j) &= sum_(n=1)^infinity (chi_j (n))/n \ 
&= sum_(n=1)^infinity (x^n)/n, wide x := e^((2 pi i j)/N) \ 
&= - log ( 1 - x),
$ where the final sequence converges on the unit circle in the complex plane centered at the $1 + 0 i$. 

In particular, if $j = 0$, $S(chi_0)$ diverges. Otherwise, each $chi_j$ maps onto the roots of unity hence the convergence is well-defined. In particular, then, we find $
S(chi_j) = cases(
  - log (1 - e^(2 pi i j/N)) &"if" j eq.not 0,
  0 &"else"
).
$ Now, for a general function $f in L^2 (ZZ\/N ZZ)$, we find by the Fourier inversion formula $
S(f) = S(hat(f)(0) chi_0 + dots.c + hat(f)(N-1) chi_(N-1)),
$ which certainly diverges if $hat(f)(0) eq.not 0$. Otherwise, we find by linearity $
S(f) = sum_(j=1)^(N-1) hat(f)(j) (- log(1 - x)).
$ So, returning to our original example, we can define $f in L^2 (ZZ\/4 ZZ)$ by $f(n) = cases(
  0 &"if" n "even",
  1 &"if" n = 1 + 4 k,
  -1 &"if" n = 3 + 4 k
)$. Then, we find $
1 - 1/3 + 1/5 - 1/7 + 1/9 - dots.c &= S(f) \
&= 1/(2 i) (S(chi_1) - S(chi_3)) \ 
&= 1/(2 i) (- log(1 - i) + log(1 + i)) \ 
&= 1/(2 i) (- log (sqrt(2)) + (pi i)/4 + log(sqrt(2)) + (pi i)/4) = pi/4.
$

== Fourier Analysis on Non-Abelian Finite Groups

When $G$ abelian, recall that $CC[G]$ was a commutative ring isomorphic to $plus.circle.big_(chi in hat(G)) CC$. More generally, we find an isomorphism $
Phi : CC[G] -> plus.circle_(j=1)^h "End"_CC (V_j) tilde.eq  plus.circle_(j=1)^h "M"_(d_j times d_j)  (CC),
$ where $h = h(G)$, $V_j$ enumerate the irreducible representations of $G$, and $d_j := dim_CC (V_j)$.

#definition("Fourier Transform")[
  Given a function $f : G -> CC$, denote by $
  theta_f = sum_(g in G) f(g) g
  $ its corresponding element in $CC[G]$. Then, its corresponding image under $Phi$ in $plus.circle.big "End"(V_j)$ is called the _Fourier transform_ of $f$, i.e. $
  hat(f) = (T_1, dots, T_h) in plus.circle.big "End"(V_j),
  $ a $h$-tuple of matrices where $T_i$ a $d_i times d_i $matrix.
]

=== Random Products in Groups
#definition("Probability Measure on a Group")[
  A probability measure on a group $G$ is a function $mu : G -> [0, infinity)$ such that $sum_(g) mu(g) = 1$. Then, we can view $mu$ as living naturally both in $RR^G$ and $RR[G]$ through the standard identification.
]

One of the key properties we notice by viewing $mu$ as living in $RR[G]$ is in multiplication; multiplication in $RR[G]$ corresponds to convolution of functions. Namely, if $mu_1, mu_2$ two measures on $G$, then $
(mu_1 ast.circle mu_2)(g) = sum_((g_1, g_2) in G times G, \ g_1 g_2 = g) mu_1 (g_1) mu_2 (g_2) = mu_1 times_(RR[G]) mu_2\
= PP("getting" g "from a random product of" g_1, g_2 "with" g_i "picked according to" mu_i).
$ For a fixed probability measure $mu$, then, we wish to investigate the limiting behavior of $mu^(ast.circle N)$ ($mu$ convolved with itself $N$ times for large $N$), which corresponds to the likelihood of obtaining a particular element from large numbers of products in the group.

#definition[
  Define the support $
  "supp"(mu) = {g in G | mu(g) eq.not 0},
  $ and the 2 subgroups $
  G_mu := "subgroup generated by" g in "supp"(mu),\
  G_mu^+:= "subgroup generated by" {g^(-1) h | g, h in "supp"(mu)}.
  $ Notice then $G_mu^+ subset G_mu subset G$.
]

#theorem[Let $mu$ a probability measure on $G$. Then, if $G_mu^+ = G$, then $lim_(N -> infinity) mu^(ast.circle N) = mu_"unif"$, where $mu_"unif"$ the uniform probability distribution which assigns $1/(hash G)$ to each element in $G$.]


== Character Tables of $S_4, A_5$ and $"GL"_3 (FF_2)$


=== $S_4$
For $S_4$, we denote the conjugacy classes by $1A, 2A, 2B, 3A, 3B, 4A$ as the conjugacy classes of elements of the form $(), (12)(34), (12), (123), (1234)$ respectively. 

#figure(
  table(
    columns: 6,
    stroke: none,
    "", $1A$, $2A$, $2B$, $3A$, $4A$,
    table.hline(start: 0, end: 7),
    table.vline(x:1, start: 0, end: 7),
    $chi_1$, $1$, $1$, $1$,$1$, $1$,
    $chi_2$, $1$, $1$, $-1$, $1$, $-1$,
    $chi_3$, $2$, $2$, $0$, $-1$,$0$,
    $chi_4$, $3$, $-1$, $1$, $0$, $-1$,
    $chi_5$, $3$, $-1$, $-1$, $0$, $1$
  )
  ) <table:s4>

$chi_1$ is the trivial representation. $chi_2$ is the sign representation given by $sigma |-> "sgn"(sigma) in {-1, 1} subset.eq CC^times$. $chi_3$ comes from noticing that $K_4 = ZZ\/2 times ZZ\/2 = 1A union.sq 2A subset.eq S_4$ gives $S_4\/K_4 tilde.eq S_3$. We then can find a new representation by composing the quotient map $pi : S_4 -> S_3$ with a representation $rho : S_3 -> "Aut"_CC (V)$. Remember that there are three irreducible representations of $S_3$. The first two are the trivial and sign, already accounted for here. The last is the unique two-dimensional representation where $chi(2A) = 0$ and $chi(3A) = -1$ (these are the conjugacy classes in $S_3$ now). Under the quotient map, then, we find that
- since $1A, 2A$ contained in $K_4$, they are mapped to the identity in $"Aut"(CC^2)$ so have trace $2$;
- $2B$, $4A$ must be mapped to elements of order 2 in $S_3$ (i.e. in $2A$) under $pi$ and thus must have trace $0$;
- $3A$ must map to elements of order $3$ in $S_3$ under $pi$ so must have trace $-1$. 
This characterizes $chi_3$.

$chi_4$ comes from the standard representation on a 4 dimensional vector space (by permuting basis vectors), then subtracting off the trivial representation. This results in a character where each entry equals the number of fixed points each conjugacy class has, minus 1.

$chi_5$ comes from considering the homomorphism representation found from $V_5 = "Hom"(V_2, V_4)$, where $V_2, V_4$ the vector spaces upon which $chi_2$, $chi_4$ "act". Hence, $V_5$ is a three dimensional representation, with $chi_5 = overline(chi)_2 chi_4$.

=== $A_5$
For $A_5$, denote the conjugacy classes $1A, 2A, 3A, 5A, 5B$.

#align(center,
  table(
    columns: 6,
    stroke: none,
    "", $1A$, $2A$, $3A$, $5A$, $5B$,
    table.hline(start: 0, end: 7),
    table.vline(x:1, start: 0, end: 7),
    $chi_1$, $1$, $1$, $1$,$1$, $1$,
    $chi_2$, $4$, $0$, $1$, $-1$, $-1$,
    $chi_3$, $5$, $1$, $-1$, $0$, $0$,
    $chi_4$, $3$, $-1$, $0$, $1 + zeta + zeta^(-1)$, $1 + zeta^2 + zeta^(-2)$,
    $chi_5$, $3$, $-1$, $0$, $1 + zeta^2 + zeta^(-2)$, $1 + zeta + zeta^(-1)$
  )
)

$chi_1$ trivial. $chi_2$ comes from the standard representation, minus the trivial. $chi_3$ similarly comes from the action of $A_5$ on the coset space $S_5\/F_20$, or equivalently on $A_5\/D_10$, minus the trivial again.

For the last two, we can check by dimensionality that it must be that the dimensions of both must be 3, so we are looking for representations $rho : A_5 -> "Aut"_CC (CC^3)$. Let $g in 5A$. Notice then that $g$ must have at most three eigenvalues, which are fifth roots of unity. But also, notice that $g$ and $g^(-1)$ are conjugate in $A_5$, and namely $g, g^(-1) in 5A$. Hence, since a linear transformation has inverse eigenvalues of its inverse, it follows that the set of eigenvalues for $g$ must be closed under taking inverses. So, the eigenvalues must be of the form ${1, zeta, zeta^(-1)}$ or ${1, zeta^2, zeta^(-2)}$ where $zeta$ a primitive root of unity. It follows then that either $tr(5A) = 1 + zeta + zeta^(-1)$ or $1 + zeta^2 + zeta^(-2)$, with, by symmetrical argument, gives the trace of $5B$ since $g in 5A => g^2 in 5B$.

Then, to find $chi(3A) =: x_3$, taking the inner product with $chi_2$ we find $
0 &= 12 + 20 x_3  - 12 (1 + zeta + zeta^(-1)) - 12 (1 + zeta^2 + zeta^(-2)) \ 
&= 20 x_3 - 12 (underbrace(1 + zeta + zeta^2 + zeta^3 + zeta^4, = 0)) => x_3 = 0.
$
From here, one can compute $chi (2A)$ using orthogonality relations.



=== $"GL"_3 (FF_2)$
#align(center,
  table(
    columns: 7,
    stroke: none,
    "size:", $1$, $21$, $56$, $42$, $24$, $24$,
    "", $1A$, $2A$, $3A$, $4A$, $7A$, $7B$,
    table.hline(start:0, end: 8),
    table.vline(x: 1, start:0, end: 8),
    $chi_1$, $1$, $1$, $1$, $1$, $1$, $1$,
    $chi_2$, $6$, $2$, $0$, $0$, $-1$, $-1$,
    $chi_3$, $7$, $-1$, $1$, $-1$, $0$, $0$,
  )
)

$chi_1$ trivial. We consider $chi_V$ given by $G$ acting on $FF_2^3$ in the standard way (as three by three matrices) Then, the character is just given by the number of fixed points each element has, so in this case the number of fixed nonzero vectors. 
- $1A$ 7, being the dimension
- A typical element of $2A$ looks like $mat(1, "", 1; "", 1, ""; "", "", 1)$ which has trace $3$.
- $g in 3A$ has minimal polynomial $(x-1)(x^2+x+1)$ so has a one-dimensional eigenspace so fixes one nonzero vector.
- $g in 4A$ has minimal polynomial $(x-1)^3$ so by similar reasoning as $3A$ fixes a one-dimensional eigenspace.
- $g in 7A$ or $7B$ must cyclically permute the basis vectors so fixes none so has trace $0$.
In summary:
#align(center,
  table(
    columns: 7,
    stroke: none,
    "", $1A$, $2A$, $3A$, $4A$, $7A$, $7B$,
    table.hline(start:0, end: 8),
    table.vline(x: 1, start:0, end: 8),
    $chi_V$, $7$, $3$, $1$, $1$, $0$, $0$
  )
)
This is not irreducible by checking orthogonality relations, but we obtain $chi_2$ by subtracting off $chi_1$.

For $chi_3$, consider $X = {"sylow"-7 "subgroups"}$. One can check $hash X = 8$, and we have a natural action of $G$ on $X$ by conjugation, which is isomorphic to the action of $G$ on $G\/N("Sylow"-7)$ so $H:= N("Sylow"-7)$ has cardinality 21. Then, the trace of each element is just the number of fixed cosets each element has acting on $G\/H$. We then subtract off 1 from this number to obtain $chi_3$.

- $g in 1A$ must have trace $8$ so $chi_3 (1A) = 7$
- if $g in 2A$, $g a H = a H <=> a^(-1) g a in H$, but $g$ of order $2$ and thus so is $a^(-1) g a$, but $H$ a group of cardinality of order $21$ so such an element can't live in it.Thus $g$ has no fixed points and $chi_3 (2A) = -1$. In particular $g$ as a permutation looks like 4 disjoint 2 cycles.
- if $g in 4A$, similar reasoning follows and we find $chi_3 (4A) = -1$ and $g$ looks like 2 disjoint 4 cycles.
- $g in 7A, 7B$ must act as a 7-cycle and so has one fixed point and thus $chi_3 (7A) = chi_3 (7B) = 0$.
- we can compute $chi_3 (3A)$ by checking the orthogonality relations by taking the inner product of it with itself. Computing this we find that $chi_3 (3A) = plus.minus 1$. We conclude it must be $1$ by remarking that $3A$ acts on $G\/H$ either by a single 3 cycles (hence with 5 fixed points) or two three cycles (hence with 2), so it must be that the second case holds which gives us a character of 1. 

== Induced Representations

Let $G$ a finite group and $H subset.eq G$, and take $chi in "Hom"(H, CC^times)$ a one-dimensional representation of $H$. Consider the space $
V_chi = {f : G -> CC | f(x h) = chi(h) dot f(x) forall h in H}.
$ Then,
#proposition[
1. $G$ acts (linearly) on $V_chi$ by the rule $g f (x) = f (g^(-1) x), forall x in G.$
2. $dim(V_chi) = [G:H]$
]

#proof[
  1. We need to show $g f in V_chi$. We compute, $
  g f (x h) = f (g^(-1) (x h)) = f((g^(-1) x) h) = chi(h) f(g^(-1) x) = chi(h) (g f) (x),
  $ for any $x in G, h in H, f in V_chi$, as required.
  2. Let $a_1, dots, a_t$ be a set of coset representatives for $H$, i.e. $G = a_1 H union.sq dots.c union.sq a_t H$. Then, we claim that the map $f |-> (f(a_1), dots, f(a_t))$, $V_chi -> CC^t$ a $CC$-vector space isomorphism.

  _Injective:_ If $f$ in the kernel of this map, then $f(a_1) = dots.c = f(a_t) = 0$. But $f in V_chi$ so $f(a_j h) = chi(h) f(a_j) = 0$ for any $h in H$, $j = 1, dots, t$. Any element in $G$ is in some $a_j H$ so equals $a_j h$ for some $h in H$, so we conclude that $f$ must be identically 0 and so this map injective.

  _Surjective:_ Given $(lambda_1, dots, lambda_t) in CC^t$, define $f$ by $f(a_j) := lambda_j$ for each $j$, and "extend" naturally to behave under action of $H$, namely $f(a_j h) := chi(h) f(a_j) = chi_h lambda_j$.
]

The representation $V_chi$ is called the _induced_ representation of $chi$ from $H$ to $G$. We sometimes write $
V_chi = "Ind"_H^G chi.
$ If $H$ is a quotient of $G$, then any representation of $H$ gives a representation of $G$ (we've done this many times before, such as with $S_4$ and $S_3$). But in general, these aren't easy to come by. But if $H$ just a subgroup of $G$, which are far more common, then we can use the induced representation technique above to look at representations of $G$.

Let $psi : H -> CC^times$ some one-dimensional representation of $H$ and $V_psi = "Ind"_H^G psi$. We wish to find the induced character $chi_V_psi$.

We begin by looking for a basis for $V_psi$. For any $a in G$, define $f_a in V_psi$ defined by $
f_a : G -> CC, wide f_a (g) := cases(
  psi(h) & "if" g = a h in a H,
  0 & "if" g in.not a H
).
$ Then, if $a_1, dots, a_t$ coset representatives for $H$ in $G$, $beta:= {f_a_1, dots, f_a_t}$ a basis for $V_psi$.  

Now, given $g in G$, what is the matrix of $g$ acting on $V_psi$ with respect to the basis $beta$? We have that $
g dot f_a_j (x) = f_a_j (g^(-1) x) = f_(g a_j) (x),
$ since, more precisely $
g f_a_j (a_i) = cases(
  0 "if" g^(-1) a_i in.not a_j H \ 
  psi(h) "if" g^(-1) = a_j h
),
$ and we can extend to general $g in G$. Hence, if $a_1, dots, a_t$ are coset representatives, $g a_j H = a_i H$ for each $a_j$ and some $a_i$, i.e. $g$ permutes the coset representatives, modulo $H$. Hence, $g a_j = a_i h_(i j)$ for some $h_(i j) in H$. So, $
g f_a_j = f_(a_i h_(i j)) = psi(h_(i j)) f_(a_i).
$ Write $g a_i H = a_i' H$ so $g a_i = a_i' h_i$. With this, $g f_a_1 = psi(h_1) f_(a_1')$, etc, and so in each $i$th column of our matrix there is a single nonzero entry in the $i'$th row with entry $psi(h_i)$. 

Thus, $
chi_(V_psi) (g) &= sum_(i | g a_i = a_i h_i,\ h_i in H)  psi(h_i) = sum_(i=1)^t tilde(psi)(a_i^(-1) g a_i),
$ namely, we only sum over the $h_i$'s that  land the in the diagonal, which are only those that come from $g$ fixing the respective cosets. We put $tilde(psi)$ to be $psi$ on $H$ and $0$ elsewhere. In all, them, we have proven the following theorem.

#theorem[
  Let $H subset.eq G$ and $psi : H -> CC^times$ a one-dimensional representation of $H$. Then, the induced character from $H$ to $G$ is given by
  $
  chi_("Ind"_H^G psi) (g) = sum_(a H in G\/H,\ "s.t." a^(-1) g a in H) psi(a^(-1) g a)  = sum_(a in G\/H) tilde(psi) (a^(-1) g a),
  $ where $
  tilde(psi) (g) = cases(
    0 & "if" g in.not H\ 
    psi(h)  & "if" g in H
  ).
  $
]

Let's massage. 

#theorem[
  $
  chi_V_psi (g) = chi_("Ind"_H^G psi) (g) = (hash G)/(hash H) dot 1/(hash C(g)) sum_(gamma in C(g) sect H) psi(gamma),
  $ where $C(g)$ the conjugacy class of the element $g$,
]

#proof[
$
chi_(V_psi) (g) &= sum_(a H in G\/H,\ "s.t." a^(-1) g a in H) psi(a^(-1) g a)\
&= 1/(hash H) sum_(a in G, \ "s.t." a^(-1) g a in H) psi(a^(-1) g a) \
&= (hash Z(g))/(hash H) sum_(a in Z(g)\/G,\ "s.t" a^(-1) g a in H) psi(a^(-1) g a) \ 
&= (hash G)/(hash H) 1/(hash C(g)) sum_(gamma in C(g) sect H) psi(gamma),
$ where $Z(g) = {b in G | b g = g b}$ the centralizer of $G$, where $hash Z(g) = (hash G)/(hash C(g))$ by the orbit-stabilizer theorem (from $G$ acting on $C(g)$ by conjugation).
]

=== Back to $"GL"_3 (FF_2)$

Let $H subset.eq G = "GL"_3 (FF_2)$ the normalizer of a Sylow-7 subgroup; then $hash H = 21$ ($8$ Sylow-7 subgroups, $168/8 = 21$). Let $
psi : H -> CC^times
$ and $
V = "Ind"_H^G psi
$ the induced character. Then, we know $dim(V) = 168\/21 = 8$. Let $P_7$ be some Sylow-7 subgroup. Then, we find that $
H\/P_7 tilde.eq ZZ\/3 ZZ, 
$ so our representation factors to $
H ->> & ZZ\/3 ZZ -> CC^times,\
& 1 |-> e^(2 pi i\/3).
$ So specializing our formula we found in the previous section, we know $
chi_V_psi (g) = 8/(hash C(g)) sum_(gamma in H sect C(g)) psi(gamma).
$ We compute for $g$ in distinct conjugacy classes: 

#align(center,
table(columns: 3, stroke: none,
row-gutter: .5em,
$hash$, $C$, $chi_V_psi$,
table.hline(start: 0, end:3),
table.vline(x:2, start: 0, end:8),
$1$, $1A$, $8$,
$21$, $2A$, $0$,
$56$, $3A$, $-1$,
$42$, $4A$, $0$,
$24$, $7A$, $1$,
$24$, $7B$, $1$,
)
)

- The case for $1A$ is simple.
- The case for $2A$ and $4A$ are trivial since for $C = 2A, 4A$, $C sect H = nothing$, since $H$ a group of odd cardinality, and $C$ consists only of elements of even order, hence they must have empty intersection, so the summation in the character formula is over nothing.
- For $3A$, we need to compute $3A sect H$. We know that $
phi: H ->> ZZ\/3ZZ, 
$ so it must be that $
P_7 |-> 0, wide "7 elts of order 3" |-> 1, wide "7 elts of order 3" |-> 2,
$ so $
3A sect H = phi^(-1) (1) union.sq phi^(-1) (2).
$  Hence, $
chi_V_psi (3A) &= 1/7 (sum_(g in phi^(-1) (1)) psi(g) + sum_(g in phi^(-1) (2)) psi(g) ) \ 
&= 1/7 [7 e^(2 pi i\/3) + 7 e^(4 pi i\/3)] \ 
&= e^(2 pi i\/3) + e^(4 pi i\/3) = -1.
$
- For $g in 7A$, $
chi_(V_psi) (g) = 8/(24) sum_(g in 7A sect H) psi(g).
$ Its easy to see $psi(g) = 1$, since $g$ of order 7. So, the difficulty lies in computing the size $7A sect H$. There are certainly 6 elements of order 7 in $H$, but which are in 7A versus 7B? The key fact to notice is that, if $g in 7A, g^2, g^4 in 7A$ as well, and $g^(-1) = g^6$, $g^(3)$ and $g^5$ are in $7B$, which one verifies by checking the minimal polynomials of the two sets of elements (either $x^3+ x +1 , x^3 + x^2 + 1$). Thus, $
chi_V_psi (g) = 1/3 (1 + 1 + 1) = 1,
$ for both $g in 7A, 7B$.

One can take the inner product $angle.l chi_V_psi, chi_V_psi angle.r$ and find that it is equal to $1$, hence this new representation is irreducible. Naming this representation $chi_4$, we find the character table so far to be (from the previous section): 

#align(center,
  table(
    columns: 7,
    stroke: none,
    "size:", $1$, $21$, $56$, $42$, $24$, $24$,
    "", $1A$, $2A$, $3A$, $4A$, $7A$, $7B$,
    table.hline(start:0, end: 8),
    table.vline(x: 1, start:0, end: 8),
    $chi_1$, $1$, $1$, $1$, $1$, $1$, $1$,
    $chi_2$, $6$, $2$, $0$, $0$, $-1$, $-1$,
    $chi_3$, $7$, $-1$, $1$, $-1$, $0$, $0$,
    $chi_4$, $8$, $0$, $-1$, $0$, $1$, $1$,
    $chi_5$, $d_5$, $?$, $?$, $?$, $?$, $?$, 
    $chi_6$, $d_6$, $?$, $?$, $?$, $?$, $?$
  ) 
) We know then from the general theory that we are missing two representations. We know that the sum of the squares of the dimensions should equal the cardinality of the group, so $
168 = 1 + 36 + 49 + 64 + d_5^2 + d_6^2 => d_5^2 + d_6^2 = 18.
$ It's not hard to see the only way this is possible is that $d_5 = 3, d_6 = 3$.

== Tensor Products

We are often interested in generating new representations from exists ones. Suppose $V_1, V_2$ are two representations.

- _Direct sum:_ $
V_1 plus.circle V_2,
$ with character $chi_(V_1 plus.circle V_2) = chi_V_1 + chi_V_2$. 

- _Hom_ representation: given by $G$ acting on $
"Hom"_CC (V_1, V_2),
$ given by $
g ast T = g compose T compose g^(-1), wide g in G, T in "Hom"_CC (V_1, V_2),
$ which had character $chi_("Hom"_CC (V_1, V_2)) = overline(chi_(V_1)) dot chi_V_2$.

- _Dual_ representation: given by the action on $V_1^ast := "Hom"(V_1, CC)$ defined by $g ell = ell compose g^(-1)$. This gives $chi_(V_1^ast) = overline(chi_V_1)$ 

We define now the _tensor representation_:

#definition("Tensor Product")[
  Given representations $V_1, V_2$, put $
  V_1 times.circle V_2 = "Hom"_CC (V_1^ast, V_2).
  $
]

Then, one readily verifies $dim(V_1 times.circle V_2) = dim(V_1) dot dim(V_2).$

More concretely, let $v_1 in V_1$ and $v_2 in V_2$. Then for $ell in V_1^ast$, we can define $
v_1 times.circle v_2 (ell) := ell(v_1) dot v_2 in V_2.
$ One readily verifies that this definition genuinely defines an element of $"Hom"_CC (V_1^ast, V_2)$. 

One notices too that $times.circle$ is _bilinear_ in both arguments, namely for any $v_1, v_1 ' in V_1$, $v_2, v_2 ' in V_2$, $lambda in CC$ and $ell in V_1^ast$, then 
$
(lambda v_1 + v_1 ') times.circle v_2 = lambda (v_1 times.circle v_2) + (v_1 ' times.circle v_2),
$ and also $
v_1 times.circle (lambda v_2 + v_2 ') = lambda (v_1 times.circle v_2) + (v_1 times.circle v_2 ').
$ Let $e_1, dots, e_n$ a basis for $V_1$ and $f_1, dots, f_m$ a basis for $V_2$, and consider $v_1 = a_1 e_1 + dots.c + a_n e_n$, $v_2 = b_1 f_1 + dots.c + b_m f_m$ for $a_i, b_j in CC$. Then, using the bilinearity, we find $
v_1 times.circle v_2 &= (a_1 e_1 + dots.c + a_n e_n) times.circle (b_1 f_1 + dots.c + b_m f_m) \
&= sum a_i b_j (e_i times.circle f_j),
$ so we find from this that the elements $e_i times.circle f_j$ for $1 <= i <= n, 1 <= j <= m$ span $V_1 times.circle V_2$ and hence define a basis.

Now, $G$ acts on $V_1 times.circle V_2$ by the rule $
g dot (v_1 times.circle v_2) = (g v_1) times.circle (g v_2).
$ Hence, we find $
chi_(V_1 times.circle V_2) = chi_("Hom" (V_1^ast, V_2)) = overline(chi_(V_1^ast)) dot chi_(V_2) = chi_(V_1) dot chi_V_2,
$ using the character properties above.

We can also prove this directly. Let $g in G$ and let $e_1, dots, e_n$ be a basis for $V_1$ of eigenvectors for $g$, and $f_1, dots, f_m$ a basis for $V_2$ of eigenvectors for $g$. Suppose $g dot e_i = lambda_i e_i$, $g dot f_j = mu_j f_j$, for some $lambda_i, mu_j in CC$. Then, $
g dot (e_i times.circle f_j) = (g dot e_i) times.circle (g dot f_j) = (lambda_i e_i times.circle mu_j f_j) = (lambda_i mu_j) (e_i times.circle f_j).
$ Hence, we find $
tr (rho_(V_1 times.circle V_2)) (g) = sum_(i = 1, dots, n\ j = 1, dots, m) lambda_i mu_j = sum_(i=1)^n lambda_i sum_(j=1)^m mu_j = chi_(V_1) (g) dot chi_(V_2) (g).
$

#example($A_5$)[
  Recall the character table of $A_5$,
  #align(center,
    table(
      columns: 6,
      stroke: none,
      "", $1$, $15$, $20$, $12$, $12$,
      "", $1A$, $2A$, $3A$, $5A$, $5B$,
      table.hline(start: 0, end: 7),
      table.vline(x:1, start: 0, end: 7),
      $chi_1$, $1$, $1$, $1$,$1$, $1$,
      $chi_2$, $4$, $0$, $1$, $-1$, $-1$,
      $chi_3$, $5$, $1$, $-1$, $0$, $0$,
      $chi_4$, $3$, $-1$, $0$, $1 + zeta + zeta^(-1)$, $1 + zeta^2 + zeta^(-2)$,
      $chi_5$, $3$, $-1$, $0$, $1 + zeta^2 + zeta^(-2)$, $1 + zeta + zeta^(-1)$
    )
  )
We consider various tensors of representations: 

 #align(center,
    table(
      columns: 6,
      stroke: none,
      "", $1A$, $2A$, $3A$, $5A$, $5B$,
      table.hline(start: 0, end: 7),
      table.vline(x:1, start: 0, end: 7),
      $V_2 times.circle V_3$, $9$, $1$, $0$, $-1$, $-1$,
  )) which we notice to equal the character of $chi_4 plus.circle chi_5$; namely, $V_2 times.circle V_3 tilde.eq V_4 plus.circle V_5$.

  Also 
  #align(center,
    table(
      columns: 6,
      stroke: none,
      "", $1A$, $2A$, $3A$, $5A$, $5B$,
      table.hline(start: 0, end: 7),
      table.vline(x:1, start: 0, end: 7),
      $V_2 times.circle V_4$, $12$, $0$, $0$, $(-1 - sqrt(5))/2$, $(-1 + sqrt(5))/2$,
  )) from which we find $
  V_2 times.circle V_4 tilde.eq V_3 plus.circle V_4 plus.circle V_5.
  $
]

== Cute Applications of Representation Theory

=== The Pillaging Knights
Suppose we are given $N$ knights, whom, after a long night of pillaging, sit at a round table to share their spoils of war. Each knight decides to split his earnings equally among his two neighbors. What happens after many iterations?

The wealth distribution may be modelled as a function on $ZZ\/N ZZ$; each knight is identified with some element of $ZZ\/N ZZ$, and the wealth is given by $f : ZZ\/N ZZ -> CC$. Then, $
f in L^2 (ZZ\/N ZZ) = plus.circle.big_(j=0)^(N-1) CC dot e^(2 pi i j x\/N).
$ Then, "wealth distribution" can be seen as a function $T : L^2 -> L^2$ given by $
T f(x) := 1/2 (f(x - 1) + f(x + 1)).
$ Namely, we can view iterating $T$ as iteratively distributing wealth, so $T^M f(x)$ would be the wealth associated to knight $x$ after $M$ distributions. To understand this operator, we can analyze how it acts on a basis for $L^2 (ZZ\/N ZZ)$; we know this is simply given by $f_j (x) := e^(2pi i j x\/N)$ where $j = 0, dots, N - 1$. 
 Then, $
 T f_j (x) = T e^(2 pi i j x\/N) &= 1/2 (e^(2 pi i j (x + 1) \/N ) + e^(2 pi i j (x - 1) \/N )) \ 
&= 1/2 (e^(2 pi i j\/N) + e^(- 2 pi i j\/N)) e^(2 pi i j x \/N) \
&= cos(2 pi j\/N) e^(2 pi i j x \/N).
$ Then, we may write the Fourier series expansion of $f$ as  $f = hat(f)(0) f_0 + hat(f)(1)f_1 + dots.c + hat(f)(N-1) f_(N-1)$, so the Fourier expansion of $T f$ is given by $
T f = hat(f)(0) f_0 + hat(f)(1) cos((2 pi)/N) f_1 + dots.c + hat(f)(N-1) cos((2 pi (N-1))/N) f_(N-1),
$ and hence $
hat(T f) (j) = hat(f)(j) cos((2 pi j)/N).
$ Then, iterating $T$ (distributing wealth) $M$ times, one finds that $
hat(T^M f(j)) = hat(f)(j) (cos ((2 pi j)/N))^M,
$ for each $j = 0, dots, N-1$. Letting $M -> infinity$, this term will go to zero unless $j = 0$, in which case $lim_(M -> infinity) hat(T^M f) (0) = hat(f)(0)$. 

What does this mean? This means that in the limiting wealth distribution, call it $T^"lim" f$, the only Fourier coefficient that survives is the one associated to the constant function 1, namely, $
 hat(T^lim f) (0)= hat(f)(0).
$ So, we find in particular for every $x in ZZ\/N ZZ$, by the Fourier inversion formula, that $
T^lim f (x) &= sum_(j=0)^(N-1) hat(T^lim f)(j) dot f_j = hat(f)(0) = 1/N sum_(y=0)^(N-1) f(y).
$ I.e., the limiting wealth distribution of every knight $x$ is simply the average of what they all started with, so this splitting profit completely equalized the wealth around the table. How equitable!

=== Functions on Mathematical Objects with Symmetry Groups

Let $X$ a "mathematical object", $G$ a group of symmetries and $V = L^2 (X) =  CC$-valued functions on $X$. We assume $X$ finite (hence $G$ finite and $V$ finite). We are interested in studying operators $T : L^2 (X) -> L^2 (X)$.

Suppose for instance $X$ a set of vertices of a graph; define for $phi in L^2 (X)$, $(T phi)(x) = sum_((y, x) "an edge") phi(y)$; $T$ the adjacent operator, extended to functions on $CC$. We claim $T$ commutes with the action of $G$; write $y tilde x$ if the vertex $y$ adjacent to the vertex $x$:
$
(T compose g) (phi) (x) &= T(g phi) (x) \ 
&=  sum_(y tilde x) (g phi)(y) \ 
&= sum_(y tilde x) phi(g^(-1) y),
$ while on the other hand $
(g compose T)(phi)(x) &= g (T(phi))(x) \ 
&= T(phi)(g^(-1) x) \ 
&= sum_(y tilde g^(-1) x) phi(y),
$ which are equal upon change of index.

Suppose $X$ the faces of a cube, and $V = L^2 (X)$. Define $
T phi (F) = 1/4 sum_(F' "adjacent to" F) phi(F').
$ What is the spectrum of $T$?

#theorem[If $V = V_1 plus.circle dots.c plus.circle V_t$, where the $V_j$'s are distinct irreducible representations of $G$, then $T$ maps $V_j$ to itself, and in particular acts as a scalar on $V_j$.]

#proof[
  $T$ can be written as a $t times t$ "matrix of matrices", $(T_(i j))$, where $T_(i j) : V_j -> V_i$. Moreover, each $T_(i j) in "Hom"_G (V_j, V_i)$ (being $G$-equivariant). More specifically: 
  
  // $
  // V_j arrow.r.hook^(eta_j) V -->^T V ->>^(pi_i) V_i
  // $

  #align(center)[#commutative-diagram(
  node((0, 1), $V$),
  node((0, 2), $V""$),
  node((1, 0), $V_j$),
  node((1, 3), $V_i$),
  arr($V_j$, $V$, $eta_j$, "inj"),
  arr($V$, $V""$, $T$),
  arr($V""$, $V_i$, $pi_i$, "surj"),
  arr($V_j$, $V_i$, $T_(i j)$),
  // arr($M_1$, $M_2$, $T$),
  // arr($R^n$, $M_1$, $phi_B_1$),
  // arr($R^m$, $M_2$, $phi_B_2$, label-pos: right),
  // arr($R^n$, $M_1$, $≀$, label-pos: right),
  // arr($R^m$, $M_2$, $≀$, label-pos: left),
  // arr($R^n$, $R^m$, $\ \ \ M_(T, B_1, B_2)$, label-pos: "below"),
  // arr("quot", (0, 1), $tilde(phi)$, label-pos: right, "dashed"),
  // arr($R$, "quot", $pi$),
)]
Where $eta_j in "Hom"_G (V_j, V)$ the inclusion map, $pi_i in "Hom"_G (V, V_i)$ the projection map (one readily verifies they are actually $G$-equivariant) and by construction $T in "Hom"_G (V, V)$; hence, $T_(i j) = pi_i T eta_j in "Hom"_(G) (V_j, V_i)$. By Schur's Lemma, then, $T_(i j) = cases(
  0 & "if" i eq.not j,
  lambda_i &"if" i = j
)$.

So, if $v in V_j$, $T(v) in V_j$ since $
T(v) =& pi_1 T(v) + pi_2 T(v) + dots.c + pi_t T(v) \ 
&= T_(1 j) v + dots.c + T_(t j) v \ 
&= T_(j j) v = pi_j v.
$
]

#remark[
  More generally whenever $T : V -> V$ is linear and $V = V_1 plus.circle dots.c plus.circle V_t$, then we may write $
  v = (v_1, dots, v_t)^t,
  $ where $v_j in V_j$ i.e. $v = v_1 + dots.c + v_t$. In this notation, $
  T v = mat(
    T_(1 1), T_(1 2), dots, T_(1 t);
    T_(2 1), T_(2 1), dots.v, T_(2 t);
    dots.v, , , dots.v;
  T_(t 1), T_(t 2), dots.c, T_(t t)
  ) dot vec(v_1, v_2, dots.v, v_t),
  $ where $T_(i j) in "Hom"(V_j, V_i)$.
]

=== Functions on a Cube
Let $X = $ set of faces of a cube, and $V = L^2 (X)$ acted on by $G = S_4$, the symmetry group the cube. Let $T : V -> V$ be defined by $
T(psi)(x) = 1/4 sum_(y tilde x) psi(y),
$ where $y tilde x$ means $y, x$ are adjacent faces; the sum is over all faces adjacent to $x$. Notice that $T$ is $G$-equivariant; moreover we can view it as a 4-way "sharing" of the value on adjacent faces, as in the knight example but now sitting on a cube rather than a circle.

We aim to decompose $L^2 (X)$ into a sum of irreducible representations. We have the character table of $S_4$;

#align(center, 
table(
    columns: 6,
    stroke: none,
    table.vline(x: 1, start:0, end: 8),
    $$, $1$, $6$, $3$, $8$, $6$,
    $$, $1 A$, $2 A$, $2 B$, $3 A$, $4 A$,
    table.hline(start:0, end:8),
    $chi_1$, $1$, $1$, $1$, $1$, $1$,
    $chi_2$, $1$, $-1$, $1$, $1$, $-1$,
    $chi_3$, $2$, $0$, $2$, $-1$, $0$,
    $chi_4$, $3$, $1$, $-1$, $0$, $-1$,
    $chi_5$, $3$, $-1$, $-1$, $0$, $1$,
    table.hline(start: 0, end: 8),
    $L^2 (X)$, $6$, $0$, $2$, $0$, $2$
)
) If $chi$ the character of $L^2 (X)$ then $chi = m_1 chi_1 + dots.c + m_5 chi_5$; we determine $m_i$ by taking the inner product of $chi$ with each of the irreducible characters; whence we may write $
L^2 (X) &= V_1 plus.circle V_3 plus.circle V_5 \ 
&= {"constant functions"} plus.circle L^2 (X)_(+, 0) plus.circle L^2 (X)_(-)
$

We'll say a function $phi : X -> CC$ is _even_ if $phi(x) = phi(x')$ where $x'$ the face opposite of $x$. The space, call it $L^2 (X)_+$, of even functions is naturally $G$-stable; if $phi in L^2 (X)_+$ and $g in G$, then $g phi(x) = g phi(x')$ while also $phi(g^(-1)) x = g phi(x),$ $phi(g^(-1) x') = g phi(x')$, hence we find $phi(g^(-1)x) = phi(g^(-1) x')$, hence $G$ sends even functions to even functions.

This space already contains constant functions, so we want to consider the complementary space; $
L^2 (X)_(+, 0)  := {phi : X -> CC | phi "even and" sum_(x in X) phi(x) = 0}.
$

Similarly, consider $L^2 (X)_(-) = $space of odd functions $ = {phi: X -> CC| phi(x') = - phi(x)}$.

Our $T$ above preserves $V_1, V_3, V_5$. Namely, $
T(bb(1)_X) = bb(1)_X,
$ so $1$ an eigenvalue with eigenvector "1". If $phi in V_5$, $
T(phi) = 0,
$ so $0$ an eigenvalue with multiplicity 3. If $phi in V_3$, suppose $phi$ $a, b, c$ on adjacent faces so $a + b + c = 0$; then
 $
T(phi)(x) = 1/4 (a + a + c+ c) =- 1/2 b = -1/2 phi(x),
$ so $
T phi = -1/2 phi,
$ hence $-1/2$ an eigenvalue with multiplicity 2.



= Midterm Practice

#proposition[
  Let $G = D_8$ be the dihedral group of order 8. Write down the character table of $G$.
]

#proof[
  We can realize $G$ as a subgroup of $S_4$ by identifying vertices of the square with numbers 1 through 4; this gives the following class equation for $G$: $
  G &= {1} & union.sq & {(13)(24)} & union.sq  & {(1234), (1432)} & union.sq  &  {(12)(34), (14)(23)} & union.sq  &  {(24), (13)} \ 
  &=: (1) & union.sq  & thin thin thin thin thin thin thin thin thin (2) & union.sq  &   wide thin thin thin (3)& union.sq  & wide thin thin thin thin thin thin thin thin (4) & union.sq  &  wide (5).
  $
  Remark that $(1) union (2) tilde.eq ZZ\/2ZZ$, and in particular is equal to the center of $G$. Hence, if we let $rho$ be a representation of $G$, we can "factor through" the center, and consider instead $
  rho : G\/(1) union (2) -> "Aut"_CC (V).
  $ One readily verifies that $G\/(1) union (2) tilde.eq K_4$, which is an abelian group hence every such irreducible representation is one-dimensional, and in particular there are 4 of them. In each, $chi((2)) = chi((1)) = 1$, and $chi$ is always just a second root of unity (namely either 1 or minus 1). In particular, we can choose $chi((3))$ and $chi((5))$ to be either $1$ or minus 1, then $chi((4))$ is must be equal to the product of these. This gives 4 total options; #align(center,
    table(
      columns: 6,
      stroke: none,
      table.vline(x:1, start:0, end:10),
      $$, $(1)$, $(2)$, $(3)$, $(4)$, $(5)$,
      table.hline(start: 0, end: 10),
      $chi_1$, $1$, $1$, $1$, $1$, $1$,
      $chi_2$, $1$, $1$, $1$, $-1$, $-1$,
      $chi_3$, $1$, $1$, $-1$, $-1$, $1$,
      $chi_4$, $1$, $1$, $-1$, $1$, $-1$,
      $chi_5$, $2$, $-2$, $0$, $0$, $0$
    )
  ) The last row can either be computed via orthogonality relations, or by considering the action of $D_8$ described in Proposition 1.2.
]

#proposition[
  Let $G$ be a finite group in which every element is conjugate 
  to its inverse.
  (a) Give an example of such a group. \
  (b) Show that the character of any complex representation of such a group is real-valued (all the entries of the character table are real).
]

#proof[
  (a) $S_n$, among others.

  (b) We know $chi(g^(-1)) = overline(chi(g))$ (always). But if $g$ conjugate to $g^(-1)$, since $chi$ a class function, $chi(g^(-1)) = chi(g)$ so combining these two equalities we find $chi(g) = overline(chi(g))$, which is only possible if $chi(g)$ real, namely has no imaginary part.
]

#proposition[
  Let $G$ a finite group and $rho : G -> "GL"_n (RR)$ a homomorphism. Show that for any integer $t >=1 $, the matrix $
  M = sum_("order"(g) = t) rho(g)
  $ is diagonalizable.
]

#proof[
  There exists a $G$-equivariant inner product $(dot, dot)$ on $RR^n$ (by replacing any arbitrary inner product with an averaging over the group). Then, for any $x, y in RR^n$, we find $
  (M x, y) &= sum_("ord"(g) = t) (rho(g) x , y) = sum_("ord"(g) = t) (x, rho(g)^(-1) y) =  (x, sum_("ord"(g) = t)  rho(g^(-1)) y) ,
  $ but $"ord"(g) =  "ord"(g^(-1))$, so we may change indices $g-> g^(-1)$ without changing the summation, and find $
  (M x, y)&= (x, sum_("ord"(g) = t)  rho(g) y) = (x, M y),
  $ hence $M = M^ast$, namely $M$ self-adjoint. By the spectral theorem, it follows that $M$ diagonalizable.
]

#proposition[Let $chi$ be the character of a 2-dimensional representation of a finite group $G$, and assume that $g$ is of order $4$ for which $chi(g) = 0$. Prove that $chi(g^(2))$ is either plus or minus 2.]

#proof[
  Suppose $rho(g) = mat(a, b; c, - a)$, so $chi(g) = 0$ as needed. Then, $
  rho(g^2) = mat(a^2 + b c, 0; 0, a^2 + b c),
  $ so $chi(g^2) = 2( a^2 + b c)$, while also $g$ of order $4$ so $
  I = rho(g^4) = mat((a^2 + b c)^2, 0; 0, (a^2 + b c)^2),
  $ hence $a^2 + b c = plus.minus 1$, and thus $
  chi(g^2) =plus.minus 2.
  $
]

// #proposition[
//   Let $D_8$ be the dihedral group of order 8 and $Q$ the quaternion group. Show that the group rings $CC[D_8]$ and $CC[Q]$ are isomorphic, while the group rings $RR[D_8]$ and $RR[Q]$ are not.
// ]

// #proof[
//   We know that $
//   CC[D_8] tilde.eq plus.circle.big_(j=1)^5 "End"_CC (V_j) tilde.eq plus.circle.big_(j=1)^5 "M"_(d_j) (CC),
//   $ with similar for $CC[Q]$. But recall that $D_8$ and $Q$ have "identical" character tables, namely they have the same number of irreducible complex representations with the same distribution of dimensions, hence it follows by this characterization that the group rings are isomorphic.
// ]

#proposition[
  Let $D_8$ be the dihedral group on $4$ elements and $Q$ the group of quaternions. Show that the group rings $CC[D_8]$ and $CC[Q]$ are isomorphic, but the groups rings $RR[D_8]$ and $RR[Q]$ are not.
]

#proof[
  Recall from proving that the number of irreducible representations is equal to the number of conjugacy classes of a group, we know $
  CC[D_8] = "End"_CC (V_1) plus.circle dots.c plus.circle "End"_CC (V_5),
  $ where $V_1, dots, V_5$ enumerate the irreducible representations; recall that we have four 1-dimensional representations and a final 2-dimensional representations, we find by picking bases for each $V_i$ that $
  CC[D_8] = CC plus.circle CC plus.circle CC  plus.circle CC  plus.circle M_2 (CC).
  $ But $Q$ has the same number of irreducible representations with the same dimensions, hence $
  CC[Q] = CC plus.circle CC plus.circle CC  plus.circle CC  plus.circle M_2 (CC),
  $ hence the two are isomorphic.

  For $RR[D_8]$, recall that all of the representations are real-valued, so we may realize the same type of isomorphism, and fnd $
  RR[D_8] = RR plus.circle RR plus.circle RR plus.circle RR plus.circle M_2 (RR).
  $ However, in $Q$, all of the representations are real other than the 2-dimensional one, which cannot be realized as a 2-dimensional representation over $RR$; however, as a group ring, $
  RR[Q] = RR plus.circle RR plus.circle RR plus.circle RR plus.circle HH,
  $ where $HH$ the ring of Hamiltonian quaternions. This is a 4-dimensional real-vector space (namely, we can identify it as a subspace of $M_4 (RR)$ by identifying $i$ with $mat(1, 1; 1, -1)$, $j$ with $mat(-1,1;1,1)$, and $k$ with $mat(0,-1;1,0)$). Hence, these two real-valued group rings cannot be isomorphic.
]

#proposition[Write down the character table of the symmetry group $G = S_4$ of the cube. Write the character of the permutation representation of $G$ acting on the $8$ vertices of the cube, and use the character table to write this character as a sum of irreducible characters.]

#proof[
See @table:s4 for the character table of $G$ (and its derivation). The character $chi_C$ of the permutation representation is given, for each conjugacy class, the number of fixed points of $G$ acting on the vertices (derived #link("https://notes.louismeunier.net/Algebra%203/algebra3.pdf#page=19", "here")): #table(
    columns: 6,
    stroke: none,
    "", $1A$, $2A$, $2B$, $3A$, $4A$,
    table.hline(start: 0, end: 7),
    table.vline(x:1, start: 0, end: 7),
    $chi_C$, $8$, $0$, $0$,$2$, $0$,
  )
  To write $chi_C$ as a sum of irreducible characters, take the inner product of $chi_C$ with each irreducible character; one should find $
  chi_C = chi_1 + chi_2 + chi_4 + chi_5.
  $
]

#proposition[
  Let $C$ be a conjugacy class in a finite group $G$. Show that the element $
  alpha_C := sum_(g in C) g in CC[G]
  $ belongs to the center of the complex group ring of $G$. If $rho : G -> "GL"_n (CC)$ is an irreducible representation of $G$, show that the matrix $
  rho(alpha_C) := sum_(g in C) rho(g) in M_n (CC)
  $ is a scalar matrix and write down the scalar in terms of the character of $rho$.
]

#proof[
  If suffices to check that $alpha_C$ commutes with every $h in G$ since $CC$ is obviously commutative; we find $
  h alpha_C h^(-1) = sum_(g in C) h g h^(-1) = sum_(tilde(g) in C) tilde(g) = alpha_C,
  $ where the summation remains fixed under the change of indexing $tilde(g) = h g h^(-1)$, since conjugacy classes are by virtue closed under conjugation.

  Next, we can view $rho(alpha_C)$ as a homomorphism $V -> V$ where $V = CC^n$ the corresponding vector space representation. In this case, the same proof as above gives that $rho(alpha_C)$ actually a $G$-equivariant homomorphism on $V$, and so by Schur's Lemma, $rho(alpha_C) = lambda I_n$ for some $lambda in CC$. To compute $lambda$, we can compute traces; on the one hand, we have $tr(lambda I_n) = n dot lambda$, while also $
  tr(rho(alpha_C)) = sum_(g in C) tr(rho(alpha_C)) = sum_(g in C) chi(g) = hash C dot chi(C),
  $ where $chi$ the corresponding character of $rho$, and where we use the fact that $chi$ constant on conjugacy classes. Comparing these, we conclude $lambda = (hash C dot chi(C))/n$; noting that $n = chi(1)$, then $
  rho(alpha_C) = (hash C dot chi(C))/chi(1) I_n.
  $
]
#proposition[
  State Maschke's Theorem about complex finite dimensional representations of finite groups. Give a counterexample to illustrate that it can fail to be true when $G = ZZ$ is the infinite cyclic group.
]

#proof[
See @thm:maschkes for the statement. The typical counter example is the two-dimensional representation of $ZZ$ given by $n |-> mat(1,n; 0, 1)$. One can show that while $CC dot e_1$ an irreducible one-dimensional subspace, there is no complementary irreducible one-dimensional space.
]

#proposition[
  Let $Q = {plus.minus 1, plus.minus i, plus.minus j, plus.minus k}$ be the Quaternion group of order 8. What are the dimensions of the irreducible representations of $Q$? Realize the abstract group $Q$ as a "concrete" group of matrices with complex entries.
]

#proof[
  There are 4 irreducible representations of dimension 1, and a unique (faithful) irreducible representation of dimension 2 (the first four can be found by modding out the center of $Q$ which gives a homomorphism to $ZZ\/2ZZ times ZZ\/2 ZZ$; the last can be found by just computing orthogonality relations).

  The "concrete" realization, as a subgroup of $"GL"_2 (CC)$, is given by $1 <-> I_2$, $-1 <-> - I_2$, and $
  i <-> mat(i, 0; 0, -i), wide j <-> mat(0, -1; 1, 0), wide k <-> mat(0, -i;-i, 0),
  $ with $-i,-j,-k$ defined in the obvious way (this, of course, up to conjugation of every element; this certainly isn't unique).
]

#proposition[
  Let $C_1, C_2, C_3$ be three conjugacy classes in a finite group $G$, and let $N(C_1, C_2, C_3)$ be the number of solutions to the equation $g_1 g_2 g_3 = 1$ with $g_j in C_j$ (with $1 <= j <= 3$). Show that $
  N(C_1, C_2, C_3) =  (hash C_1 hash C_2 hash C_3)/(hash G) sum_(chi) (chi(C_1) chi(C_2) chi(C_3))/(chi(1)),
  $ where the sum is taken over the irreducible characters $chi$ of $G$, and $chi(C_j)$ is a notation for $chi(g)$ with $g$ any element of $C_j$.
]

#proof[(A First Proof)
The key observation is to notice that, using the notations of 3 questions ago, consider the element $alpha_C_1 alpha_C_2 alpha_C_3 in CC[G]$;one notices that the coefficient of this element corresponding to the identity in $G$ is equal to $N(C_1, C_2, C_3)$. We'd like to "pick out" this element, which we can do by taking the inner product of the element with $chi_"reg"$, the character of the regular representation; this gives on the one hand $
 chi_"reg" (alpha_C_1 alpha_C_2 alpha_C_3) = hash G dot N(C_1, C_2, C_3).
$ On the other hand, we know that $chi_"reg" = sum_(chi) chi(1) dot chi$, where the summation ranges over the irreducible representations of $G$; so, it suffices to find the character of $alpha_C_1 alpha_C_2 alpha_C_3$ on each representation. If $rho$ an irreducible representation with character $chi$, then using three questions ago, we find $
chi(alpha_C_1 alpha_C_2 alpha_C_3) &= tr(rho(alpha_C_1) rho(alpha_C_2) rho(alpha_C_3)) \ 
&= tr((hash C_1 dot chi(C_1))/(chi(1)) dot (hash C_2 dot chi(C_2))/(chi(1)) dot (hash C_3 dot chi(C_3))/(chi(1)) I_chi(1)) \ 
&= hash C_1 hash C_2 hash C_3 (chi(C_1) chi(C_2) chi(C_3))/(chi(1)^2).
$ Hence, we find that $
hash G dot N(C_1, C_2, C_3) &= chi_"reg" (alpha_C_1 alpha_C_2 alpha_C_3) \
&= sum_(chi) chi(1) chi(alpha_C_1 alpha_C) \ 
&=hash C_1 hash C_2 hash C_3 sum_(chi)  (chi(C_1) chi(C_2) chi(C_3))/(chi(1)),
$ giving the answer upon dividing both sides by $hash G$.
]

#proof[(A Second Proof) Recall the isomorphism of rings $
underline(rho) = (rho_1, dots, rho_h) : CC[G] -> plus.circle.big_(i=1)^h "End"_CC (V_i),
$ developed earlier to find the number of irreducible characters of a group. From question 2., we know that $
underline(rho)(alpha_C_1 alpha_C_2 alpha_C_3) &= (rho_1 (alpha_C_1) rho_1 (alpha_C_2) rho_1 (alpha_C_3), dots, rho_h (alpha_C_1) rho_h (alpha_C_2) rho_h (alpha_C_3)) \ 
&= (hash C_1 hash C_2 hash C_3 (chi_1 (C_1) chi_1(C_2) chi_1 (C_3))/(chi_1(1) ) I_(chi_1 (1)), dots, hash C_1 hash C_2 hash C_3 (chi_h (C_1) chi_h (C_2) chi_h (C_3))/(chi_g(1) ) I_(chi_h (1))) \ 
&=hash C_1 hash C_2 hash C_3  dot ((chi_1 (C_1) chi_1(C_2) chi_1 (C_3))/(chi_1(1) ) I_(chi_1 (1)), dots,  (chi_h (C_1) chi_h (C_2) chi_h (C_3))/(chi_g(1) ) I_(chi_h (1))),
$ where $chi_i$ the character of $rho_i$. Restricting to the vector space structure of $CC[G]$, we know that $CC[G] tilde.eq L^2 (G)$, the space of complex-valued functions on $G$. Then, notice that $N(C_1, C_2, C_3)$ is the coefficient of $alpha_C_1 alpha_C_2 alpha_C_3$ corresponding to $1$ in the group ring, or, viewing this element as a function, call it $f$, in $L^2 (G)$, the value of $f(1)$. $L^2 (G)$ is endowed with a natural inner product, and we can find $f(1)$ by taking the inner product of $f$ with the function $delta_1 : G -> CC$ given by $delta_1 (g) = cases(1 "if" g = id, 0 "else")$, which gives $
angle.l f, delta_1 angle.r = 1/(hash G) dot  f(1).
$ On the other hand, there is a corresponding natural inner product on the vector space $plus.circle.big_(i=1)^h "End"_CC (V_i)$. Namely, on each space $"End"_CC (V_i)$, the natural inner product is $
angle.l A, B  angle.r_ast := tr(A B^ast),
$ where $B^ast$ denotes the conjugate transpose of $B$. Then, the inner product on the direct sum of the spaces is given by the sum such inner products on each component, i.e. given $A = (A_1, dots, A_h), B = (B_1, dots, B_h)$, we define $
angle.l A, B angle.r_+ &:= sum_(i=1)^h tr(A_i B_i^ast).
$ I claim that this inner product is "equivalent" to the original one on $L^2 (G)$. Namely, given $f_1, f_2 in L^2 (G)$, note that $rho_i (f_2)^ast = overline(rho_i (f_2)) = rho_i (f_2^(-1))$, so we find $
angle.l underline(rho)(f_1), underline(rho)(f_2) angle.r_+ &= sum_(i=1)^h tr(rho_i (f_1) rho_i (f_2)^ast) \
&= sum_(i=1)^h tr(rho_i (f_1) rho_i (f_2^(-1))) \ 
&= sum_(i=1)^h tr(rho_i (f_1 f_2^(-1))) \
&= sum_(chi) chi (f_1 f_2^(-1))
// TODO off by a factor somewhere or other....
$ 

Finally, notice that $
underline(rho)(delta_1) = (rho_1 (1), dots, rho_h (1)) = (I_(chi_1(1)), dots, I_(chi_h (1)))
$
From which we find $
angle.l  underline(rho)(f), underline(rho)(delta_1) angle.r_+ &= sum_(i=1)^h tr(hash C_1 hash C_2 hash C_3 (chi_i (C_1) chi_i (C_2) chi_i (C_3))/(chi_i (1) ) I_(chi_i (1))) \ 
&= sum_(chi) hash C_1 hash C_2 hash C_3 dot chi(C_1) chi(C_2) chi(C_3) 
$
]
= Galois Theory

The original motivation of Galois Theory was the study of polynomial equations and so-called "solvability by radicals". More modernly, the motivation is in the study of fields via their symmetries.

One original question was with solving the cubic equation, $a x^3 + b x^2 + c x + d = 0$. We outline the proof here. Without loss of generality, one assumes $a = 1$ and $b = 0$, by dividing by $a$ (if $a = 0$, this reduces to a quadratic) and making an appropriate summation. This gives the so-called "depleted cubic" equation, we write $
x^3 + p x + q = 0.
$ Writing $x = u + v$, we find $
(u + v)^3 + p (u + v) + q = 0 \ 
=> u^3 + v^3 + 3 u v (u + v) + p (u + v) + q = 0\
=> [u^3 + v^3 + q] + (3 u v + p)(u + v) = 0;
$ then, if $u^3 + v^3 + q  = 0$ and $3 u v + p = 0$, we find a solution; namely, we have now a system of two equations $
cases(u^3 + v^3 = - q,
u v = - p/3).
$ Cubing the second, we find $
cases(u^3 + v^3 = - q,
u^3 v^3 = - p^3/27
),
$ from which we see $u^3$ and $v^3$ are solutions to a quadratic equation $
x^2 + q x - p^3/27 = 0;
$ this equation is often called the "quadratic resolvent" of the cubic. Hence, by applying the quadratic formula, we know $
u^3, v^3 = (- q plus.minus sqrt(p^2 + 4 p^3\/27))/2
$ so $
u, v = root(3, (- q plus.minus sqrt(p^2 + 4 p^3\/27))/2).
$ Substituting back to our original expression, we find our general solution $
x = root(3, (- q + sqrt(p^2 + 4 p^3\/27))/2) + root(3, (- q - sqrt(p^2 + 4 p^3\/27))/2)
$ to the cubic equation. One notices that this should give 9 solutions (3 cube roots exists, for each cube root), and in general gives complex numbers. We'll discuss the implications of this to follow.

There is a similar formula for the general quartic equation, involving square, cube, and fourth roots, with a similar method leading to a resolvent cubic. However, attempting the same method for the quintic equation leads to a resolvent sextic equation, which is clearly no help at all. We'll see that this is intimately tied to the symmetries, namely, the symmetry groups, of the roots of the respective polynomials.

== Field Extensions

#definition("Field Extension")[
  If $E$ and $F$ are fields, we say $E$ is an 
  _extension_ of $F$ if $F$ is a subfield of $E$; we'll often denote $E\/F$.
]

Note that if $E$ an extension of $F$, then $E$ is also a vector space over $F$ (by "forgetting" the multiplication).

#definition("Degree")[
  The _degree_ of $E$ over $F$ is the dimension of $E$ as an $F$ vector space, often denoted $[E: F] = dim_F (E)$. We call then $E$ a _finite_ extension of $F$ if $[E:F] < infinity$.
]

#example[
  1. Consider $E = CC$ and $F = RR$, then $[E: F] = 2$ (with, for instance, basis ${1, i}$).
  2. Consider $E = CC$ and $F = QQ$, then $[E : C] = infinity$.
  3. Let $F$ be any field and let $E = F[x]\/(p(x))$ where $p(x)$ irreducible, hence $E$ is a field itself. $E$ an extension of $F$, since $F$ can be realized as a subfield via the constant polynomials in $E$. Then, $[E : F] = "deg"(p(x))$.
  4. Let $E = F(x) = "fraction field of" F[x] = {f(x)/g(x) | f, g in F[x], g eq.not 0}$. By similar reasoning to 3., this also an extension of $F$, but now $[E : F] = infinity$ (for instance, ${x^n : n in NN}$ is an infinite, linearly independent subset of $E$).
]

#theorem("Multiplicativity of Degree")[
  Given finite extensions $K subset F subset E$, we have $
  [K : E] = [E : F] dot [F : K].
  $
]

#proof[
  Put $n := [E : F], m:= [F : K]$. Let $alpha_1, dots, alpha_n$ be a basis for $E$ as an $F$-vector space and $beta_1, dots, beta_m$ a basis for $F$ as a $K$-vector space. Now, notice that if $a in E$, then $
  a = lambda_1 alpha_1 + dots + lambda_n alpha_n,
  $  for $lambda_i in F$. Then, $lambda_i$ may be viewed as elements of the vector space $F$ over $K$, so we may write $
  lambda_i = lambda_(i 1) beta_1 + dots.c + lambda_(i m) beta_m,
  $ for some $lambda_(i j) in K$. Hence, $
  a &= (lambda_(11) beta_1 + dots.c + lambda_(1 m) beta_m) alpha_1 + (lambda_(2 1) beta_1 + dots + lambda_(2 m) beta_m) alpha_2 + dots.c + (lambda_(n 1) beta_1 + dots.c + lambda_(n m) beta_m)alpha_n \ 
  &= sum_(1 <= i <= n) sum_(1 <= j <= m) lambda_(i j) alpha_i beta_j.
  $ Since the representation in each basis ${alpha_i}, {beta_j}$ was unique, it must be that this representation also unique. Thus, ${alpha_i beta_j}_(1 <= i <= n \ 1 <= j <= m)$ is a $K$-basis for $E$, so $dim_(K) (E) = m dot n = dim_(F) (E) dot dim_(K) (F)$.
]

== Ruler and Compass Constructions

#definition[
  A complex number is said to be _constructible by ruler and compass_ if it can be obtained from $QQ$ by successive applications of the field operations plus extractions of square roots.
]

The set of elements constructible by ruler and compass is an extension of $QQ$ of infinite degree. Namely, each extraction of a square root can be abstractly realized as adjoining a square root of an element, say $a$, that doesn't have a rational square root to $QQ$, which forms a field extension $QQ(sqrt(alpha))$. We can repeat this process, adjoining new elements and constructing further extensions.  A number is then solvable by constructible by ruler and compass if it is contained in some field extension of $QQ$ obtained via some finite number of adjoinments of square roots.

#theorem[
  If $alpha in RR$ is the root of an irreducible cubic polynomial over $QQ$, then $alpha$ is _not_ constructible by ruler and compass.
]

#proof[
  Suppose otherwise, that $alpha$ is constructible. Then, there exists fields $QQ subset.eq F_1 subset.eq F_2 subset.eq dots.c subset.eq F_n$ with $[F_(i+1) : F_i] = [F_1 : QQ] = 2$ for each $i$ (namely, $F_(i+1) = F_i (sqrt(a_i))$ for some $a_i$ in $F_(i)$ such that $sqrt(a_i) in.not F_(i)$). Hence, by multiplicativity we know $[F_n : QQ] = 2^n$. On the other hand, if $p$ the irreducible (over $QQ$) cubic polynomial for which $alpha$ is a root, $QQ(alpha) = QQ[x]\/p(x)$, so $[QQ(alpha) : QQ] = 3$.

  So, it must be that $F_n$ an extension of $Q(alpha)$ so $[F_n : QQ(alpha)] = d in NN$, but by multiplicativity, $3 d = 2^n$ which is impossible.

  #align(center)[#commutative-diagram(
    node-padding: (40pt, 40pt),
  // node((0, 1), $V$),
  node((0, 2), $F_n$),
  node((1, 0), $QQ(alpha)$),
  node((2, 1), $QQ$),
  arr($QQ$, $QQ(alpha)$, $3$),
  arr($QQ$, $F_n$, $2^n$),
  arr($QQ(alpha)$, $F_n$, $d$)
  // arr($V_j$, $V$, $eta_j$, "inj"),
  // arr($V$, $V""$, $T$),
  // arr($V""$, $V_i$, $pi_i$, "surj"),
  // arr($V_j$, $V_i$, $T_(i j)$),
  // arr($M_1$, $M_2$, $T$),
  // arr($R^n$, $M_1$, $phi_B_1$),
  // arr($R^m$, $M_2$, $phi_B_2$, label-pos: right),
  // arr($R^n$, $M_1$, $≀$, label-pos: right),
  // arr($R^m$, $M_2$, $≀$, label-pos: left),
  // arr($R^n$, $R^m$, $\ \ \ M_(T, B_1, B_2)$, label-pos: "below"),
  // arr("quot", (0, 1), $tilde(phi)$, label-pos: right, "dashed"),
  // arr($R$, "quot", $pi$),
)]
]

#example[
  1. $p(x) = x^3 - 2$ has root $alpha = root(3, 2)$ ("duplicating the cube").
  2. $p(x) = 4 x^3 + 3 x + 1/2$ has root $r = cos ((2 pi )/9)$ ("trisection of the angle").
]

== Automorphisms of Field Extensions
#definition("Algebraic")[
  An element $alpha$ in an extension $E$ over $F$ is said to be _algebraic_ if it is the root of a polynomial $f in F[x]$.
]

#example[
  $sqrt(2), i$ are algebraic over $Q$, but $pi$, for instance, is not. In fact, one can show the set of algebraic numbers in $RR$ over $QQ$ is countable.
]

#lemma[
  If $E$ a finite extension of $F$, any $alpha$ in $E$ is algebraic.
]

#proof[
  Put $n := [E: F]$ and let $alpha in E$. Then, ${1, alpha, dots, alpha^n}$ must be a linearly dependent subset of $E$, hence there must exist scalars $a_i in F$ such that $a_0 + a_1 alpha + dots.c + a_n alpha^n = 0$. Letting $f(x) = a_0 + a_1 x + dots.c + a_n x^n$ completes the proof.
]

#definition("Automorphisms of a Field Extension")[
  The automorphism group of $E\/F$ is defined as the group $
  "Aut"(E\/F) = {sigma : E -> E  quad #vbar(1.5em) quad #stack(
    spacing: .5em,
    $sigma(x + y) = sigma(x) + sigma(y)$,
    $sigma(x y) = sigma(x) sigma(y)$,
    $sigma|_F = id$
  )}.
  $ In particular, $sigma in "Aut"(E\/F)$ respects the field structure on $E$, and leaves the distinguished subfield $F$ in $E$ invariant.
]

#remark[
  Note that an automorphism is a bijection $E -> E$ which is a homomorphism of rings. In particular, any homomorphism $phi : E -> E$ is automatically injective, so if $[E : F] < infinity$, $phi$ injective $<=> phi$ surjective. Hence we need not specify this condition in the definition above.
]

#corollary[
  $sigma(1) = 1$, $sigma(0) = 0$ and $sigma(a^(-1)) = sigma(a)^(-1)$ for $sigma in "Aut"(E\/F).$
]

#proposition[
  If $[E : F] < infinity$, $"Aut"(E\/F)$ acts on $E$ with finite orbits.
]

#proof[
  Let $alpha in E$, and $f(x) = alpha_n x^n + dots.c + a_1 x + a_0$ a polynomial with coefficients in $F$ such that $f(alpha) = 0$, which exists since $alpha$ must be algebra since $[E : F] < infinity$. Then, notice that $
  sigma(f(alpha)) = sigma(0) = 0
  $ on the one hand, while also $
  sigma(f(alpha)) = sigma(a_n alpha^n + dots.c + a_1 alpha + a_0) = a_n sigma(alpha)^n + dots.c + a_1 sigma(alpha) + a_0 = f(sigma(alpha)),
  $ using each of the defining axioms of $"Aut"(E\/F)$. Hence, $sigma(alpha)$ also a root of $f$, and thus $
  "Orb"_"Aut"(E\/F) (alpha) subset {"roots of" f "in" E},
  $ which is a finite set, since $f$ has finite degree $n$ hence at most $n$ roots. Thus, $"Orb"_"Aut"(E\/F) (sigma)$ must also be finite.
]

#remark[
  Notice that we only used the fact that $alpha$ was algebraic, not the full scope of the finiteness of $E\/F$. In fact, the same proof applies when $E\/F$ "algebraic", namely when every element of $E$ algebraic.
]

#theorem[
  If $[E : F] < infinity$, then $hash"Aut"(E\/F) < infinity$.
]

#proof[
  Let $alpha_1, dots, alpha_n$ generate $E$ over $F$ so $E = F(alpha_1, dots, alpha_n)$. Then if $sigma in "Aut"(E\/F)$, it is completely determined by the $n$-tuple $(sigma alpha_1, dots, sigma alpha_n)$. By the previous proof, we know that $
  (sigma alpha_1, dots, sigma alpha_n) subset.eq "Orb"_G (alpha_1) times dots.c times "Orb"_G (alpha_n),
  $ where $G := "Aut"(E\/F)$. The set on the RHS is finite by the previous proof, and thus $sigma$ is determined by a finite amount of "data", and thus there can exist only finitely many $sigma$'s.
]

#example[
  If $E\/F$ generated by a single element $alpha$ (so $E = F(alpha)$), let $p(x) in F[x]$ be the minimal polynomial of $alpha$. Then, $F(alpha) tilde.eq F[x]\/(p(x))$, so $[F(alpha) : F] = "deg"(p(x))$. Then, $sigma in "Aut"(F(alpha)\/F)$ completely determined by $sigma(alpha) in {"roots of" p(x)}$. This set has cardinality at most $"deg"(p(x)) = [F(alpha) : F]$; thus, $
  hash"Aut"(E\/F) <= [E : F].
  $ We'll see this holds more generally.
]

#theorem[
  If $E\/F$ is any finite extension of fields, then $hash"Aut"(E\/F) <= [E : F]$.
]

#proof[
  We prove by induction on the number of generators of $E$ over $F$. Namely, we write $E = F(alpha_1, dots, alpha_n)$.

  Let $M$ be any extension of $F$, fixed. We'll consider the space $"Hom"_F (E, M)$, and we'll prove the slightly stronger statement that $hash Hom_F (E, M) <= [E : F]$, which proves the desired result by setting $M = E$. 

  Consider $n = 1$. Then, $E = F(alpha) = F[alpha]$, so $
  [E : F] = "deg" p_alpha (x) =: d,
  $ where $p_alpha (x)$ the minimal degree polynomial in $F[x]$ that is satisfied by $alpha$. Then, any $phi$ in the space of interest $"Hom"_F (E, M)$ is completely determined by the image of $alpha$. In particular, if $p_alpha (x) = a_0 + a_1 x + dots.c + a_(d-1) x^(d - 1)$, then $
  0 = phi(0) =  phi(p_alpha (alpha)) = a_0 + a_1 phi(alpha) + dots.c + a_(d - 1) phi(alpha)^(d - 1)= 0,
  $ so, the map $phi |-> phi(alpha)$ is an inclusion $"Hom"_F (E, M) -> {"roots of" p_alpha (x)}$. Since the set on the right is a set of size at most $d$, the proof follows.

  Suppose now the case for $n$ and let $E = F(alpha_1, dots, alpha_(n+1))$, and let $F' = F(alpha_1, dots, alpha_n)$. If $F' = E$, we're done. Else, we have the set-up,
  $
  F bar.h^(d_1) F' = F(alpha_1, dots, alpha_n) bar.h^(d_2) E = F'(alpha_(n+1)).
  $ Let $g(x) in F'[x]$ be the minimal polynomial of $alpha_(n+1)$, so $d_2 = "deg" g(x)$. Consider the restriction map $
  "Hom"_F (E, M) -> "Hom"_F (F', M).
  $ By the induction hypothesis, since $F'$ generated by $n$ elements, we have $hash "Hom"_F (F', M) <= d_1 = [F' : F]$. Now, give $phi_0 in "Hom"_F (F', M)$, we'd like to compute how many $phi' : E -> M$ such that $phi|_(F') = phi_0$. Really, then, we need to consider how many options there are of $phi(alpha_(n+1))$. We know that $alpha_(n+1)$ is a root of $g(x) =lambda_(d_2) x^(d_2) + dots.c + lambda_1 x + lambda_0$ where $lambda_j in F'$. Then, $
  0 = phi(g(alpha_(n+1))) &= phi(lambda_(d_2)) phi(alpha_(n+1))^(d_2) + dots.c + phi(lambda_1) phi(alpha_(n+1)) + phi(lambda_0).
  $ However, note that $lambda_(d_2)$ not in $F$ so $phi$ not constant on the $lambda_i$'s, as in the previous case. However, we can write then $
  = phi_0 (lambda_(d_2)) phi(alpha_(n+1))^(d_2) + dots.c + phi_0 (lambda_1) phi(alpha_(n+1)) + phi_0(lambda_0),
  $ so $phi(alpha_(n+1))$ is a root of the polynomial "$phi_0 (g(x)) in M[x]$", by which we mean the polynomial $g(x)$ with the coefficients evaluated on $phi_0$. There are at most $d_2$ choices of roots of this new polynomial, hence at most $d_2$ choices for $phi(alpha_(n+1))$. Thus, we find $
  hash "Hom"_(F) (E, M) <= d_1 dot d_2 = [E : F],
  $ by multiplicativity of the degrees.
]

#definition("Galois")[
  An extension $E\/F$ is said to be _Galois_ if $hash"Aut"(E\/F) = [E : F]$, in which case we write $"Gal"(E\/F) = "Aut"(E\/F)$.
]

#example[
  Let $E = CC$ and $F = RR$ so $[E : F] = 2$. Then, the conjugation map $
  c : CC -> CC, wide x + i y |-> overline(x + i y) = x - i y
  $ is an automorphism of $CC\/RR$. So, $
  "Aut"(CC\/RR) = {1, c};
  $  there couldn't possible be any more maps else the previous upper bound would be contradicted.
]

#example[
  Let $F = QQ$ and $E = QQ(root(3, 2)) = QQ[x]\/(x^3 - 2).$ We can also consider this as a subfield of $RR$ by identifying $root(3, 2)$ with the distinct real cube root of $2$. Then, $
  "Aut"(QQ(root(3, 2))\/QQ) <-> {"roots of" x^3 - 2 "over" QQ(root(3, 2))}, 
  $ since $root(3, 2)$ must be mapped to another element which cubes to 3. However, there is only one such element, namely itself, so the only possible automorphism is the identity and so $hash "Aut"(QQ(root(3, 2))\/QQ) = 1 < 3$.
]

=== A Thorough Example
// #example[
  Consider now $F = QQ$ and $E = QQ(root(3, 2), zeta)$ where $zeta^3 = 1$ (but is not 1) so $zeta$ satisfies the quadratic equation $x^2 + x + 1$; so, we can realize $QQ(root(3, 2), zeta) subset CC$. Moreover, note that $[QQ(root(3, 2), zeta): QQ] = 6$; we have as basis ${1, root(3, 2), root(3, 2)^2, zeta, zeta root(3, 2), zeta root(3, 2)^2}$. 

  Alternatively, one can use the multiplicativity of the degree to deduce this number; this "sequence of extensions" is visualized below.

  #align(center)[#commutative-diagram(
    node-padding: (40pt, 40pt),
  // node((0, 1), $V$),
  node((0, 1), $QQ(root(3,2), zeta)$),
  node((1, 0), $QQ(zeta)$),
  node((1,2), $QQ(root(3, 2))$),
  node((2, 1), $QQ$),
  arr($QQ$,$QQ(root(3, 2))$, "3"),
  arr($QQ$,$QQ(zeta)$, "2"),
  arr($QQ(zeta)$, $QQ(root(3, 2), zeta)$, "3"),
  arr($QQ(root(3,2))$, $QQ(root(3, 2), zeta)$, "2"),
  arr($QQ$, $QQ(root(3, 2), zeta)$, "6"),
  // arr($QQ$, $QQ(alpha)$, $3$),
  // arr($QQ$, $F_n$, $2^n$),
  // arr($QQ(alpha)$, $F_n$, $d$)
  // arr($V_j$, $V$, $eta_j$, "inj"),
  // arr($V$, $V""$, $T$),
  // arr($V""$, $V_i$, $pi_i$, "surj"),
  // arr($V_j$, $V_i$, $T_(i j)$),
  // arr($M_1$, $M_2$, $T$),
  // arr($R^n$, $M_1$, $phi_B_1$),
  // arr($R^m$, $M_2$, $phi_B_2$, label-pos: right),
  // arr($R^n$, $M_1$, $≀$, label-pos: right),
  // arr($R^m$, $M_2$, $≀$, label-pos: left),
  // arr($R^n$, $R^m$, $\ \ \ M_(T, B_1, B_2)$, label-pos: "below"),
  // arr("quot", (0, 1), $tilde(phi)$, label-pos: right, "dashed"),
  // arr($R$, "quot", $pi$),
)]
// (Notice, then $x^3 - 2$ also irreducible over $QQ$). So, we'll see that $
// "Aut"(E\/QQ) = 6,
// $ and so moreover we'll see that $"Aut"(E\/QQ) = S_3$.
// // ]

We wish to compute $hash "Aut"(E\/QQ)$. Let $phi$ be an automorphism; then, since $E$ generated by $root(3,2)$ and $zeta$, $phi$ is completely determined by what it maps $root(3,2)$ and $zeta$ to.

First, $phi(zeta)$ must be a root of the polymomial $x^2 + x + 1$, so there are precisely two possibilities, $zeta$ and $overline(zeta)$. Similarly, $phi(root(3,2))$ must be a root of the polynomial $x^3 - 2$ (in $E$). So, it may of course map to $root(3, 2)$, but also, since $zeta^3 = overline(zeta)^3 = 1$, $zeta dot root(3, 2)$ and $overline(zeta) dot root(3, 2)$ are also roots of $x^3 - 2$. Hence, there are 2 possibilities for $phi(zeta)$ and $3$ for $phi(root(3,2))$, for a total of $6$ automorphisms. 

We can more concretely determined the group structure of $"Aut"(E\/QQ)$. Being a group of order 6, it must be (isomorphic to) either $ZZ\/6ZZ$ or $S_3$. We claim it is the second case. The easiest way to show this is that $"Aut"(E\/QQ)$ can be made to act transitively on a set of 3 elements. Let $r_1 = root(3,2), r_2 = zeta root(3,2), r_3 = overline(zeta) root(3, 2)$ enumerate the roots of $x^3 - 2$ in $E$. Then, the automorphisms in $"Aut"(E\/QQ)$ have a natural induced action on the roots. We can tabulate the possibilities; across the top, we write what $zeta$ is mapped to by a given $phi$, and across the left we write what $root(3,2)$ is mapped to:

#align(center,
table(
columns: 3,
gutter: .5em,
stroke: none,
"", $zeta -> zeta$, $zeta -> overline(zeta)$,
table.hline(start:0,end:3),
table.vline(start:0, end:4, x: 1),
table.vline(start:0, end:4, x: 2),
$root(3, 2) -> root(3, 2)$, $id$, $(r_2 r_3)$,
table.hline(start:0,end:3),
$root(3, 2) -> zeta root(3, 2)$, $(r_1 r_2 r_3)$, $(r_1 r_2)$,
table.hline(start:0,end:3),
$root(3, 2) -> zeta root(3, 2)$, $(r_1 r_3 r_2)$, $(r_1 r_3)$,
)
)

To compute these, consider for instance the $phi$ such that $phi(zeta) = zeta$ and $phi(root(3, 2)) = zeta root(3, 2)$. Then, $phi(r_1) = r_2$, and $
phi(r_2) = phi(zeta root(3, 2)) = phi(zeta) phi(root(3, 2)) = zeta zeta root(3, 2) = overline(zeta) root(3, 2) = r_3,
$ and finally $
phi(r_3) = phi(overline(zeta)) phi(root(3, 2)) = overline(zeta) zeta root(3, 2) = root(3, 2) = r_1,
$ so, $phi$ acts as the 3-cycle $(r_1 r_2 r_3)$ on the set of roots. 

Hence, we conclude that $
"Aut"(E\/QQ) = "Gal"(E\/QQ) = S_3.
$

== Properties of Galois Extensions

Throughout, we assume $E\/F$ a finite Galois extension, and we put $G = "Gal"(E\/F)$.

Denote by $E^G = {alpha in E | g alpha = alpha forall g in G}$ the set of fixed points of $E$ under $G$.

#proposition[$E^G$ is a subfield of $E$ which contains $F$, so we have the inclusion of extensions $E supset E^G supset F$.]

#proof[
If $x, y in E$ are fixed under $G$, then $g (x + y) = g x + g y = x + y$, with a similar computation for products. So, $E^G$ closed under addition, multiplication and is moreover a subfield.

For the second claim, note that by definition, automorphisms of $E\/F$ are constant on elements of $F$, so certainly $F subset E^G$.
]

#theorem[
  $E^G = F$.
]

#proof[
  We have $
  E bar.h E^G bar.h F,
  $ of extensions. Consider now $"Aut"(E\/E^G)$. This certainly contains $G$ as a subgroup. We know then $
  [E : F] = hash G <= hash"Aut"(E\/E^G) <= [E : E^G].
  $ But we know that $[E : E^G]$ divides $[E: F]$ by multiplicativity, so we conclude that $[E : E^G] = [E : F]$ hence $[E^G : F] = 1$. Thus, $E^G = F$.
]

#theorem[
  If $f(x)$ is an irreducible polynomial in $F[x]$ which has a root in $E$, then $f(x)$ splits completely into linear factors in $E[x]$.

  More generally for non-Galois groups, if an extension has this property, we say $E\/F$ is normal.
]<thm:onnormality>

#proof[
  Let $r in E$ be a root of $f(x)$. Let ${r_1, dots, r_n}$ be the orbit of $r$ under the action of $G$ and consider the polymomial $
  g(x) = (x - r_1)(x -r_2)&dots.c(x-r_n) \
  &= x^n - sigma_1 x^(n-1) + sigma_2 x^(n-2) + dots.c + (-1)^n sigma_n
  in E[x],
  $  where $sigma_1, dots, sigma_n$ are the so-called "elementary symmetric functions" in $r_1, dots, r_n$. Namely, $
  sigma_1 &= r_1 + dots.c + r_n,\
  sigma_2 &= r_1 r_2 + r_2 r_3 + dots.c + r_(n-1) r_n = sum_(1 <= i < j <= n) r_i r_j\
  sigma_3 &= sum_(1 <= i < j < k <= n) r_i r_j r_k,\
  &dots.v\
  sigma_n &= r_1 dots.c r_n.
  $ Remark that each $sigma_i$ invariant under permutations of the $r_i$'s. Hence, in particular, $sigma_i in E^G$; by construction, the $r_i$'s were defined as the orbit of our original root $r$ under the action of $G$ i.e. $G$ acts on the set ${r_1, dots, r_n}$ by permutation. So, the expression $sigma_i$ is an element of $E$, which is invariant under the action of $G$ and so by definition in $E^G$. But remember, $E\/F$ Galois thus $E^G = F$ so each $sigma_i in F$. 
  
  In particular, then, $g(x)$ a polynomial with coefficients in $F$ so $g(x) in F[x]$. Remember our original $f(x)$ is irreducible in $F[x]$ so namely is the minimal irreducible polymomial on $r$ over $F$; any other polymomial that vanishes on $r$ must be divisible by $f$, hence $f(x)|g(x)$, from which we conclude $f(x)$ factors completely into linear factors in $E[x]$.
]

== Splitting Fields

Let $F$ be a field and $f(x) in F[x]$.

#definition("Splitting Field")[
  A _splitting field_ of $f(x)$ is an extension $E\/F$ satisfying: 

  1. $f(x)$ factors into linear factors in $E[x]$, namely, $
  f(x) = (x - r_1) dots.c (x - r_n) 
  $ for $r_i in E$;
  2. $E$ is generated as a field by the roots $r_1, dots, r_n$.
]

=== Construction of a Splitting Field

We'll construct a splitting field by induction on $deg(f(x)) = n$. If $n = 1$, there's nothing to do and $E =F$. Let then $deg(f(x)) = n + 1$ and let $p(x)$ be an irreducible factor of $f(x)$. Then, let $
L := F[x]\/(p(x)).
$ $L$ a field, since $p$ irreducible, and it contains a root of $p(x)$ and hence by $f(x)$, by construction. Let $r$ be the root of $p(x)$ in $L$; namely, recall that $r = x + (p(x))$. Then, $x - r$ divides $f(x)$ in $L[x]$, so $f(x) = (x - r)g(x)$ for some $g$ of degree $n$. By the induction hypothesis, we can construction $E$ to be a splitting field of $g(x)$ over $L$; then, in particular, $f$ also splits over $E$, so $E$ also a splitting field of $f$, completing the construction.

Pictorally, viewing $L$ as $F$ adjoining a root $r_1$ of $f$, we have:

#align(center)[#commutative-diagram(
  node-padding: (30pt, 30pt),
  node((6,0), $F$),
  node((6,1), $f(x)$),
  node((5,0), $L = F(r_1)$),
  node((5,1), $(x - r_1) g(x) = f(x)$),
  arr($F$, $L = F(r_1)$, ""),
  node((4,0), $L_2= L(r_2)$),
  node((4,1), $(x-r_2) h(x) = g(x)$),
  arr($L = F(r_1)$, $L_2= L(r_2)$, ""),
  node((3,0), $dots.v$),
  arr($L_2= L(r_2)$, $dots.v$, ""),
  node((2,0), $L_N$),
  arr($dots.v$, $L_N$, ""),
  node((2,1), $(x-r_1)(x-r_2)dots.c(x-r_N) = f(x)$)
  // arr( $dots.v$)
  // node((0, 1), $V$),
  // node((0, 1), $QQ(root(3,2), zeta)$),
  // node((1, 0), $QQ(zeta)$),
  // node((1,2), $QQ(root(3, 2))$),
  // node((2, 1), $QQ$),
  // arr($QQ$,$QQ(root(3, 2))$, "3"),
  // arr($QQ$,$QQ(zeta)$, "2"),
  // arr($QQ(zeta)$, $QQ(root(3, 2), zeta)$, "3"),
  // arr($QQ(root(3,2))$, $QQ(root(3, 2), zeta)$, "2"),
  // arr($QQ$, $QQ(root(3, 2), zeta)$, "6"),
)]

Noting that, by virtue, this process terminates after finitely many iterations since $f$ of fintie degree.

#remark[
  It's very hard to compute the degree of a splitting field of $f(x)$, since at each iteration of the construction several, or just a single, new root of the polynomial will be adjoined.

  In particular, if $f(x)$ is irreducible of degree $n$ and $E$ the splitting field of $f(x)$, then $
  n <= [E : F] <= n!.
  $ The lower bound comes from the fact that we need to adjoin at least one root of $f$ to $F$ to get to $E$; if a single adjointment suffices to include all the roots of $f$, then $[E : F] = n$. The upper bound comes from the "worst-case", where the first root adjoinment adds no other roots of $f$ to $F(r_1)$, and $f(x) = (x - r_1) g(x)$ where $g$ irreducible over $F(r_1)$, and this repeats at each iteration (at each stage, only exactly one root is added). In this case, $[E : F] = [E : F(r_n)] dot [F(r_n) : F(r_(n-1))] dots.c [F(r_1) : F] = n!$.
]

== Properties of a Splitting Field

#theorem[
  If $f(x) in F[x]$ and $E, E'$ are splitting fields of $f(x)$ over $F$, then $E$ and $E'$ are isomorphic as extensions of $F$ i.e. there is an isomorphisms of fields between $E$ and $E'$ that is constant on $F$.
]

#proof[
  We proceed by induction on $n = deg(f(x))$.

  If $n = 1$, then $E = E' = F$.

  Suppose the case for all polynomials of degree $n$ and take $f$ a polynomial of degree $n + 1$. Let $p(x)$ be an irreducible factor of $f(x)$ and let $r$ be a root of $p(x)$ in $E$, $r'$ a root of $p(x)$ in $E'$. Then, we have the "inclusion of fields":
  #align(center)[#commutative-diagram(
 node((2,1), $F$),
 node((1,0), $F(r)$),
 node((1,2), $F(r')$),
 arr($F$, $F(r)$, ""),
 arr($F$, $F(r')$, ""),
 node((0,0), $E$),
 node((0,2), $E'$),
 arr($F(r)$, $E$, ""),
 arr($F(r')$, $E'$, ""),
 node-padding: (30pt, 30pt)
)]

We know then that $F(r)$ and $F(r')$ are isomorphic, since $F(r) = F[x]\/(p(x)) = F(r')$ // TODO.
Let $phi$ be an isomorphism from $F(r)$ to $F(r')$.

Let $L = F(r) =^phi F(r')$, so $E, E'$ are both extensions of $L$. Then, $E$ and $E'$ are both splitting fields of $g(x)$ where $g(x)(x - r) = f(x)$. By the induction hypothesis, then, $E, E'$ are isomorphic as extensions of $L$.
]

#remark[
  This theorem establishes a type of uniqueness of splitting fields, up to isomorphism. However, remark that in constructing our isomorphism, we had to pick, arbitrarily, roots $r, r'$ and "identify" them, so to speak. There is no canonical or natural way to pick such roots. Hence, while the two splitting fields $E, E'$ are isomorphic, the possible isomorphism between them is not unique.
]

#proposition[
  If $E\/F$ is Galois, then $E$ is the splitting field of a polynomial $f(x) in F[x]$.
]

#proof[
  Since $[E : F] < infinity$, let $alpha_1, dots, alpha_n$ be a finite set of generators for $E$ over $F$. Let $f_1, dots, f_n$ be irreducible polynomials in $F[x]$ having $alpha_1, dots, alpha_n$ as roots. Let $f(x) = f_1 (x)f_2 (x)dots.c f_n (x)$. By normality, all the $f_j$'s factor completely in $E[x]$, hence so does $f$. So, the roots of $f(x)$ generate $E\/F$ so $E$ is the splitting field of $f(x)$.
]

== Finite Fields

If $F$ a finite field (a field that is finite as a set), then there is some unique minimal $p$ such that $1 + dots.c + 1 = p dot 1 = 0$ (for if no such $p$ existed, $F$ would not be finite). Moreover, $p$ must be prime, for if not then $0 = p = a dot b$ for nonzero elements $a, b$, so $a, b$ are zero divisors in $F$, which is impossible since $F$ a field. We often denote by $p = "char"(F)$, and call then $ZZ\/p ZZ subset F$ the prime (sub)field of $F$. Let $n = dim_(FF_p) (F)$ be the dimension of $F$ as vector space over this prime field. Then, we conclude $hash F = p^n$; every finite field has cardinality a prime power. 

Conversely, given some prime $p$ and some integer $n$, does there exist an integer $n$ such that $hash F = p^n$? We'll prove this in the affirmative.

#theorem[
Given a prime $p$ and $n >= 1$, there is a field of cardinality $p^n$; in fact, it is unique up to isomorphism.
]

#proof[
Note that if $F$ a field of cardinality $p^n$, $F^times$ is an abelian group of cardinality $p^n - 1$. Then, for every $x in F^times$, $x^(p^n - 1) = 1$, so $
x^(p^n) - x = 0, forall x in F = F^times union{0}.
$ In particular, $F$ is the collection of roots of the polynomial of $x^(p^n) - x$.

With this in mind, then, for a fixed prime $p$ and integer $n >= 1$, let $F$ be the splitting field of the polynomial $x^(p^n) - x$ over $FF_p$. We claim that $F$ has cardinality $p^n$.

Note that $x^(p^n) - x$ has distinct roots in any extension of $FF_p$. Since $f'(x) = -1$ (in the extension), we know that $"gcd"(f(x), f'(x)) = 1$ 
so there are no multiple roots. Hence, $hash F >= p^n$. Conversely, note that the set of roots of $x^p^n - x$ is itself a field; // TODO 
so, $hash F <= p^n$ and thus $hash F = p^n$.

By the previous section, $F$ being a splitting field of a polynomial, it is unique up to isomorphism, completing the proof of the theorem.
]
// #proof[

// ]

A natural extension of this theorem is to ask whether $F$ is Galois over $FF_p$.

#definition("Frobenius Homomorphism")[
  The map $phi: F -> F$ defined by $phi(alpha) = alpha^p$ is called the _Frobenius homomorphism_ of $F$.
]

Because $phi$ is a homomorphism of fields, $phi$ is an injection. $phi$ is also $FF_p$-linear, so $phi$ in particular an automorphism of $F$. So, $phi in "Aut"(F\/FF_p)$. What is the order of $phi$? We know that $
phi^k (alpha) = alpha^(p^k),
$ so we wish to find the minimal $k$ such that $alpha^p^k = alpha$ for all $alpha in F$. Then, for such a $k$, the polynomial $x^p^k - x$ has at least $p^n$ roots in $F$ so it must be that $k >= n$ since any polymomial has at most its degree number of roots. But we know also that $phi^n = id$, since by the very construction of $F$ as a splitting field, $alpha^p^n = alpha$ for every $alpha in F$. So, $k = n$ i.e. $phi$ of order $n$ in $"Aut"(F\/FF_p)$. Hence, we know that $ZZ\/n ZZ subset "Aut"(F\/FF^p)$, in particular $hash"Aut"(F\/FF^p) >= n$.

From the general theory, we also know that $"Aut"(F\/FF^p) <= [F : FF^p] = n$, and thus we know precisely that $hash"Aut"(F\/FF^p) = n$. Thus, we have in summary the following theorem:

#theorem[
  $F$ is a Galois extension of $FF_p$, whose Galois group is the cyclic group $ZZ\/n ZZ$, with a canonical generator given by the Frobenius automorphism. Concretely, $
  "Gal"(F\/FF_p) = {1, phi, phi^2, dots, phi^(n-1)}.
  $
]

#example[
  Let $q = 8 = 2^3$, then $F = FF_2 [x]\/(x^3+x+1)$ a (really, _the_) field of cardinality $8$. By the theory we've developed here, we also know that $F$ the splitting field of the polynomial $x^8 - x$ over $FF_2$.
]

== Generalization of Galois

Here, we aim to extend some of the definitions from previous sections to apply to field extensions of infinite degree.

#definition("Normal")[
  An extension $E\/F$ is said to be _normal_ if every irreducible polynomial in $F[x]$ with a root in $E$ splits into linear factors in $E[x]$.
]

#theorem[If $E\/F$ Galois, then $E$ is normal over $F$.]

#proof[In the finite case this was proven @thm:onnormality.]

We can present a (partial) converse to this statement subject to some technicality.

#definition("Separable")[
  An extension $E\/F$ is _separable_ if every irreducible polynomial with a root in $E$ has no multiple roots in $E$.
]

#proposition[
  If $"char"(F) = 0$, every extension of $F$ is separable.
]

#proof[
  Let $f(x)$ be irreducible in $F[x]$. Suppose $f(x) = (x - r)^e g(x)$ in $E[x]$. Then, $
  f'(x) = e (x - r)^(e - 1) g(x) + (x - r)^e g'(x).
  $ Then, observe that if $e > 1$, then $r$ still a root of $f'(x)$. In particular, then $r$ a root of $"gcd"(f(x), f'(x)) in F[x]$. 
  
  Suppose now $"char"(F) = 0$. Write $
  f(x) = a_n x^n + a_(n-1) x^(n-1) + dots.c + a_1 x + a_0, wide a_i in F,
  $ so $
  f'(x) = n a_n x^(n - 1) + (n - 1) a_(n-1)x^(n-2) + dots.c + a_1.
  $ Then, $gcd(f, f')$ must divide $f$. But $f$ irreducible, so it must be that $gcd(f, f') = 1$ or $f$; clearly $f$ cannot divide $f'$ since $f'$ has degree $n-1$ and $f$ has degree $n$, and thus $gcd(f, f') = 1$ from which we conclude from our observations above that $f$ cannot have any multiple roots.
]

#remark[
We implicitly used the assumption on the characteristic of the field when taking the derivative; in particular, since $"char"(F)  = 0$, taking the derivative only reduced the degree by 1, namely, $n eq.not 0$. If, say, $"char"(F) = p$, then for instance the polynomial of degree $p$, $f(x) = x^p$, has derivative $f'(x) = p x^(p - 1) = 0$, of degree $0$. In this case, we find $gcd(f, f') = f$.
]

#theorem[If $E\/F$ is finite Galois, then it is separable.]

#theorem[
  If $E\/F$ is a finite, normal and separable, then $E\/F$ is Galois.
]

#proof[
  Recall our proof of $hash"Aut"(E\/F) <= [E:F]$; the proof of this theorem is identical to that one, but replacing certain inequalities with equalities using the extra hypotheses of normality and separability.

  We'll prove by induction the more general statement $hash"Hom"_F (K, E) = [K: F]$, where $F subset.eq K subset.eq E$, inducting on the degree of $K$ over $F$.

  Put $n := [K : F]$. If $n = 1$, then $"Hom"_F (K, E) = "Hom"_F (F, E) = {id}$ so this is trivial.

  Suppose the case for $n-1$. Suppose firstly that $K = F(alpha) = F[x]\/p(x)$ where $p(alpha) = 0$ and $p(x)$ irreducible over $F$ with $deg(p) = [K : F]$. Then, $
  "Hom"_F (K, E) = "Hom"_F (F(alpha), E) = {"roots of" p(x) "in" E},
  $  since any homomorphism is constant on $F$ so determined by $alpha$. Namely, we try to construct a ring homomorphism $
  phi : F[x]\/p(x) -> E
  $ or equivalently, $phi : F[x] -> E$ such that $p in ker(phi)$; hence $p(phi(x)) = 0$.

  By normality and separability, $hash {"roots of" p(x) "in" E} = "deg"(p(x)) = [K : F]$.

  Suppose now more generally that $K = F(alpha_1, dots, alpha_(t)) = F(alpha_1, dots, alpha_(t - 1)) (alpha_t) =: K_(t - 1) (alpha_t)$, such that $K_(t-1) subset.neq K$ (else, would be done). By assumption, $[K_(t - 1) :F] < [K : F] = n$ so our induction hypothesis applies and we know $hash"Hom"_F (K_(t - 1), E) = [K_(t - 1): F].$ We need now to show that there are exactly $[K : K_(t-1)]$ extensions of $phi_0 : K_(t - 1) -> E$ for each $phi_0 in "Hom"_F (K_(t - 1), E)$.

  Let $p(x)$ be the minimal polynomial of $alpha_t$ over $K_(t - 1)$ so $"deg" p(x) = [K : K_(t - 1)]$ and we can identify $K = K_(t - 1)[x]\/(p(x))$. If $phi|_(K_(t - 1)) = phi_0$, then since $p(alpha_t) = 0$, $
  phi(p(alpha_t)) = p^(phi_0) (phi(alpha_t)) = 0;
  $ for, if $
  p(x) = a_m x^m + dots.c + a_1 x + a_0,
  $ with $a_i in K_(t - 1)$, then we denote $
  p^(phi_0) (x) = phi_0 (a_m) x^m + dots.c + phi_0 (a_1) x + phi_0 (a_0),
  $ i.e. $p$ with the coefficients evaluted on $phi_0$. Then, $phi_0 (a_i) in E$ so $p^(phi_0) (x) in E[x]$. So, $phi(alpha_t)$ a root of $p^(phi_0) (x)$ in $E[x]$.
  
   We claim $p^(phi_0) (x)$ splits into distinct linear factors in $E[x]$. It suffices to prove that $p^(phi_0)$ has a single root in $E$, by normality. 

  //  We know $p(x)$ has a root in $E$, namely $alpha_t$, so $p(x)|g(x)$ where $g$ the minimal polynomial of $alpha_t$ over $F$. By normality, $g$ separates into linear factors in $E[x]$, which are distinct by separability. The coefficients of $g$ are in $F$, so $g^(phi_0) (x) = g(x)$, since $phi_0$ on each coefficient is the identity. So, $p^(phi_0) (x)|g^(phi_0) (x) = g(x)$, so $g$ can also be seen as a polynomial in $K_(t - 1) [x]$ hence $p^(phi_0) (x)$ splits into linear factors in $E$ // TODO
   
   We know $p(x)$ has a root in $E$, namely $alpha_t$, so $p(x)|g(x)$  where $g(x)$ the minimal polynomial of $alpha_t$ over $F$. By normality and separability, $g$ splits into linear factors over $E$, and thus $p^(phi_0)|g^(phi_0)$. But $g$ has coefficients in $F$ so $g^(phi_0) = g$ thus $p^(phi_0)|g$. so $p^(phi_0) (x)$ has exactly $[K : K_(t-1)]$ roots. Thus, we can conclude $
   hash"Hom"_(F) (K, E) &= hash"Hom"_F (K_(t - 1), E) times hash {"extensions" phi "of" phi_0 : K_(t- 1) -> F} \ 
   &= [K_(t - 1) : F] [K : K_(t - 1)] = [K : F],
   $ so taking $K = E$, we conclude $
   hash"Hom"_F (E, E) = hash"Aut"(E\/F) = [E : F].
   $
]
// TODO what the fuck is going on here? rewrite better proof for this .

This motivates the following definition generalization, with the benefit that it works for infinite degree extensions.

#definition("Galois Extension")[
  An extension $E\/F$ is said to be _Galois_ if it is normal and separable over $F$.
]

In summary we've proven the following:
#theorem[
  If $E\/F$ is a finite extension, then TFAE: 
  1. $hash"Aut"(E\/F) = [E : F]$;
  2. $E$ is normal and separable over $F$;
  3. $E$ is a ("the", up to isomorphism) splitting field of a separable polynomial over $F$.
]

#proposition[
  If $E\/F$ is a Galois extension and $K$ is any subfield of $E$ containing $F$, then $E\/K$ is also Galois.
]
#proof[
This is immediate from 3. of the previous theorem, and from 2.; if $alpha in E$, $E\/F$ is normal and separable so there is a polynomial $f(x) in F[x]$ which is irreducible, splits into distinct linear factors in $E$, and satisfies $f(alpha) = 0$. Let $g(x)$ be the minimal polynomial of $alpha$ over $K$ so $g(x) in K[x]$, $g(alpha) = 0$ and $g$ irreducible. So, $f(x) in K[x]$ as well so it must be by minimality that $g|f$, in $K[x]$. So, it must be that $g$ splits into distinct linear factors in $E[x]$ since $f$ does. Hence, $E\/K$ normal and separable.

Another way of seeing this is the following, using part 1. Let $G = "Gal"(E\/F)$ and $X = "Hom"_F (K, E)$. We saw last time that $hash X = [K : F]$. We have a natural action of $G$ on $X$; if $phi in X$ and $sigma in G$, then define $
sigma ast phi := sigma compose phi.
$ It turns out that $X$ actually a transitive $G$-set. Previously, we showed that any $phi : K -> E$ extends to a map $tilde(phi) : E -> E$; then if $phi_1, phi_2 : K -> E$, let $sigma = tilde(phi)_1compose tilde(phi)_2^(-1)$. By the orbit-stabilizer theorem, then, we find that $
hash X dot hash "Stab"_G (id : K -> E) = hash G.
$ We know $hash X = [K : F]$ and $hash G = [E : F]$. Moreover, the elements of $G$ that fix $id : K -> E$ are precisely the number of elements that fix $K$, hence $hash"Aut"(E\/K)$; so, rearranging, we find $
hash"Aut"(E\/K) = [E:F]/[K:F],
$ which is equal to $[E : K]$ by multiplicativity.
]

#remark[
  Note that $K$ need not be Galois over $F$ in this setup.
]

#theorem[
  The map $K |-> "Gal"(E\/K)$ is an injection from ${"subfields" F subset K subset E} -> {"subgroups of" "Gal"(E\/F)}$.
]<thm:injectionsidegal>

#proof[
  We can show there exists a left-inverse to this map, namely, given $H = "Gal"(E\/K)$, how can you recover $K$ from $H$? Let $K = E^H$.
]

#corollary[
  If $E\/F$ is finite Galois, then there are finitely many fields $F subset K subset E$.
]
#proof[
  $"Gal"(E\/F)$ is a finite group so has finitely many subgroups. From the previous theorem, then since the map from subfields to subgroupsis injective there are at most $hash {"subgroups"}$ distinct subfields.
]

#corollary[
  If $E\/F$ is any finite separable extension, then there are finitely many subfields $F subset K subset E$.
]

#proof[
  If $E$ is separable, $E$ is generated by $alpha_1, dots, alpha_t$ where the $alpha_j$ is the root of a separable polynomial $g_j (x) in F[x]$. Let $tilde(E)$ be the splitting field of $g_1 (x) dots.c g_j (x)$. Then, $tilde(E)\/F$ Galois, and $E subset tilde(E)$, hence by the previous corollary there are finitely many fields $F subset K subset tilde(E)$ and thus those $K$ which are also subsets of $E$ is less than this finite number.\
]

#remark[
  $E\/F$ separable is essential in this corollary. Consider $F = FF_p (u, v)$ where $u, v$ two indeterminates. Let $E = F(u^(1\/p), v^(1\/p))$. Then, $K_alpha = F(u^(1\/p) + alpha v^(1\/p))$ for $alpha in F$ are distinct subfields of $E$ containing $F$.
]

#theorem("Primitive Element Theorem")[
  If $E\/F$ is finite and separable, then there exists an $alpha in E$ such that $E = F(alpha) = F[alpha] tilde.eq F[x]\/(p_alpha (x))$, where $p_alpha (x)$ is the minimal polynomial of $alpha$ in $E\/F$.
]

#proof[
  If the ground field $F$ is finite, then the result is clear because then $E$ is also finite, so $E^times$ is cyclic so finitely generated.

  Suppose then $F$ infinite. We know $E = F(alpha_1, dots, alpha_n)$; we proceed by induction by $n$. If $n = 1$ we're done. Suppose $n = 2$, and let $E = F(alpha, beta)$. Consider $E_t := F(alpha + t beta)$ where $t in F$, which is an extension of $F$ and a subfield of $E$. There are infinitely many $t$'s, but by the previous theorem can only be finitely many $E_t$'s. In particular, there must be $t_1, t_2 in F$ such that $E_t_1 = E_t_2$, namely $
  E_0 := F(alpha + t_1 beta) = F(alpha + t_2 beta).
  $ Then, $alpha + t_1 beta, alpha + t_2 beta in E_0$, so in particular $(t_1 - t_2) beta in E_0$ (by subtracting), and by construction $t_1 eq.not t_2$, so we can divide out and conclude $beta in E_0$. So, subtracting $t_1 dot beta$ from $alpha + t_1 beta$, we conclude $alpha, beta in E_0$, so $E_0 supset E$, but the converse was by construction, so we conclude $E_0 = E$.

  Suppose the case for $n$ and let $E = F(alpha_1, dots, alpha_(n+1))$. We may rewrite this as $F(alpha_1, dots, alpha_(n)) (alpha_(n+1))$. Applying the induction hypothesis, we find this equal to $E = F(beta)(alpha_(n+1)) = F(beta, alpha_(n+1))$, and so applying the $n = 2$ case, we are done.
]

#remark[
  The separability assumption is key in the statement. Consider $F = FF_p (u, v)$ and $E = FF_p (u^(1\/p), v^(1\/p))$, an extension of degree $p^2$ over $F$. We claim there is no primitive element. Suppose $alpha in E$ is such that $alpha = R(u^(1\/p), v^(1\/p)) = f(u^(1\/p), v^(1\/p))/g(u^(1\/p), v^(1\/p))$. then, $alpha^p = f(u, v)/g(u, v) in F$, so $[F(alpha) : F] = 1$ or $p$ for every $alpha in E$. In particular, this means $F(alpha) eq.not E$. Hence, the primitive element theorem doesn't apply; there are infinitely many distinct subfields.

  We glossed over the computation of the degree. Note that $u^(1\/p)$ satisfies the polynomial $x^p - u$ which is irreducible. $v^(1\/p)$ satisfies $x^p - v$, which we claim has no roots in $F(u^(1\/p))$. If $v = R(u^(1\/p), v)^p = R(u, v^p)$, which is impossible so $v$ not a $p$th power in $F(u^(1\/p))$. So, $[F(u^(1\/p), v^(1\/p)) : F] = p^2$ by multiplicativity.
]

We use this theorem to prove the converse of @thm:injectionsidegal.

#proposition[
  $[E : E^H] = hash H$.
]
#proof[
  By the primitive element theorem, $E = E^H (alpha)$ for some $alpha in E$. Consider $H alpha =$ orbit of $alpha$ under $H$ $={alpha_1, dots, alpha_n}$. We claim $hash H alpha = hash H$. It must be that $"Stab"_H (alpha) = {1}$, since if $g alpha = alpha$, $g$ acts as the identity on $E$ hence equals $id$ in $H$. From the orbit-stabilizer theorem, we conclude the claim.

  Consider then $p(x) = (x - alpha_1)dots.c (x - alpha_n) in E^H [x]$, which is in this space since upon expansion each of the coefficients are fixed under $H$. $p(alpha) = 0$; moreover, we claim $p(alpha)$ is irreducible over $E^H$. $H$ acts transitively on the roots of the polynomial, by design, so it must be irreducible; if it weren't, then there would be two (or more) orbits of the roots of the polynomial.

  Thus, we conclude $[E : E^H] = "deg"(p) = n = hash H$.
]

#corollary[
  $H = "Gal"(E\/E^H)$.
]

In particular, this establishes the following maps: $
{#stack(spacing: .5em, "subfields", $F subset K subset E$)} #stack(spacing: .2em, $arrow.r.long^(K |-> "Gal"(E\/K))$, $arrow.l.long_(E^H arrow.l.bar H)$) {#stack(spacing: .5em, "subgroups", $H subset G$)}
$
and so
#theorem("Galois Correspondance")[
  These two maps are mutually inverse bijections.
]

There is additionally a partial ordering on both of these sets by inclusion, and these maps respect this ordering; namely, $
F subset K_1 subset K_2 subset E => "Gal"(E\/K_1) supset "Gal"(E\/K_2),
$ and similarly $
H_1 subset H_2 subset G => E^(H_1) supset E^(H_2).
$ Namely, we say the Galois correspondance is "inclusion reversing".


=== Computational Example
// #example[
  Let $F = QQ$ and $E$ be the splitting field of $x^4 - 2$. Let $r = root(4,2)$ and $E_0 = QQ(root(4, 2))$ so $x^4 - 2 in E_0 [x]$. Moreover, we automatically gain another root, $- root(4, 2) in E_0$, so this polynomial factors $
  x^4 - 2 = (x - root(4, 2))(x + root(4, 2))(x^2 + sqrt(2)),
  $ where here we are formally defining $sqrt(2) = (root(4, 2))^2$; this is no further reducible, so we need to adjoin another element. Let $E = E_0 [x]\/(x^2 + sqrt(2))$. Note that then $sqrt(-sqrt(2)) = i root(4, 2) = i r$; namely, we can view $E = E_0 (i r) = E_0 (i)$. So, we have 

#align(center,
    commutative-diagram(
      node-padding: (30pt, 30pt),
      node((3,0), $QQ$),
      node((2,0), $QQ(r)$),
      node((1,0), $E=QQ(r,i)$),
      arr($QQ$, $QQ(r)$, $4$, label-pos:right),
      arr($QQ(r)$, $E=QQ(r,i)$, $2$, label-pos:right),
      arr($QQ$, $E=QQ(r,i)$, $8$, curve: 45deg)
    )
)
  Then, there are $4$ roots in $E$ of $x^4 - 2$, namely $plus.minus root(4, 2), plus.minus i root(4, 2)$, and moreover $sigma in "Gal"(E\/QQ)$ is determined by $(sigma(r), sigma(i))$ where $sigma(r)$ can map to any root and $sigma(i)$ can map to $i$ or $-i$.

  Consider the automorphism $sigma(root(4, 2)) = i root(4, 2)$, $sigma(i) = i$. Then, $sigma$ acts on the set of roots as a $4$-cycle. Another is $tau(root(4, 2)) = root(4, 2)$, $tau(i) = - i$. Then, $tau$ swaps $plus.minus root(4, 2)$. In particular, $sigma, tau$ then generated the entire group, from which we readily see that $"Gal"(E\/QQ) tilde.eq D_8$.

  Let us relabel $"Gal"(E\/QQ) = {1, r, r^2, r^3, D_1, D_2, V, H}$ in the familiar way, and explore all the possible subfields on $E$. By the Galois correspondance, we can begin by loooking at the list of all subgroups by inclusion:
  #align(center,
    commutative-diagram(
      node-padding: (30pt, 30pt),
      node((3,0),${1,r,r^2,r^3}$),
      node((3,1), ${1, V, H, r^2}$),
      node((3,-1),${1,D_1, D_2, r^2}$),
      node((2,0), ${1,r^2}$),
      node((2,-2), ${1,D_1}$),
      node((2,-1), ${1,D_2}$),
      node((2,1),${1,V}$),
      node((2,2),${1,H}$),
      node((1,0), ${1}$),
      node((4,0), $D_8$),
      arr($D_8$, ${1,r,r^2,r^3}$, ""),
      arr($D_8$, ${1, V, H, r^2}$, ""),
      arr($D_8$, ${1,D_1, D_2, r^2}$, ""),
      arr(${1,r,r^2,r^3}$, ${1,r^2}$,""),
      arr(${1, V, H, r^2}$, ${1,r^2}$,""),arr(${1,D_1, D_2, r^2}$, ${1,r^2}$,""),
      arr(${1,D_1, D_2, r^2}$, ${1,D_1}$, ""),
      arr(${1,D_1, D_2, r^2}$, ${1,D_2}$, ""),
      arr(${1, V, H, r^2}$, ${1,V}$, ""),
      arr(${1, V, H, r^2}$, ${1,H}$, ""),
      arr(${1,D_1}$, ${1}$, ""),
      arr(${1,D_2}$, ${1}$, ""),
      arr(${1,r^2}$, ${1}$, ""),
      arr(${1,V}$, ${1}$, ""),
      arr(${1,H}$, ${1}$, ""),
    )
  )

  _This is the so-called "lattice" of subgroups of $D_8$_. For each such subgroup $H subset D_8$, we can compute $E^H$ and find the following picture;

#align(center,
    commutative-diagram(
      node-padding: (45pt, 40pt),
      node((4,0), $QQ$),


      node((3,-1), $QQ(sqrt(2))$),
      node((3,0), $QQ(i)$),
      node((3,1), $QQ(sqrt(-2))$),
      node((0,0), $E$),

      node((2,0), $QQ(i, sqrt(2))$),
      node((2,-2), $QQ(root(4,2))$),
      node((2,-1), $QQ(i root(4, 2))$),

      node((2,1), $QQ((1 + i) root(4, 2))$),
      node((2,2), $QQ((1- i) root(4, 2))$),


      arr($QQ$, $QQ(sqrt(2))$, $2$),
      arr($QQ$, $QQ(i)$, $2$),
      arr($QQ$, $QQ(sqrt(-2))$, $2$, label-pos: right),
      arr($QQ(sqrt(2))$, $QQ(i, sqrt(2))$, $2$),
      arr($QQ(i)$, $QQ(i, sqrt(2))$, $2$),
       arr($QQ(sqrt(-2))$, $QQ(i, sqrt(2))$, $2$, label-pos: right),
       

       arr($QQ(sqrt(2))$, $QQ(root(4, 2))$, $2$),
        arr($QQ(sqrt(2))$, $QQ(i root(4, 2))$, $2$),
        arr($QQ(sqrt(-2))$, $QQ((1 + i) root(4, 2))$, $2$, label-pos: right),
        arr($QQ(sqrt(-2))$, $QQ((1- i) root(4, 2))$, $2$, label-pos: right),

        arr($QQ(root(4, 2))$, $E$, $2$),
        arr($QQ(i root(4, 2))$, $E$, $2$),
        arr($QQ(i, sqrt(2))$, $E$, $2$),
        arr($QQ((1 + i) root(4, 2))$, $E$, $2$),
        arr($QQ((1- i) root(4, 2))$, $E$, $2$)
    )
  )

  === Complements of Galois Correspondance

  #proposition[
    If $sigma in "Gal"(E\/F)$ and $F subset K subset E$, $sigma K = {sigma x | x in K}$ is also a subfield of $E\/F$. Moreover, if $H$ corresponds to $K$ under the Galois correspondance, then $sigma H sigma^(-1)$ corresponds to $sigma K$ under the correspondance.
  ]

  #theorem[
    Given $F subset K subset E$, where $E\/F$ Galois, TFAE:
    1. $sigma K = K$ for every $sigma in "Gal"(E\/F)$;
    2. $K$ is Galois over $F$;
    3. $"Gal"(E\/K)$ is a normal subgroup of $"Gal"(E\/F)$.
  ]

  #proof[
    (1. $=>$ 3.) Let $H = "Gal"(E\/K)$. $sigma K = K$ for all $sigma in G = "Gal"(E\/F)$ implies, under the Galois correspondance, $sigma H sigma^(-1) = H$ for every $sigma in G$ so in particular $H$ normal in $G$.

    (1. $=>$ 2.) Restriction gives a homomorphism $eta: "Gal"(E\/F) -> "Aut"(K\/F)$ (noting that this is only well-defined because of assumption 1; namely, since $K$ is "$G$-stable" in a sense, we can restrict the domain of $G$ to act only on $K$). We have that $ker(eta) = {sigma : sigma "fixes" K "pointwise"} = "Gal"(E\/K)$ hence by the isomorphism theorem $ "Gal"(E\/F)\/"Gal"(E\/K) arrow.hook "Aut"(K\/F)$. Counting the size of the LHS, we readily find $
    hash ("Gal"(E\/F)\/"Gal"(E\/K)) = [E: F]/[E : K] = [K : F],
    $ while $hash"Aut"(K\/F) <= [K: F]$, so it must be that equality is achieved i.e. $hash"Aut"(K\/F) = [K : F]$, and in particular we find the isomorphism $
    "Gal"(E\/F)\/"Gal"(E\/K) tilde.eq "Gal"(K\/F).
    $

    Other directions left as an exercise.

    #text(fill: red,
    [
      (3. $=>$ 1.)
    Let $H := "Gal"(E\/K)$. We know by the previous proposition  that for $sigma in "Gal"(E\/F)$, $sigma H sigma^(-1) = "Gal"(E\/sigma K)$. But $H$ normal in $"Gal"(E\/K)$ so $ sigma H sigma^(-1)= H$. By the "mutual bijectiveness" of the Galois correspondance, it must be that $sigma K = K$.

    (2. $=>$ 1.) For every $phi in "Gal"(K\/F)$, we know there are $[E : K]$ extensions $tilde(phi) : E -> K$ (which can thus be viewed $E -> E$ so in $"Gal"(E\/F)$). Since $hash"Gal"(K\/F) = [K : F]$, it follows that we have $[K : F] dot [E : K] = [E : F]$ automorphisms of $E\/F$ which arise from extensions of $phi in "Gal"(K\/F)$, but this the entire size of the group so every such automorphism is of this form and thus is invariant on $K$.
      ]
    )
  ]


== Radical Extensions

#definition("Radical Extension")[
  An extension $E\/F$ is called a _radical extension_ if there exists an integer $n >= 1$ and element $a in F$ such that $E = F[root(n, a)]$. I.e., assuming $x^n - a$ irreducible in $F[x]$, then $E = F[x]\/(x^n - a)$.
]

#definition("Tower of Radicals")[
  A _tower of radical extensions_ $E\/F$ is a sequence of extensions $
  F = E_0 subset E_1 subset E_2 subset dots.c subset E_n = E,
  $ where for each $i = 1, dots, n$, $E_i$ is a radical extension of $E_(i - 1)$ i.e. $E_(i) = E_(i-1) (root(n_i, a_i))$ where $a_i in E_(i - 1)$ and $n_i >= 1$ an integer.
]

A classical question in Galois theory is whether every finite extension of $QQ$ is contained in a tower of radical extensions; another way of phrasing this is given a polynomial $f(x) in QQ[x]$, can its roots be expressed in terms of radicals?

Recall that we said an element $alpha in CC$ is _constructible_ if it is contained in a tower of quadratic extensions. We saw that not every algebraic number $alpha$ was constructible by showing that if $[QQ(alpha) : QQ] = 3$, $alpha$ is not constructible since any tower of quadratic extensions had to have a degree of a power of $2$ over $QQ$. We'd like to similarly find some kind of invariant of a general radical extension. However, the degree of such an extension is too crude, without enough structure. Rather, we'll look at properties of the corresponding automorphism group of such extensions.

=== Automorphism Groups of Radical Extensions

Let $E = F(a^(1\/n))$ a radical extension. What can we say about $"Aut"(E\/F)$? In general, it may be trivial (For instance $QQ(root(3,2))\/QQ$). What conditions do we need to put on $F$ for $F(a^(1\/n)) subset$ splitting field of $x^n - a$?

Given a single root $a^(1\/n)$, then notice that every other root of the form $zeta^k a^(1\/n)$ for $k = 0, dots, n - 1$ where $zeta$ a primitive $n$th root of unity. Hence, we have the following:

#theorem[
  Suppose $F$ contains $n$ distinct $n$th roots of unity, and let $mu_n (F) := {x in F^times | x^n = 1} tilde.eq ZZ\/n ZZ$ be the group of such elements. Then, $F(a^(1\/n))$ is Galois with abelian Galois group. Moreover, this group is canonically a subgroup of $mu_n (F)$.
]

#proof[
  If $sigma in F(a^(1\/n))$, then $sigma(a^(1\/n))$ must map to some other element which, raising to the $n$, equals $a$ itself. Then, since $F$ contains $n$ distinct $n$th roots of unity, then we know moreover that $
  sigma(a^(1\/n)) = zeta_sigma dot a^(1\/n),
  $ where $zeta_sigma in mu_n (F)$ a root of unity. Moreover, then, this root of unity completely determines the action of $sigma$ so we may define a map $
  eta : "Aut"(F(a^(1\/n))) -> mu_n (F), wide sigma |-> zeta_sigma, thin thin "where" sigma(a^(1\/n)) = zeta_sigma dot a^(1\/n).
  $ Then, one verifies that this is a group homomorphism, and if $sigma in ker(eta)$, then it must be that $zeta_sigma = 1$ so $sigma = id_("Aut")$ hence $eta$ an injection. Thus, $"Aut"(F(a^(1\/n)))$ can be realized as a subgroup of $mu_n (F)$, which is abstractly isomorphic to $ZZ\/n ZZ$, which is abelian thus $"Aut"(F(a^(1\/n)))$ itself abelian.

  Finally, $F(a^(1\/n))\/F$ can be viewed as the splitting field of $f(x) := x^n - a$ over $F$, since it contains all of the roots of $f$, and is minimally generated. Thus, the extension is Galois after all.
  // Define the map $
  // eta: "Aut"(E\/F) -> mu_n (F), wide sigma |-> sigma(a^(1\/n))/(a^(1\/n)).
  // $ This is a group homomorphism. Moreover, we claim $eta$ injective. If $sigma in ker(eta)$, then $eta(sigma) = 1$ so $sigma(a^(1\/n)) = a^(1\/n)$ so $sigma = id$ on $E$. 
  
  // $im(eta) tilde.eq "Gal"(E\/F)$.

  // // TODO
]

=== Solvable Groups and the Main Theorem of Galois

#definition("Solvable")[A finite group $G$ is said to be _solvable_ if there is a sequence of subgroups $
{1} subset G_1 subset G_2 subset dots.c subset G_n = G,
$ such that:
1. $G_(i-1) triangle.l G_i$ ($G_(i-1)$ normal in $G_i$) for each $i = 1, dots, n$;
2. $G_i\/G_(i-1)$ is abelian for each $i = 1, dots, n$.
]

#remark[
  A given $G_i$ _need not_ be normal in the whole $G$, just $G_(i+1)$.
]

#example[
1. Any abelian group is solvable, ${1} triangle.l G$
2. $S_3$ is solvable, ${1} triangle.l A_3 triangle.l S_3$
3. $S_4$ is solvable, ${1} triangle.l V:={(), (12)(34), (13)(24), (14)(23)} tilde.eq ZZ\/2ZZ times ZZ\/2ZZ triangle.l A_4 triangle.l S_4$, with $
S_4\/A_4 = ZZ\/2ZZ, wide A_4\/V = ZZ\/3ZZ.
$
4. $S_5$ is not solvable; the only normal subgroup is $A_5$, and $A_5$ contains no normal subgroups (indeed, then, $A_5$ also not solvable).
]

We'll assume throughout that the remainder that $"char"(F) = 0$. The main theorem we'd like to get at:

#theorem[If $E\/F$ is a tower of radical extensions, then it is contained in a Galois extension $tilde(E)\/F$ with solvable Galois group.]<thm:radicalsolvable>

Namely, one can "detect" if a given field extension is a tower of radical extensions by checking if it can be embedded in a Galois extension with solvable Galois group.

#proposition[
  If $G$ is a solvable group, then any quotient $overline(G)$ of $G$ is solvable.
]

#proof[
  Write $
  1 triangle.l G_1 triangle.l G_2 triangle.l dots.c triangle.l G_n = G.
  $ For $overline(G)$ to be a quotient of $G$ means in particular that there is a surjective map $eta : G ->> overline(G)$. Then, simply take the restriction of $eta$ to each subgroup $G_i$, call this $eta_i : G_i ->> overline(G)_i$, i.e. $overline(G)_i = eta(G_i)$. Then, $eta$ induces a homomorphism $
  overline(eta)_i : G_i\/G_(i-1) -> overline(G)_i\/overline(G)_(i-1), wide a G_(i-1) |-> eta(a)overline(G)_(i-1).
  $ One readily verifies that this map surjective. Thus, $overline(G)_i\/overline(G)_(i-1)$ is the image of a surjective map of an abelian group and thus abelian itself.

In particular, we have the following picture:
  #align(center, commutative-diagram(
    node-padding: (8pt, 35pt),
    node((0,0), ${1}$), node((0,1), $triangle.l$), node((0,2), $G_1$),node((0,3), $triangle.l$),
    node((0,4), $G_2$),node((0,5), $triangle.l$), node((0,6), $dots.c$),node((0,7), $triangle.l$), node((0,8), $G_(n-1)$),node((0,9), $triangle.l$), node((0,10), $G_(n) = G$),
    node((1,0), ${1}$), node((1,1), $triangle.l$),  node((1,2), $overline(G)_1$),node((1,3), $triangle.l$),
    node((1,4), $overline(G)_2$), node((1,5), $triangle.l$), node((1,6), $dots.c$), node((1,7), $triangle.l$), node((1,8), $overline(G)_(n-1)$), node((1,9), $triangle.l$), node((1,10), $overline(G)_(n)$),
    arr($G_1$, $overline(G)_1$, $eta_1$, "surj"),
    arr($G_2$, $overline(G)_2$, $eta_2$, "surj"),
    arr($G_(n-1)$, $overline(G)_(n-1)$, $eta_(n-1)$, "surj"),
    arr($G_(n) = G$, $overline(G)_(n)$, $eta$, "surj"),
  ))
]

#proof([(Of @thm:radicalsolvable)])[
  Suppose $F = E_0 subset E_1 subset dots.c subset E_n = E$ where $E_i = E_(i-1) (a_i^(1\/m))$ for $a_i in E_(i-1)$. We prove by induction on $n$.

  For $n = 1$, $E = F(alpha)$ with $alpha^m = a in F$. Let $tilde(E)$ be the splitting field of $x^m - a$, i.e. $tilde(E) = F(zeta, alpha) = F(zeta)(alpha)$. Then, we have the tower $
  F subset F(zeta) subset F(zeta)(alpha).
  $ Then, denoting $sigma_a in "Gal"(F(zeta)\/F)$ which maps $zeta |-> zeta^a$ (for $a in (ZZ\/m ZZ)^times$), one readily verifies $sigma_a compose sigma_b = sigma_(a b)$ so in particular we obtain an injection $
  "Gal"(F(zeta)\/F) arrow.hook (ZZ\/m ZZ)^times.
  $ This gives in particular $"Gal"(F(zeta)\/F)$ abelian. Then, since $zeta in F(zeta)$, it follows that $"Gal"(F(zeta, alpha)\/F(zeta))$ is also abelian, being a subgroup of $ZZ\/m ZZ$ (more concretely, as the group of $m$th roots of unity) as well. Finally, $"Gal"(F(alpha, zeta)\/F)$ is abelian too since it is a splitting field.

  Let $G_1 = "Gal"(F(zeta, alpha)\/F(zeta))$  and $G = "Gal"(F(zeta, alpha)\/F)$. We claim $G_1$ normal in $G$. Indeed, $
  F(zeta, alpha)^(G_1) = F(zeta)
  $ is Galois over $F$, and 
  // since $G_1$ abelian and $G\/G_1 subset (ZZ\/m ZZ)^times$ 
  since under the Galois correspondance $
  G <-> F, wide G_1 <-> F(zeta), wide 1 <-> F(zeta, alpha), 
  $ and since $F(zeta)\/F$ is Galois, the corresponding Galois group $G_1$ is normal in $G$, and so again by the correspondance $G\/G_1 = "Gal"(F(zeta)\/F) subset (ZZ\m ZZ)^times$. Thus, $F(alpha) subset F(alpha, zeta)$ which is Galois with solvable Galois group, thus proving the base case.

  Suppose the claim for $n-1$. We have $
  #stack(
    spacing: .6em,
    dir: ttb,
    $E_(n-1) subset E_n = E_(n-1) (beta)$, $#h(-7em)#rotate(90deg)[$subset$]$,  $#h(-7em)tilde(E)_(n-1)$  ),
  $ where $beta^m = b in E_(n-1)$. By the induction hypothesis, $tilde(E)_(n-1)\/F$ is solvable.

  Let ${b_1, dots, b_t}$ be the orbit of $b$ under $"Gal"(tilde(E)_(n-1)\/F)$ and let $
  g(x) := (x^m - b_1)(x^m - b_2) dots.c (x^m - b_t).
  $ Then, $g in F[x]$, since it's coefficients are fixed under $"Gal"(tilde(E)_(n-1)\/F)$. Let $tilde(E)_(n)$ be the splitting field of $g(x)$ over $F$. In particular, we can write $
  tilde(E)_n = tilde(E)_(n-1) (root(m, b_1), root(m, b_2), dots, root(m, b_t), zeta),
  $ where $zeta$ an $m$th root of unity. Then, we can view this as the following tower of extensions:
  #align(center,
  commutative-diagram(
    node((2,0), $tilde(E)_(n-1)$),
    node((1,0), $tilde(E)_(n-1) (zeta)$),
    node((0,0), $tilde(E)_(n-1) (zeta, root(m, b_1), root(m, b_2), dots, root(m, b_t))$),
    arr($tilde(E)_(n-1)$, $tilde(E)_(n-1) (zeta)$, $subset (ZZ\/m ZZ)^times$, label-pos: right),
    arr($tilde(E)_(n-1) (zeta)$, $tilde(E)_(n-1) (zeta, root(m, b_1), root(m, b_2), dots, root(m, b_t))$, $H$, label-pos: right),
  )
  )
  Then, we find that similar to the base case, $"Gal"(tilde(E)_(n-1) (zeta)\/tilde(E)_(n-1)) subset (ZZ\/m ZZ)^times$, and if we put $H = "Gal"(tilde(E)_n\/tilde(E)_(n-1) (zeta))$, automorphisms here are determined by how they act on an $t$ tuple of $m$th roots, and thus $
  H subset.eq ZZ\/m ZZ times  dots.c times ZZ\/m ZZ,
  $ so in particular $H$ abelian and $H triangle.l G := "Gal"(tilde(E)_n \/tilde(E)_(n-1))$, and so that $G\/H subset (ZZ\/m ZZ)^times$. Thus, we find that $G$ is solvable and normal in $"Gal"(tilde(E)_n\/F)$ and so $"Gal"(tilde(E)_n\/F)\/G$ is solvable thus $"Gal"(tilde(E)_n\/F)$ is solvable.

]

#theorem("Main Theorem of Galois")[If $f(x) in F[x]$ is solvable by radicals, then $"Gal"(f)$ is a solvable group (where $"char"(F) = 0$).]<thm:galoismain>

#proof[
  If $f(x)$ is solvable, then $E$ the splitting field of $F$ is contained in a tower of radical extensions. Therefore, $E$ is contained in a solvable extension of $F$, say $tilde(E)$; $
  F subset E subset tilde(E).
  $ If $G = "Gal"(E\/F)$, then, $G$ is a quotient of $tilde(E)\/F$ and thus $G$ is solvable.
]

#theorem[
  If $f(x)$ is a quintic polynomial and $"Gal"(f) = S_5$, then $f(x)$ is not solvable by radicals.
]

To show this theorem not vacuous, we first show that there exists such a polynomial, with $F = QQ$.

#proposition[Let $G$ be a transitive subgroup of $S_5$ containing a transposition. Then, $G = S_5$.]

#proof[
  $G$ transitive implies $5|hash G$ by orbit-stabilizer // TODO,
  so we can assume WLOG that $sigma = (12345) in G$ and $tau = (12) in G$. Conjugating $tau$ by $sigma, sigma^2, sigma^3, sigma^4$, we further find $(23),(34), (45), (51) in G$. Further conjugating $tau$ by $(23)$ we find $(13) in G$. We can then conjugate this element by $sigma$, and repeat, and ultimately find al the transpositions are in $G$. Since such elements generate $S_5$, we conclude $G = S_5$. 
]

#proposition[
  Let $f(x)$ be a polynomial of degree $5$ satisfying:
  1. $f(x)$ is irreducible over $QQ$;
  2. $f(x)$ has exactly three real roots.
  Then, $"Gal"(f) = S_5$.
]

#proof[
  Let $r_1, dots, r_5$ the roots of $f$ and so $E = QQ(r_1, dots, r_5)$ the splitting field of $f$. We want to show that there exists an automorphism of order 2 that acts on the roots as a transposition, since then by the previous proposition we'd be done since condition 1. ensures $"Gal"(E\/QQ)$ is transitive acting on the roots.
  
  We can embed $E subset CC\/RR$. The only automorphisms of $CC\/RR$ are the identity and complex conjugation. Then, restricting complex conjugation to $E\/QQ$, we find a automorphism of order 2, and since 3 of the roots are real, this conjugation will leave them fixed, hence we are indeed done.
]

We prove now a converse of @thm:galoismain:

#theorem[Every solvable extension of $F$ is constructible by radicals.]

#proof[
  We remark first:
  1. It is enough to show this for abelian $E\/F$, since $E$ solvable so $F subset E_1 subset dots.c subset E_n = E$, and each quotient abelian. So if we can prove for each "subextension", we're done.
  2. We can assume $F$ contains the $n$th roots of unity where $n = [E : F]$ by just adjoining them if not.

  Now, we can view $E$ as an $F$-linear representation of $G= "Gal"(E\/F)$. Since $G$ abelian, we know each of its irreducible representations are one-dimensional. We can write then $
  E = plus.circle.big_(chi in hat(G)) E[chi],\ wide hat(G) = "Hom"(G, F^times), wide E[chi] = {v in E | sigma v = chi(sigma) v forall sigma in G},
  $ since we can identify one dimensional representations with maps into $F^times$ (where we are crucially using that $F$ contains enough roots of unity). 

  We claim $dim_F E[chi] <= 1$.  Suppose $v in E[chi]$ and $v eq.not 0$, and let $w in E[chi]$. We claim they differ by a scalar. Consider $w/v in E$. For any $sigma in G$ $
  sigma(w/v) = sigma(w)/sigma(v) = (chi(sigma) w)/(chi(sigma) v) = w/v,
  $ hence $w/v in E^G = F$ so $w = lambda v$ for some $lambda in F$. It follows that $E[chi] = F dot v$, so $E[chi]$ has dimension (at most) 1.

  Let us compare now dimension on each side; on the one hand, $
  dim_F E = [E : F] = hash G = n,
  $ while $
  dim_F plus.circle.big_chi E[chi] = sum_(i=1)^n dim_F E[chi] <= hash hat(G) =  n,
  $ so equality must actually be attained, and in particular each $E[chi]$ must have dimension one (i.e. every irreducible component 'appears' precisely once). Thus, we find that $E$ is isomorphic to the regular representation of $G$, namely $F[G]$, as a representation of $G$.

  #remark[This is in fact always true for abelian extensions, for general, not necessarily abelian $G$.]
  For each $chi in hat(G)$, let $y_chi in E[chi]$ be a basis (generator), so $
  E = F(y_chi : chi in hat(G)).
  $ For any $sigma in G$, then $
  sigma(y_chi^n) = sigma(y_chi)^n = (chi(sigma) dot y_chi)^n = chi(sigma)^n dot y_chi^n = y_chi^n,
  $ since $chi(sigma)$ some $n$th root of unity, since $G$ abelian. So, $y_chi^n =: a_chi in E^G = F$, and thus $y_chi = a_chi^(1/n)$ and in particular $
  E = F(a_chi^(1\/n) : chi in hat(G)),
  $ completing the proof.
  ]

  === Solution to the Cubic, Revisted

  Recall we can write any cubic with distinct roots (over $QQ$) as $x^3 + p x + q = (x - r_1) (x - r_2)(x - r_3)$ with $G subset S_3$ the Galois group of $E = QQ(r_1, r_2, r_3)$, which acts transitively on the roots so either $ZZ\/3 ZZ$ or $S_3$. We have $
  QQ -^2 K -^(ZZ\/3 ZZ) E.
  $ Let $sigma = (r_1 r_2 r_2)$. We want to diagonalize $sigma$. It should have eigenvalues $1, zeta$ or $zeta^2$ where $zeta$ a primitive 3rd root of unity. Consider $v_1 = r_1 + zeta r_2 + zeta^2 r_3$, then $sigma v_1 = zeta^2 v_1$ and $v_2 = r_1 + zeta^2 r_2 + zeta r_3$, then $sigma v_2 = zeta v_2$. So, these two vectors are eigenvectors. There are a plethora of eigenvectors with eigenvalue 1, such as the symmetric functions on $r_1, r_2, r_3$. Then, we find in particular that $
  v_1^3, v_2^3 in E^sigma (zeta) = K (zeta),
  $ and so $
  r_1 + zeta r_2 + zeta^2 r_3 = root(3, A), wide r_1 + zeta^2 r_2 + zeta r_3 = root(3, B),
  $ where $A, B in K(zeta)$. We don't like $zeta$ here; if we add these two, we find $
  2 r_1 - r_2 - r_3 = root(3, A) + root(3, B).
  $ In particular, recall that in our "depleted cubic", the sum of the roots equals zero, so this simplifies $
  3 r_1 = root(3, A) + root(3, B) => r_1 = root(3, A/27) + root(3, B/27).
  $
  
  // The symmetric functions of $r_1, r_2, r_3$ are fixed under $ZZ\/3 ZZ$. $r_1 + r_2 + r_3$ actually equals 

  Similarly, we can study the quartic equation. We have the chain of normal subgroups $
  S_4 triangle.r A_4 triangle.r V (triangle.r {1, tau} triangle.r) triangle.r  1, 
  $ namely $S_4$ solvable. Let $f(x)$ be quartic and $E$ the splitting field of $f$, assuming $"Gal"(f) = S_4$. By this chain of normal subgroups above and the Galois correspondance, we should find a corresponding sequence of subfields fixed by the corresponding subgroups $
  QQ subset K subset L subset L' subset E.
  $ By looking at the degrees, the first would append a square root, the second a cube root, and the last two another two square roots.

  Consider $V triangle.l S_4$. We know $L$ Galois over $QQ$, and so $"Gal"(L\/QQ) = S_4\/V = S_3$. This seems to imply we can reduce our quartic to a cubic! Suppose $f$ factors $
  f(x) = (x - r_1)(x - r_2)(x-r_3)(x-r_4).
  $ We seek a polynomial $g(x) in QQ[x]$ such that the splitting field of $g$ is $L$. In particular, we wish to find an element in $E$ that is fixed under $V$ but not globally fixed by $S_4$. Consider $r := r_1 r_2 + r_3 r_4$. It is fixed under $V$, but under the action of $S_4$ can map to $r_1 r_3 + r_2 r_4$ and $r_1 r_4 + r_2 r_3$, so in particular $r$ has 3 Galois conjugates. The minimal polynomial of $r$ (namely, the "cubic resolvent") can be written $
  g(x) = (x - (r_1 r_2 + r_3 r_4))(x - (r_1 r_3 + r_2 r_4))(x - (r_1 r_4 + r_2 r_3)) in E^(S_4) [x] = QQ[x].
  $ Let us assume $f(x) = x^4 + a x^2 + b x + c$ where $a, b, c in QQ$. We wish then to find the coefficients of $g$ in terms of $a, b, c$. $
  g(x) = x^3 - (r_1 r_2 + r_3 r_4 + r_1 r_3 + r_2 r_4 + r_1 r_4 + r_2 r_3) x^2 + dots.c
  $ The quadratic term is the pairwise product, which we see to be equal to $a$ (namely the second symmetric function) so $g(x) = x^3 - a x^2 + dots.c$. The remaining terms can be found with a little more work, but ultimately are polynomials in $a, b, c$.

=== Back to Constructible Numbers

Recall that we showed that if a number $alpha$ is constructible by ruler and compass, then $[QQ(alpha) : QQ] = 2^t$ for some $t >= 0$. Let $f(x)$ be any irreducible polymomial of degree 8 over $QQ$. Assume that $f(x)$ has a Galois group $S_8$. Then, $[QQ(alpha) : QQ] = 8$, but we claim $alpha$ not solvable. Under the Galois correspondance, we have the following setup then: 


#align(center)[#commutative-diagram(
  node-padding: (40pt, 40pt),
  node((0,0), $S_7$),
  node((0,2), $QQ(alpha)$),
  arr($S_7$, $QQ(alpha)$, "", "bij"),
  node((2,0), $S_8$),
  node((2,2), $QQ$),
  arr($S_8$, $QQ$, "", "bij"),
  arr($QQ$, $QQ(alpha)$, $8$),
  node((1,1), $K$),
  node((1,0), $H$),
  arr($S_8$, $H$, "2", "dashed"),
  arr($H$, $S_7$, "4", "dashed"),
  arr($QQ(alpha)$, $K$, "", "dashed"),
   arr((1,1), (2,2), [], "dashed"),
   arr($K$, $H$, "",  "bij", "dashed"),

  // node((0, 1), $V$),
  // node((0, 2), $V""$),
  // node((1, 0), $V_j$),
  // node((1, 3), $V_i$),
  // arr($V_j$, $V$, $eta_j$, "inj"),
  // arr($V$, $V""$, $T$),
  // arr($V""$, $V_i$, $pi_i$, "surj"),
  // arr($V_j$, $V_i$, $T_(i j)$),
  // // arr($M_1$, $M_2$, $T$),
  // // arr($R^n$, $M_1$, $phi_B_1$),
  // // arr($R^m$, $M_2$, $phi_B_2$, label-pos: right),
  // // arr($R^n$, $M_1$, $≀$, label-pos: right),
  // // arr($R^m$, $M_2$, $≀$, label-pos: left),
  // // arr($R^n$, $R^m$, $\ \ \ M_(T, B_1, B_2)$, label-pos: "below"),
  // // arr("quot", (0, 1), $tilde(phi)$, label-pos: right, "dashed"),
  // // arr($R$, "quot", $pi$),
)]

// Assume that $f(x)$ has precisely $6$ real roots so $"Gal"(f)$ contains an 8-cycle $(12345678)$


In particular, if $QQ(alpha)$ were constructible, then we should be able to "insert" an intermediary field $K$ such that it has a Galois group $H$ such that $S_8 supset H supset S_7$. But this is not possible:

#proposition[
  For $n >= 4$, $S_(n-1)$ is a maximal subgroup of $S_n$.
]

#proof[
  If such a subgroup existed, $H subset S_n$, then $S_n$ acts on $S_n\/H$ which implies a map $S_n ->> S_t$ for some  $t < n$.
]


This leads to an improved theorem: 

#theorem[$alpha$ is constructible by ruler and compass if and only if $QQ(alpha)$ is contained in a Galois $E\/QQ$ with $hash"Gal"(E\/QQ) = 2^t$.]


Indeed, this suggests the following theorem: 

#theorem[Every group of cardinality $p^t$ is solvable where $p$ prime.]

Indeed, such a group must have nontrivial center $Z(G)$. From here, one can proceed by induction on $G\/Z(G)$, which will now be a group of a smaller prime power.

== The Fundamental Theorem of Algebra


Using some ideas from Galois theory (and a little group theory recall), we prove the fundamental theorem of algebra: 

#theorem[$CC$ is algebraically closed.]

Recall that "algebraically closed" means that every polynomial $f in RR[x]$ splits into linear factors in $CC$. So, we equivalently prove that there are no non-trivial extensions $K$ of $CC$ over $RR$; for, supposing $f in RR[x]$ has a root $r in.not CC$, then $K = CC(r)$ an extension of $CC$. We show that no such $K$ can exist.

We'll use the following facts:
1. Every polynomial of odd degree in $RR[x]$ has a root in $RR$ (this is by the intermediate value theorem, since if such a polynomial $f$ diverges to $plus.minus infinity$ at $x -> infinity$, then $f -> minus.plus infinity$ at $x -> -infinity$ and thus must somewhere be equal to zero); thus every odd degree extension of $RR$ is _trivial_.
2. Every quadratic equation in $CC[x]$ has a root in $CC$ (just following from the quadratic formula).


#proof[
  Let $K$ be a finite extension of $CC$ and $K'$ the Galois closure of $K$ over $RR$:

  #align(center)[
// https://t.yw.je/#N4Igdg9gJgpgziAXAbVABwnAlgFyxMJZARgBoAGAXVJADcBDAGwFcYkQBpAchAF9T0mXPkIoATBWp0mrdhz4CQGbHgJEJxKQxZtEIAML6FglSPWkxWmbpAAlW8aVDVo5OVKaa22XoBij5WE1FDJPaR12ABk+KRgoAHN4IlAAMwAnCABbJHcQHAgkABYaACMYMCgkAFoAZlzGejLGAAVnMz00rHiACxwQL2t2AGUAAgAKMQA9HABKR3SspDI8gsQxflSM7MRc-KXS8srEOo2QBe2JFaQagYi9MXmtopo944OK6sKATlufEGyaA0mq1TMEQJ0en1Tucci9VjcQGUPogqgA2XLeGwAcUeix2cKQl0x7CxAH1yLjtrtVgBWd5HWr1LBgGxQCA4HBxSlIOlXNb06p1X42B6A5ms9mcyq8Si8IA
#align(center, commutative-diagram(
  node-padding: (60pt, 50pt),
  node((0, 1), [$K'$]),
  node((0, 2), [$K$]),
  node((1, 2), [$CC$]),
  node((2, 2), [$RR$]),
  node((1, 0), [$F$]),
  node((1, 1), [#text(fill: gray,$L$)]),
  arr((0, 1), (1, 0), [$S$], curve: -30deg, label-pos: right),
  arr((0, 2), (1, 2), []),
  arr((0, 1), (0, 2), [], curve: 20deg),
  arr((1, 2), (2, 2), [$2$]),
  arr((1, 0), (2, 2), [$m$], curve: -40deg, label-pos: right),
  arr((0, 1), (2, 2), [$G$], curve: -50deg),
  arr((0, 1), (1, 2), [$G_0$]),
  arr((0, 1), (1, 1), [], curve: -18deg, "dotted"),
  arr((1, 1), (1, 2), [#text(fill: gray, "2")], curve: -20deg, "dotted"),
))
  ]

Let $G$ be the Galois group of $K'$ over $RR$. Then, $hash G = 2^t m$ for some $m$ odd, so by the Sylow theorems, $G$ has a subgroup of cardinality $2^t$, call it $S$, and let $F = (K')^S$ be the corresponding field extension over $RR$. Then, $[F : RR] = m$, which is odd. By the previous remarks, $F = RR$, and thus $S$ must equal $G$ and in particular $hash G = 2^t$. 

Let $G_0 := "Gal"(K'\/CC)$, then $hash G_0 = 2^(t - 1)$. If $G_0$ is nontrivial, then it contains a subgroup $G_(00)$ of index $2$ in $G_0$. Let $L = (K')^(G_(00))$ be the corresponding field. Then, $L$ is a quadratic extension of $CC$, which doesn't exist and thus we have a contradiction, i.e. $L = CC$. Thus, it must be that $G_0$ is trivial, and hence $K' = CC$, and in particular $K = CC$.
]


== Systematic Computation of Galois Groups


Consider a polynomial $f$ in variables $x_1, dots, x_r$ over $QQ$, where $G:="Gal"(f)subset.eq S_n$. Define the _resolvent_ of $f$ as $
R(x_1, dots, x_n) := product_(sigma in S_n) (r_1 x_(sigma 1) + r_2 x_(sigma 2) + dots.c + r_n x_(sigma n)).
$ This polynomial lives in $E^G [x_1, dots, x_n] = QQ[x_1, dots, x_n]$. This polynomial factors, in $QQ[x_1, dots, x_n]$, into $
R(x_1, dots, x_n) = product_(sigma in S_n\/G) underbrace({product_(sigma in Sigma) (r_1 x_(sigma 1) + dots.c + r_n x_(sigma n))}, =: R_Sigma) = product_(Sigma in S_n\/G) R_(Sigma),
$ where $Sigma$ iterates over the cosets of $S_n\/G$. Then, there is a natural action on the set of factors ${R_Sigma}$ by left-multiplication on the indexing variable.

Moreover, this action is transitive.
 
#theorem[
  $G = "Stab"_(S_n) (R_1)$ where $R_1 = R_(G)$ with $G$ being thought of as a coset in $S_n\/G$.
]
#proof[
If $tau in G$, then by changing indexing variable, $
tau dot R_G &= product_(sigma in G) (r_1 x_(tau sigma 1) + dots.c + r_n x_(tau sigma n)) \ 
&= product_(tau sigma in G) (r_1 x_(tau sigma 1) + dots.c + r_n x_(tau sigma n))\
&= product_(sigma in tau^(-1) G) (r_1 x_(tau sigma 1) + dots.c + r_n x_(tau sigma n))\
&= R_G,
$ since $tau^(-1) G = G$ as $tau in G$ itself. So, $G subset "Stab"_(S_n) (R_1)$. Moreover, by orbit-stabilizer, $
hash "Stab"_(S_n) (R_1) = (hash S_n)/(hash"Orb"(R_1)).
$ But since the action transitive, $hash"Orb"(R_1)=$ number of factors of $R$ $=$ size of $S_n\/G$ $ = hash S_n\/ hash G$. Thus, $hash"Stab"_(S_n)(R_1) = hash G$ from which we conclude $"Stab"_(S_n)(R_1) = G$ indeed.
// We may write $
// R(x_1, dots, x_n) = product_(Sigma in S_n\/G) (product_(sigma in Sigma) (underbrace(r_1 x_(sigma 1) + dots.c r_n x_(sigma n), #stack(spacing: .8em,[irreducible over $QQ$]))),
// $ and the stabilizer of $R_1$ is $G$.
]

There are more efficient ways, particularly over finite field. Suppose $f(x) in FF_p [x]$. Then, recall that $x^p - x$ has as factors every element in $FF_p$. Then, $
"gcd"(f(x), x^p - x) = product_(f(r) = 0) (x - r).
$ This still isn't necessarily easy, but one can begin by rewriting $x^p -x$  mod $f(x)$; one begins by writing $x^p = x(x^((p-1)/2))^2$ mod $f(x)$. Then, one proceeds by computing via the Euclidean algorithm, which will be on the order of about $log(p)$ (?).

Given some $f in QQ[x]$, then, one can, through manipulation, place $f in ZZ[x]$ (by clearing denominators, etc). Then, one can consider $f mod p in ZZ\/p ZZ[x]$ for various $p$ to study its roots using the above algorithm.

== "The Converse Problem of Galois Theory"

One natural converse to our work above is whether given a group $G$, does there exist an extension $E\/QQ$ with $"Gal"(E\/QQ) = G$? This is still very much open, but the following holds:

#theorem[For any finite group $G$, there exists $E\/F$ with $[F : QQ] < infinity$ with $"Gal"(E\/F) = G$.]

The idea is to:

1. Embed $G subset S_n$ (Lagrange), and suppose wlog $n$ prime.
2. We see $E\/QQ$ is an extension with Galois group $S_n$.
3. Let $F = E^G$, then by Galois correspondance $"Gal"(E\/F) = G$.



// then look at $QQ(x_1. dots, x_n)^G$, where $x_1, dots, x_n$ are indeterminates. For instance, it turns out $QQ(x_1, dots, x_n)^(S_n) = QQ(sigma_1, dots, sigma_n)$, where $sigma_i$ enumerate the elementary symmetry polynomials in $x_j$'s. The latt

= Final Exercises

#proposition[
  Let $f(x)$ be an irreducible polynomial over $F$ and assume that $f(x)\/(x-r)$ remains irreducible over $F(r)$ where $r$ is a root of $f(x)$. Show that the Galois group of $f(x)$ over $F$ acts doubly transitively on the set of roots of $f$.
]

#proof[
  Denote by $E$ the splitting field of $f$ over $F$. Since $f(x)\/(x-r)$ remains irreducible in $F(r)$, $E$ is also the splitting field of $f(x)\/(x-r)$ over $F(r)$. Let $r_1 eq.not r_3, r_2 eq.not r_4$ be four roots of $f(x)$ in $E\/F$. Since $"Gal"(f(x)\/(x-r))$ acts transitively on the set of roots minus $r$ of $f$, pick $phi in "Gal"(f(x)\/(x-r))$ // TODO :(
]

#proposition[
  Suppose that $f(x)$ is a polynomial of degree $n$ over $F=QQ$ satisfying the hypotheses in Q1, and assume that $f(x)$ has exactly $n-2$ real roots. Show that the Galois group of $f(x)$ is equal to $S_n$. 
]

#proof[
  The existence of a pair of complex conjugate roots means there is a transposition in $G = "Gal"(f)$. $G$ then a doubly-transitive subgroup of $S_n$ containing a transposition, which we assume wlog is $(r_1 r_2)$ acting on the set of roots of $f$. For any two roots $r_3 eq.not r_4$, pick $phi in G$ such that $phi(r_3) = r_1, phi(r_4) = r_2$, appealing to double-transitivity. Then, $
  (phi^(-1) compose (r_1 r_2) compose phi) (r_k) = cases(r_4 & "if" k = 3, r_3 & "if" k = 4, r_k & "o.w."),
  $ hence $phi^(-1) compose (r_1 r_2) compose phi = (r_3 r_4)$. In this manner, we can generate every transposition in $G$, hence since such elements generate $S_n$, we conclude $G = S_n$.
]

#proposition[
   Let $G$ be a finite group. Show that there exists fields $E supset F$ for which $"Gal"(E\/F)$ is isomorphic to $G$.
]

#proof[
  Let $n$ be such that $G subset S_n$, appealing to Lagrange; assume wlog $n$ is prime. Then, let $f(x) in QQ[x]$ be an irreducible polynomial with exactly 2 complex roots and $n-2$ real roots. Let $E$ be the splitting field of $f(x)$ over $QQ$. Then, we claim $H := "Gal"(E\/QQ) = S_n$. 

  First, $H$ acts transitively on the set of $n$ roots of $f(x)$ so $n|hash H$. By Sylow, there is a copy of $ZZ\/n ZZ subset H$, hence an $n$-cycle, in $H$, WLOG $(1 2 dots n)$.

  Then, since there is a complex conjugate pair of roots of $f$, complex conjugation i.e. a transposition exists in $H$, call it $(a b)$.

  Since $n$ prime, $(a b)$, $(1 2 dots n)$ generate $S_n$ thus $H = S_n$. Namely, this isn't true for general $n$, but what is true for general $n$ is $(12), (12 dots n)$ generates $S_n$. However, if we let $sigma := (12dots n)$ and $k$ such that $sigma^k (a) = b$, then since $n$ prime, $sigma^k$ still an $n$-cycle, and so if we relabel $a <-> 1$ and $b <-> 2$, then in this relabelling $(a b) <-> (1 2)$ and $sigma^k <-> (1 2 dots n)$ which together generate $S_n$.

  Finally, let $F = E^G$. By the Galois correspondance, $"Gal"(E\/F) = G$.
]

#proposition[Let $p$ be a prime and let $f(x)$ be a polynomial of degree $p+1$ over a field $F$, whose galois group is isomorphic to the group $"PGL"_2 (FF_p)$. Show that the splitting field of $f(x)$ over $F$ is generated over $F$ by any three of its roots $r_1, r_2, r_3$. Show that $f(x)\/(x-r_1)$ is irreducible over $F(r_1)$ and $f(x)\/(x-r_1)(x-r_2)$ is irreducible over $F(r_1, r_2)$.]

#proposition[List all the subfields of the field $QQ(zeta)$ generated by a primitive $8$th root of unity.]

#proof[
  // TODO must be at least four since certainly contains at least 2 quadratic subfields QQ[sqrt(2)], QQ[i].
  Let $G = "Gal"(QQ(zeta)\/QQ)$ (which is galois being the splitting field of $x^4 +1$).
  There are 4 primitive 8th roots of unity, $plus.minus sqrt(2)/2 plus.minus sqrt(2)/2 i$, just label $zeta = sqrt(2)/2 + sqrt(2)/2 i$. Any homomorphism $phi in G$ is determined by $phi$ and moreover must map $phi$ to another primitive 8th root of unity, so one of either $zeta, - zeta, overline(zeta), - overline(zeta)$; viewing $phi$ as a permutation on ${zeta, - zeta, overline(zeta), - overline(zeta)}$, we readily find: #align(center, table(
    stroke: none,
    inset: .5em,
    columns: 2,
    $zeta |-> zeta$, $()$,
    $zeta |-> -zeta$, $(1 2)(3 4)$,
    $zeta |-> overline(zeta)$, $(1 3) (2 4)$,
    $zeta |-> - overline(zeta)$, $(1 4)(2 3)$
  )) From here we see $G tilde.eq ZZ\/2 times ZZ\/2$, which has four subgroups, the identity and three copies of $ZZ\/2$: $
  H_1 := angle.l (12)(34) angle.r &arrow.squiggly.long "fixes" i  wide ("since" i = zeta^2 |-> (-zeta)^2 = zeta^2 = i)\
   H_2 := angle.l (13)(24) angle.r &arrow.squiggly.long "fixes" zeta + overline(zeta) = sqrt(2)\
    H_3 := angle.l (14)(23) angle.r &arrow.squiggly.long "fixes" sqrt(2)i wide ("since" sqrt(2)i = zeta - overline(zeta) |-> - overline(zeta) + zeta = sqrt(2) i)\
    H_4 := 1 &arrow.squiggly.long "fixes" QQ
  $
  Appealing to the galois correspondance, we find the following subfield correspondance: 
  #table(columns: 3,
  align: horizon,
  stroke: none,
    commutative-diagram(
    node-padding: (35pt, 35pt),
      node((2,0), $G$),
      node((1,-1), $H_1$),
      node((1,0), $H_2$),
      node((1,1), $H_3$),
      node((0,0), $H_4$),
      arr((0,0),(1,-1), $2$),
      arr((0,0),(1,0), $2$),
      arr((0,0),(1,1), $2$),
      arr((1,-1),(2,0), $2$),
      arr((1,0),(2,0), $2$),
      arr((1,1),(2,0), $2$),
    ),
    $arrow.squiggly.long$,
    commutative-diagram(
      node-padding: (35pt, 35pt),
        node((2,0), $QQ$),
        node((1,-1), $QQ (i)$),
        node((1,0), $QQ (sqrt(2))$),
        node((1,1), $QQ (sqrt(2) i)$),
        node((0,0), $QQ (zeta)$),
        arr((0,0),(1,-1), $2$),
        arr((0,0),(1,0), $2$),
        arr((0,0),(1,1), $2$),
        arr((1,-1),(2,0), $2$),
        arr((1,0),(2,0), $2$),
        arr((1,1),(2,0), $2$)
    )
    )
    In summary, the five distinct subfields of $QQ(zeta)$ are itself, $QQ(i), QQ(sqrt(2)), QQ(sqrt(2) i), QQ$. Note that there are no further subfields of $QQ$ since $QQ$ generated by $1$.

    _One can approach this differently by using the (unproven in this class) fact that $"Gal"(QQ(zeta_n)\/QQ) = (ZZ\/n ZZ)^times$ where $zeta_n$ a primitive $n$th root of unity. In this case, this idenfication is clear through association of exponent of $zeta$ with element of $(ZZ\/8 ZZ)^times$. I personally prefer my approach..._ 
]

#proposition[Show that the extension $QQ(sqrt(2+sqrt(2)))$ is Galois over $QQ$, and compute its Galois group.]

#proof[

  Let $f(x) = (x^2 - 2)^2 - 2 = x^4 - 4 x^2 + 2 in QQ[x]$. Letting $r_1 := sqrt(2 + sqrt(2))$, $r_2 := - r_1$, $r_3 := sqrt(2 - sqrt(2))$ and $r_4 := - r_3$ enumerates the roots of $f$. Then, certainly $QQ(r_1, r_3)\/QQ$ the splitting field of $f$ and $QQ(r_1) subset QQ(r_1, r_3)$. We claim this is an equality, namely that $r_3 in QQ(r_1)$. Indeed, notice that $
  r_1 r_3 = sqrt((2 + sqrt(2))(2 - sqrt(2))) = sqrt(2), 
  $  and $sqrt(2) in QQ(r_1)$ since $r_1^2 - 2 = sqrt(2)$. Thus, $r_3 = sqrt(2) dot r_1^(-1) in QQ(r_1)$. Thus, $QQ(r_1) = QQ[x]\/(f(x))$ so is Galois over $QQ$. 
  
  Moreover, since $f$ of degree 4, $[QQ(r_1) : QQ] = 4$, so we have two options for the Galois group. Consider the map $r_1 |-> r_3$. One verifies that this is a 4-cycle acting on the roots of $f$, from which it follows that $"Gal"(QQ(r_1)\/QQ) = ZZ\/4ZZ$.


  _Note that, more generally, if $QQ(sqrt(d))$ a quadratic extension of $QQ$ and we adjoin additional elements $sqrt(a + b sqrt(d)),sqrt(a - b sqrt(d))$, that we have the relation $sqrt(a + b sqrt(d))dot sqrt(a - b sqrt(d)) = sqrt(a^2 - b^2 d)$ so if in particular $a^2 - b^2 d$ a perfect square in $QQ$ or $QQ(sqrt(d))$, then we are in a similar situation to the above._

  
  // Consider the tower #align(center,
  // commutative-diagram(
  //   node-padding: (30pt, 30pt),
  //   node((0,0), $QQ(r_1, r_3)$),
  //   node((1,0), $QQ(r_1)$),
  //   node((2,0), $QQ$),
  //   arr((1,0), (0,0), ""),
  //   arr((2,0), (1,0), "")
  // )
  // ) Note that $QQ(r_1, r_3)\/QQ$ the splitting field of $f$. Consider $G := "Gal"(QQ(r_1, r_3)\/QQ)$. $phi in G$ is determined by $phi(r_1), phi(r_3)$, and each of these must be sent to a root of $f$ so one of $r_1, dots, r_4$. Not all of these are admissible; viewing such homomorphisms as elements of $S_4$ acting on ${r_1, dots, r_4}$, we readily find the following table:

  // #align(center, table(
  //   columns: 5,
  //   stroke: none,
  //   inset: 0.35em,
  //   align: center,
  //   "", $r_3 |-> r_1$, $r_3 |-> r_2$, $r_3 |-> r_3$, $r_3 |-> r_4$,
  //   table.hline(start: 0, end: 5),
  //   table.vline(start:0, end: 5, x: 1),
  //   $r_1 |-> r_1$, box(fill: black, height: 1em, width: 3em), box(fill: black, height: 1em, width: 3em), $()$, $(3 4)$,
  //   $r_1 |-> r_2$, box(fill: black, height: 1em, width: 3em), box(fill: black, height: 1em, width: 3em), $(1 2)$, $(12)(34)$,
  //   $r_1 |-> r_3$, $(13)(24)$, $(1324)$, box(fill: black, height: 1em, width: 3em),box(fill: black, height: 1em, width: 3em),
  //   $r_1 |-> r_4$, $(1423)$, $(14)(23)$, box(fill: black, height: 1em, width: 3em),box(fill: black, height: 1em, width: 3em)
  // )
  // ) From this, we see that $G = D_8$. Then, $H := "Gal"(QQ(r_1, r_3)\/QQ(r_1)) subset G$ is the subgroup that fixes $QQ(r_1)$ i.e. fixes $r_1, r_2$. We see that the only elements that do this are $(), (34)$ so $H = {(), (34)} tilde.eq ZZ\/2$.

  // $G = D_8, H = "Gal"(QQ(r_1, r_3)\/QQ(r_1)) = ZZ\/2 times ZZ\/2 triangle.l G$ so $N := "Gal"(QQ(r_1)\/QQ) = G\/H = ZZ\/2ZZ$. The only automorphisms are determined by $r_1 |-> r_1, r_1 |-> - r_1$.
]


#proposition[
  Show that the symmetric group $S_(12)$ contains subgroups of cardinality 31104 and 82994 (Hint: $31104 = (3!)^4 dot 4!$ and $82294 = (4!)^3 dot 3!$). Explain how you might try to go about constructing degree 12 polynomials with those Galois groups.
]

#proof[
  Let $H_1$ be the subgroup of $S_12$ consisting of $S_3 times S_3 times S_3 times S_3$ (acting disjointly on $1,2, 3; 4, 5, 6;$ etc) times $S_4$, with $S_4$ acting on ${1, 2, 3}, {4, 5, 6}, {7, 8, 9}, {10, 11, 12}$ by identifying $1 <-> 4 <-> 7 <-> 10$ etc. (namely, if $1 |-> 4$ then $2 |-> 5$ and $3 |-> 6$ etc) (??). Then, $hash H_1 = (hash S_3)^4 dot hash S_4 = (3!)^4 4!$. Similarly, let $H_2$ be the same construction interchanging $S_4$ with $S_3$ wherever they appear.

  To try to construct degree polynomials with such Galois groups, we can appeal to the method of question 3 by beginning with an irreducible polynomial of degree 12 over $QQ$ with Galois group equal to $S_12$ (which may be hard to do who knows), let $E\/QQ$ be its splitting field, and let $F = E^(H_i)$. Then, $F$ Galois over $E$ with Galois group $H_i$. By Proposition 3.3, every (finite degree) Galois extension is a splitting field, so there is some polymomial $g(x) in F[x]$ with Galois group $H_i$.
]

#remark[
  The following questions are all connected, aimed at culminating with the final proposition.
]

#proposition[
  Let $G$ be a transitive subgroup of the symmetric group $S_n$ on $n$ letters, and let $H$ be a normal subgroup of $G$. Show that the action of $G$ on the set $X := {1, dots, n}$ induces a natural action of $G$ on the set $X_H := {H x : x in X}$ of sets of $X$ consisting of the orbits for $H$ in $X$. Use this to conclude that all the $H$-orbits in $X$ have the same cardinality. Give an example to illustrate the failure of this conclusion when $H$ is not assumed to be normal in $G$.
]

#proof[
  Define the action $ast$ on $X_H$ by $
  g ast H x = g H x = H (g x),
  $  the second equality following from normalcy ie $g H = H g$ for every $g in G$. This is a group action; the composition axioms are clear. Moreover, we need to show it is well-defined, ie the definition is independent of choice of orbit representative $x$. Suppose $H x = H y$. Then, $y in H x$ so there is some $h in H$ such that $y = h x$. Then, on the one hand, $
  g ast H x = H (g x),
  $ while also $
  g ast H y = g ast H (h x) = H (g h x).
  $ By normalcy, $g h g^(-1) = tilde(h) in H$ so $
  H (g h x) = H tilde(h) g x = H (g x),
  $ so this indeed well-defined. Thus, we conclude $hash H x = hash H y$ for any $x, y in X$ since by transitivity of $G$ there is some $g in G$ such that $g x = y$ so $g H x = H y$ hence $hash H x = hash H y$.

  For a counterexample when $H$ not assumed to be normal, we have that $D_8$ a transitive subgroup of $S_4$ and $H:= angle.l (13) angle.r$ a (not normal) subgroup of $D_8$ (viewed as "D1" reflection), while $H dot 1 = {1, 3}$ and $H dot 2 = {2}$.
  
  // TODO something is not right above... at least i'm not sure. Does this imply the action is necessarily transitive?
  // Then, $1 ast H x = H x$, and for $g, h in G$, $
  // (g h) ast H x = H (g h x)   = g ast (h ast H x),
  // $ so this a well-defined group action. Moreover, it is transitive, since given orbits $H x$ and $H y$, since $G$ transitive acting on $X$ there is a $g in G$ such that $g x= y$ hence $g^(-1) x = y$, so $
  // g ast H x = H  g^(-1)x
  // $
]

#proposition[Let $p$ be a prime number. Show that any non-trivial normal subgroup of a transitive subgroup of $S_p$ also acts transitively on ${1, dots, p}$.]

#proof[
We have $X = union.big.sq_(H x in X_H) H x$, and since by the previous question each $H x$ has the same cardinality, $
p = hash X = hash X_H dot hash (H dot 1),
$ which since $p$ prime would imply either $hash X_H = p$ or $1$. In the former case, this implies $hash (H dot x) = 1$ for every $x in X$ which is only possible if $H$ trivial, so we must be the latter case, in which case $hash (H x) = p$ so in particular the orbit $H x$ is all of $X$ so $H$ acts transitively on $X$ as well.
]

#proposition[
  Show that any transitive subgroup of $S_p$ contains a non-trivial Sylow $p$ subgroup of cardinality $p$.
]

#proof[
Let $G$ be such a subgroup. By transitivity and orbit-stabilizer, we know $hash G = hash X dot hash "Stab"_G (1) = m p$ so $p|hash G$. Moreover, $hash G|p!$ since $G subset S_p$, so we may write $hash G = p dot t$ where $p divides.not t$, i.e. the highest power of $p$ in $hash G$ is 1. By Sylow theorems, there is a Sylow $p$-subgroup of cardinality $p$ in $G$.
]

#proposition[
  Let $G$ be a transitive subgroup of $S_p$ and let $H$ be a non-trivial normal subgroup of $G$. Show that any Sylow $p$-subgroup of $G$ is also contained in $H$.
]

#proof[
  By 4.9, $H$ also transitive so by 4.10 there is certainly _a_ Sylow $p$-subgroup in $H$, call it $P$. This must also be then a Sylow $p$-subgroup of $G$. By the second Sylow theorem, any two Sylow $p$ sub-groups are conjugate, so for any other Sylow $p$-subgroup $P_1 subset G$, $P_1 = g P g^(-1)$ for some $g in G$. But since $H$ normal in $G$, $g P g^(-1)$ remains in $H$ so $P_1 subset H$ as well, thus any Sylow $p$-subgroup of $G$ is also a subgroup of $H$.
]

#proposition[
  Show that any transitive solvable subgroup of $S_p$ contains a _unique_ Sylow $p$ subgroup, and hence is contained in the normalizer of its Sylow $p$-subgroup.
]

#proof[
Write ${1} = G_0 triangle.l G_1 triangle.l dots.c triangle.l G_t = G subset S_p$. Since $G$ transitive and $G_(t-1) triangle.l G$, by 4.9, $G_(t-1)$ itself transitive. Then, $G_(t - 2)$ is a normal subgroup of $G_(t-1)$ so $G_(t-2)$ also transitive, etc, thus each $G_(i)$ transitive, being a normal subgroup of a transitive subgroup of $S_p$. Then, by 4.11, any Sylow $p$-subgroup of $G$ is contained in $G_(t-1)$, and thus arguing inductively we find that any Sylow $p$-subgroup of $G$ contained in $G_(i)$. In particular, any subgroup Sylow $p$-subgroup is contained in $G_1$, but by solvability $G_1$ abelian. So, since any two Sylow $p$-subgroups $P_1, P_2$ are conjugate ie $P_1 = g P_2 g^(-1)$ for some $g in G$, and since both $P_1, P_2 subset G_1$, it must be that $P_1 = P_2$ since $g P_2 g^(-1) = g g^(-1) P_2 = P_2$ (with the multiplication occuring in $G_1$ now). Thus, we conclude that there is only one such Sylow-$p$ subgroup in the top level $G$.

Hence, $G subset N(P)$ (in $S_p$). // TODO I think thats what they mean.
// by the previous question every Sylow-$p$ subgroup of $G$ is also contained in $G_(t-1)$. Then, since $G_(t - 1)$ normal in $G$ and $G$ transitive,

]

#proposition[
  After identifying $X := {1, dots, p}$ with $ZZ\/p ZZ$, show that the normalizer of the Sylow $p$-subgroup generated by the cyclic permutation $T : x |-> x + 1$ is the group of affine linear transformations of the form $x |-> a x + b$ with $a in (ZZ\/p ZZ)^times$ and $b in ZZ\/p ZZ$.
]

#proof[
Let $P = angle.l T angle.r$ be the relevant Sylow $p$-subgroup. Let $sigma in N(P)$, so by assumption there is an $a in X$ such that $sigma T sigma^(-1) = T^a$ ($T^a = T compose dots.c compose T$). Then, for any $x in X$, $(sigma T) x = (T^a sigma) x$; the LHS becomes $
sigma (x + 1),
$ while the RHS becomes $
sigma(x) + a,
$ so in short $
sigma(x + 1) = sigma(x) + a,
$ for any $x in X$. Let $b := sigma(0)$, then $
sigma(1) &= b + a\
 sigma(2) &=  sigma(1) + a + a = b  + 2 a\
 &dots.down\
 sigma(x) &= a x +  b,
$ with the final form following by induction if you like. Thus, $sigma$ indeed acts as an affine linear transformation, noting that $a, b$ were dependent only on $sigma$, and that it suffices to look at $sigma T$ since $T$ generates $P$. 

Precisely, this says $N(P)$ is contained in the group of affine linear transformations, so one need show the converse inclusion. This is clear enough.
]

#proposition[
  Show that any transitive solvable subgroup of $S_p$ is conjugate to a subgroup of the group of affine linear transformations of cardinality $p(p-1)$ described in 4.13.
]

#proof[
By 4.12, there is a unique sylow $tilde(P)$ subgroup in $G$ and that $G subset tilde(N):= N(tilde(P))$ in $S_p$. With $P$ the sylow $p$-subgroup from 4.13, we know $tilde(P) = g P g^(-1)$ for some $g in S_p$. I claim the normalizers are $tilde(N), N := N(P)$ are also conjugate by $g$. Let $sigma in N$ and $tilde(h) in tilde(P)$, so $g sigma g^(-1) in g N g^(-1)$ and also there is an $h in P$ such that $tilde(h) = g h g$. Then, $
(g sigma g^(-1)) tilde(h) (g sigma g^(-1))^(-1) &= g sigma g^(-1) g h g g sigma^(-1) g^(-1) = g sigma h sigma^(-1) g^(-1).
$ Since $sigma in N$, $sigma h sigma^(-1) in P$ and thus $g sigma h sigma^(-1) g^(-1) in tilde(P)$. So in short, $g sigma g^(-1) in tilde(N)$ indeed thus $g N g^(-1) subset tilde(N)$. A similar computation shows the other inclusion. Thus, $G$ a subgroup of $tilde(N) = g N g^(-1)$ i.e. is conjugate to a subgroup of $N = {a x + b | a in (ZZ\/p ZZ)^times, b in ZZ\/p ZZ}$, as we aimed to show.
]

#proposition[
  Prove the theorem of Galois, quote #quote[
    _an irreducible polynomial $f$ of prime degree $p$ is solvable by radicals if and only if the splitting field of $f$ is generated by any two roots of $f$._
    ]
]

#proof[
$(=>)$ The main theorem of Galois theory tells us that under these hypotheses, $G:="Gal"(f)$ is solvable. Moreover, since $deg(f) = p$ prime, $G subset S_p$. $G$ acts transitively on the $p$-sized set of roots of $f$, so $G$ a transitive solvable subgroup of $S_p$, so by 4.14, is conjugate to a subgroup of $N$. Let $r_1, r_2$ be any two distinct roots of $f$ and let $H = "Gal"(E\/F(r_1, r_2))$ where $E$ the splitting field of $E$ over $F$. Then, this group also conjugate to a subgroup of $N$, which fixes two elements $r_1, r_2$. I claim $H$ must be trivial. A typical element of $H$ can be realized as an affine linear action (up to conjugation, but whatever) $sigma : x |-> a x + b$. $sigma r_1 = r_1, sigma r_2 = r_2$ so thus $
a r_1 + b = r_1, wide a r_2 + b = r_2.
$ This gives a system of linear equations.Canceling $b$, we find $
r_1 (1 - a) = r_2 (1 - a).
$ Here we have two cases: if $a = 1$, then $b$ must equal zero so we have the trivial element which must be in $H$ anyways. Else, $1 - a$ is invertible hence $r_1 = r_2$, a contradiction to the distinctness of the roots. Thus, the only possibility is $H = {1}$ i.e. $"Gal"(E\/F(r_1, r_2)) = {1}$, which is only possible if $E = F(r_1, r_2)$, as we aimed to show.

($impliedby$) Now $F(r_1, r_2)\/F$ the splitting field of $f$, and still $G := "Gal"(f)$ a transitive subgroup of $S_p$. It suffices to show that $G$ is solvable.

 By general theory $[F(r_1, r_2) : F] <= p (p -1)$ since it arises from $F$ from the adjoinment of two roots of $f$, hence $hash G <= p (p - 1)$. By transitivity, $p | hash G$, so thus $G$ has a sylow $p$-subgroup, and moreover it must be unique by the bound on the cardinality of $G$. So, $G subset N(P)$, the normalizer of its sylow $p$-subgroup in $S_p$; namely, $P$ is normal in $G$. By the previous questions, then, $G$ conjugate to a subgroup of the affine linear subgroup, call it $N$, of cardinality $p(p-1)$ in $S_p$, the normalizer of $P_p := angle.l (12dots.c p) angle.r$ in $S_p$. Then, remark that $
 N\/P_p tilde.eq (ZZ\/p ZZ)^times,
 $ and thus $G\/P$ conjugate to a subgroup of $(ZZ\/p ZZ)^times$, and is thus abelian. Hence, we have a chain $1 triangle.l P triangle.l G$ with $G\/P$ abelian and $P tilde.eq ZZ\/p ZZ$ abelian, thus $G$ solvable, from which it follows $f$ solvable by radicals.
]


#remark[Everything that appears after this is just miscellanea.]

#proposition[Compute the sum $
1 - 1/2 + 1/4 - 1/5 + 1/7 - 1/8 + dots.c = sum_(n=1)^infinity a_n/n,
$ where $a_n := cases(
  0 & "if" 3|n,
  1 & "if" n = 1 + 3 k,
  -1 & "if" n = -1 + 3 k
)$.]

#proof[
  Notice that $a_n$ can be viewed as a function $ZZ\/3ZZ -> CC$. The space of such functions is spanned by the set of irreducible characters of $ZZ\/3ZZ$; since this group abelian (and moreover cyclic), its irreducible characters are given by $
  chi_(k) (n) := e^(2pi i n k\/3) = zeta^(n k), wide k = 0, 1, 2; n in ZZ\/3ZZ,
  $ and $zeta := e^(2pi i\/3)$ a primitive third root of unity. Then, we should be able to find complex scalars $lambda_0, lambda_1, lambda_2$ such that $
  a_n = lambda_0 chi_0 (n) + lambda_1 chi_1 (n) + lambda_2 chi_2 (n).
  $ Taking inner products of both sides wrt $chi_k$ for each $k$ yields $
  lambda_k = (a_n, chi_k) &=1/3 (a_0 chi_k (0) + a_1 chi_k (1) + a_2 chi_k (2)) = (zeta^k - zeta^(-k))/2,
  $ so in particular, $
  lambda_0 &= 0\
  lambda_1 &=( zeta - zeta^(-1))/3\
  lambda_2 &= (zeta^2 - zeta^(-2))/3 = - lambda_1.
  $ Hence, we find $
  sum_(n=1)^infinity a_n/n &=lambda_1 [sum_(n=1)^infinity ((zeta)^n)/n - sum_(n=1)^infinity ((zeta^(2))^n)/n]\
  &= lambda_1 [- log(1 - zeta) + log(1 - zeta^2)] \ 
  &= lambda_1 [log((1 - zeta^2)/(1 - zeta))] \
  &= lambda_1 log(1 + zeta) \ 
  &= lambda_1 log(-zeta^(-1))\
  &= lambda_1 [log(-1) + log(e^(4 pi i\/3))]\
  &= lambda_1 [i pi + 4 pi i\/3]\
  &= lambda_1 dot 7/3 pi i \
  &= 7\/9 dot pi i [zeta - zeta^(-1)]\
  &= 7\/9 dot pi i dot i sqrt(3) = - (7sqrt(3))/9.
  $ We used above that:
  - $- log(1 - x) = sum_(n=1)^infinity x^n/n$
  - $zeta = e^(2 pi i \/3) = 1/2 + (i sqrt(3))/2$.

  #text(fill: red, "I did this myself, I don't know if its fully correct. The logic is right at the very least.")
]
