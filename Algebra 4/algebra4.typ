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
  Hom_G (V_j, V) = CC^(m_)j.
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
  g = mat([rho_V (g)], 0; 0, [rho_W(g)]),
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
&= 1/(hash G) hash G chi_j (id) = chi_j (id) = d_j,
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

$chi_1$ is the trivial representation. $chi_2$ is the sign representation given by $sigma |-> "sgn"(sigma) in {-1, 1} subset.eq CC^x$. $chi_3$ comes from noticing that $K_4 = ZZ\/2 times ZZ\/2 = 1A union.sq 2A subset.eq S_4$ gives $S_4\/K_4 tilde.eq S_3$. We then can find a new representation by composing the quotient map $pi : S_4 -> S_3$ with a representation $rho : S_3 -> "Aut"_CC (V)$. Remember that there are three irreducible representations of $S_3$. The first two are the trivial and sign, already accounted for here. The last is the unique two-dimensional representation where $chi(2A) = 0$ and $chi(3A) = -1$ (these are the conjugacy classes in $S_3$ now). Under the quotient map, then, we find that
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
psi : H -> CC^x
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
$ Then, $
T e^(2 pi i j x\/N) &= 1/2 (e^(2 pi i j (x + 1) \/N ) + e^(2 pi i j (x - 1) \/N )) \ 
&= 1/2 (e^(2 pi i j\/N) + e^(- 2 pi i j\/N)) e^(2 pi i j x \/N) \
&= cos(2 pi j\/N) e^(2 pi i j x \/N).
$ Then, we may write $f = hat(f)(0) f_0 + hat(f)(1)f_1 + dots.c + hat(f)(N-1) f_(N-1)$, so $
T f = hat(f)(0) f_0 + hat(f)(1) cos((2 pi)/N) f_1 + dots.c + hat(f)(N-1) cos((2 pi (N-1))/N) f_(N-1),
$ and hence $
hat(T f) (j) = hat(f)(j) cos((2 pi j)/N).
$ Thus, $
hat(T^M f(j)) = hat(f)(j) (cos ((2 pi)/N))^M.
$

=== Functions on Mathematical Objects with Symmetry Groups

Let $X$ a "mathematical object", $G$ a group of symmetries and $V = L^2 (X) =  CC$-valued functions on $X$. We assume $X$ finite (hence $G$ finite and $V$ finite). We are interested in studying operators $T : L^2 (X) -> L^2 (X)$.

Suppose $X$ a set of vertices of a graph; define for $phi in L^2 (X)$, $(T phi)(x) = sum_((y, x) "an edge") phi(y)$; $T$ the adjacent operator, extended to functions on $CC$. We claim $T$ commutes with the action of $G$; write $y tilde x$ if the vertex $y$ adjacent to the vertex $x$:
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
T(psi)(x) = 1/4 sum_(y tilde x) phi(y),
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

This space already contains constant function, so we want to consider the complementary space; $
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

#proposition[
  Let $D_8$ be the dihedral group of order 8 and $Q$ the quaternion group. Show that the group rings $CC[D_8]$ and $CC[Q]$ are isomorphic, while the group rings $RR[D_8]$ and $RR[Q]$ are not.
]

#proof[
  We know that $
  CC[D_8] tilde.eq plus.circle.big_(j=1)^5 "End"_CC (V_j) tilde.eq plus.circle.big_(j=1)^5 "M"_(d_j) (CC),
  $ with similar for $CC[Q]$. But recall that $D_8$ and $Q$ have "identical" character tables, namely they have the same number of irreducible complex representations with the same distribution of dimensions, hence it follows by this characterization that the group rings are isomorphic.
]

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
  There are 4 irreducible representations of dimension 1, and a unique (faithful) irreducible representation of dimension 2 (the first four can be found by modding out the center of $Q$ which gives a homomorphism to $ZZ\/2ZZ times ZZ\/2$; the last can be found by just computing orthogonality relations).

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
  extension of $F$ if $F$ is a subfield of $E$.
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
  2. $p(x) = x^3 + 3 x + 1/2$ has root $r = cos ((2 pi )/9)$ ("trisection of the angle").
]