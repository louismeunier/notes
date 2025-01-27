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
  Let $pi = 1/(hash g) sum_(g in G) rho(g)$. Then, notice that $im (pi) = V^G$ and $pi^2 = pi$ hence a projection from $V$ onto $V^G$. Using the previous proposition and linearity of the trace completes the proof.
]

== Characters

#definition[
  Let $dim (V) < infinity$ and $G$ a group. The _character_ of $V$ is the function $
  chi_V : G -> CC, wide chi_V (g) := tr(rho(g)).
  $
]

#proposition[Characters are class functions, namely constant on conjugacy classes.]

#theorem[If $V_1, V_2$ are 2 representations of $G$, then $V_1 tilde.eq_G V_2 <=> chi_(V_1) = chi_(V_2)$.]

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
  Hom_G (V_j, V) = CC^m_j.
  $
]

#proof[
"$Hom$ is linear with respect to $plus.circle$".
]

#proposition[
  If $V, W$ are two representations, then so is $V plus.circle W$ with point-wise action, and $chi_(V plus.circle W) = chi_V + chi_W$.
]

#theorem[
  $chi_(Hom(V, W)) = overline(chi_V) chi_W$.
]
#proof[
  Use an eigenbasis for $V, W$ respectively to define a corresponding eigenbasis for $Hom(V, W)$ such as to write any $g in G$ as a diagonal matrix. The entries will contain an expression depending solely on the eigenvalues for $g$ acting on $V, W$.
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
  $ collecting all the irreducible representation homomorphisms into a single vector. Then, this extends naturally by linearity to a ring homomorphism $
  underline(rho) : CC[G] -> "End"_CC (V_1) plus.circle dots.c plus.circle "End"_CC (V_t).
  $ By picking bases for each $"End"_CC (V_j)$, we find that $dim_CC ("End"_CC (V_j)) = d_j^2$ hence $dim_CC ("End"_CC (V_1) plus.circle dots.c plus.circle "End"_CC (V_t)) = d_1^2 + dots.c + d_t^2 = hash G$, as we saw in the previous theorem. On the other hand, $dim_CC (CC[G]) = hash G$ hence the dimensions of the two sides are equal. We claim that $underline(rho)$ an isomorphism of rings. By dimensionality as $CC$-vector spaces, it suffices to show $underline(rho)$ injective.

  Let $theta in ker(underline(rho))$. Then, $rho_j (theta) = 0$ for each $j = 1, dots, t$, i.e. $theta$ acts as 0 on each of the irreducibles $V_1, dots, V_t$. Applying Maschke's, it follows that $theta$ must act as zero on every representation, in particular on $CC[G]$. Then, for every $sum beta_g g in CC[G]$, $theta dot (sum beta_g g) = 0$ so in particular $theta dot 1 = 0$ hence $theta = 0$ in $CC[G]$. Thus, $underline(rho)$ has trivial kernel as we wanted to show and thus $CC[G]$ and $"End"_CC (V_1) plus.circle dots.c plus.circle "End"_CC (V_t)$ are isomorphic as rings (moreover, as $CC$-algebras).

  We look now at the centers of the two rings, since they are (in general) noncommutative. Namely, $
  Z(CC[G]) = {sum lambda_g g | (sum lambda_g g) theta = theta (sum lambda_g g) forall theta in CC[G]}.
  $ Since multiplication in $CC$ is commutative and "factors through" internal multiplication, it follows that $sum lambda_g g n Z(CC[G])$ iff it commutes with every group element, i.e. $
  (sum lambda_g g) h = h (sum lambda_g g) & <=> sum_g (lambda_g h^(-1) g h) = sum_g lambda_g g \
  & <=> sum_g lambda_(h^(-1) g h) g = sum_g lambda_g g \ 
  & <=> lambda_(h^(-1) g h) = lambda_g forall g in G.
  $ Hence, $sum lambda_g g in Z(CC[G])$ iff $lambda_(h^(-1) g h) = lambda_g$ for every $g, h in G$. It follows, then, that the induced map $g |-> lambda_g$ a class function, and thus $dim_CC (Z(CC[G])) = h(G)$.

  On the other hand, $dim_CC (Z("End"_CC (V_j))) = 1$ (by representing as matrices, for instance, one can see that only scalar matrices will commute with all other matrices), hence $dim_CC (Z("End"_CC (V_1) plus.circle dots.c plus.circle "End"_CC (V_t))) = t$. $underline(rho)$ naturally restricts to an isomorphism of these centers, hence we conclude justly $t = h(G)$.
]