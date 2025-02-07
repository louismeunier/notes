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

We suppose for now $G$ abelian. In this case, $hash hat(G) = hash G$ so $hat(G)$ is an orthonormal basis for $L^2 (G)$ (comparing dimensions).

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
Phi : CC[G] -> plus.circle_(j=1)^h "End"_CC(V_j) tilde.eq  plus.circle_(j=1)^h "M"_(d_j times d_j) (CC),
$ where $h = h(G)$, $V_j$ enumerate the irreducible representations of $G$, and $d_j := dim_CC(V_j)$.

#definition("Fourier Transform")[
  Given a function $f : G -> CC$, denote by $
  theta_f = sum_(g in G) f(g) g
  $ its corresponding element in $CC[G]$. Then, ots corresponding image under $Phi$ in $plus.circle.big "End"(V_j)$ is called the _Fourier transform_ of $f$, i.e. $
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
  G_mu := "subgroup generated by" g in "supp"(mu),
  G_mu^+:= "subgroup generated by" {g^(-1) h | g, h in "supp"(mu)}.
  $ Notice then $G_mu^+ subset G_mu subset G$.
]

#theorem[Let $mu$ a probability measure on $G$. Then, if $G_mu^+ = G$, then $lim_(N -> infinity) mu^(ast.circle N) = mu_"unif"$, where $mu_"unif"$ the uniform probability distribution which assigns $1/(hash G)$ to each element in $G$.]


== Character Tables of $S_4, A_5$ and $"GL"_3 (FF_5)$


=== $S_4$
For $S_4$, we denote the conjugacy classes by $1A, 2A, 2B, 3A, 3B, 4A$ as the conjugacy classes of elements of the form $(), (12)(34), (12), (123), (1234)$ respectively. 
#align(center,
  table(
    columns: 6,
    stroke: none,
    "", $1A$, $2A$, $2B$, $3A$, $4A$,
    table.hline(start: 0, end: 7),
    table.vline(x:1, start: 0, end: 7),
    $chi_1$, $1$, $1$, $1$,$1$, $1$,
    $chi_2$, $1$, $1$, $-1$, $1$, $1$,
    $chi_3$, $2$, $2$, $0$, $-1$,$0$,
    $chi_4$, $3$, $-1$, $1$, $0$, $-1$,
    $chi_5$, $3$, $-1$, $-1$, $0$, $1$
  )
)

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
  chi_("Ind"_H^G psi)= sum_(a in G\/H) tilde(psi) (a^(-1) g a),
  $ where $
  tilde(psi) (g) = cases(
    0 & "if" g in.not H\ 
    psi(h)  & "if" g in H
  ).
  $
]