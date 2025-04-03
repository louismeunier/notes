// ! external
#import "../typst/notes.typ": *
#import "../typst/shortcuts.typ": *

#import "@preview/cetz:0.2.2"

// ! configuration
#show: doc => conf(
  course_code: "MATH455",
  course_title: "Analysis 4",
  subtitle: "Abstract Metric, Topological Spaces; Functional Analysis.",
  semester: "Winter 2025",
  professor: "Prof. Jessica Lin",
  // cute: "../analysis 3/page.png",
  doc
)

#import "@preview/commute:0.2.0": node, arr, commutative-diagram

#set align(left)

// #let calold = cal

// #let cal(it) = math.class("normal",
//   text(font: "New Computer Modern Math", stylistic-set: 1, $calold(it)$)
// )


#show math.equation: set text(font: "New Computer Modern Math") 
// $cal(A) cal(B) cal(C) cal(D) cal(E) cal(F) cal(G) cal(H) cal(I) cal(J) cal(K) cal(L) cal(M) cal(N) cal(O) cal(P) cal(Q) cal(R) cal(S) cal(T) cal(U) cal(V) cal(W) cal(X) cal(Y) cal(Z)$

// TODO starts here

// % ! 01-07
= Abstract Metric and Topological Spaces
== Review of Metric Spaces
Throughout fix $X$ a nonempty set.
#definition("Metric")[
$rho : X times X -> RR$ is called a _metric_, and thus $(X, rho)$ a _metric space_, if for all $x, y, z in X$, 
- $rho(x, y) >= 0$,
- $rho(x, y) = 0 <=> x = y$,
- $rho(x, y) = rho(y, x)$, and
- $rho(x, y) <= rho(x, z) + rho(z, y)$.
]
#definition("Norm")[
  Let $X$ a linear space. A function $||dot|| : X -> [0, infinity)$ is called a _norm_ if for all $u, v in X$ and $alpha in RR$,
  - $||u|| = 0 <=> u = 0$,
  - $||u + v|| <= ||u||+||v||$, and 
  - $||alpha u|| = |alpha| ||u||$.
]

#remark[A norm induces a metric by $rho(x, y) := ||x - y||$.]

#definition[Given two metrics $rho, sigma$ on $X$, we say they are _equivalent_ if $exists C > 0$ such that $1/C sigma(x, y) <= rho(x, y) <= C sigma(x, y)$ for every $x, y in X$. A similar definition follows for equivalence of norms.]

Given a metric space $(X, rho)$, then, we have the notion of 
- open balls $B(x, r) = {y in X : rho(x, y) < r}$,
- open sets (subsets of $X$ with the property that for every $x in X$, there is a constant $r > 0$ such that $B(x, r) subset.eq X$), closed sets, closures, and 
- _convergence_.

#definition("Convergence")[
  ${x_n} subset.eq X$ converges to $x in X$ if $lim_(n->infinity) rho(x_n, x) = 0$.
]

We have several (equivalent) notions, then, of continuity; via sequences, $epsilon-delta$ definition, and by pullbacks (inverse images of open sets are open).

#definition("Uniform Continuity")[
  $f : (X, rho) -> (Y, sigma)$ uniformly continuous if $f$ has a "modulus of continuity", i.e. there is a continuous function $omega : [0, infinity) -> [0, infinity)$ such that $
  sigma(f(x_1), f(x_2)) <= omega( rho(x_1, x_2))
  $ for every $x_1, x_2 in X$.
]

#remark[For instance, we say $f$ Lipschitz continuous if there is a constant $C > 0$ such that $omega(dot) = C (dot)$. Let $alpha in (0, 1)$. We say $f$ $alpha$-Holder continuous if $omega(dot) = C (dot)^alpha$ for some constant $C$.
] 

#definition("Completeness")[
  We say $(X, rho)$ _complete_ if every Cauchy sequence in $(X, rho)$ converges to a point in $X$.
]

#remark[
  If $(X, rho)$ complete and $E subset.eq X$, then $(E, rho)$ is complete iff $E$ closed in $X$.
]

== Compactness, Separability
#definition("Open Cover, Compactness")[
  ${X_lambda}_(lambda in Lambda) subset.eq 2^X$, where $X_lambda$ open in $X$ and $Lambda$ an arbitrary index set, an _open cover_ of $X$ if for every $x in X$, $exists lambda in Lambda$ such that $x in X_lambda$.

  $X$ is _compact_ if every open cover of $X$ admits a compact subcover. We say $E subset.eq X$ compact if $(E, rho)$ compact.
]

#definition([Totally Bounded, $epsilon$-nets])[
  $(X, rho)$ _totally bounded_ if $forall epsilon > 0$, there is a finite cover of $X$ of balls of radius $epsilon$. If $E subset.eq X$, an _$epsilon$-net_ of $E$ is a collection ${B(x_i, epsilon)}_(i=1)^N$ such that $E subset.eq union.big_(i=1)^N B(x_i, epsilon)$ and $x_i in X$ (note that $x_i$ need not be in $E$).
]

#definition("Sequentially Compact")[
  $(X, rho)$ _sequentially compact_ if every sequence in $X$ has a convergent subsequence whose limit is in $X$.
]

#definition("Relatively/Pre- Compact")[
  $E subset.eq X$ _relatively compact_ if $overline(E)$ compact.
]

#theorem[TFAE: 
1. $X$ complete and totally bounded;
2. $X$ compact;
3. $X$ sequentially compact.
]

// #proof[
// (1. $=>$ 2.) Let ${cal(U)_lambda}_(lambda in Lambda)$ be an arbitrary open cover of 
// ]

#remark[
  $E subset.eq X$ relatively compact if every sequence in $E$ has a convergent subsequence.
]

Let $f : (X, rho) -> (Y, sigma)$ continuous with $(X, rho)$ compact. Then, 
- $f(X)$ compact in $Y$;
- if $Y = RR$, the max and min of $f$ over $X$ are achieved;
- $f$ is uniformly continuous.

Let $C(X) := {f : X -> RR | f "continuous"}$ and $||f||_infinity := max_(x in X) |f(x)|$ the sup (max, in this case) norm. Then, 
#theorem[
  Let $(X, rho)$ compact. Then, $(C(X), ||dot||_infinity)$ is complete.
]

#proof[
  Let ${f_n} subset.eq C(X)$ Cauchy with respect to $||dot||_infinity$. Then, there exists a subsequence ${f_n_k}$ such that for each $k >= 1$, $||f_(n_(k+1)) - f_n_k||_infinity <= 2^(-k)$ (to construct this subsequence, let $n_1 >= 1$ be such that $||f_n - f_(n_1)||_infinity < 1/2$ for all $n >= n_1$, which exists since ${f_n}$ Cauchy. Then, for each $k >= 1$, define inductively $n_(k+1)$ such that $n_(k+1) > n_k$ and $||f_n - f_(n_(k+1))||_infinity < 1/(2^(k+1))$ for each $n >= n_(k+1)$. Then, for any $k >= 1$, $||f_(n_(k+1)) - f_n_k||_infinity < 2^(-k)$, since $n_(k+1) > n_k$.).

  Let $j in NN$. Then, for any $k >= 1$,$
  ||f_(n_(k+j)) - f_(n_k)||_infinity <= sum_(ell = k)^(k + j - 1) ||f_(n_(ell + 1)) - f_n_ell||_infinity <= sum_(ell) 2^(-ell)
  $ and hence for each $x in X$, with $c_k := f_(n_k) (x)$, $
  |c_(k+j) - c_k| <= sum_(ell = k)^infinity 2^(-ell).
  $ The RHS is the tail of a converging series, and thus $|c_(k+j) - c_k| -> 0$ as $k -> infinity$ i.e. ${c_k}$ a Cauchy sequence, in $RR$. $(RR, |dot|)$ complete, so $lim_(k->infinity) c_k =: f(x)$ exists for each $x in X$. So, for each $x in X$, we find $
  |f_(n_k) (x) - f(x)| <= sum_(ell = k)^infinity 2^(-ell),
  $ and since the RHS is independent of $x$, we may pass to the sup norm, and find $
  ||f_(n_k) - f||_infinity <= sum_(ell = k)^infinity 2^(-ell),
  $ with the RHS $-> 0$ as $k -> infinity$. Hence, $f_n_k -> f$ in $C(X)$ as $k -> infinity$. In other words, we have uniform convergence of ${f_n_k}$. Each ${f_n_k}$ continuous, and thus $f$ also continuous, and thus $f in C(X)$.

  It remains to show convergence along the whole sequence. Suppose otherwise. Then, there is some $alpha > 0$ and a subsequence ${f_n_j} subset.eq {f_n}$ such that $||f_n_j - f||_infinity > alpha > 0$ for every $j >= 1$. Then, let $k$ be sufficiently large such that $||f - f_n_k||_infinity <= alpha/2$. Then, for every $j >= 1$ and $k$ sufficiently large, $
  ||f_n_j - f_n_k||_infinity &>= ||f_n_j - f||_infinity - ||f - f_n_k||_infinity \
  &> alpha - alpha/2 > 0,
  $ which contradicts the Cauchy-ness of ${f_n}$, completing the proof.
]

#definition("Density/Separability")[
A set $D subset.eq X$ is called _dense_ in $X$ if for every nonempty open subset $A subset.eq X$, $D sect A eq.not nothing$. We say $X$ _separable_ if there is a countable dense subset of $X$.
]

#remark[
  If $A$ dense in $X$, then $overline(A) = X$.
]

#proposition[
  If $X$ compact, $X$ separable.
]

#proof[
  Since $X$ compact, it is totally bounded. So, for $n in NN$, there is some $K_n$ and ${x_i} subset.eq X$ such that $X subset.eq union.big_(i=1)^K_n B(x_i, 1/n)$. Then, $D = union.big_(n=1)^infinity union.big_(i=1)^K_n {x_i}$ countable and dense in $X$.
]


// % ! 01-09
== Arzelà-Ascoli
The goal in this section is to find conditions for a sequence of functions ${f_n} subset.eq C(X)$ to be precompact, namely, to have a uniformly convergent subsequence.

#corollary[Any Cauchy sequence converges if it has a convergent subsequence.]

#proof[
  Let ${x_n}$ be a Cauchy sequence in a metric space $(X, rho)$ with convergent subsequence ${x_n_k}$ which converges to some $x in X$. Fix $epsilon > 0$. Let $N >= 1$ be such that if $m, n >= N$, $rho(x_n, x_m) < epsilon/2$. Let $K >= 1$ be such that if $k >= K$, $rho(x_n_k, x) < epsilon/2$. Let $n, n_k >= max {N, K}$,  then $
  rho(x, x_n) <= rho(x, x_n_k) + rho(x_n_k, x_n) <epsilon/2 + epsilon/2 = epsilon.
  $
]

#definition("Equicontinuous")[
  A family $cal(F) subset.eq C(X)$ is called _equicontinuous_ at $x in X$ if $forall epsilon>0$ there exists a $delta = delta(x, epsilon) > 0$ such that if $rho(x, x') < delta $ then $|f(x) - f(x')| < epsilon$ for every $f in cal(F)$.
]

// TODO examples in notes

#remark[$cal(F)$ equicontinuous at $x$ iff every $f in cal(F)$ share the same modulus of continuity.]

#definition("Pointwise/uniformly bounded")[
  ${f_n}$ pointwise bounded if $forall x in X$, $exists M(x) > 0$ such that $|f_n (x)| <= M(x) forall n$, and uniformly bounded if such an $M$ exists independent of $x$.
]

#lemma("Arzelà-Ascoli Lemma")[
  Let $X$ separable and let ${f_n} subset.eq C(X)$ be pointwise bounded and equicontinuous. Then, there is a function $f$ and a  subsequence ${f_n_k}$ which converges pointwise to $f$ on all of $X$.
]

#proof[
  Let $D = {x_j}_(j=1)^infinity subset.eq X$ be a countable dense subset of $X$. Since ${f_n}$ p.w. bounded, ${f_n (x_1)}$ as a sequence of real numbers is bounded and so by the Bolzano-Weierstrass (BW) Theorem there is a convergent subsequence ${f_(n(1, k)) (x_1)}_(k)$ that converges to some $a_1 in RR$. Consider now ${f_(n (1, k)) (x_2)}_k$, which is again a bounded sequence of $RR$ and so has a convergent subsequence, call it ${f_(n(2, k)) (x_2)}_k$ which converges to some $a_2 in RR$. Note that ${f_(n(2, k))} subset.eq {f_(n(1, k))}$, so also $f_(n(2, k)) (x_1) -> a_1$ as $k->infinity$. We can repeat this procedure, producing a sequence of real numbers ${a_ell}$, and for each $j in NN$ a subsequence ${f_(n(j, k))}_k subset.eq {f_n}$ such that $f_(n(j, k)) (x_ell) -> a_ell$ for each $1 <= ell <= j$. Define then $
  f : D -> RR, f(x_j) := a_j.
  $ Consider now $
  f_n_k := f_(n (k, k)), k >= 1,
  $ the "diagonal sequence", and remark that $f_(n_k) (x_j) -> a_j = f(x_j)$ as $k-> infinity$ for every $j >= 1$. Hence, ${f_n_k}_k$ converges to $f$ on $D$, pointwise.

  We claim now that ${f_n_k}$ converges on all of $X$ to some function $f : X -> RR$, pointwise. Put $g_k := f_n_k$ for notational convenience. Fix $x_0 in X$, $epsilon > 0$, and let $delta > 0$ be such that if $x in X$ such that $rho(x, x_0) < delta$, $|g_k (x) - g_k (x_0)| < epsilon/3$ for every $k >= 1$, which exists by equicontinuity. Since $D$ dense in $X$, there is some $x_j in D$ such that $rho(x_j, x_0) < delta$. Then, since $g_k (x_j) -> f(x_j)$ (pointwise), ${g_k (x_j)}_k$ is Cauchy and so there is some $K >= 1$ such that for every $k, ell >= K$, $|g_ell (x_j) - g_k (x_j)| < epsilon/3$. And hence, for every $k, ell >= K$, $
  |g_k (x_0) - g_ell (x_0)| &<= |g_k (x_0) - g_k (x_j)| + |g_k (x_j) - g_ell (x_j)| + |g_ell (x_j) - g_ell (x_0)| < epsilon,
  $ so namely ${g_k (x_0)}_k$ Cauchy as a sequence in $RR$. Since $RR$ complete, then ${g_k (x_0)}_k$ also converges, to, say, $f(x_0) in RR$. Since $x_0$ was arbitrary, this means there is some function $f : X -> RR$ such that $g_k -> f$ pointwise on $X$ as we aimed to show.
  ]


#definition("Uniformly Equicontinuous")[
  $cal(F) subset.eq C(X)$ is said to be uniformly equicontinuous if for every $epsilon < 0$, there exists a $delta > 0$ such that $forall x, y in X$ with $rho(x, y) < delta$, $|f(x) - f(y)| < epsilon$ for every $f in cal(F)$. That is, every function in $cal(F)$ has the same modulus of continuity.
]

#proposition("Sufficient Conditions for Uniform Equicontinuity")[
  1. $cal(F) subset.eq C(X)$ uniformly Lipschitz
  2. $cal(F) subset.eq C(X) sect C^1 (X)$ has a uniform $L^infinity$ bound on the first derivative
  3. $cal(F) subset.eq C(X)$ uniformly Holder continuous
  4. $(X, rho)$ compact and $cal(F)$ equicontinuous
]

#proof[
  1. If $C > 0$ is such that $|f(x) - f(y)| <= C rho(x, y)$ for every $x, y in X$ and $f in cal(F)$, then for $epsilon > 0$, let $delta = epsilon/C$, then if $rho(x, y) <= delta$, $|f(x) - f(y)| <= C delta < epsilon$, and $delta$ independent of $x$ (and $f$) since it only depends on $C$ which is independent of $x, y, f$, etc.

  // 2. Actually implies 1.; if say $|f'|<=M$ for every $f in cal(F)$, then by the mean value theorem, for every $x, y in X$, there is some $c in X$ such that $$

  3. Akin to 1.
]

#theorem("Arzelà-Ascoli")[
  Let $(X, rho)$ a compact metric space and ${f_n} subset.eq C(X)$ be a uniformly bounded and (uniformly) equicontinuous family of functions. Then, ${f_n}$ is pre-compact in $C(X)$, i.e. there exists ${f_n_k} subset.eq {f_n}$ such that $f_n_k$ is uniformly convergent on $X$.
]

#proof[
  Since $(X, rho)$ compact it is separable and so by the lemma there is a subsequence ${f_n_k}$ that converges pointwise on $X$. Denote by $g_k := f_n_k$ for notational convenience.

  We claim ${g_k}$ uniformly Cauchy. Let $epsilon > 0$. By uniform equicontinuity, there is a $delta > 0$ such that $rho(x, y) < delta => |g_k (x) - g_k (y)| < epsilon/3$. Since $X$ compact it is totally bounded so there exists ${x_i}_(i=1)^N $ such that $X subset.eq union.big_(i=1)^N B(x_i, delta)$. For every $1 <= i <= N$, ${g_k (x_i)}$ converges by the lemma hence is Cauchy in $RR$. So, there exists a $K_i$ such that for every $k, ell >= K_i$ $|g_k (x_i) - g_ell (x_i)| <= epsilon/3$. Let $K := max{K_i}$. Then for every $ell, k <= K$, $|g_k (x_i) - g_ell (x_i)| <= epsilon/3$ for every $i = 1, dots, N$. So, for all $x in X$, there is some $x_i$ such that $rho(x, x_i) < delta$, and so for every $k, ell >= K$, $
  |g_k (x) - g_ell (x)| & <= |g_k (x) - g_k (x_i)| \ 
  & wide + |g_k (x_i) - g_ell (x_i)| \ 
  & wide + |g_ell (x_i) - g_ell (x)| < epsilon,
  $ the first and last follow by the equicontinuity and the second from the lemma. This holds for every $x$ and thus $||g_k - g_ell||_infinity < epsilon$, so ${g_k}$ Cauchy in $C(X)$. But $C(X)$ complete so converges in the space.
]

#remark[
  If $K subset.eq X$ a compact set, then $K$ bounded and closed.
]

#theorem[Let $(X, rho)$ compact and $cal(F) subset.eq C(X)$. Then, $cal(F)$ a compact subspace of $C(X)$ iff $cal(F)$ closed, uniformly bounded, and (uniformly) equicontinuous.]

#proof[
  $(impliedby)$ Let ${f_n} subset.eq cal(F)$. By Arzelà-Ascoli Theorem, there exists a subsequence ${f_n_k}$ that converges uniformly to some $f in C(X)$. Since $cal(F)$ closed, $f in cal(F)$ and so $cal(F)$ sequentially compact hence compact.

  $(implies)$ $cal(F)$ compact so closed and bounded in $C(X)$. To prove equicontinuous, we argue by contradiction. Suppose otherwise, that $cal(F)$ not-equicontinuous at some $x in X$. Then, there is some $epsilon_0 > 0$ and ${f_n} subset.eq cal(F)$ and ${x_n} subset.eq X$ such that $|f_n (x_n) - f_n (x)| >= epsilon_0$ while $rho(x, x_n) < 1/n$. Since ${f_n}$ bounded and $cal(F)$ compact, there is a subsequence ${f_n_k}$ that converges to $f$ uniformly. Let $K$ be such that $forall k >= K$, $||f_n_k - f||_infinity <= epsilon_0/3$. Then, $
  |f(x_n_k) -f | &>=  | |f(x_n_k) - f_n_k (x_n_k)| - |f_n_k (x_n_k) - f_n_k (x)| - |f_n_k (x) - f(x)| | \ 
  &>= epsilon_0/3,
  $ while $rho(x_n_k, x) <= 1/n_k$, so $f$ cannot be continuous at $x$, a contradiction.
]

== Baire Category Theorem

#definition("Hollow/Nowhere Dense")[
We say a set $E subset.eq X$ _hollow_ if $"int"(E) = nothing$. We say a set $E subset.eq X$ _nowhere dense_ if its closure is hollow, i.e. $"int"(overline(E)) = nothing$.
]

#remark[
  Notice that $E$ hollow $<=>$ $E^c$ dense, since $"int"(E) = nothing => ("int"(E))^c = overline(E^c) = X$.
]

#theorem("Baire Category Theorem")[
  Let $X$ be a complete metric space. 

  (a) Let ${F_n}$ a collection of closed hollow sets. Then, $union.big_(n=1)^infinity F_n$ also hollow.

  (b) Let ${cal(O)_n}$ a collection of open dense sets. Then, $sect.big_(n=1)^infinity cal(O)_n$ also dense.
]

#proof[
  Notice that $(a) <=> (b)$ by taking complements. We prove $(b)$.

  Put $G := sect.big_(n=1)^infinity cal(O)_n$. Fix $x in X$ and $r > 0$, then to show density of $G$ is to show $G sect B(x, r) eq.not nothing$. 
  
  Since $cal(O)_1$ dense, then $cal(O)_1 sect B(x, r)$ nonempty and in particular open. So, let $x_1 in X$ and $r_1 < 1/2$ such that $overline(B)(x, r_1) subset.eq B(x, 2 r_1) subset.eq cal(O)_1 sect B(x, r)$.

  Similarly, since $cal(O)_2$ dense, $cal(O)_2 sect B(x_1, r_1)$ open and nonempty so there exists $x_2 in X$ and $r_2 < 2^(-2)$ such that $overline(B)(x_2, r_2) subset.eq cal(O)_2 sect B(x_1, r_1)$.

  Repeat in this manner to find $x_n in X$ with $r_n  < 2^(-n)$ such that $overline(B)(x_n, r_n) subset.eq cal(O)_n sect B(x_(n-1), r_(n-1))$ for any $n in NN$. This creates a sequence of sets $
  overline(B)(x_1, r_1) supset.eq overline(B)(x_2, r_2) supset.eq dots.c,
  $ with $r_n -> 0$. Hence, the sequence of points ${x_n}$ Cauchy and since $X$ complete, $x_j -> x_0 in X$, so in particular $
  {x_0} = sect.big_(n=1)^infinity overline(B)(x_n, r_n),
  $ hence $x_0 in cal(O)_n$ for every $n$ and thus $G sect B(x, r)$ nonempty.
]

#corollary[Let $X$ complete and ${F_n}$ a sequence of closed sets in $X$. If $X = union.big_(n>=1) F_n$, there is some $n_0$ such that $"int"(F_n_0) eq.not nothing$.]

#proof[
  If not, violates BCT since $X$ is not hollow in itself; $"int"(X) = X$.
]

#corollary[
  Let $X$ complete and ${F_n}$ a sequence of closed sets in $X$. Then, $union.big_(n=1)^infinity partial F_n$ hollow.
]

#proof[
  We claim $"int"(partial F_n) = nothing$. Suppose not, then there exists some $B(x_0, r) subset.eq partial F_n$. Then $x_0 in partial F_n$ but $B(x_0, r) sect F_n^c = nothing$, a contradiction.
  // TODO why?
  So, since $partial F_n$ closed and $partial F_n sect B(x_0, r) = nothing$ for every such ball, by BCT $union.big_(n=1)^infinity partial F_n$ must be hollow.
]

// ! 01-16
=== Applications of Baire Category Theorem

#theorem[
  Let $cal(F) subset C(X)$ where $X$ complete. Suppose $cal(F)$ pointwise bounded. Then, there exists a nonempty, open set $cal(O) subset.eq X$ such that $cal(F)$ uniformly bounded on $cal(O)$.
]

#proof[
  Let $
  E_n &:= {x in X : |f(x)| <= n forall f in cal(F)} \ 
  &= sect.big_(f in cal(F)) underbrace({x : |f(x)| <= n}, "closed").
  $ Since $cal(F)$ pointwise bounded, for every $x in X$ there is some $M_x > 0$ such that $|f(x)| <= M_x$ for every $f in cal(F)$. Hence, for every $n in NN$ such that $n >= M_x$, $x in E_n$ and thus $X = union.big_(n=1)^infinity E_n$. 
  
  $E_n$ closed and hence by the previous corollaries there is some $n_0$ such that $"int"(E_n_0) eq.not nothing$ and hence there is some $r > 0$ and $x_0 in X$ such that $B(x_0, r) subset.eq E_n_0$. Then, for every $x in B(x_0, r)$, $|f(x)| <= n_0$ for every $f in cal(F)$, which gives our desired non-empty open set upon which $cal(F)$ uniformly bounded.
]

#theorem[
  Let $X$ complete, and ${f_n} subset.eq C(X)$ such that $f_n -> f$ pointwise on $X$. Then, there exists a dense subset $D subset.eq X$ such that ${f_n}$ equicontinuous on $D$ and $f$ continuous on $D$.
]

#proof[
  For $m, n in NN$, let $
  E(m, n) &:= {x in X : |f_j (x) - f_k (x)| <= 1/m forall j,k >= n} \ 
  &= sect.big_(j,k>=n) {x : |f_j (x) - f_k (x)| <= 1/m}.
  $ The union of the boundaries of these sets are hollow, hence $D := (union.big_(m,n >= 1) partial E(m,n))^c$ is dense. Then, if $x in D sect E(m, n)$, then $x in (partial E(m,n))^c$ implies $x in "int"(E(m,n))$.

  We claim ${f_n}$ equicontinuous on $D$. Let $x_0 in D$ and $epsilon > 0$. Let $1/m <= epsilon/4$. Then, since ${f_n (x_0)}$ convergent it is therefore Cauchy (in $RR$). Hence, there is some $N$ such that $|f_j (x_0) - f_k (x_0)| <= 1/m$ for every $j, k >= N$, so $x_0 in D sect E(m, N)$ hence $x_0 in "int"(E(m,N)).$

  Let $B(x_0, r) subset.eq E(m, N)$. Since $f_N$ continuous at $x_0$ there is some $delta > 0$ such that $delta < r$ and $
  |f_N (x) - f_N (x_0)| < 1/m forall x in B(x_0, delta),
  $ and hence $
  |f_j (x) - f_j (x_0)| & <= |f_j (x) - f_N (x)| + |f_N (x) - f_N (x_0)| + |f_N (x_0) - f_j (x_0)| \ 
  & <= 3/m <= 3/4 epsilon,
  $ for every $x in B(x_0, delta)$ and $j >= N$, where the first, last bounds come from Cauchy and the middle from continuity of $f_N$. Hence, we've show ${f_n}$ equicontinuous at $x_0$ since $delta$ was independent of $f$.

  In particular, this also gives for every $x in B(x_0, delta)$ the limit $
  3/4 epsilon > lim_(j->infinity) |f_j (x) - f_j (x_0)| = |f(x) - f(x_0)|,
  $ so $f$ continuous on $D$.
]

== Topological Spaces
Throughout, assume $X eq.not nothing$.

#definition("Topology")[
  Let $X eq.not nothing$. A _topology_ $cal(T)$ on $X$ is a collection of subsets of $X$, called _open sets_, such that 
  - $X, nothing in cal(T)$;
  - If ${E_n} subset.eq cal(T)$, $sect.big_(n=1)^N E_n in cal(T)$ (closed under _finite_ intersections);
  -  If ${E_n} subset.eq cal(T)$, $union.big_n E_n in cal(T)$ (closed under _arbitrary_ unions).

  If $x in X$, a set $E in cal(T)$ containing $x$ is called a neighborhood of $x$.
]

#proposition[$E subset.eq X$ open $<=>$ for every $x in E$, there is a neighborhood of $x$ contained in $E$.]

#proof[
  $=>$ is trivial by taking the neighborhood to be $E$ itself. $impliedby$ follows from the fact that, if for each $x$ we let $cal(U)_x$ a neighborhood of $x$ contained in $E$, then $
  E = union.big_(x in E) cal(U)_x,
  $ so $E$ open being a union of open sets.
]
#example[
  Every metric space induces a natural topology given by open sets under the metric. The _discrete topology_ is given by $cal(T) = 2^X$ (and is actually induced by the discrete metric), and is the largest topology. The _trivial topology_ ${nothing, X}$ is the smallest.  The _relative topology_ defined on a subset $Y subset.eq X$ is given by $cal(T)_Y := {E sect Y : E in cal(T)}$.
]

#definition("Base")[
  Given a topological space $(X, cal(T))$, let $x in X$. A collection $cal(B)_x$ of neighborhoods of $x$ is called a _base_ of $cal(T)$ at $x$ if for every neighborhood $cal(U)$ of $x$, there is a set $B in cal(B)_x$ such that $B subset.eq cal(U)$. 

  We say a collection $cal(B)$ a base for all of $cal(T)$ if for every $x in X$, there is a base for $x, cal(B)_x subset.eq cal(B)$.
]

#proposition[
  If $(X, cal(T))$ a topological space, then $cal(B) subset.eq cal(T)$ a base for $cal(T)$ $<=>$ every nonempty open set $cal(U) in cal(T)$ can be written as a union of elements of $cal(B)$.
]

#proof[
  $=>$ If $cal(U)$ open, then for $x in cal(U)$ there is some basis element $B_x$ contained in $cal(U)$. So in particular $cal(U) = union.big_(x in cal(U)) B_x$.

  $impliedby$ Let $x in cal(U)$ and $cal(B)_x := {B in cal(B) | x in B}$. Then, for every neighborhood of $x$, there is some $B$ in $cal(B)_x$ such that $B subset.eq cal(U)$ so $cal(B)_x$ a base for $cal(T)$ at $x$.
]

#remark[
  A base $cal(B)$ defines a unique topology, ${nothing, union cal(B)_x}$.
]
//  ! 01-21

#proposition[
$cal(B) subset.eq 2^X$ a base for a topology on $X$ $<=>$ 
- $X = union.big_(B in cal(B)) B$
- If $B_1, B_2 in cal(B)$ and $x in B_1 sect B_2$, then there is a $B in cal(B)$ such that $x in B subset.eq B_1 sect B_2$.
]

#proof[
  ($=>$) If $cal(B)$ a base, then $X$ open so $X = union_B B$. If $B_1, B_2 in cal(B)$, then $B_1 sect B_2$ open so there must exist some $B subset.eq B_1 sect B_2$ in $cal(B)$.

  ($impliedby$) Let $
  cal(T) = {cal(U) | forall x in cal(U), exists B in cal(B) "with" x in B subset.eq cal(U)}.
  $ One can show this a topology on $X$ with $cal(B)$ as a base.
] 
// #remark[Finite intersections stay closed in $cal(B)$.]

#definition[
  If $cal(T)_1 subset.neq cal(T)_2$, we say $cal(T)_1$ _weaker/coarser_ and $cal(T)_2$ _stronger/finer_.

  Given a subset $S subset.eq 2^X$, define $
  cal(T)(S) = sect.big "all topologies containing" S = "unique weakest topology containing" S
  $ to be the topology _generated_ by $S$.
]

#proposition[
  If $S subset.eq 2^X$, $
  cal(T)(S) = union.big {"finite intersections of elts of" S}.
  $ We call $S$ a "subbase" for $cal(T)(S)$ (namely, we allow finite intersections of elements in $S$ to serve as a base for $cal(T)(S)$).
]

#proof[
  Let $cal(B) := {X, "finite intersections of elements of" S}$. We claim this a base for $cal(T)(S)$.
]

#definition("Point of closure/accumulation point")[
  If $E subset.eq X, x in X$, $x$ is called a _point of closure_ if $forall cal(U)_x$, $cal(U)_x sect E eq.not nothing$. The collection of all such sets is called the _closure_ of $E$, denoted $overline(E)$. We say $E$ _closed_ if $E = overline(E)$.
]

#proposition[
  Let $E subset.eq X$, then 
  - $overline(E)$ closed,
  - $overline(E)$ is the smallest closed set containing $E$,
  - $E$ open $<=>$ $E^c$ closed.
]

== Separation, Countability, Separability

#definition[
  A neighborhood of a set $K subset.eq X$ is any open set containing $K$.
]

#definition("Notions of Separation")[
  We say $(X, cal(T))$:

  - _Tychonoff Separable_ if $forall x, y in X, exists cal(U)_x, cal(U)_y$ such that $y in.not cal(U)_x, x in.not cal(U)_y$
  - _Hausdorff Separable_ if $forall x, y in X$ can be separated by two disjoint open sets i.e. $exists cal(U)_x sect cal(U)_y = nothing$
  - _Normal_ if Tychonoff and in addition any 2 disjoint closed sets can be separated by disjoint neighborhoods.
]

#remark[
  Metric space $subset.eq$ normal space $subset.eq$ Hausdorff space $subset.eq$ Tychonoff space.
]

#proposition[
  Tychonoff $<=>$ $forall x in X$, ${x}$ closed.
]

#proof[
  For every $x in X$, $
  {x} "closed" &<=> {x}^c "open" \ 
  &<=> forall  y in {x}^c, exists cal(U)_y subset.eq {x}^c \ 
  &<=> forall y eq.not x, exists cal(U)_y "s.t." x in.not cal(U)_y,
  $ and since this holds for every $x$, $X$ Tychonoff.
]

#proposition[
  Every metric space normal.
]

#proof[
  Define, for $F subset.eq X$, the function $
  "dist"(F, x) := inf {rho(x, x') | x' in F}.
  $ Notice that if $F$ closed and $x in.not F$, then $"dist"(F, x) > 0$ (since $F^c$ open so there exists some $B(x, epsilon) subset.eq F^c$ so $rho(x, x') >= epsilon$ for every $x' in F$). Let $F_1, F_2$ be closed disjoint sets, and define $
  cal(O)_1 := {x in X | "dist"(F_1, x) < "dist"(F_2, x)}, \
  cal(O)_2 := {x in X | "dist"(F_1, x) > "dist"(F_2, x)}.
  $ Then, $F_1 subset.eq cal(O)_1, F_2 subset.eq cal(O)_2$, and $cal(O)_1 sect cal(O)_2 = nothing$. If we show $cal(O)_1, cal(O)_2$ open, we'll be done.

  Let $x in cal(O)_1$ and $epsilon > 0$ such that $"dist"(F_1, x) + epsilon <= "dist"(F_2, x)$. I claim that $B(x, epsilon/5) subset.eq cal(O)_1$. Let $y in B(x, epsilon/5)$. Then, $
  "dist"(F_2, y) &>= rho(y,y') - epsilon/5 wide "for some" y' in F_2 \ 
  &>= rho(x, y') - rho(x, y) + epsilon/5 wide "reverse triangle inequality" \ 
  & >= "dist"(F_2, x) - (2 epsilon)/5 \ 
  & >= "dist"(F_1, x) + epsilon - (2 epsilon)/5 \ 
  & >= rho(x, tilde(y)) + (2 epsilon)/5 wide "for some" tilde(y) in F_1 \ 
  & >= rho(y, tilde(y)) - rho(y, x) + (2epsilon)/5wide "reverse triangle inequality" \
  & >= rho(y, tilde(y)) - epsilon/5 + (2 epsilon)/5 \ 
  & >= "dist"(F_1, y) + epsilon/5 > "dist"(F_1, y),
  $ hence, $y in cal(O)_1$ and thus $cal(O)_1$ open. Similar proof follows for $cal(O)_2$.
]
// ! page 17
// ! 01-23

#proposition[Let $X$ Tychonoff. Then $X$ normal $<=>$ $forall F subset.eq X$ closed and neighborhood $cal(U)$ of $F$, there exists an open set $cal(O)$ such that $
F subset.eq cal(O) subset.eq overline(cal(O)) subset.eq cal(U).
$ This is called the "nested neighborhood property" of normal spaces.]

#proof[
  ($=>$) Let $F$ closed and $cal(U)$ a neighborhood of $F$. Then, $F$ and $cal(U)^c$ closed disjoint sets so by normality there exists $cal(O), cal(V)$ disjoint open neighborhoods of $F$, $cal(U)^c$ respectively. So, $cal(O) subset.eq cal(V)^c$ hence $overline(cal(O)) subset.eq overline(cal(V))^c = cal(V)^c$ and thus $
  F subset.eq cal(O) subset.eq overline(cal(O)) subset.eq cal(V)^c subset.eq cal(U).
  $

  ($impliedby$) Let $A, B$ be disjoint closed sets. Then, $B^c$ open and moreover $A subset.eq B^c$. Hence, there exists some open set $cal(O)$ such that $A subset.eq cal(O) subset.eq overline(cal(O)) subset.eq B^c$, and thus $B subset.eq overline(cal(O))^c$. Then, $cal(O)$ and $overline(cal(O))^c$ are disjoint open neighborhoods of $A$, $B$ respectively so $X$ normal.
]

#definition("Separable")[
  A space $X$ is called _separable_ if it contains a countable dense subset.
]

#definition("1st, 2nd Countable")[
  A topological space $(X, cal(T))$ is called 

  - _1st countable_ if there is a countable base at each point; and
  - _2nd countable_ if there is a countable base for all of $cal(T)$.
]

#example[Every metric space is first countable; for $x in X$ let $cal(B)_x = {B(x, 1/n) | n in NN}$.]

#proposition[
  Every 2nd countable space is separable.
]

#definition("Convergence")[
  Let ${x_n} subset.eq X$. Then, we say $x_n -> x$ in $cal(T)$ if for every neighborhood $cal(U)_x$, there exists an $N$ such that $forall n >= N$, $x_n in cal(U)_x$.
]

#remark[In general spaces, such a limit may not be unique. For instance, under the trivial topology, the only nonempty neighborhood is the whole space, so every sequence converges to every point in the space.]

#proposition[Let $(X, cal(T))$ be Hausdorff. Then, all limits are unique.]

#proof[
  Suppose otherwise, that $x_n ->$ both $x$ and $y$. If $x eq.not y$, then since $X$ Hausdorff there are disjoint neighborhoods $cal(U)_x, cal(U)_y$ containing $x, y$. But then $x_n$ cannot be on both $cal(U)_x$ and $cal(U)_y$ for sufficiently large $n$, contradiction.
]

#proposition[Let $X$ be 1st countable and $E subset.eq X$. Then, $x in overline(E)$ $<=>$ there exists ${x_j} subset.eq E$ such that $x_j -> x$.]

#proof[
  ($=>$) Let $cal(B)_x = {B_j}$ be a base for $X$ at $x in overline(E)$. Wlog, $B_j supset.eq B_(j+1)$ for every $j >= 1$ (by replacing with intersections, etc if necessary). Hence, $B_j sect E eq.not nothing$ for every $j$. Let $x_j in B_j sect E$, then by the nesting property $x_j -> x$ in $cal(T)$.

  ($impliedby$) Suppose otherwise, that $x in.not overline(E)$. Let ${x_j} in E_j$. Then, $overline(E)^c$ open, and contains $x$. Then, $overline(E)^c$ a neighborhood of $x$ but does not contain any $x_j$ so $x_j arrow.r.not x$.
]

== Continuity and Compactness

#definition[
  Let $(X, cal(T)), (Y, cal(S))$ be two topological spaces. Then, a function $f : X -> Y$ is said to be continuous at $x_0$ if for every neighborhood $cal(O)$ of $f(x_0)$ there exists a neighborhood $cal(U)(x_0)$ such that $f(cal(U)) subset.eq cal(O)$. We say $f$ continuous on $X$ if it is continuous at every point in $X$.
]

#proposition[
  $f$ continuous $<=>$ $forall cal(O)$ open in $Y$, $f^(-1) (cal(O))$ open in $X$.
]

#definition("Weak Topology")[
Consider $cal(F) := {f_lambda : X -> X_lambda}_(lambda in Lambda)$ where $X, X_lambda$ topological spaces. Then, let $
S := {f^(-1)_lambda (cal(O)_lambda) | f_lambda in cal(F), cal(O)_lambda in X_lambda} subset.eq X.
$ We say that the topology $cal(T)(S)$ generated by $S$ is the _weak topology_ for $X$ induced by the family $cal(F)$.
]

#proposition[
  The weak topology is the weakest topology in which each $f_lambda$ continuous on $X$.
]

#example[
  The key example of the weak topology is given by the product topology. Consider ${X_lambda}_(lambda in Lambda)$ a collection of topological spaces. We can defined a "natural" topology on the product $X := product_(lambda in Lambda) X_lambda$ by consider the weak topology induced by the family of projection maps, namely, if $pi_lambda : X -> X_lambda$ a coordinate-wise projection and $cal(F) = {pi_lambda : lambda in Lambda}$, then we say the weak topology induced by $cal(F)$ is the _product topology_ on $X$. In particular, a base for this topology is given, by previous discussions, $
  cal(B) = {sect.big_(j=1)^n pi^(-1)_(lambda_j) (cal(O)_j)} = {product_(lambda in Lambda) cal(U)_lambda : cal(U)_lambda "open" "and all by finitely many " U_(lambda) 's  = X_lambda}.
  $
]

#definition("Compactness")[
  A space $X$ is said to be _compact_ if every open cover of $X$ admits a finite subcover.
]

#proposition[
  - Closed subsets of compact spaces are compact
  - $X$ compact $<=>$ if ${F_k} subset.eq X$-nested and closed, $sect_(k=1)^infinity F_k eq.not nothing $.
  - Continuous images of compact sets are compact
  - Continuous real-valued functions on a compact topological space achieve their min, max.
]

#proposition[
  Let $K$ compact be contained in a Hausdorff space $X$. Then, $K$ closed in $X$.
]

#proof[
  We show $K^c$ open. Let $y in K^c$. Then for every $x in K$, there exists disjoint open sets $cal(U)_(x y), cal(O)_(x y)$ containing $y, x$ respectively. Then, it follows that ${cal(O)_(x y)}_(x in K)$ an open cover of $K$, and since $K$ compact there must exist some finite subcover, $K subset.eq union.big_(i=1)^N cal(O)_(x_i y)$. Let $E := sect.big_(i=1)^N cal(U)_(x_i y)$. Then, $E$ is an open neighborhood of $y$ with $E sect cal(O)_(x_i y) = nothing$ for every $i = 1, dots N$. Thus, $E subset.eq sect.big_(i=1)^N cal(O)_(x_i y)^c = (union.big_(i=1)^N cal(O)_(x_i y))^c subset.eq K^c$ so since $y$ was arbitrary $K^c$ open.
]

#definition("Sequential Compactness")[
  We say $(X, cal(T))$ _sequentially compact_ if every sequence in $X$ has a converging subsequence with limit contained in $X$.
]

#proposition[
  Let $(X, cal(T))$ second countable. Then, $X$ compact $<=>$ sequentially compact.
]

#proof[
($=>$) Let ${x_k} subset.eq X$ and put $F_n := overline({x_k | k >= n})$. Then, ${F_n}$ defines a sequence of closed and nested subsets of $X$ and, since $X$ compact, $sect.big_(n=1)^infinity F_n$ nonempty. Let $x_0$ in this intersection. Since $X$ 2nd and so in particular 1st countable, let ${B_j}$ a (wlog nested) countable base at $x_0$. $x_0 in F_n$ for every $n >= 1$ so each $B_j$ must intersect some $F_n$. Let $n_j$ be an index such that $x_n_j in B_j$. Then, if $cal(U)$ a neighborhood of $x_0$, there exists some $N$ such that $B_j subset.eq cal(U)$ for every $j >= N$ and thus ${x_n_j} subset.eq B_N subset.eq cal(U)$, so $x_n_j -> x_0$ in $X$.

($impliedby$) Remark that since $X$ second countable, every open cover of $X$ certainly has a countable subcover by intersecting a given cover with our countable basis. So, assume we have a countable cover $X subset.eq union.big_(n=1)^infinity cal(O)_n$ and suppose towards a contradiction that no finite subcover exists. Then, for every $n >= 1$, there exists some $m(n) >= n$ such that $cal(O)_(m(n)) \\ union.big_(i=1)^n cal(O)_i eq.not nothing$. Let $x_n$ in this set for every $n >= 1$. Since $X$ sequentially compact, there exists a convergent subsequence ${x_n_k} subset.eq {x_n}$ such that $x_n_k -> x_0$ in $X$, so there exists some $cal(O)_N$ such that $x_0 in cal(O)_N$. But by construction, $x_n_k in.not cal(O)_N$ if $n_k >= N$, and we have a contradiction.
]

#theorem[If $X$ compact and Hausdorff, $X$ normal.]

#proof[
  We show that any closed set $F$ and any point $x in.not F$ can be separated by disjoint open sets. Then, the proof in the more general case follows.

  For each $y in X$, $X$ is Hausdorff so there exists disjoint open neighborhoods $cal(O)_(x y)$ and $cal(U)_(x y)$ of $x, y$ respectively. Then, ${cal(U)_(x y) | y in F}$ defines an open cover of $F$. Since $F$ closed and thus, being a subset of a compact space, compact, there exists a finite subcover $F subset.eq union.big_(i=1)^N cal(U)_(x y_(i))$. Put $cal(N) := sect.big_(i=1)^N cal(O)_(x y_i)$. This is an open set containing $x$, with $cal(N) sect union.big_(i=1)^N cal(U)_(x y_(i)) eq nothing$ hence $F$ and $x$ separated by $cal(N), union.big_(i=1)^N cal(U)_(x y_i)$.
]
== Connected Topological Spaces

#definition("Separate")[
  2 non-empty sets $cal(O)_1, cal(O)_2$ _separate_ $X$ if $cal(O)_1$, $cal(O)_2$ disjoint and $X = cal(O)_1 union cal(O)_2$.
]

#definition("Connected")[We say $X$ _connected_ if it cannot be separated.]

#remark[
  Note that if $X$ can be separated, then $cal(O)_1, cal(O)_2$ are closed as well as open, being complements of each other.
]

#proposition[
  Let $f : X-> Y$ continuous. Then, if $X$ connected, so is $f(X)$.
]

#proof[
  Suppose otherwise, that $f(X) = cal(O)_1 union.sq cal(O)_2$ for nonempty, open, disjoint $cal(O)_1, cal(O)_2$. Then, $X = f^(-1)(cal(O)_1) union.sq f^(-1)(cal(O)_2)$, and each of these inverse images remain nonempty and open in $X$, so this a contradiction to the connectedness of $X$.
]

#remark[
  On $RR$, $C subset.eq RR$ connected $<=>$ an interval $<=>$ convex.
]

#definition("Intermediate Value Property")[
  We say $X$ has the intermediate value property (IVP) if $forall f in C(X)$, $f(X)$ an interval.
]

#proposition[
  $X$ has IVP $<=>$ $X$ connected.
]

#proof[
  ($impliedby$) If $X$ connected, $f(X)$ connected in $RR$ hence an interval.

  ($=>$) Suppose otherwise, that $X = cal(O)_1 union.sq cal(O)_2$. Then define the function $f : X -> RR$ by $x |-> cases(
    1 "if" x in cal(O)_2,
    0 "if" x in cal(O)_1
  )$. Then, for every $A subset.eq RR$, $
  f^(-1) (A) = cases(
    nothing & "if" {0, 1} subset.not.eq A,
    cal(O)_1 & "if" 0 in A,
    cal(O)_2 & "if" 1 in A,
    X & "if" {0, 1} subset.eq A
  ),
  $ which are all open sets, hence $f$ continuous. But $f(X) = {0, 1}$ which is not an interval, hence the IVP fails and so $X$ must be connected.
]

#definition("Arcwise/Path Connected")[
  $X$ _arc connected/path connected_ if $forall x, y in X$, there exists a continuous function $f : [0, 1] -> X$ such that $f(0) = x, f(1) = y$.
]
#proposition[
  Arc connected $=>$ connected.
]

#proof[
  Suppose otherwise, $X = cal(O)_1 union.sq cal(O)_2$. Let $x in cal(O)_1, y in cal(O)_2$ and define a continuous function $f:[0, 1] -> X$ such that $f(0) = x$ and $f(1) = y$. Then, $f^(-1) (cal(O)_i)$ each open, nonempty and disjoint for $i = 1,2 $, but $
  f^(-1)(cal(O)_1) union.sq f^(-1)(cal(O)_2) = [0, 1],
  $ a contradiction to the connectedness of $[0, 1]$.
]

== Urysohn's Lemma and Urysohn's Metrization Theorem

We present the main lemma of this section first, but need more tools before proving it.
#lemma("Urysohn's")[Let $A, B subset.eq X$ closed and disjoint subsets of a normal space $X$. Then, $forall [a, b] subset.eq RR$, there exists a continuous function $f : [a, b]-> RR$ such that $f(X) subset.eq [a, b]$, $f|_A = a$ and $f|_B = b$.]<lemma_urysohns>

#remark[We have a partial converse of this statement as well:]

#proposition[
  Let $X$ Tychonoff and suppose $X$ satisfies the properties of Urysohn's Lemma. Then, $X$ normal.
]

#proof[
  Let $A, B$ be closed nonempty disjoint subsets. Let $f : X -> RR$ continuous such that $f|_A = 0$, $f|_B = 1$ and $0 <= f <= 1$. Let $I_1, I_2$ be two disjoint open intervals in $RR$ with $0 in I_1$ and $1 in I_2$. Then, $f^(-1) (I_1)$ open and contains $A$, and $f^(-1) (I_2)$ open and contains $B$. Moreover, $f^(-1) (I_1) sect f^(-1) (I_2) = nothing$; hence, $f^(-1) (I_1), f^(-1) (I_2)$ disjoint open neighborhoods of $A, B$ respectively, so indeed $X$ normal.
]

#definition("Normally Ascending")[
  Let $(X, cal(T))$ a topological space and $Lambda subset.eq RR$. A collection of open sets ${cal(O)_lambda}_(lambda in Lambda)$ is said to be _normally ascending_ if $forall lambda_1, lambda_2 in Lambda$, $
  overline(cal(O)_(lambda_1)) subset.eq cal(O)_(lambda_2) "if" lambda_1 < lambda_2.
  $
]

#lemma[
  Let $Lambda subset.eq (a, b)$ a dense subset, and let ${cal(O)_lambda}_(lambda in Lambda)$ a normally ascending collection of subsets of $X$. Let $f : X -> RR$ defined such that $
  f(x) =  cases(
b & "if" x in (union.big_(lambda in Lambda) cal(O)_lambda)^c \
inf{lambda in Lambda | x in cal(O)_lambda} & "else"
  ).
  $ Then, $f$ continuous.
]<lemma_urysohns_1>

#proof[
  We claim $f^(-1) (-infinity, c)$ and $f^(-1) (c, infinity)$ open for every $c in RR$. Since such sets define a subbase for $RR$, it suffices to prove continuity on these sets. We show just the first for convenience. Notice that since $f(x) in [a, b]$, if $c in (a, b)$ then $f^(-1) (-infinity, c) = f^(-1)[a, c)$, so really it suffices to show that $f^(-1)[a, c)$ open to complete the proof.

  Suppose $x in f^(-1)([a, c])$ so $a <= f(x) < c$. Let $lambda in Lambda$ be such that $a < lambda < f(x)$. Then, $x in.not cal(O)_lambda$. Let also $lambda' in Lambda$ such that $f(x) < lambda' < c$. By density of $Lambda$, there exists a $epsilon > 0$ such that $f(x) + epsilon in Lambda$, so in particular $
  overline(cal(O))_(f(x) + epsilon) subset.eq cal(O)_(lambda') => x in cal(O)_lambda',
  $ by nesting. So, repeating this procedure, we find $
  f^(-1)([a, c)) subset.eq union.big_(a <= lambda < lambda' < c) cal(O)_(lambda')\\overline(cal(O))_(lambda),
  $ noticing the set on the right is open. By similar reasoning, the opposite inclusion holds and we have equality. Hence, $f$ continuous.
]

#lemma[Let $X$ normal, $F subset.eq X$ closed, and $cal(U)$ a neighborhood of $F$. Then, for any $(a, b) subset.eq RR$, there exists a dense subset $Lambda subset.eq (a, b)$ and a normally ascending collection ${cal(O)_lambda}_(lambda in Lambda)$ such that $
F subset.eq cal(O)_lambda subset.eq overline(cal(O))_lambda subset.eq cal(U), wide forall lambda in Lambda.
$]<lemma_urysohns_2>

#remark[
  This is essentially a generalization of the nested neighborhood property, and indeed the proof essentially just uses this property repeatedly to construct the collection ${cal(O)_lambda}$.
]

#proof[
  Without loss of generality, we assume $(a, b) =(0, 1)$, for the two intervals are homeomorphic, i.e. the function $f : (0, 1) -> RR, f(x) := a(1 -x) + b x$ is continuous, invertible with continuous inverse and with $f(0) = a, f(1) = b$ so a homeomorphism. 

  Let $
  Lambda := {m/(2^n) | m, n in NN | 1 <= m <= 2^(n-1)} = union.big_(n in NN) underbrace({m/2^n | m in NN, 1 <= m <= 2^(n-1)}, =: Lambda_n),
  $ which is clearly dense in $(0, 1)$. We need now to define our normally ascending collection. We do so by defining on each $Lambda_1$ and proceding inductively. 

  For $Lambda_1$, since $X$ normal, let $cal(O)_(1\/2)$ be such that $F subset.eq cal(O)_(1\/2) subset.eq overline(cal(O))_(1\/2) subset.eq cal(U)$, which exists by the nested neighborhood property.

  For $Lambda_2 = {1/4, 3/4}$, we use the nested neighborhood property again, but first with $F$ as the closed set and $cal(O)_(1\/2)$ an open neighborhood of it, and then with $overline(cal(O))_(1\/2)$ as the closed set and $cal(U)$ an open neighborhood of it. In this way, we find $
  underbrace(F subset.eq cal(O)_(1\/4) subset.eq overline(cal(O))_(1\/4) subset.eq cal(O)_(1\/2), "nested nbhd") subset.eq overbrace(overline(cal(O))_(1\/2) subset.eq cal(O)_(3\/4) subset.eq overline(cal(O))_(3\/4) subset.eq cal(U), "nested nbhd").
  $ 

  We repeat in this manner over all of $Lambda$, in the end defining a normally ascending collection ${cal(O)_(lambda)}_(lambda in Lambda)$.
]

#proof([(Of Urysohn's Lemma, @lemma_urysohns)])[
  Let $F = A$ and $cal(U) = B^c$ as in the previous lemma @lemma_urysohns_2. Then, there is some dense subset $Lambda subset.eq (a, b)$ and a normally ascending collection ${cal(O)_(lambda)}_(lambda in Lambda)$ such that $A subset.eq cal(O)_lambda subset.eq overline(cal(O))_lambda subset.eq B^c$ for every $lambda in Lambda$. Let $f(x)$ as in the previous previous lemma, @lemma_urysohns_1. Then, if $x in B$, $B subset.eq (union.big_(lambda in Lambda) cal(O)_lambda)^c$ and so $f(x) = b$. Otherwise if $x in A$, then $x in sect.big_(lambda in Lambda) cal(O)_lambda$ and thus $f(x) = inf{lambda in Lambda} = a$. By the first lemma, $f$ continuous, so we are done.
]

#theorem("Urysohn's Metrization Theorem")[
  Let $X$ be a second countable topological space. Then, $X$ is metrizable (that is, there exists a metric on $X$ that induces the topology) if and only if $X$ normal.
]

#proof[
  ($=>$) We have already showed, every metric space is normal.

  ($impliedby$) Let ${cal(U)_n}$ be a countable basis for $cal(T)$ and put $
  A := {(n,m) in NN times NN | overline(cal(U))_n subset.eq cal(U)_m}.
  $ By Urysohn's lemma, for each $(n, m) in A$ there is some continuous function $f_(n,m) : X -> RR$ such that $f_(n, m)$ is $1$ on $cal(U)_(m)^c$ and $0$ on $overline(cal(U))_n$ (these are disjoint closed sets). For $x, y in X$, define $
  rho(x, y) := sum_((n, m) in A) 1/(2^(n +m)) |f_(n, m) (x) - f_(n, m) (y)|.
  $ The absolute valued term is $<= 2$, so this function will always be finite. Moreover, one can verify that it is indeed a metric on $X$. It remains to show that it induces the same topology; it suffices to compare bases of the two.

  Let $x in cal(U)_m$. We wish to show there exists $B_rho (x, epsilon) subset.eq cal(U)_m$. ${x}$ is closed in $X$ being normal, so there exists some $n$ such that $
  {x} subset.eq cal(U)_n subset.eq overline(cal(U))_n subset.eq cal(U)_m,
  $ so $(n, m) in A$ and so $f_(n,m) (x) = 0$. Let $epsilon = 1/(2^(n+m))$. Then, if $rho(x, y) < epsilon$, it must be $
  1/(2^(n + m)) &> sum_((n',m') in A) 1/(2^(n' + m')) |f_(n', m') (x) - f_(n',m')(y)| \ 
  & >= 1/2^(n+m) |underbrace(f_(n,m) (x), = 0) - f_(n, m) (y)| \ 
  &= 1/(2^(n + m)) |f_(n, m) (y)|,
  $ so $abs(f_(n, m) (y)) < 1$ and thus $y in.not cal(U)_m^c$ so $y in cal(U)_m$. It follow that $B_rho (x, epsilon) subset.eq cal(U)_m$, and so every open set in $X$ is open with respect to the metric topology.

  Conversely, if $B_rho (x, epsilon)$ some open ball in the metric topology, then notice that $y |-> rho(x, y)$ for fixed $y$ a continuous function, and thus $(rho(x, dot))^(-1) (-epsilon, epsilon)$ an open set in $cal(T)$ containing $x$. But this set also just equal to $B_rho (x, epsilon)$, hence $B_rho (x, epsilon)$ open in $cal(T)$. We conclude the two topologies are equal, completing the proof.
]

#remark[
  Recall metric $=>$ first countable hence not first countable $=>$ not metrizable.
]

== Stone-Weierstrass Theorem

We need to use the following theorem, which we'll prove later.

#theorem("Weierstrass Approximation Theorem")[
  Let $f : [a, b] -> RR$ continuous. Then, for every $epsilon > 0$, there exists a polynomial $p(x)$ such that $||f - p||_infinity < epsilon$.
]

#definition("Algebra, Separation of Points")[
  We call a subset $cal(A) subset.eq C(X)$ an _algebra_ if it is a linear subspace that is closed under multiplication (that is, $f, g in cal(A) => f dot g in cal(A)$).

  We say $cal(A)$ _separates points_ in $X$ if for every $x, y in X$, there exists an $f in cal(A)$ such that $f(x) eq.not f(y)$.
]

#theorem("Stone-Weierstrass")[
  Let $X$ be a compact Hausdorff space. Suppose $cal(A) subset.eq C(X)$ an algebra that separates points and contains constant functions. Then, $cal(A)$ dense in $C(X)$.
]

We tacitly assume the conditions of the theorem in the following lemmas as as not to restate them.

#lemma[For every $F subset.eq X$ closed, and every $x_0 in F^c$, there exists a neighborhood $cal(U)(x_0)$ such that $F sect cal(U) = nothing$ and $forall epsilon > 0$ there is some $h in cal(A)$ such that $h < epsilon$ on $cal(U)$, $h > 1 - epsilon$ on $F$, and $0 <= h <= 1$ on $X$.

In particular, $cal(U)$ is _independent_ of choice of $epsilon$.
]

#proof[
Our first claim is that for every $y in F$, there is a $g_y in cal(A)$ such that $g_y (x_0) = 0$ and $g_y (y) > 0$, and moreover $0 <= g_y <= 1$. Since $cal(A)$ separates points, there is an $f in cal(A)$ such that $f(x_0) eq.not f(y)$. Then, let $
g_y (x) := [(f(x) - f(x_0))/(||f - f(x)||_infinity)]^2.
$ Then, every operation used in this new function keeps $g_y in cal(A)$. Moreover one readily verifies it satisfies the desired qualities. In particular since $g_y$ continuous, there is a neighborhood $cal(O)_y$ such that $g_y|_(cal(O)_y) > 0$. Hence, we know that $F subset.eq union.big_(y in F) cal(O)_y$, but $F$ closed and so compact, hence there exists a finite subcover i.e. some $n >= 1$ and finite sequence ${y_i}_(i=1)^n$ such that $F subset.eq union.big_(i=1)^n cal(O)_(y_i)$. Let for each $y_i$ $g_y_i in cal(A)$  with the properties from above, and consider the "averaged" function $
g(x) := 1/n sum_(i=1)^n g_y_i (x) in cal(A).
$ Then, $g(x_0) = 0$, $g > 0$ on $F$ and $0 <= g <= 1$ on all of $X$. Hence, there is some $1 > c > 0$ such that $g >= c$ on $F$, and since $g$ continuous at $x_0$ there exists some $cal(U)(x_0)$ such that $g < c/2$ on $cal(U)$, with $cal(U) sect F = nothing$. So, $0 <= g|_(cal(U)) < c/2$, and $1 >= g|_(F) >= c$. To complete the proof, we need $(0, c/2) <-> (0, epsilon)$ and $(c, 1) <-> (1 - epsilon, 1)$. By the Weierstrass Approximation Theorem, there exists some polynomial $p$ such that $p|_([0, c/2]) < epsilon$ and $p|_([c, 1]) > 1 - epsilon$. Then if we let $h(x) := (p compose g) (x)$, this is just a polynomial of $g$ hence remains in $cal(A)$, and we find $
h|_(cal(U)) < epsilon, wide h|_(F) > 1 - epsilon, wide 0 <= h <= 1.
$
]


#lemma[
  For every disjoint closed set $A, B$ and $epsilon > 0$, there exists $h in cal(A)$ such that $h|_A < epsilon$, $h|_B > 1 - epsilon$, and $0 <= h <= 1$ on $X$.
]

#proof[
  Let $F = B$ as in the last lemma. Let $x in A$, then there exists $cal(U)_x sect B = nothing$ and for every $epsilon > 0$, $h|_(cal(U)_x) < epsilon$ and $h|_(B) > 1 - epsilon$ and $0<= h <= 1$. Then $A subset.eq union.big_(x in A) cal(U)_x$. Since $A$ closed so compact, $A subset.eq union.big_(i=1)^N cal(U)_(x_i)$. Let $epsilon_0 < epsilon$ such that $(1 - epsilon_0/N)^N > 1 - epsilon$. For each $i$, let $h_i in cal(A)$ such that $h_i|_(cal(U)_(x_i)) < epsilon_0/N$, $h_i|_(B) > 1 - epsilon_0/N$ and $0 <= h_i <= 1$. Then, put $
  h(x) = h_1 (x) dot h_2 (x) dots.c h_N (x) in cal(A).
  $ Then, $0 <= h <= 1$ and $h|_B > (1 - epsilon_0/N)^N > 1 - epsilon$. Then, for every $x in A$, $x in cal(U)_x_i$ so $h_i (x) < epsilon_0/N$ and $h_i (x) <= i$ so $h(x) < epsilon_0/N$ so $h|A < epsilon_0/N < epsilon$.
]

#proof[(Of Stone-Weierstrass) 
  WLOG, assume $f in C(X)$, $0 <= f <= 1$, by replacing with $
  tilde(f)(x) = (f(x) + ||f||_infinity)/(||f + ||f||_infinity||_infinity)
  $ if necessary, since if there exists a $tilde(g) in cal(A)$ such that $||tilde(f) - tilde(g)||_infinity < epsilon$, then using the properties of $cal(A)$ we can find some appropriate $g in cal(A)$ such that $||f - g||_infinity < epsilon$.

  Fix $n in NN$, and consider the set ${0, 1/n, 2/n, dots, (n - 1)/n, 1}$, and let for $1 <= j <= n$ $
  A_j := {x in X | f(x) <= (j - 1)/n}, wide B_j := {x in X | f(x) >= j/n},
  $ which are both closed and disjoint. By the lemma, there exists $g_j in cal(A)$ such that $
  g_j|_A_j < 1/n, wide g_j|_(B_j) > 1 - 1/n,
  $ with $0 <= g_j <= 1$. Let then $
  g(x) := 1/n sum_(j=1)^n g_j (x) in cal(A).
  $ We claim then $||f - g||_infinity <= 3/n$, which proves the claim by taking $n$ sufficiently large.

  Suppose $k in [1, n]$. If $f(x) <= k/n$, then $
  g_j (x) = cases(
    < 1/n & "if" j - 1 >= k \ 
    <= 1 & "else"
  ),
  $ so $
  g(x) = 1/n sum_(j=1)^n g_j (x) = 1/n [ sum_(j=1)^k g_j (x) + sum_(j=k+1)^n g_j (x)] <= 1/n [k + (n - k)/n] <= k/n + (n - k)/n^2 <= (k + 1)/n.
  $ Similarly if $f(x) >= (k - 1)/n$, then $
  g_j (x) = cases(
    > 1 - 1/n & "if" j <= k - 1 \
    >= 0 & "else"
  ),
  $so $
  g(x) >= 1/n sum_(j=1)^(k-1) (1 - 1/n) >= 1/n (k - 1) ( 1 - 1/n)  = (k - 1)/n - (k - 1)/n^2 >= (k - 2)/n.
  $ So, we've show that if $(k - 1)/n <= f (x) <= k/n$, then $(k - 2)/n <= g(x) <= (k + 1)/n$, and so repeating this argument and applying triangle inequality we conclude $||f - g||_infinity <= 3/n$.
]

#theorem("Borsuk")[
$X$ compact, Hausdorff and $C(X)$ separable $<=>$ $X$ is metrizable.
]

= Functional Analysis

Here, we will primarily work with a normed vector space (nvs). Moreover, we usually work in:

#definition("Banach Space")[
  A normed vector space $(X, ||dot||)$ is a _Banach space_ if it is complete as a metric space under the norm-induced metric.
]

== Introduction to Linear Operators

#definition("Linear Operator, Operator Norm")[
  Let $X, Y$ be vector spaces. Then, a map $T : X -> Y$ is called _linear_ if $forall x, y in X, alpha, beta in RR$, $T(alpha x+ beta y) = alpha T(x) + beta T(y)$.

  If $X, Y$ normed vector spaces, we say $T$ is a bounded linear operator if $T$ linear and the _operator norm_ $
  ||T|| = ||T||_(cal(L) (X, Y)) = sup_(x in X, \ ||x||_X <= 1) ||T x||_Y < infinity
  $ is finite. Then, we put $
  cal(L)(X, Y) := {"bounded linear operators" X -> Y}.
  $ We'll also write $cal(L)(X) := cal(L)(X, X)$.
]

#theorem("Bounded iff Continuous")[
  If $X, Y$ are nvs, $T in cal(L) (X, Y)$ iff and only if $T$ is continuous, i.e. if $x_n -> x$ in $X$, then $T x_n -> T x$ in $Y$.
]

#proof[
  If $T in cal(L)(X, Y)$, $
  ||T x_n - T x||_Y  &= ||T (x_n - x)||_Y \ 
  &= ||x_n - x||_X dot ||T(x_n - x)/(||x_n - x||_X)||_Y \ 
  &<= underbrace(||T||, < infinity) ||x_n - x||_X -> 0,
  $ hence $T$ continuous. Conversely, if $T$ continuous, then by linearity $T 0 = 0$, so by continuity, there is some $delta > 0$ such that $||T x||_Y < 1$ if $||x||_X < delta$. For $x in X$ nonzero, let $lambda = delta/(||x||_X)$. Then, $||lambda x||_X <= delta$ so $||T (lambda x)||_Y < 1$, i.e. $(|| T (x)||_Y delta)/(||x||_X) < 1$. Hence, $
  ||T|| = sup_(x in X : x eq.not 0) (|| T (x)||_Y )/(||x||_X) <= 1/delta,
  $ so $T in cal(L)(X, Y)$.
]

#proposition([Properties of $cal(L)(X, Y)$])[
  If $X, Y$ nvs, $cal(L)(X, Y)$ a nvs, and if $X, Y$ Banach, then so is $cal(L)(X,Y).$
]

#proof[
  (a) For $T, S in cal(L)(X, Y)$, $alpha, beta in RR$, and $x in X$, then $
  ||(alpha T +beta S) (x)||_Y & <= |alpha| ||T x||_Y + |beta| ||S x||_Y \ 
  & <= |alpha| ||T|| ||x||_X + |beta| ||T|| ||x||_X.
  $ Dividing both sides by $norm(x)$, we find $||alpha T + beta S|| < infinity$. The same argument gives the triangle inequality on $||dot||$. Finally, $T = 0$ iff $||T x||_Y = 0$ for every $x in X$ iff $||T|| = 0$.

  (b) Let ${T_n} subset.eq cal(L)(X, Y)$ be a Cauchy sequence. We have that $
  ||T_n x - T_m x||_Y <= ||T_n - T_m|| ||x||_X,
  $ so in particular the sequence ${T_n (x)}$ a Cauchy sequence in $Y$ for any $x in X$. $Y$ complete so this sequence converges, say $T_n (x) -> y^ast$ in $Y$. Let $T(x) := y^ast$ for each $x$. We claim that $T in cal(L)(X, Y)$ and that $T_n -> T$ in the operator norm. We check: $
  alpha T(x_1) + beta T(x_2) &= lim_(n -> infinity) alpha T_n (x_1) + lim_(n->infinity) beta T_n (x_2) \ 
  &= lim_(n->infinity) [T_n (alpha x_1) + T_n (beta x_2)] \ 
  &= lim_(n->infinity) T_n (alpha x_1 + beta x_2) \ 
  &= T(alpha x_1 + beta x_2),
  $ so $T$ linear.

  Let now $epsilon > 0$ and $N$ such that for every $n >= N$ and $k >= 1$ such that $||T_n - T_(n + k)|| < epsilon/2$. Then, $
  ||T_n (x) - T_(n + k) (x)||_Y &= norm((T_n - T_(n+k)) (x))_Y \ 
  & <= norm(T_n - T_(n+k)) norm(x)_X \ 
  & < epsilon/2 norm(x)_X.
  $ Letting $k -> infinity$, we find that $
  ||T_n (x) - T(x)||_Y < epsilon/2 ||x||_X,
  $ so normalizing both sides by $||x||_X$, we find $norm(T_n - T) < epsilon/2$, and we have convergence.
]

#definition("Isomorphism")[
  We say $T in cal(L)(X, Y)$ an _isomorphism_ if $T$ is bijective and $T^(-1) in cal(L)(Y, X)$. In this case we write $X tilde.eq Y$, and say $X, Y$ isomorphic.
]

== Finite versus Infinite Dimensional

If $X$ a nvs, then we can look for a basis $beta$ such that $"span"(beta) = X$. If $beta = {e_1, dots, e_n}$ has no proper subset spanning $X$, then we say $dim(X) = n$.

As we saw on homework, any two norms on a finite dimensional space are equivalent.

#corollary[
  (a) Any two nvs of the same finite dimension are isomorphic.

  (b) Any finite dimensional space is complete, and so any finite dimensional subspace is closed.

  (c) $overline(B)(0, 1)$ is compact in a finite dimensional space.
]

#proof[
  (a) Let $(X, ||dot||)$ have finite dimension $n$. Then, we claim $(X, ||dot||) tilde.eq (RR^n, |dot|)$. Let ${e_1, dots, e_n}$ be a basis for $X$. Let $T : RR^n -> X$ given by $
  T(x) = sum_(i=1)^n x_i e_i,
  $ where $x = (x_1, dots, x_n) in RR^n$, which is clearly linear. Moreover, $
  T x = 0 <=> sum_(i=1)^n x_i e_i = 0 <=> x = 0,
  $ so $T$ injective, and so being linear between two spaces of the same dimension gives $T$ surjective. It remains to check boundedness.

  First, we claim $x |-> ||T(x)||$ is a norm on $RR^n$. $||T (x)|| = 0 <=> x = 0$ by the injectivity of $T$, and the properties $||T(lambda x)|| = |lambda| ||T x||$ and $||T (x + y)|| <= ||T x|| + ||T y||$ follow from linearity of $T$ and the fact that $||dot||$ already a norm. Hence, $||T (dot)||$ a norm on $RR^n$ and so equivalent to $|dot|$, i.e. there exists constants $C_1, C_2 > 0$ such that $
  C_1|x| <= ||T(x)|| <= C_2|x|,
  $  for every $x in X$. It follows that $||T||$ (operator norm now) is bounded.

  Letting $T(x) = y$, we find similarly $
  C_1'||y|| <= |T^(-1) (y)| <= C_2' ||y||,
  $ so $||T^(-1)||$ also bounded. Hence, we've shown any $n$-dimensional space is isomorphic to $RR^n$, so by transitivity of isomorphism any two $n$-dimensional spaces are isomorphic.

  (b) The property of completeness is preserved under isomorphism, so this follows from the previous statement since $RR^n$ complete.

  (c) Consider $overline(B)(0, 1) subset.eq X$. Let $T$ be an isomorphism $X -> RR^n$. Then, for $x in overline(B)(0, 1)$, $||T x|| <= ||T|| < infinity$, so $T(overline(B)(0, 1))$ is a bounded subset of $RR^n$, and since $T$ and its inverse continuous, $T(overline(B)(0, 1))$ closed in $RR^n$. Hence, $T(overline(B)(0, 1))$ closed and bounded hence compact in $RR^n$, so since $T^(-1)$ continuous $T^(-1) (T (overline(B)(0, 1))) = overline(B)(0, 1)$ also compact, in $X$.
]

#theorem("Riesz's")[
  If $X$ is an nvs, then $overline(B)(0, 1)$ is compact if and only if $X$ if finite dimensional.
]<thm_rieszs>

#lemma("Riesz's")[
  Let $Y subset.neq X$ be a closed nvs (and $X$ a nvs). Then for every $epsilon > 0$, there exists $x_0 in X$ with $||x_0|| = 1$ and such that $
  ||x_0 - y||_X > epsilon forall y in Y.
  $
]
#proof[
Fix $epsilon > 0$. Since $Y subset.neq X$, let $x in Y^c$. $Y$ closed so $Y^c$ open and hence there exists some $r > 0$ such that $B(x, r) sect Y = nothing$. In other words, $
inf {||x - y'|| | y' in Y} > r > 0.
$ Let then $y_1 in Y$ be such that $
r < ||x - y_1|| < epsilon^(-1) r,
$ and take $
x_0 := (x - y_1)/(||x - y_1||_X).
$ Then, $x_0$ a unit vector, and for every $y in Y$, $
x_0 - y &= (x - y_1)/(||x - y_1||) - y \ 
&= 1/(||x - y_1||) [x - y_1 - y ||x - y_1|| ] \ 
&= 1/(||x - y_1||) [x - y'],
$ where $y' = y_1 + y ||x - y_1|| in Y$, since it is closed under vector addition. Hence $
||x_0 - y|| = 1/(||x - y_1||) ||x - y'|| > epsilon/r ||x - y'|| > epsilon,
$ for every $y in Y$.
]

#proof[(Of @thm_rieszs)
($impliedby$) By the previous corollary.


($=>$) Suppose $X$ infinite dimensonal. We will show $B:= overline(B)(0, 1)$ not compact.

_Claim:_ there exists ${x_i}_(i=1)^infinity subset.eq B$ such that $||x_i - x_j|| > 1/2$ if $i eq.not j$.

We proceed by induction. Let $x_1 in B$. Suppose ${x_1, dots, x_n} subset.eq B$ are such that $||x_i - x_j|| > 1/2$ . Let $X_n = "span"{x_1, dots, x_n}$, so $X_n$ finite dimensional hence $X_n subset.neq X$. By the previous lemma (taking $epsilon = 1/2$) there is then some $x_(n+1) in B$ such that $||x_1 - x_(n+1)|| >1/2$ for every $i = 1, dots, n$. We can thus inductively build such a sequence ${x_i}_(i=1)^infinity$. Then, every subsequence of this sequence cannot be Cauchy so $B$ is not sequentially compact and thus $B$ is not compact.
]

== Open Mapping and Closed Graph Theorems

#definition([$T$ open])[
  If $X, Y$ toplogical spaces and $ T :X -> Y$ a linear operator, $T$ is said to be _open_ if for every $cal(U) subset.eq X$ open, $T(cal(U))$ open in $Y$.

  In particular if $X, Y$ are metric spaces (or nvs), then $T$ is open iff the image of every open ball in $X$ containes an open ball in $Y$, i.e. $forall x in X, r > 0$ there exists $r' > 0$ such that $T(B_X (x, r)) supset.eq B_Y (T x, r')$. Moreover, by translating/scaling appropriately, it suffices to prove for $x = 0, r = 1$.
]

#theorem("Open Mapping Theorem")[
  Let $X, Y$ be Banach spaces and $T : X -> Y$ a bounded linear operator. If $T$ is surjective, then $T$ is open.
]

#proof[
Its enough to show that there is some $r > 0$ such that $T (B_X (0, 1)) supset.eq B_Y (0, r)$.

_Claim:_ $exists c > 0$ such that $overline(T(B_X (0, 1))) supset.eq B_Y (0, 2 c)$. 

Put $E_n = n dot overline(T(B_X (0, 1)))$ for $n in NN$. Since $T$ surjective, $union.big_(n=1)^infinity E_n = Y$. Each $E_n$ closed, so by the Baire Category Theorem there exists some index $n_0$ such that $E_n_0$ has nonempty interior, i.e. $
"int"(overline(T(B_X (0, 1)))) eq.not nothing,
$ where we drop the index by homogeneity. Pick then $c > 0$ and $y_0 in Y$ such that $B_Y (y_0, 4 c) subset.eq overline(T(B_X (0, 1)))$. We claim then that $B_Y (-y_0, 4 c) subset.eq overline(T(B_X (0, 1)))$ as well. Indeed, if $B_Y (y_0, 4 c) subset.eq overline(T(B_X (0, 1)))$, then $forall tilde(y) in Y$ with $||y_0 - tilde(y)||_Y < 4 c$, 
// TODO not sure about this partial
Then, $||-y_0 + tilde(y)||_Y < 4 c$ so $- tilde(y) in B_Y (-y_0, 4 c)$. But $tilde(y) =lim_(n->infinity) T(x_n)$ and so $- tilde(y) = lim_(n->infinity) T(- x_n)$. Since ${-x_n} subset.eq B_X (0, 1)$, this implies $- tilde(y) in overline(T(B_X (0, 1)))$ hence the "subclaim" holds.

Now, for any $tilde(y) in B_Y (0, 4 c)$, $||tilde(y)|| <= 4 c$ so $
tilde(y) = y_0 underbrace(- y_0 + tilde(y), in B_Y (-y_0, 4 c)) = overbrace(y_0 + tilde(y), in B(y_0, 4 c)) - y_0.
$ Therefore, $
B_Y (0, 4c) &= B_Y (y_0 - y_0, 4 c) \ 
& subset.eq B_Y (y_0, 4 c) + B_Y (-y_0, 4c) \ 
& overline(T(B_X (0, 1))) + overline(T(B_X (0, 1))) = 2 overline(T(B_X (0, 1))),
$ (where summation of two sets is the vector addition of all the elements in the sets), hence $B_Y (0, 2 c) subset.eq overline(T(B_X (0, 1)))$.

We claim next that $T(B_X (0, 1)) supset.eq B_Y (0, c)$. Choose $y in Y$ with $||y||_Y <c$. By the first claim, $B_Y (0, c) subset.eq overline(T(B_X (0, 1/2)))$, so for every $epsilon > 0$ there is some $z in X$ with $||z||_X < 1/2$ and $||y - T z||_Y < epsilon$.
// TODO is this by continuity?
Let $epsilon = c/2$ and $z_1 in X$ such that $||z_1||_X <1/2$ and $||y - T z_1||_Y < c/2$. But the first claim can also be written as $B_Y (0, c/2) subset.eq overline(T(B_X (0, 1/4)))$ so if $epsilon = c/4$, let $z_2 in X$ such that $||z_2||_X < 1/4$ and $||(y - T z_1 ) - T z_2||_Y < c/4$. Continuing in this manner we find that $
B_Y (0, c/(2^k)) subset.eq overline(T(B_X (0, 1/(2^(k+1))))),
$ so exists $z_k in X$ such that $||z_k||_X < 1/(2^k)$ and $||y - T(z_1 + dots.c + z_k)||_Y < c/(2^k)$. Let $x_n = z_1 + dots.c + z_n in X$. Then ${x_n}$ is Cauchy in $X$, since $
||x_n - x_m||_X <= sum_(k=m)^n ||z_k||_X < sum_(k=m)^n 1/2^k -> 0.
$ Since $X$ a Banach space, $x_n -> overline(x)$ and in particular $||overline(x)|| <= sum_(k=1)^infinity ||z_k||_X < sum_(k=1)^infinity 1/(2^k) = 1$, so $overline(x) in B_X (0, 1)$. Since $T$ bounded it is continuous, so $T x_n -> T overline(x)$, so $y = T overline(x)$ and thus $B_Y (0, c) subset.eq T(B(0, 1))$.
]

#corollary[
  Let $X, Y$ Banach and $T : X -> Y$ be bounded, linear and bijective. Then, $T^(-1)$ continuous.
]

#corollary[
  Let $(X, ||dot||_1), (X, ||dot||_2)$ be Banach spaces. Suppose there exists $c > 0$ such that $||x||_2 <= C||x||_1$ for every $x in X$. Then, $||dot||_1, ||dot||_2$ are equivalent.
]

#proof[
  Let $T$ be the identity linear operator and use the previous corollary.
]

#definition([$T$ closed])[
  If $X, Y$ are nvs and $T$ is linear, the _graph_ of $T$ is the set $
  G(T) = {(x, T x) | x in X} subset.eq X times Y.
  $ We then say $T$ is _closed_ if $G(T)$ closed in $X times Y$.
]

#remark[Since $X, Y$ are nvs, they are metric spaces so first countable, hence closed $<->$ contains all limit points.

In the product topology, a countable base for $X times Y$ at $(x, y)$ is given by $
{B_X (x, 1/n) times B(y, 1/m)}_(n, m in NN).
$ Then, $G(T)$ closed iff $G(T)$ contains all limit points. How can we put a norm on $X times Y$ that generates this product topology? Let $
||(x,y)||_1 := ||x||_X + ||y||_Y.
$ If $(x_n, y_n) -> (x, y)$ in the product topology, then since $Pi_1, Pi_2$ continuous maps, $(x_n, y_n) -> (x, y)$ in the $||dot||_1$ topology. On the other hand if $(x_n, y_n) -> (x, y)$ in the $||dot||_1$ norm, then $
||x_n - x||_X <= ||(x_n, y_n) - (x, y)||_1,
$ hence since the RHS $-> 0$ so does the LHS and so $x_n -> x$ in $||dot||_X$; similar gives $y_n -> y$ in $||dot||_Y$. From here it follows that $(x_n, y_n) -> (x, y)$ in the product topology.

So, to prove $G(T)$ closed, we just need to prove that if $x_n -> x$ in $X$ and $T x_n -> y$, then $y = T x_n$.
]

// What norm do we put on $X times Y$? $||(x, y)||_2 = ||x|| + ||y||$. Then if $(x_n, y_n) -> (x, y)$ in the product topology, then since the projection maps are continuous $x_n -> x, y_n -> y$ in the respective topologies on $X, Y$. On the other hand if $(x_n, y_n)$

// // TODO
// So, to prove $G(T)$ is closed we just need to prove that if $x_n -> x$ in $X$ and $T x_n -> y$ in $Y$, then $y = T x$.


// #remark[
//   If $T$ is continuous, then $G(T)$ is closed. The converse?
// ]

#theorem("Closed Graph Theorem")[
  Let $X, Y$ be Banach spaces and $T : X-> Y$ linear. Then, $T$ is continuous iff $T$ is closed.
]

#proof[
  ($=>$) Immediate from the above remark.

($impliedby$) Consider the function $
x |-> ||x||_ast := ||x||_X + ||T x||_Y.
$ So by the above, $T$ closed implies $(X, ||dot||_ast)$ is complete, i.e. if $x_n -> x$ in $||dot||_ast$ in $X$ iff $x_n -> x$ in $norm(dot)_X$ and $T x_n -> T x$ in $norm(dot)_Y$. However, $||dot||_X <= norm(dot)_ast$, hence since $(X, norm(dot)_X)$ and $(X, norm(dot)_ast)$ are Banach spaces, by the corollary, there is some $C > 0$ such that $norm(dot)_ast <= C norm(dot)_X$. So, $
norm(x)_X + norm(T x)_Y <= C norm(x)_X,
$ so $
norm(T x)_Y <= norm(x)_X + norm(T x)_Y <= C norm(x)_X,
$ so $T$ bounded and thus continuous.
  // ($impliedby$) Suppose $T$ closed and consider the function $x -> ||x||_ast$, where $||x||_ast := ||x||_X + ||T x||_Y$. Then, $T$ closed implies $(X, ||dot||_ast)$ is complete, i.e. $x_n -> x$ under $||dot||_ast$ iff $x_n -> x$ and $T x_n -> T x$. However, $||dot||_X <= ||dot||_ast$ on $X$, and so since $(X, ||dot||_X)$, $(X, ||dot||_ast)$ are both Banach spaces, by the corollary, there is $c > 0$ such that $||dot||_ast <= C ||dot||_X$, hence $
  // ||x||X + ||T x||_Y <= C ||c||_X,
  // $ and hence $
  // ||T x||_Y <= ||x||_X + ||T x||_Y <= C ||x||_X,
  // $ so $T$ is bounded and thus $T$ continuous.
]

#remark[
  The Closed Graph Theorem simplifies proving continuity of $T$. It tells us we can assume if $x_n -> x$, ${T x_n}$ Cauchy so $exists y$ such that $T x_n -> y$ since $Y$ is Banach. So, it suffices to check that $y = T x$ to check continuity; we don't need to check convergence of $T x_n$.
]

== Uniform Boundedness Principle

Recall the following consequence of the Baire Category Theorem: #theorem[
  Let $cal(F) subset.eq C(X)$ where $(X, rho)$ a complete metric space. Suppose $cal(F)$ pointwise bounded. Then, there exists a nonempty open set $cal(O) subset.eq X$ such that there is some $M > 0$ such that $|f (x)| <= M$ for every $x in cal(O), f in cal(F)$.
] This leads to the following result:

#theorem("Uniform Boundedness Principle")[
  Let $X$ a Banach space and $Y$ a nvs. Consider $cal(F) subset.eq cal(L)(X, Y)$. Suppose $cal(F)$ is pointwise bounded, i.e. for every $x in X$, there is some $M_x > 0$ such that $
  norm(T x)_Y <= M_x, forall T in cal(F).
  $ Then, $cal(F)$ is uniformly bounded, i.e. $exists M > 0$ such that $
  ||T||_Y <= M, forall T in cal(F).
  $
]

#proof[
  For every $T in cal(F)$, let $f_T : X -> RR$ be given by $
  f_T (x) = ||T x||_Y.
  $ Since $T in cal(L)(X, Y)$, $T$ is continuous, so $x_n ->_X x => T x_n ->_Y T x$, hence $norm(T x_n)_Y -> norm(T x)_Y$ so $f_T$ continuous for each $T$ i.e. $f_T in C(X)$, so ${f_T} subset.eq C(X)$ pointwise bounded. So by the previous theorem, there is some ball $B(x_0, r) subset.eq X$ and some $K > 0$ such that $norm(T x) <= K$ for every $x in B(x_0, r)$ and $T in cal(F)$. Thus, for every $x in B(0, r)$, $
  norm(T x) &= norm(T (x - x_0 + x_0))\
   &<= norm(T underbrace((x - x_0), in B(x_0, r))) + norm(T x_0) \ 
   &<= K + M_x_0, wide forall x in B(0, r), T in cal(F).
  $ Thus, for every $x in B(0, 1)$, $
  norm(T x) = 1/r norm(T underbrace((r x), in B(0, r))) <= 1/r (K + M_x_0) =: M,
  $ so its clear $norm(T) <= M$ for every $T in cal(F)$.
]

#theorem("Banach-Saks-Steinhaus")[
  Let $X$ a Banach space and $Y$ a nvs. Let ${T_n} subset.eq cal(L)(X, Y)$. Suppose for every $x in X$, $lim_(n->infinity) T_n (x)$ exists in $Y$. Then, 

a. ${T_n}$ are uniformly bounded in $cal(L)(X, Y)$;\

b. For $T : X -> Y$ defined by $
T (x) := lim_(n -> infinity) T_n (x),
$ we have $T in cal(L)(X, Y)$;\

c. $norm(T) <= liminf_(n->infinity) norm(T_n)$ (_lower semicontinuity result_).
]

#proof[
  (a) For every $x in X$, $T_n (x) -> T(x)$ so $norm(T x) < infinity$ hence $sup_n norm(T_n x) < infinity$. By uniform boundedness, then, we find $sup_n norm(T) =: C < infinity$.

  (b) $T$ is linear (by linearity of $T_n$). By (a), $
  norm(T_n x) <= C norm(x),
  $ for every $n, x$, so $
  norm(T x) <= C norm(x) forall x in X,
  $ so $T$ bounded.

  (c) We know $
  norm(T_n x) <= norm(T_n) norm(x) forall x in X,
  $ so $
  norm(T_n x)/(norm(x)) <= norm(T_n),
  $ so $
  liminf_(n) norm(T_n x)/(norm(x)) = (norm(T x))/(norm(x)) <= liminf_n norm(T_n),
  $ so by "suping" both sides, $
  norm(T) <= liminf_(n) norm(T_n).
  $
]

#remark[
  - We do note have $T_n -> T$ in $cal(L)(X, Y)$ i.e. with respect to the operator norm.
  - If $Y$ is a Banach space, then $lim_(n->infinity) T_n (x)$ exists in $Y$ $<=>$ ${T_n x}$ Cauchy in $Y$ for every $x in X$.
]

== Introduction to Hilbert Spaces

#definition("Inner Product")[
  An _inner product_ on a vector space $X$ is a map $(dot, dot) : X times X -> RR$ such that for every $lambda, mu in RR$ and $x, y, z in X$,
  - $(lambda x + mu y, z) = lambda (x, z) + mu (y, z)$;
  - $(x, y) = (y, x)$;
  - $(x, x) >= 0$ and $(x, x) = 0 <=> x = 0$.
]

#remark[
  The first and second conditions combined imply that $(dot, dot)$ actually _bilinear_, namely, linear in both coordinates.
]

#remark[
  An inner product induces a norm on a vector space by $
  norm(x) := (x, x)^(1/2).
  $
]

#proposition("Cauchy-Schwarz Inequality")[
  Any inner product satisfies Cauchy-Schwarz, namely, $
  abs((x, y)) <= norm(x) norm(y),
  $ for every $x, y in X$.
]
#proof[
Suppose first $y = 0$. Then, the right hand side is clearly 0, and by linearity $(x, y) = 0$, hence we have $0 <= 0$ and are done. Suppose then $y eq.not 0$. Then, let $z = x - ((x, y))/((y,y))y$ where $y eq.not 0$. Then, $
0 <= norm(z)^2 &= (x - ((x, y))/((y,y))y, x - ((x, y))/((y,y))y) \ 
&= (x,x) - ((x,y))/((y,y)) (x, y) - ((x, y))/((y,y))(y, x) + (x, y)^2/((y,y)^2) (y,y) \ 
&= (x,x) - (2 ((x, y))^2)/((y,y))+ ((x, y)^2)/((y,y)) \ 
&= norm(x) - ((x, y)^2)/((y,y))\ 
&=> ((x, y)^2)/((y,y)) <= norm(x) =>  (x, y)^2 <= norm(x)^2norm(y)^2 \
&=> |(x, y)| <= norm(x)norm(y).
$
]

#corollary[
  The function $norm(x) := (x,x)^(1/2)$ is actually a norm on $X$.
]

#proof[
  By definition, $norm(x) >= 0$ and equal to zero only when $x = 0$. Also, $
  norm(lambda x)  = (lambda x, lambda x)^(1/2) = abs(lambda)(x,x)^(1/2) = abs(lambda) norm(x).
  $ Finally, $
  norm(x + y)^2 &= (x + y, x + y) \
  &= (x, x) + 2 (x, y) + (y, y) \ 
  &= norm(x)^2  + norm(y)^2+ 2(x, y) \
  "by Cauchy-Schwarz"wide& <=  norm(x)^2 + norm(y)^2 + 2 norm(x) norm(y) \ 
  &= (norm(x) + norm(y))^2,
  $ hence by taking square roots we see $norm(x + y) <= norm(x) + norm(y)$ as desired.
]

#proposition("Parallelogram Law")[
Any inner product space satisfies the following: $
norm(x + y)^2 + norm(x - y)^2 = 2norm(x)^2 + 2 norm(y)^2.
$
]

#corollary[
  $(dot, dot)$ is continuous, i.e. if $x_n -> x$ and $y_n -> y$, then $(x_n, y_n) -> (x, y)$.
]

#proof[
  $
  abs((x_n, y_n) - (x, y)) &= abs((x_n, y_n) - (x, y_n) + (x, y_n) - (x, y)) \ 
  &= abs((x_n - x, y_n) + (x, y_n - y)) \ 
  & <= abs((x_n - x, y_n)) + abs((x, y_n - y)) \ 
  "(Cauchy-Schwarz)"wide & <= underbrace(norm(x_n - x), -> 0)underbrace(norm(y_n), <= M) + norm(x) underbrace(norm(y_n - y), -> 0) -> 0.
  $
]

#definition("Hilbert Space")[
A _Hilbert Space_ $H$ is a complete inner product space, namely, it is complete with respect to the norm induced by the inner product.
]

#example[
  1. $ell^2$, the space of square-summable real-valued sequences, equipped with inner product $(x, y) = sum_(i=1)^infinity x_i y_i$.
  2. $L^2$, with inner product $(f, g) = integral f(x) g(x) dif x$.
]

#definition("Orthogonality")[
  We say $x, y$ _orthogonal_ and write $x perp y$ if $(x, y) = 0$. If $M subset.eq H$, then the _orthogonal complement_ of $M$, denoted $M^perp$, is the set $
  M^perp = {y in H | (x, y) = 0,  forall x in M}.
  $
]

#remark[
  $M^perp$ is always a closed subspace of $H$. If $y_1, y_2 in M^perp$, then for every $x in M$, $
  (x, alpha y_1 + beta y_2) = alpha (x, y_1) + beta (x, y_2) = 0,
  $ so $M^perp$ a subspace.

  If $y_n -> y$ in the norm on $H$ and ${y_n} subset.eq M^perp$, then using the continuity of $(dot, dot)$, we know that for every $x in M$, $(x, y_n) -> (x, y)$. But the $(x, y_n) = 0$ for every $n$ and thus $(x, y) = 0$ so $y in M^perp$, hence $M^perp$ closed.
]

#proposition[
  If $M subset.neq H$ is a closed subspace, then every $x in H$ has a unique decomposition $
x = u + v, wide u in M, v in M^perp.
  $ Hence, we may write $H = M plus.circle M^perp$. Moreover, $
  norm(x - u) = inf_(y in M) norm(x - y), wide norm(x - v) = inf_(y in M^perp) norm(x - y).
  $
]
#proof[
Let $x in H$. If $x in M$, we're done with $u = x, v = 0$. Else, if $x in.not M$, then we claim that there is some $u in M$ such that $norm(x - u) = inf_(y in M) norm(x - y) =: delta > 0$. By definition of the infimum, there exists a sequence ${u_n} subset.eq M$ such that $
norm(x - u_n)^2 <= delta^2 + 1/n.
$ Let $overline(x) := u_m - x$, $overline(y) = u_n - x$. By the Parallelogram Law, $
norm(overline(x) - overline(y))^2 + norm(overline(x) + overline(y))^2 = 2 norm(overline(x))^2 + 2 norm(overline(y))^2
$ hence $
norm(u_m - u_n)^2 + norm(u_m + u_n - 2 x)^2 = 2 norm(u_m - x)^2 + 2 norm(u_n - x)^2.
$ Now, the second term can be written $
norm(u_m + u_n - 2 x)^2  = 4 norm((u_m + u_n)/2  - x)^2,
$ hence we find $
norm(u_m - u_n)^2 = 2 norm(u_m-x)^2 + 2 norm(u_n - x)^2 - 4 norm((u_m + u_n)/2  - x)^2.
$ Recall that $M$ a subspace, hence $1/2 (u_m + u_n) in M$ so $norm(x - 1/2 (u_m + u_n)) >= delta$ as defined before. Thus, we find that by our choice of ${u_n}$, $
norm(u_m - u_n)^2 &<= 2( delta^2 + 1/m) + 2(delta^2 + 1/n) - 4 delta^2 = 2/m + 2/n,
$ and thus, by making $m, n$ sufficiently large we can make $norm(u_m - u_n)$ arbitrarily small. Hence, ${u_n} subset.eq M$ are Cauchy. $H$ is complete, hence the ${u_n}$'s converge, and thus since $M$ closed, $
u_n -> u in M.$ Then, we find $
norm(x - u) &<=  norm(x - u_n) + norm(u_n - u) \ 
& <= underbrace((delta^2 + 1/n)^(1/2), -> delta) + underbrace(norm(u_n - u), -> 0) -> delta. 
$ But also, $u in M$ and thus $norm(x - y) >= delta$, and we conclude $norm(x - u) = delta = inf_(y in M) norm(x - y)$.

Next, we claim that if we define $v = x - y$, then $v in M^perp$. Consider $y in M$, $t in RR$, then $
norm(x - underbrace((u - t y), in M))^2 &= norm(v + t y)^2 = norm(v)^2 + 2 t (v, y) + t^2 norm(y)^2.
$ Then, notice that the map $
t |-> norm(v + t y)^(2)
$ is minimized when $t = 0$, since $norm(x - z)$ for $z in M$ is minimized when $z = u$, as we showed in the previous part, so equivalently $norm(x - (u  - t y))^2$ minimized when $t = 0$.
Thus, 
$
0 = partial/(partial t) norm(v + t y)^(2)|_(t=0) &=  partial/(partial t) [norm(v)^2 + 2 t (v, y) + t^2 norm(y)^2]_(t=0) \ 
&= (2 (v, y) + 2 t norm(y)^2)_(t = 0) = (v, y) \
&=> (v, y) = 0 forall y in M => v in M^perp.
$ So, $x = u + v$ and $u in M, v in M^perp$. For uniqueness, suppose $x = u_1 + v_1 = u_2 + v_2$. Then, $u_1 - u_2 = v_2 - v_1$, but then $
norm(v_2 - v_1)^2 = (v_2 - v_1, v_2 - v_1) = (v_2 - v_1, u_2 - u_1) = 0,
$ so $v_2 = v_1$ so it follows $u_2 = u_1$ and uniqueness holds.
]

#definition([Dual of $H$])[
  The _dual_ of $H$, denoted $H^ast$, is the set $
  H^ast := {f : H -> RR | f "continuous and linear"}.
  $ On this space, we may equip the operator norm $
  norm(f)_(H^ast) = norm(f) = sup_(x in H) (abs(f (x)))/(norm(x)_H) = sup_(norm(x) <= 1) abs(f(x)).
  $
]

#example[
  For $y in H$, let $f_y : H -> RR$ be given by $f_y (x) = (x, y)$. By CS, $
  norm(f_y)_(H^ast) &= sup_(norm(x) <= 1) (x, y)  <= sup_(norm(x) <= 1) norm(x) norm(y)  <= norm(y).
  $ Also, if $y eq.not 0$, then $
  f_y (y/(norm(y))) = (y/(norm(y)), y) = norm(y).
  $ Thus, $norm(f_y)_(H^ast) = norm(y)_(H)$. It turns out all such functionals are of this form.
]

#theorem("Riesz Representation for Hilbert Spaces")[
  If $f in H^ast$, there exists a unique $y in H$ such that $f(x) = (x, y)$ for every $x in X$.
]

#proof[
  We show first existence. If $f equiv 0$, then $y = 0$. Otherwise, let $M = {x in X | f(x) = 0}$, so $M subset.neq H$. $f$ linear, so $M$ a linear subspace. $f$ is continuous, so in addition $M$ is closed. By the previous theorem, $M^perp eq.not {0}$. Let $z in M^perp$ of norm $1$.

  Fix $x in H$, and define $
  u := f(x) z - f(z) x.
  $ Then, notice that by linearity $
  f(u)= f(x) f(z) - f(z) f(x) = 0, 
  $ so $u in M$. Thus, since $z in M^perp$, $(u, z) = 0$, so in particular, $
  (u, z) = 0 &= (f(x) z - f(z) x - z) \ 
  &= f(x)(z,z) - f(z) (x, z) \ 
  &= f(x) norm(z)^2 - (x,  f(z) z) \
  &= f(x) - (x, f(z) z),
  $ hence, rearranging we find $
  f(x) = (x, f(z) z),
  $ and thus letting $y = f(z) z$ completes the proof of existence, noting $z$ independent of $x$.

  For uniqueness, suppose $(x, y) = (x, y')$ for every $x in X$. Then, $(x, y - y') = 0$ for every $x in X$, hence letting $x = y - y'$ we conclude $(y - y', y - y') = 0$ thus $y - y' = 0$ so $y = y'$, and uniquness holds.
]

#definition("Orthonormal Set")[
  A collection ${e_j} subset.eq H$ is _orthonormal_ if $(e_i, e_j) = delta_(i)^j$.
]

#remark[
The following section writes notations assuming $H$ has a countable. However, for more general Hilbert spaces, all countable summations can be replaced with uncountable ones in which only countably many elements are nonzero. The theory is very similar.
]

#definition("Orthonormal Basis")[
  A collection ${e_j} subset.eq H$ is an _orthonormal basis_ for $H$ if ${e_j}$ is an orthonormal set, and $x = sum_(j=1)^infinity (x, e_j) e_j$ for every $x in H$, in the sense that $
  norm(x - sum_(j=1)^N (x, e_j) e_j) -> 0, wide N -> infinity.
  $
]

#theorem("General Pythagorean Theorem")[
  If ${e_j}_(j=1)^infinity subset.eq H$ are orthonormal and ${alpha_i}_(i=1)^infinity subset.eq RR$ are orthonormal, then for any $N$, $
  norm(sum_(i=1)^N alpha_i e_i)^2 = sum_(i=1)^N abs(alpha_i)^2.
  $
]


#proof[
  $
  norm(sum_(i=1)^N alpha_i e_i)^2 &= (sum_(i=1)^N alpha_i e_i,sum_(j=1)^N alpha_j e_j)  = sum_(i=1)^N sum_(j=1)^N alpha_i alpha_j underbrace((e_i, e_j), = delta_(i)^j) = sum_(i=1)^N alpha_i^2.
  $
]

We can also #link("https://notes.louismeunier.net/Algebra%202/algebra2.pdf#page=75", "Gram-Schmidt") in infinite-dimensional Hilbert spaces. Let ${x_i} subset.eq H$. Let $
e_1 = x_1/(norm(x_1)),
$ and inductively, for any $n >= 2$, define $
v_N = x_N - sum_(i=1)^(N-1) (x_N, e_i) e_i.
$ Then, for any $N$, $"span"(v_1, dots, v_N) = "span"(e_1, dots, e_N)$, and for any $j < N$, $
(v_N, e_j) = (x_N, e_j) - sum_(i=1)^N (x_N, e_i) (e_i, e_j) = (x_N, e_j) - (x_N, e_j) = 0.
$ Let then $e_N = v_N/(norm(v_N))$. Then, ${e_i}_(i=1)^infinity$ will be orthonormal; we discuss how to establish when this set will actually be a basis to follow.

#theorem("Bessel's Inequality")[
  If ${e_i}_(i=1)^infinity$ are orthonormal, then for any $x in H$, $
  sum_(i=1)^infinity abs((x, e_i))^2 <= norm(x)^2.
  $
]

#proof[
  We have $
  0 &<= norm(x - sum_(i=1)^N (x, e_i) e_i)^2 \ 
  &= (x - sum_(i=1)^N (x, e_i) e_i, x - sum_(j=1)^N (x, e_j) e_j) \ 
  &= norm(x) - 2 sum_(i=1)^N (x, e_i)^2+ sum_(i=1)^N (x, e_i)^2 \ 
  &= norm(x) - sum_(i=1)^N (x, e_i)^2,
  $ so $sum_(i=1)^N (x, e_i)^2 <=  norm(x)$; letting $N -> infinity$ proves the desired inequality, since the RHS is independent of $N$.
]

#theorem[
  If ${e_i}_(i=1)^infinity$ are orthonormal, then TFAE: 

  (a) completeness: if $(x, e_i) = 0$ for every $i$, then $x = 0$, the zero vector;

  (b) Parseval's identity holds: $norm(x)^2 = sum_(i=1)^infinity (x, e_i)^2$ for every $x in H$;

  (c) ${e_i}_(i=1)^infinity$ form a basis for $H$, i.e. $x = sum_(i=1)^infinity (x, e_i) e_i$ for every $x in H$.
]

#proof[
 ((a) $=>$ (c))  By Bessel's, $sum_(i=1)^infinity (x, e_i)^2 <= norm(x)^2$. So, for any $M >= N$, $
  norm(sum_(i=N)^M (x, e_i) e_i)^2 = sum_(i=N)^M (x, e_i)^2,
  $ which must converge to zero as $N, M -> infinity$, since the whole series converges (being bounded). Hence, ${sum_(i=1)^N (x, e_i) e_i}_(N)$ is Cauchy in $norm(dot)$ and since $H$ complete, $sum_(i=1)^N (x, e_i) e_i$ converges in $H$. Putting $y = x - sum_(i=1)^infinity (x, e_i) e_i$, we find $
  (y, e_i) = (x, e_i ) - (x, e_i) = 0 forall i,
  $ hence by assumption in $(a)$,  it follows that $y = 0$ so $x = sum_(i=1)^infinity (x, e_i) e_i$ and thus ${e_i}$ a basis for $H$ and $(c)$ holds.

  ((c) $=>$ (b)) Since $x = sum_(i=1)^infinity (x, e_i) e_i$, then, $
  norm(x)^2 - sum_(i=1)^N (x, e_i)^2 = norm(x - sum_(i=1)^N (x, e_i) e_i)^2 -> 0
  $ as $N->infinity$, hence $norm(x)^2 = sum_(i=1)^infinity (x, e_i)^2$.

  ((b) $=>$ (a)) If $(x, e_i) = 0$ for every $i$, then by Parseval's $norm(x)^2 = sum_(i=1)^infinity 0 = 0$ so $x = 0$.
]

#remark[
  (a) is equivalent to $"span"(e_1, e_2, dots,)$ is _dense_ in $H$.
]

#theorem[Every Hilbert space has an orthonormal basis.]

#proof[
  Let $cal(F) = {"orthonormal subsets of" H}$. $cal(F)$ can be (partially) ordered by inclusion, as can be upper bounded by the union over the whole space. By Zorn's Lemma, there is a maximal set in $cal(F)$, which implies completeness, (a).
]

#proposition[
  $H$ is separable iff $H$ has a countable basis.
]

#proof[
  ($impliedby$) If $H$ has a countable basis ${e_j}$, $"span"_QQ {e_j}$ is a countable dense set.

($=>$) If $H$ is separable, let ${x_n}$ be a countable dense set. Use Gram-Schmidt, to produce a countable, orthonormal set, which is dense and hence a (countable) basis for $H$.
]

#remark[
  All this can be extended to uncountable bases.
]

== Adjoints, Duals and Weak Convergence (for Hilbert Spaces)

First consider $T : H -> H$ bounded and linear. Fix $y in H$. We claim that the map $
x |-> (T(x), y)
$ belongs to $H^ast$, namely is bounded and linear. Linearity is clear since $T$ linear. We know by Cauchy-Schwarz that $
abs((T(x), y)) <= norm(T (x)) norm(y) <= norm(T)norm(x) norm(y) <= C norm(x),
$ so indeed $x |-> (T(x), y) in H^ast$. By Riesz Representation Theorem, there is some unique $z in H$ such that $
(T(x), y) = (x, z) forall x in H.
$
This motivates the following.
#definition([Adjoint of $T$])[
  Let $T^ast : H -> H$ be defined by $
  (T x, y) = (x, T^ast y), forall x, y in H.
  $
]

#remark[
  In finite dimensions, $T$ can be identified with some $n times n$ matrix, in which case $T^ast = T^t$, the transpose of $T$; namely $T x dot b = x dot T^t b$.
]

#proposition[
  If $T in cal(L)(H):= cal(L)(H, H)$, then $T^ast in cal(L)(H)$ and $norm(T^ast) = norm(T)$.
]

#proof[
  Linearity of $T^ast$ is clear. Also, for any $norm(y) <= 1$, $
  norm(T^ast y)^2 = (T^ast y, T^ast y) = (T T^ast y, y) <= norm(T) norm(T^ast (y)) norm(y)
  $ so $norm(T^ast y) <= norm(T)$ for all $norm(y) = 1$. so $norm(T^ast) <= norm(T)$ hence $T^ast in cal(L)(H)$. But also, if $x in H$ with $norm(x) = 1$, then symmetrically, $
  norm(T x)^2 = (T x, T x) = (x, T^ast T x) <= norm(T^ast) norm(T x)
  $ so similarly $norm(T) <= norm(T^ast)$ hence equality holds.
]

#proposition[
  $(T^ast)^ast = T$.
]

#proof[
  On the one hand, $
  (T^ast y, x) = (y, (T^(ast))^ast x) = ((T^ast)^ast x, y)
  $ while also $
  (T^ast y, x) = (x, T^ast y) = (T x, y)
  $ so $(T x, y) = ((T^ast)^ast, y)$, from which it follows that $T = T^(ast ast)$.
]

#proposition[
  $(T + S)^ast = T^ast + S^ast$, and $(T compose S)^(ast) = S^ast compose T^ast$.
]

We'll write $N(T)$ for the nullspace/kernel of $T$, and $R(T)$ for the range/image of $T$.
#proposition[
  Suppose $T in cal(L)(H)$. Then, 
  - $N(T^ast) = R(T)^perp$ (and hence, if $R(T)$ closed, $H = N(T^ast) plus.circle R(T)$);
  - $N(T) = R(T^ast)^perp$ (and hence, if $R(T^ast)$ closed, $H = N(T) plus.circle R(T^ast)$).
]

#proof[
$N(T^ast) = {y in H : T^ast y = 0}$, so if $y in N(T^ast)$, $(T x, y) = (x, T^ast y) = (x, 0) = 0$, which holds iff $y$ orthogonal to $T x$, and since this holds for all $x in H$, $y in R(T)^perp$.

Then, if $R(T)$ closed, the by orthogonal decomposition we'll find $H = R(T) plus.circle R(T)^perp = R(T) plus.circle N(T^ast)$.

The other claim follows similarly.
]

#remark[
  Recall that $R(T)^perp$ is closed; hence $
  (R(T)^perp)^perp = {z in H | (y, z) = 0 forall y in R(T)^perp},
  $ and is also closed; hence $(R(T)^perp)^perp = overline(R(T))$ thus equivalently $N(T^ast)^perp = overline(R(T))$.
]

#remark[
  By the Closed Graph Theorem, $T$ linear and bounded gives $T$ closed; namely, the graph of $T$ closed; this is _not_ the same as saying the range of $T$ closed.
]

#example[
  Consider $C([0, 1]) subset.eq L^2 ([0, 1])$, and $T : C([0, 1]) -> L^2 ([0, 1])$ given by the identity, $T f = f$. Then, $T$ is bounded, but $R(T) = C([0, 1])$; this subspace is _not_ closed in $L^2 ([0, 1])$, since there exists sequences of continuous functions that converge to an $L^2$, but not continuous, function.
]

#remark[
  The prior theorem is key in "solvability", especially if $T$ a differential or integral operator. If we wish to find $u$ such that $T u = f$, we need that $f in R(T)$, hence $f in N(T^ast)^perp$.
]

#example[
Let $M subset.neq H$ a closed linear subspace. Then, $H = M plus.circle M^perp$; define the projection operator $
P : H -> H, wide x = u + v in M plus.circle M^perp |-> u.
$ This means, in particular, $x = P x + (id - P) x$. We claim $P in cal(L)(H)$, $norm(P) = 1$, $P^2 = P$, and $P^ast = P$.

Linearity is clear. To show $P^2 = P$, write $x = P x + v$. Then, composing both sides with $P$, we find $P x = P^2 x + P v = P^2 x,$ so $P x = P^2 x$ for every $x in H$. To see the norm, we find that for every $x in H$, $
norm(x)^2 = (x, x) &= (P x + (id - P) x, P x + (id - P) x) \ 
&= norm(P x)^2 + 2 underbrace((P x, (id - P) x), perp) + norm((id - P) x)^2 \ 
&= norm(P x)^2 +  norm((id - P) x)^2 >= norm(P x)^2 \
&=> norm(P x) <= norm(x) => norm(P) <= 1,
$ and moreover if $x in M$, $P x = x$ so $norm(P x) = norm(x)$ hence $norm(P) = 1$ indeed.

Finally, the show $P$ self-adjoint, let $x, y in H$, then, $
0 &= (P x, (id - P ) y)  =(P x, y - P y)  => (P x, y) = (P x, P y).
$ Symmetrically, $(x, P y) = (P x, P y)$, hence $(P x, y) = (x, P y),$ and so $P = P^ast$.
]

== Introduction to Weak Convergence

We let throughout $X$ be a Banach space.

#definition("Weak convergence")[
  We say ${x_n} subset.eq X$ _converges weakly_ to $x in X$, and write $
  x_n harpoon.rt x
  $

  iff for every $f in X^ast = {f : X -> RR "bounded, linear"}$, $f(x_n) -> f(x)$.
]

#definition([Weak topology $sigma(X, X^ast)$])[
  The weak topology $sigma(X, X^ast)$ is the weak topology induced by $
  cal(F) = X^ast.
  $ In particular, this is the smallest topology in which every $f$ continuous.
]

Recall that this was defined as being $tau({f^(-1) (cal(O))})$ for $cal(O)$ open in $RR$. A base for this topology is given by $cal(B) = {"finite intersections of" {f^(-1) cal(O)}}$. Namely, let $cal(B)_X := {B_(epsilon, f_1, f_2, dots, f_n) (x)}$ where $
B_(epsilon, f_1, f_2, dots, f_n) (x) = {x' in X | abs(f_k (x') - f_k (x)) < epsilon, forall 1 <= k <= n}.
$ So, $x_n -> x$ in $sigma(X, X^ast)$ if for every $epsilon > 0$, and ball $B_(epsilon, f_1, dots, f_m) (x)$, there is an $N$ such that for every $n >= N$, $x_n in B_(epsilon, f_1, dots, f_m) (x)$, hence for every $f in X^ast$, $abs(f(x_n) - f(x)) < epsilon$.

For Hilbert spaces, by Riesz we know $f in H^ast$ can always be identified with $f(x) = (x, y)$ for some $y in H$. So, we find $x_n harpoon.rt x$ in $H$ iff for every $y in H$, $(x_n, y) -> (x, y)$.

#remark[
If $x_n -> x$ in $H$, then $(x_n, y) -> (x, y)$; so this normal convergence implies weak convergence.
]

#proposition[
  (i) Suppose $x_n harpoon.rt x$ in $H$. Then, ${x_n}$ are bounded in $H$, and $norm(x) <= liminf_(n->infinity) norm(x_n)$.

  (ii) If $y_n -> y$ (strongly) in $H$ and $x_n harpoon.rt x$ (weakly) in $H$, then $(x_n, y_n) -> (x, y)$.
]

#remark[
  It does _not_ hold, though, that $x_n harpoon.rt x$, $y_n harpoon.rt y$ gives $(x_n, y_n) -> (x, y)$.
]

#proof[
  (i) If $x_n harpoon.rt x$, then $
  (x_n, x/norm(x)) -> (x, x/norm(x)) = norm(x).
  $ By Cauchy-Schwarz, we also have $
  abs((x_n, x/(norm(x)))) <= norm(x_n) (norm(x)/norm(x)) = norm(x_n),
  $ hence we conclude $
  liminf_(n->infinity) (x_n, x/(norm(x))) <= liminf_(n->infinity) norm(x_n) => norm(x) <= liminf_(n->infinity) norm(x_n).
  $
  To argue ${x_n}$ bounded, need the uniform boundedness principle. Let ${x_n} subset.eq H^(ast ast) = H$. By weak convergence, for every $f = f_y in H^ast$, $f |-> f(x_n) = (x_n, y) -> (x, y)$. So, $
  sup_(n) f(x_n) <= C. 
  $ Thus, the map $f |-> f(x_n)$ a bounded linear operator on $H^ast$, so by uniform boundedness $sup_n norm(x_n) <= C$.
  // TODO this makes no sense

  (ii) If $y_n -> y$ in $H$, $
  abs((x_n, y_n) - (x, y)) &<= abs((x_n, y_n - y)) + abs((x_n - x, y)) \ 
  &<= underbrace(norm(x_n), "bounded") underbrace(norm(y_n - y), -> 0) + underbrace(abs((x_n -x, y)), -> 0 "by weak") -> 0.
  $
]

The real help of weak convergence is in the ease of achieving weak compactness;

#theorem("Weak Compactness")[
  Every bounded sequence in $H$ has a weakly convergent subsequence.
]<thm:weakcompactness>

#theorem("Helley's Theorem")[
Let $X$ a separable normed vector space and ${f_n} subset.eq X^ast$ such that there is a constant $C > 0$ such that $abs(f_n (x)) <= C norm(x)$ for every $x in X$ and $n >= 1$. Then, there exists a subsequence ${f_n_k}$ and an $f in X^ast$ such that $f_n_k (x) -> f(x)$ for every $x in X$.
]<thm:helleys>

#proof[
 This is essentially a specialization of the Arzelà-Ascoli lemma. To apply it, we need $X$ separable (done), the sequence to be pointwise bounded (done), and the sequence to be equicontinuous. To verify this last one, we know that $
 norm(f_n (x)) <= C norm(x) => norm(f_n) <= C, forall n >= 1,
 $ hence by linearity, for any $x, y in X$, $
 norm(f_n (x) - f_n (y)) <= C norm(x - y), forall n >= 1,
 $ so in particular ${f_n}$ uniformly Lipschitz, thus equicontinuous.
]

#proof[
  (Of @thm:weakcompactness) Let ${x_n} subset.eq H$ be bounded and let $H_0 = overline("span"{x_1, dots, x_n, dots})$, so $H_0$ is separable, and $(H_0, (dot,dot))$ is a Hilbert space (being closed). Let $f_n in H_0^ast$ be given by $
  f_n (x) = (x_n, x), forall x in H_0.
  $ Then, $
  abs(f_n (x)) <= norm(x_n) norm(x) <= C norm(x),
  $ since ${x_n}$ bounded by assumption. By Helly's Theorem, then, there is a subsequence ${f_n_k}$ such that $f_n_k (x) -> f(x)$ for every $x in H_0$, where $f in H_0^ast$. By Riesz, then, $f(x) = (x, x_0)$ for some $x_0 in H_0^ast$. This implies $
  (x_n_k, x) -> (x_0, x), forall x in H_0.
  $ Let $P$ the projection of $H$ onto $H_0$. Then, for every $x in H$, $
  (x_n_k, (id - P) x) = (x_0, (id - P) x) = 0
  $ so for any $x in H$, $
  lim_(k->infinity) (x_n_k, x) &= lim_(k->infinity) (x_n_k, P x + (id - P) x) \ 
  &= lim_(k->infinity) \(x_n_k, underbrace(P x, in H_0)) \ 
  &= (x_0, P x) = (x_0, P x + (id -P) x) = (x_0, x),
  $ as we aimed to show.
]

== Review of $L^p$ Spaces

We always consider $Omega subset.eq RR^d$.

#definition([$L^p (Omega)$])[
  For $1 <= p < infinity$, define $
  L^p (Omega) := {f : Omega -> RR | f "measurable and" integral_Omega abs(f)^p dif x < infinity},
  $ endowed with the norm $
  norm(f)_(L^p (Omega)) = norm(f)_p := [integral_Omega abs(f(x))^p dif x]^(1/p).
  $ For $p = infinity$, define $
  L^infinity (Omega) = {f : Omega -> RR | f "measurable and" exists C < infinity "s.t." abs(f) <= C "a.e."},
  $ endowed with the norm $
  norm(f)_(L^infinity (Omega)) = norm(f)_infinity := inf {C : abs(f) <= C "a.e."}.
  $
]

The following are recalled but not proven here, see #link("https://notes.louismeunier.net/Analysis%203/analysis3.pdf#page=47", "here").

#theorem("Holder's Inequality")[For $1 <= p,q <= infinity$ with $1/p + 1/q = 1$, then if $f in L^p (Omega), g in L^q (Omega)$, then $f g in L^(1) (Omega)$, and $
integral abs(f g) dif x <= norm(f)_p norm(g)_q.
$]
#theorem("Minkowski's Inequality")[
  For all $1 <= p <= infinity$, $norm(f + g)_p <= norm(f)_p + norm(g)_p$. In particular, $L^p (Omega)$ is a normed vector space.
]

#theorem("Riesz-Fischer Theorem")[
  $L^p (Omega)$ is a Banach space for every $1 <= p <= infinity$.
]

#theorem[
$C_c (RR^d)$, the space of continuous functions with compact support, simple functions, and step functions are all dense subsets of $L^p (RR^d)$, for every $1 <= p < infinity$.
]

#theorem([Separability of $L^p (Omega)$])[
  $L^p$ is separable, for every $1 <= p < infinity$.
]
#proof[
  We prove for $Omega = RR^d$. Let $
  cal(R) := {product_(i=1)^d (a_i, b_i) | a_i, b_i in QQ},
  $ and let $
  cal(E) := {"finite linear combinations of" chi_R "for" R in cal(R) "with coefficients in" QQ},
  $ where $chi_R$ the indicator function of the set $R$. Then, we claim $cal(E)$ dense in $L^p (RR^d)$.

  Given $f in L^p (RR^d)$ and $epsilon > 0$, by density of $C_c (RR^d)$ there is some $f_1$ with $norm(f - f_1)_p < epsilon$. Let $"supp"(f_1) subset.eq R in cal(R)$. Now, let $delta > 0$. Write $
  R = union_(i=1)^N R_i, wide R_i in cal(R),
  $ such that $
  "osc"_(R_i) (f_1) := sup_(R_i) f_1 - inf_(R_i) f_1 < delta.
  $ Then, let $
  f_2 (x) = sum_(i=1)^N q_i chi(R_i), wide q_i in QQ "s.t." q_i approx f_1|_(R_i),
  $ so $
  norm(f_2 - f_1)_infinity < delta.
  $ Hence, $
  norm(f_2 - f_1)_p &<= (integral_(R) abs(f_2 (x) - f_1 (x))^p dif x)^(1/p) \ 
  &<= abs(f_1 - f_2)_(infinity) dot m(R)^(1/p) < delta dot m(R)^(1/p),
  $ where $m$ the Lebesgue measure on $RR^d$. $delta$ was arbitrary so we may take it arbitrarily small such that $delta m(R)^(1/p) < epsilon$, hence for such a $delta$, $
  norm(f - f_2)_p <= norm(f - f_1)_p + norm(f_1 - f_2)_p < 2 epsilon.
  $ Now, $f_2 in cal(E)$, and thus $cal(E)$ is dense in $L^p (RR^d)$, and countable by construction, thus $L^p (RR^d)$ separable.
]

#remark[
  $L^infinity (Omega)$ is _not_ separable, and $C_c (RR^d)$ is _not_ dense in $L^infinity (Omega)$.
]

#remark("Special Cases")[
- If $Omega$ has finite measure, $L^p (Omega) subset.eq L^(p') (Omega)$ for every $p <= p'$.
- $ell^p := {a = (a_n)_(n=1)^infinity | sum_(n=1)^infinity abs(a_n)^p < infinity}$ endowed with the norm $abs(a)_ell^p := (sum_(n=1)^infinity abs(a_n)^p)^(1\/p)$.
]

== $(L^p)^ast$: The Riesz Representation Theorem

We are interested in functions $T : L^p (Omega) -> RR$ which is bounded and linear. For instance, let $g in L^q (Omega)$ and $f in L^p (Omega)$ where $p, q$ conjugates, and define $
T (f) := integral_Omega f(x) g(x) dif x.
$ This is clearly linear, and by Holders, $
abs(T f) &= abs(integral_(Omega) f g) <= norm(f)_p norm(g)_q.
$ so $
abs(T (f/(norm(f)_p))) <= norm(g)_q, thin thin forall f in L^p (Omega), thin thin=> norm(T) <= norm(g)_q,
$ and thus $T in (L^p (Omega))^ast$. Moreover, if $1 < p < infinity$, $1 < q < infinity$, let $
f(x) = (abs(g(x))^(q - 2) g(x))/(norm(g)_q^(q-1)).
$ Then, $
integral_Omega abs(f(x))^p dif x &= 1/(norm(g)_q^((q - 1) p)) integral_(Omega) abs(g(x))^((q - 2) p) abs(g(x))^p dif x \ 
&= 1/(norm(g)_q^((q - 1) p)) integral_(Omega) abs(g(x))^(q p - p) dif x.
$ Since $1/p + 1/q = 1$, we have $q + p = p q$, so further $
&= 1/(norm(g)_q^q) integral_(Omega) abs(g(x))^(q) dif x = 1/(norm(g)_q^q)  dot norm(g)_q^(q) = 1,
$ so $f$ as defined indeed in $L^p (Omega)$ and moreover has $L^p$-norm of 1. In addition, $
abs(T f) &= 1/(norm(g)_q^(q - 1)) integral_(Omega) abs(g (x)^(q - 2)) g(x) g(x) dif x \ 
&=1/(norm(g)_q^(q - 1)) integral_(Omega) abs(g(x))^q dif x \ 
&=1/(norm(g)_q^(q - 1)) norm(g)_q^(q) = norm(g)_q,
$ so $norm(T) = norm(g)_q$ as desired. We have, more generally, akin to the Riesz representation theorem,


#theorem([Riesz-Representation Theorem for $L^p (Omega)$])[
  Let $1 <= p < infinity$. For any $T in (L^p (Omega))^ast$, there exists a unique $g in L^q (Omega)$ such that $T(f) = integral_(Omega) f(x) g(x) dif x$ with $norm(T) = norm(g)_q$.
]<thm:rieszforlp>

We'll only prove for $Omega subset.eq RR$. First: 
#proposition[
  Let $T, S in (L^p (Omega))^ast$. If $T = S$ on a dense subset $E subset.eq L^p (Omega)$, then $T = S$ everywhere.
]

#proof[
  Let $f_0 in L^p (Omega)$. By density, there exists ${f_n} subset.eq E$ such that $f_n -> f$ in $L^p (Omega)$. By continuity, $T f_n -> T f_0$ and $S f_n -> S f_0$, while $T f_n = S f_n$ for every $n >= 1$, so by uniqueness of limits in $RR$, $T f_0 = S f_0$.
]

The general outline of the proof of @thm:rieszforlp is the following: 
- prove the theorem for $f$ a step function;
- prove the theorem for $f$ bounded and measurable;
- conclude the full theorem by appealing to the previous proposition.
To do this, we need first to recall the notion of _absolutely continuous functions_. Fix $[a, b] subset.eq R$ and $G : [a, b] -> RR$. $G$ is said to be absolutely continuous on $[a, b]$ if for every $epsilon > 0$ there exists a $delta > 0$ such that for every disjoint collection ${(a_k, b_k)}_(k=1)^N subset.eq [a, b]$ with $sum_(k=1)^N (a_k - b_k) < delta$, then $sum_(k=1)^N abs(G(b_k) - G(a_k)) < epsilon$.  In particular, we need the following result, proven #link("https://notes.louismeunier.net/Analysis%203/analysis3.pdf?page=79", "here"):

#theorem[If $G : [a, b] -> RR$ is absolutely continuous, then $g = G'$ exists a.e. on $[a, b]$, $g in L^1 ([a, b])$, and for every $x in [a, b]$, $
G(x) - G(a) = integral_(a)^x g(t) dif t.
$]

#proof([(Of @thm:rieszforlp with $Omega = [a, b]$)])[
  Let $T in (L^p ([a, b]))^ast$.

  _Step 1:_ Let $f$ a step function. The function $chi_[a, x) in L^p ([a, b])$; define $
  G_T (x) := T(chi_([a, x))).
  $ We claim $G_T$ absolutely continuous. Consider ${(a_k, b_k)}_(k=1)^N$ disjoint. Then, for every $[c, d] subset.eq [a, b],$ $,
  G_T (d) - G_T (c) = T(chi_([a, d))) - T(chi_([a, c])) = T(chi_([a, d)) - chi_([a, c))) = T(chi_[c, d)),
  $ so $
  sum_(k=1)^N (G_T (b_k) - G_T (a_k)) &= sum_(k=1)^N c_k dot (G_T (b_k) - G_T (a_k)), wide c_k := "sgn"(G_T (b_k) - G_T (a_k)) \ 
  &= sum_(k=1)^N c_k dot T(chi_[a_k, b_k)) \ 
  &= T(sum_(k=1)^N c_k chi_([a_k, b_k))) \ 
  & <= norm(T) norm(sum_(k=1)^N c_k chi_([a_k, b_k)))_p.
  $ By the disjointedness of the intervals, we may write $
  integral_(a)^b abs(sum_(k=1)^N c_k chi_([a_k, b_k)))^p dif x <= sum_(k=1)^N integral_(a_k)^b_k dif x = sum_(k=1)^N (b_k - a_k).
  $ So, $norm(sum_(k=1)^N c_k chi_([a_k, b_k)))_p = (sum_(k=1)^N (b_k - a_k))^(1/p)$, thus $
  sum_(k=1)^N abs(G_T (b_k) - G_T (a_k)) <= norm(T) dot (sum_(k=1)^N (b_k - a_k))^(1/p).
  $ Hence, for $epsilon > 0$, letting $delta = (epsilon/norm(T))^p$ proves absolute continuity of $G_T$. Thus, $g = G'_T$ exists and is such that $g in L^1 ([a, b])$ and $
  G_T (x) = integral_(a)^x g(t) dif t, thin forall x in [a, b].
  $ Hence, $
  T(chi_([c, d))) = G_T (d) - G_T (c) &= integral_(a)^d g(t) dif t - integral_(a)^c g(t) dif t \ 
  &= integral_(c)^d g(t) dif t  \
  &= integral_(a)^b g(t) dot chi_([c, d)) (t) dif t.
  $ This proves the theorem for indicator functions; by linearity of $T$ and linearity of the integral, we can repeat this procedure to find a function $g$ such that $T f = integral_(a)^b f(t) g(t) dif t$ for every step function $f$.

_Step 2:_ Let $f$ bounded and measurable. We know that for every step function $psi$, $T psi = integral_(a)^b psi(t) g(t) dif t$ (with the $g$ as "found" in step 1). So, $
abs(T f - integral_(a)^b psi(t) g(t)) &= abs(T (f - psi) - integral_(a)^b (f(t) - psi(t))g(t) dif t) \ 
&<= norm(T) norm(f - psi)_(p) + integral_(a)^b abs(f(t) - psi(t)) abs(g(t)) dif t.
$ Then, since $g in L^1 ([a, b])$, for every $epsilon > 0$ there is some $delta > 0$ such that if $E$ a set of measure less than $delta$, $integral_(E) abs(g(t)) dif t < epsilon$. Fix $epsilon > 0$ and $delta > 0$ such that this holds; let $delta < epsilon$ if necessary wlog. Since $f$ bounded and measurable, there is some step function $psi$ such that $abs(f - psi) < delta$ on $E subset.eq [a, b]$, and that $m(E^c) < delta$ and $abs(psi) <= norm(f)_infinity$. Hence, $
norm(f - psi)_p^p &= integral_(E) abs(f - psi)^p + integral_(E^c) abs(f - psi)^p \ 
&<= delta^p dot m(E) + (2 norm(f)_infinity)^p m(E^c) \ 
&<= delta^p |b - a| + (2 norm(f)_infinity)^p delta.
$ Also, $
integral_(a)^b abs(f - psi) abs(g) dif t &<= integral_(E) delta dot abs(g) dif t + integral_(E^c) 2 norm(f)_infinity abs(g) dif t \ 
&<= delta norm(g)_1 + 2 norm(f)_infinity epsilon.
$ All together then, $
abs(T f - integral_(a)^b f(t) g(t) dif t) &<= norm(T) (delta^p |b - a| + (2 norm(f)_infinity)^p delta)^(1/p) + delta norm(g)_1 + 2 norm(f)_infinity epsilon \ 
& < C(norm(f)_infinity, norm(g)_1, a, b, norm(T)) dot epsilon^(1/p),
$ where $C$ a constant. The LHS does not depend on $epsilon$, hence taking the limit $epsilon -> 0^+$, we conclude $
T f = integral_a^b f(t) g(t) dif t.
$ Note that all simple functions are bounded and measurable, so the necessary property also holds for $f$ simple. 

 We need now to show $g in L^q ([a, b])$ and $norm(g) = norm(T)$.

- Case 1: $p > 1$ so $q < infinity$. Let $g_n := cases(
g & "if" abs(g) <= n,
0 & "o.w."
)$ and $f_n := cases(
  abs(g)^(q - 1) "sgn"(g) & "if" abs(g) <= n,
  0 & "o.w."
)$. Then, $
norm(g_n)_q^q &= integral_({abs(g) <= n}) abs(g)^q dif t \ 
&= integral_({abs(g) <= n}) f_n dot g_n dif t \ 
&= integral_({abs(g) <= n}) f_n g dif t \ 
&= T f_n <= norm(T) norm(f_n)_p,
$ since $f_n$ bounded and measurable so Step 2 applies. Also, $
norm(f_n)_p^p &= integral_({abs(g) <= n}) abs(g)^((q - 1)p) dif t \ 
&= integral_({abs(g) <= n}) abs(g)^q dif t = norm(g_n)_q^q.
$ All together then, $
norm(g_n)_q^q <= norm(T) norm(g_n)_q^(q\/p) => norm(g_n)_q^(q(1 - 1/p)) = norm(g_n)_q <= norm(T).
$ By construction, $abs(g_n)^q -> abs(g)^q$ a.e. and monotonely, so by the monotone convergence theorem, $
norm(g_n)_q -> norm(g)_q,
$ so $norm(g)_q <= norm(T)$ and so $g in L^q ([a, b])$. From here, as in the example at the beginning of this section, one can show equality by chosing $f$ appropriately.

- Case 2: $p = 1$ so $q = infinity$. We claim that $norm(g)_infinity = sup_(norm(f)_1 = 1,\ f "bdd") integral f g$. Let $epsilon > 0 $ and $A subset.eq [a, b]$ such that $abs(g) >= norm(g)_infinity - epsilon$ on $A$ where $m(A) > 0$. Let $
f(x) = chi_A/m(A) "sgn"(g).
$ Then, $f$ bounded and $norm(f)_1 = 1$. So, $
integral f g = 1/m(A) integral_(A) abs(g) >= 1/m(A) integral_A (norm(g)_infinity - epsilon) = norm(g)_infinity - epsilon,
$ hence we have proven $<=$ of our claim. By Holder, $
sup_(norm(f) = 1) integral f g <= norm(f)_1 norm(g)_infinity = norm(g)_infinity,
$ so $>=$ holds and the claim is proven. Thus, $
norm(g)_infinity = sup_(norm(f) = 1 ,\ f "bdd") T f <= norm(T) norm(f)_1 = norm(T),
$ so in particular $g in L^infinity ([a, b])$. For the other inequality, $
abs(T f) = abs(integral f g dif t) <= norm(f)_1 norm(g)_infinity,
$ hence $
norm(T) <= norm(g)_infinity
$ so $norm(g)_infinity = norm(T)$ as we aimed to show.


_Step 3:_ We need to show $T f = integral_a^b f g dif t$ for every $f in L^p ([a, b])$. Simple functions are dense in $L^p ([a, b])$, and since $T f = integral_(a)^b f g dif t$ for every simple function $f$, we conclude $T f  = integral_(a)^b f g dif t$ for every $f in L^p ([a, b])$ by the previous density lemma.

Moreover, $g$ is unique because if $
integral_(a)^b f g = integral_(a)^b f g',
$ then $
integral_(a)^b f (g - g') = 0,
$ for every $f in L^p$. Let $f(t) = "sgn"(g - g')$, then $
0 = integral_(a)^b abs(g - g') dif t => g = g' "a.e.".
$ So, $g$ uniquely defined up to a set of measure 0 so $g = g'$ in $L^q$.
]

#proof(([(Of RRT if $Omega = RR$)]))[
  Fix $T in (L^p (RR))^ast$. Then, $T|_([-N, N]) in (L^p ([-N, N]))^ast$ for every $N >= 1$, and $norm(T|_([-N,N])) <= norm(T)$. Then, by RRT on $[-N, N]$, there is a $g_N in L^q ([-N, N])$ such that $T f = integral_(-N)^N f g_N dif t$. By uniqueness, $g_(N+1)|_([-N,N]) = g_N$. Define $
  g(t) := g_N (t), wide t in [-N, N].
  $ So, $g_N (t) -> g(t)$ pointwise and $abs(g_N (t))^q -> abs(g (t))^q$ pointwise and monotonely. By monotone convergence, then, $integral_RR abs(g_N)^q dif t -> integral_(RR) abs(g)^q dif t$. So, $g in L^q (RR)$ since $norm(g_N)_(L^q ([-N, N])) <= norm(T)$ for every $N >= 1$. Let $f_N (t) = f(t) chi_[-N, N]$. Then, $f_N -> f$ in $L^p (RR)$ so $T f_N -> T f$. So also $
  T f_N = integral_(-N)^N f_N  g_N = integral_(-N)^N f(t) g_N (t) dif t = integral_(RR) f g_N dif t -> T f,
  $ if we take by convention the $g_N$'s to be zero outside of $[-N, N]$. But also, $f in L^p (RR)$ and $g_N -> g$ in $L^q (RR)$, so applying Holder's to the quantity $integral_RR f g_N$, we know $
  integral_RR f g_N -> integral_RR f g,
  $  hence equating the two $
  T f = integral_RR f g,
  $ for every $f in L^p (RR)$. A similar proof to the previous gives the necessary norm identity.\
]

#proof(([(Of RRT for general $Omega subset.eq RR$)]))[
  If $T in (L^p (Omega))^ast$, let $hat(T) in (L^p (RR))^ast$ given by $hat(T) f = T (f |_Omega)$. Then by the previous case there is $hat(g) in L^q (RR)$ such that $hat(T) (f) = integral f hat(g)$. Let $g = hat(g)|_(Omega)$, then $T f = integral_Omega f g$.
]

So, RRT gives us that for $p in [1, infinity]$, $(L^p (Omega))^ast tilde L^q (Omega)$, and that $norm(f)_p = sup_(g in L^q \ norm(g)_q = 1) abs(integral f g)$.

In particular, if $p  = 1$, $
norm(f)_(L^1) = integral f "sgn" f(x) dif x = sup_(norm(g)_infinity = 1) integral f g.
$

What, though, is $(L^infinity)^ast$. Certainly, $L^1 (Omega) subset.eq (L^infinity (Omega))^ast$ since for $f in L^infinity$, $T f = integral f g dif x$ with $g in L^1$, which is bounded by Holders. However, it turns out that this inclusion is a strict one. Consider for instance $
T f := f(0), wide T : L^infinity ([-1,1]) -> RR.
$ Then, certainly $abs(T f) <= norm(f)_infinity$ so $T in (L^infinity)^ast$. However, there is no function $g$ such that $f (0) = integral f(t) g(t) dif t$.

== Weak Convergence in $L^p (Omega)$

#definition([Weak convergence in $L^p (Omega)$])[
  Let $Omega subset RR^d$, $p in [1, infinity)$ and $q$ its conjugate. Then, we say $f_n -> f$ _weakly_ in $L^p (Omega)$, and write $
  f_n harpoon.rt_(L^p (Omega)) f,
  $ if for every $g in L^q (Omega)$, $
  lim_(n->infinity) integral_(Omega) f_n g dif x = integral f g dif x.
  $
] 

#remark[
  Weak limits are unique; suppose otherwise that $f_n harpoon.rt f, overline(f)$. Let $g = "sgn"(f - overline(f)) dot abs(f - overline(f))^(p - 1)$, which is in $L^q (Omega)$. So, $
  lim_(n) integral g f_n dif x = integral g f dif x = integral g overline(f) dif x,
  $ by assumption, so $
  0 = integral_(Omega) g (f - overline(f)) dif x = integral abs(f - overline(f))^p dif x,
  $ hence $f = overline(f)$ a.e. (and so equal as elements of $L^p (Omega)$).
]

#remark[
  Many of the properties of weakly convergent sequences in a Hilbert space carry over to this setting.
]

#proposition[
  Let $Omega subset.eq RR^d$. 

  (i) If $p in (1, infinity)$, $f_n harpoon.rt_(L^p (Omega)) f$, then ${f_n} subset.eq L^p (Omega)$ are bounded, and moreover $norm(f)_p <= liminf_(n) norm(f_n)_p$.

  (ii) If $p in [1, infinity)$ and $f_n harpoon.rt_(L^p (Omega)) f, g_n ->_(L^p (Omega)) g$, then $lim_(n->infinity) integral g_n f_n dif x = integral g f dif x$.
]

#proof[
  Identical to Hilbert space proofs; replace usage of Cauchy-Schwarz with Holder's.
]

#remark[
  In (i), $p in (1, infinity)$, since $L^p$ "reflexive" in this case, i.e. $(L^p)^(ast ast) = L^p$ (just as we had in the Hilbert space case). We don't have this property for $p = 1$.
]

#remark[
  A related notion of convergence is called _weak$""^ast$ convergence_, written $f_n harpoon.rt^ast_(L^p (Omega)) f$; we say this holds if for every $g in L^q (Omega)$ such that $(L^q)^ast = L^p$, then $integral f_n g dif x -> integral f g dif x$. So if $p in (1, infinity)$, weak convergence = weak$""^ast$ convergence, by Riesz.
]

#remark[
  There are many equivalent notions to weak convergence.
]

#theorem("Equivalent Weak Convergence")[
  Let $p in (1, infinity)$. Suppose ${f_n} subset.eq L^p (Omega)$ are bounded and $f in L^p$. Then, $f_n harpoon.rt_(L^p (Omega)) f$ iff

  - for any $g in G subset.eq L^q (Omega)$ such that $overline("span"(G))= L^q (Omega)$, then $lim_(n->infinity) integral f_n g = integral f g$;
  - $forall A subset.eq Omega$ measurable with finite measure, then $lim_(n->infinity) integral_A f_n dif x = integral_(A) f dif x$;
  - if $d = 1$ and $Omega = [a, b]$, then $lim_(n->infinity) integral_(a)^x f_n dif x = integral_(a)^x f dif x$ for every $x in [a, b]$.
  - $f_n -> f$ pointwise a.e..
  // TODO
]

#remark[Some of these notions extend to $p = 1$, but we state in the $p > 1$ case for simplicity.]

#theorem("Radon-Riesz")[
  Let $p in (1, infinity)$. Suppose $f_n harpoon.rt_(L^p (Omega)) f$, then $f_n ->_(L^p (Omega)) f$ iff $lim_(n->infinity) norm(f_n)_p = norm(f)_p$.

  Alternatively, there exists a subsequence ${f_n_k}$ such that $f_n_k -> f$ in $L^p (Omega)$ iff  $liminf_(n->infinity) norm(f_n)_p = norm(f)_p$.
]

#proof[
($=>$) If $f_n ->_(L^p (Omega)) f$ then $norm(f_n)_p -> norm(f)_p$ by triangle inequality.

The converse, ($impliedby$), is hard.
]

#theorem("Weak Compactness")[
  Let $p in (1, infinity)$, then every bounded sequence in $L^p (Omega)$ has a weakly convergent subsequence, with limit in $L^p (Omega)$.
]

#proof[
  Let ${f_n} subset.eq L^p (Omega)$ be bounded.
  $p in (1, infinity)$ so so is $q$, and in particular $L^q (Omega)$ is separable. Let $T_n in (L^q (Omega))^ast$ be given by $T_n (g) := integral f_n g dif x$ for $g in L^q (Omega)$. Then, $norm(T_n) = norm(f_n)_p <= C$. So, $
  sup_(n) abs(T_n (g)) <= norm(T_n) norm(g)_q <= C norm(g)_q.
  $ By Helley's Theorem (@thm:helleys), there exists a subsequence ${T_n_k}$ and $T subset.eq (L^q (Omega))^ast$ such that $lim_(k->infinity) T_n_k (g) = T(g)$ for every $g in L^q (Omega)$. By Riesz, there exists some $f in L^p (Omega)$ such that $T (g) = integral f g dif x$, and hence $
  lim_(k) integral f_n_k g dif x = integral f g dif x,
  $ for every $g in L^q (Omega)$, so $f_n_k harpoon.rt_(L^p (Omega)) f$.
]

== Convolution and Mollifiers

#definition("Convolution")[
  $
  (f ast g) (x) :=  integral_(RR^d) f(x - y) g(y) dif y = integral_(RR^d) f(y) g(x - y) dif y.
  $
]

#proposition("Properties of Convolution")[\
  a. $(f ast g) ast h = f ast (g ast h)$ (convolution is associative)\
  b. Let $tau_z f(x) := f(x - z)$ be the $z$-translate of $x$ which centers $f$ at $z$. Then, $
  tau_z (f ast g) = (tau_z f) ast g = f ast (tau_z g).
  $\
  c. $"supp"(f ast g) subset.eq overline({x + y | x in "supp"(f), y in "supp"(g)})$.
]

#proof[
  (a) Assuming all the necessary integrals are finite, we can change order of integration, $
  ((f ast g) ast h )(x) &= (integral f(y) g(x - y) dif y) ast h(x) \ 
  &= integral integral f(y) g(x - z - y) dif y \, h(z) dif z \
  &= integral integral f(y) g(x - y - z) h(z) dif z dif y  wide (y' = x - y )\ 
  &= integral integral f(x - y') g(y' - z) h(z) dif z dif y' \ 
  &= integral f(x - y')  (g convolve h)(y') dif y' = (f convolve (g convolve h)) (x).
  $

  (b) For the first equality, $
tau_z (f ast g) (x) &= tau_z integral f(x - y) g(y) dif y \ 
    &= integral f(x - z - y) g(y) dif y \
    &= integral (tau_z f(x - y)) g(y) dif y = ((tau_z f) convolve g)(x).
  $ The second follows from a change of variables in the second line.

  (c) We'll show that $A^c subset.eq ("supp"(f ast g))^c$ where $A$ the set as defined in the proposition. Let $x in A^c$, then if $y in "supp"(g)$, $x - y in.not "supp"(f)$ so $f(x - y) = 0$; else if $y in.not "supp"(g)$ it must be $g(y) = 0$. So, if $x in A^c$, it must be that $
  integral f(x - y) g(y) dif y = integral_("supp"(g)) underbrace(f(x - y), = 0)g(y)  dif y+ integral_("supp"(g)^c) f(x - y) underbrace(g(y), = 0) dif y  = 0.
  $
]

We've been rather loose with finiteness of the convolutions so far. To establish this, we need the following result.

#theorem("Young's Inequality")[
  Let $f in L^1 (RR^d), g in L^p (RR^d)$ for any $p in [1, infinity]$. Then, $
  norm(f ast g)_p <= norm(f)_1 norm(g)_p,
  $ hence $f ast g in L^p (RR^d)$.
]

#proof[
Suppose first $p = infinity$, then $
(f ast g)(x) = integral f(y) g(x - y) dif y <= norm(g)_infinity integral abs(f(y)) dif y = norm(g)_infinity norm(f)_1,
$ for every $x in RR^d$, so passing to the $L^infinity$-norm, $
norm(f ast g)_infinity <= norm(f)_1 norm(g)_infinity.
$

Suppose now $p = 1$. Then, $
norm(f ast g)_1 = integral abs(integral f(x - y) g(y) dif y) dif x.
$ Let $F(x, y) = f(x - y) g(y)$, then for almost every $y in RR^d$, $
integral abs(F(x, y)) dif x &= integral abs(g(y)) abs(f(x - y)) dif x \
&=  abs(g(y)) integral abs(f(x - y)) dif x\
&= abs(g(y)) norm(f)_1.
$ Applying Tonelli's Theorem, we have then $
integral.double abs(F(x, y)) dif y dif x &= integral.double abs(F(x, y)) dif x dif y = integral abs(g(y)) norm(f)_1 dif y = norm(f)_1 norm(g)_1,
$ (so really $F in L^1 (RR^d) times L^1 (RR^d)$), hence all together $
norm(f convolve g)_1 = integral abs(integral F(x, y) dif y) dif x <= integral.double abs(F(x, y)) dif y dif x = norm(f)_1 norm(g)_1.
$
#remark[
  It also follows that for a.e. $x in RR^d$, $integral abs(F(x, y)) dif y < infinity$, i.e. $integral abs(f(x - y) g(y)) dif y < infinity$. Moreover, since if $g in L^p (Omega)$ then $abs(g)^p in L^1 (Omega)$, a similar argument gives that for almost every $x in RR^d$, $ integral abs(f(x - y)) abs(g(y))^p dif y < infinity$.
]
Suppose now $1 < p < infinity$. For a.e. $x in RR^d$, $integral abs(g(y))^p abs(f(x - y)) dif y < infinity$, so $g in L^p (RR^d)$ implies for a.e. $x in RR^d$, $|g(dot)|^p abs(f(x - dot)) in L^1 (RR^d)$ as a function of $dot$. This further implies $g(y) f^(1/p) (x - y) in L^p (RR^d, dif y)$. Also, if $f in L^1 (RR^d)$, then $f^(1/q) in L^q (RR^d)$. All together then, $
integral abs(f(x - y)) abs(g(y)) dif y &= integral overbrace(abs(f^(1/q) (x - y)), q)underbrace(abs(f^(1/p) (x - y)) abs(g(y)) dif y, p) \ 
"Holder's" wide &<= (integral abs(f(x - y)) dif y)^(1/q) (integral abs(f(x - y)) abs(g(y))^p dif y)^(1/p),
$ hence, raising both sides to the $p$, $
abs((f convolve g )(x))^p <= norm(f)_1^(p/q) dot (abs(f) convolve abs(g)^p)(x)
$ and integrating both sides $
integral abs((f ast g) (x))^p dif x <= norm(f)_1^(p/q) integral (underbrace(abs(f), in L^1 (RR^d)) ast underbrace(abs(g)^p, in L^1 (RR^d))) (x) dif x.
$ Hence, we can bound the right-hand term using the previous case for $p = 1$, and find $
integral abs((f ast g) (x))^p dif x &<= norm(f)_1^(p/q) norm(f)_1 norm(g^p)_1 \
&= norm(f)_1^(p/q + 1) norm(g)_p^p \ 
&= norm(f)_1^((p + q)/q) norm(g)_p^p \ 
((p + q)/q = p) wide &= norm(f)_1^p norm(g)_p^p,
$ so raising both sides to $1/p$, we conclude $
norm(f ast g)_p <= norm(f)_1 norm(g)_p.
$
]

#proposition[
  If $f in L^1 (RR^d)$ and $g in C^1 (RR^d)$ with $abs(partial_(x_i) g)in L^infinity (RR^d)$ for $i = 1, dots, d$, then $(f ast g) in C^1 (RR^d)$ and moreover $
  partial_(x_i) (f ast g) = f ast (partial_x_i g).
  $
]

#remark[
  There are many different conditions we can place on $f, g$ to make this true; most basically, we need $abs((partial_i g) ast f) < infinity$.
]

#proof[
$
(partial)/(partial x_i) (integral f(y) g(x - y) dif y) &= integral underbrace(f(y), in L^1 (RR^d)) underbrace(partial_i g(x - y), in L^infinity (RR^d)) dif y < infinity,
$ citing the previous theorem for the finiteness; the dominated convergence theorem allows us to pass the derivative inside.
]

#remark[This also follows for the gradient; namely $gradient (f ast g) = f ast (gradient g)$ with a component-wise convolution.]

Consider the function $
rho(x) = cases( C exp(-1/(1 - abs(x)^2)) & "if" abs(x) <= 1, 0 & "o.w."),
$ where $C  = C(d)$ a constant such that $integral_(RR^d) rho(x) dif x = 1$. Then, note that $rho in C^infinity_c (RR^d)$ (infinitely differentiable with compact support). Let now $
rho_(epsilon) (x) := 1/(epsilon^d) rho(x/epsilon).
$ Notice that $rho_epsilon (x)$ is supported on $B(0, epsilon)$, but $
integral_(RR^d) rho_epsilon (x) dif x = 1/(epsilon^d) integral_(RR^d) rho(x/epsilon) dif x = 1/epsilon^d dot epsilon^d dot integral_(RR^d) rho(y) dif y = 1,
$ for every $epsilon$, by making a change of variables $y = x/epsilon$. We'll be interested in the convolution $
f_epsilon (x) := (rho_epsilon convolve f) (x)
$ for some function $f$. $rho_epsilon$ is often called a "convolution kernel". In particular, it is a "good kernel", namely has the properties:
- $integral_(RR^d) rho_epsilon (y) dif y = 1$;
- $integral_(RR^d) abs(rho_epsilon (y)) dif y <= M$ for some finite $M$;
- $forall delta > 0$, $integral_({abs(y) > delta}) abs(rho_epsilon (y)) dif y ->_(epsilon -> 0) 0.$

The second condition is trivially satisfied in this case since our kernel is nonnegative. The last also follows easily since $rho_epsilon$ has compact support; more generally, this imposes rapid decay conditions on the tails of good kernels.

Since $rho_(epsilon) in C_c^infinity (RR^d)$, for "reasonable" $f$, $f_epsilon = rho_epsilon convolve f in C^infinity (RR^d)$ by the previous proposition. In fact, we'll see that in many contexts $f_epsilon -> f$ as $epsilon -> 0$ in some notion of convergence. So, $f_epsilon$ provides a good, now smooth, approximation to $f$.

#proposition[
  Suppose $f in L^infinity (RR^d)$ and $f_epsilon$ is well-defined. Then, if $f$ is continuous at $x$, then $f_(epsilon) (x) -> f(x)$ as $epsilon -> 0$. 
  
  If $f in C(RR^d)$, then $f_epsilon -> f$ uniformly on compact sets.
]

#proof[
 $f$ continuous at $x$ gives that for every $eta > 0$ there exists a $delta > 0$ such that $abs(f(y) - f(x))< eta$  whenver $abs(x - y) < delta$. Then $
 abs(f_epsilon (x) - f(x)) &= abs(integral rho_epsilon (y) f(x - y) dif y - f(x) underbrace(integral rho_epsilon (y) dif y, = 1)) \ 
 &= abs(integral rho_epsilon (y) (f(x - y) - f(x)) dif y) \ 
 &<= integral_({abs(y) <= delta}) abs(f(x  - y) - f(x)) abs(rho_epsilon (y)) dif y + integral_({abs(y) > delta}) abs(f(x - y) - f(x)) abs(rho_epsilon (y)) dif y \ 
 (#stack(spacing: .3em, text(size: 8pt, "cnty in first argument"),[#text(size: 8pt, [$L^infinity$-bound in second])]))
   wide & <= integral_({abs(y) <= delta}) eta abs(rho_epsilon (y)) dif y + 2 norm(f)_infinity integral_(abs(y) > delta) abs(rho_epsilon (y)) dif y \ 
   & <= eta dot M + 2 norm(f)_infinity integral_({abs(y)> delta}) abs(rho_epsilon)
 $ for $epsilon -> 0$, by using the second property of good kernels for the first bound. By the last property, the right-most term $->0$ as $epsilon -> 0$; moreover, then, $
 lim_(epsilon -> 0) abs(f_epsilon (x) - f(x)) <= C eta 
 $ for some $C$ and every $eta > 0$, and thus $f_epsilon (x) -> f(x)$ as $epsilon -> 0$.

 Now, if $f in C(RR^d)$ fix a subset $K subset.eq RR^d$ compact. Hence, $norm(f)_(L^infinity (K)) <infinity$ and $f$ uniformly continuous on $K$ since $K$ compact; so the modulus continuity is uniform for all $x in K$, so for $delta > 0$ and for every $x in K$, $
 integral_({abs(y) <= delta}) abs(f(x - y) - f(x)) abs(rho_epsilon (y)) dif y <= C eta.
 $ Also, using the bound on $f$, we may write the second integral in the argument above as $
 integral_(epsilon > abs(y) > delta) abs(f(x - y) - f(x)) abs(rho_epsilon (y)) dif y <= norm(f)_(L^infinity (K + B_epsilon)) integral_({abs(y) > delta}) abs(rho_epsilon (y)) dif y ->_(epsilon -> 0) 0
 $ where we take $K$ slighly larger as $K + B_epsilon$, which is still compact. So, since this held for all $x in K$, $
 max_(x in K) abs(f_epsilon (x) - f(x)) ->_(epsilon -> 0) 0.
 $

 _Note that we proved the first for general good kernels but the second only in our constructed one_.
]

#remark[
  This pointwise convergence result is why "good kernels" are called "approximations to the identity".
]

#remark[
  If $f in C_c (RR^d)$, then $"supp"(f_epsilon) subset.eq overline("supp" (f) + B(0, epsilon))$; so, $f_epsilon$ is compactly supported if $f$ is. Hence in this case $f_epsilon -> f$ uniformly on $RR^d$.
]

#theorem("Weierstrass Approximation Theorem")[
Let $[a, b] subset.eq RR$ and let $f in C([a, b])$. Then for every $eta > 0$, there exists a polynomial $P_N (x)$ of degree $N$ such that $
  norm(P_N - f)_(L^infinity ([a, b])) < eta.
$ That is, polynomials are dense in $C([a, b])$.
]

#proof[
  Extend $f$ to be continuous with compact support on all of $RR$ in whatever convenient way, such that $"supp"(f) subset.eq [-M, M]$ for some sufficiently large $M > 0$. Consider now $
  K_epsilon (x) := 1/(sqrt(epsilon)) e^(- (pi x^2)/epsilon),
  $  noting that $
  integral_(-infinity)^infinity K_epsilon (x) dif x = integral_(-infinity)^infinity 1/(sqrt(epsilon)) e^(- (pi x^2)/epsilon) dif x = 1,
  $ which is clear by a change of variables $y = sqrt(2 pi)/(sqrt(epsilon)) x$. As a consequence, $integral_(-infinity)^infinity abs(K_epsilon (x)) dif x = 1 < infinity$, since $K_epsilon >= 0$. Finally, $
  integral_(abs(x) > delta) abs(K_epsilon (x)) dif x &= integral_(abs(x) > delta)1/(sqrt(pi)) e^(-(pi x^2)/epsilon) dif x \ 
  &= integral_(abs(y) > sqrt(2 pi)/(sqrt(epsilon)) delta) e^(-(y^2)/2)/(sqrt(2 pi)) dif y \ 
  #text(size: 9pt, [since $abs(y) >= 1$ here for suff. small $epsilon$]) wide & <=  integral_(abs(y) > sqrt(2 pi)/(sqrt(epsilon)) delta) abs(y)/(sqrt(2 pi)) e^(-(y^2)/2)/(sqrt(2 pi)) dif y \
  &<= C  e^(-(y^2)/2)#vbar(2em)_(thin sqrt(2 pi)/(sqrt(epsilon)) delta)^(thin infinity) ->_(epsilon -> 0) 0.
  $  So, $K_epsilon$ is a good kernel, and so $(f ast K_epsilon) (epsilon) ->_(epsilon -> 0) f$ uniformly in $[a, b]$ by our last remark. In particular, for $eta>0$ there is some $epsilon_0 > 0$, $
  abs((f ast K_epsilon_0) - f)_(L^infinity ([a, b])) < eta/2.
  $ We claim now that there is a polynomial $P_N$ such that $norm(P_N - (f ast K_epsilon_0))_(L^infinity ([ a, b])) < eta/2$. Recall that $e^x = sum_(n=0)^infinity (x^n)/(n!)$, which converges uniformly on compact sets. So, there exists a polynomial $S_N$ (from truncating this sum) such that $norm(K_epsilon_0 - S_N)_(L^infinity ([-M, M])) < eta/(4 norm(f)_infinity M)$. Thus, $
  abs(f ast K_epsilon_0 (x) - f ast S_n (x)) &<=  abs(integral f(x - y) (K_epsilon_0 (y) - S_N (y)) dif y) \
  "supp"(f) subset [-M, M] wide &<=integral_(-M)^M abs(f(x - y)) abs(K_epsilon_0 (y) - S_N (y)) dif y \ 
  &<= 2 M norm(f)_infinity eta/(4 M norm(f)_infinity) =  eta/2,
  $ for every $x$. Let $P_N (x) = (f ast S_n) (x)$, which we see to be a polynomial.
]

#theorem[
  Let $f in L^p (RR^d)$ with $p in [1, infinity)$. Then $f_epsilon ->_(L^p (RR^d)) f$.
]
#proof[
  Since $f in L^p (RR^d)$, for every $eta > 0$ there is a $tilde(f) in C_c (RR^d)$ such that $norm(f - tilde(f))_p < eta$. Since $tilde(f) in C_c (RR^d)$, by the previous theorem dealing with mollifiers and uniform convergence, $tilde(f)_epsilon -> tilde(f)$ uniformly. In particular, we have $norm(tilde(f)_epsilon - tilde(f))_p ->_(p) 0$, hence $
  norm(f - f_epsilon)_p <= norm(f_epsilon - tilde(f)_epsilon)_p + norm(tilde(f)_epsilon - tilde(f))_p + norm(tilde(f) - f)_p.
  $ We've dealt with the second two bounds. For the first, $
  norm(f_epsilon - tilde(f)_epsilon)_p &= norm((f - tilde(f)) convolve rho_epsilon)_p \
  ("Young's") wide &<= norm(rho_epsilon)_1 norm(f - tilde(f))_p = norm(f - tilde(f))_p,
  $ so $
  norm(f - f_epsilon)_p <= 2 norm(f - tilde(f))_p + norm(tilde(f)_epsilon - tilde(f))_p < 3 eta.
  $
]

#corollary[
  $C_c^infinity (RR^d)$ dense in $L^p (RR^d)$.
]
#proof[
  We showed $tilde(f)_epsilon$ approximates $f$ in $L^p (RR^d)$, and by construction $tilde(f)_epsilon$ is smooth with compact support.
]

== Strong Compactness in $L^p (RR^d)$

We saw that for $p in (1, infinity)$, ${f_n} subset L^p (Omega)$, that any bounded sequence admits a weakly converging subsequence, $f_n_k harpoon.rt_(L^p) f$. In addition, if the norms also converge i.e. $lim_(n -> infinity) norm(f_n)_p = norm(f)_p$, then we actually have strong convergence $f_n_k ->_(L^p) f$.

We provide now a strong compactness result in $L^p$, akin to Arzelà-Ascoli.
#theorem("Strong Compactness")[
  Let ${f_n} subset.eq L^p (RR^d)$ for $p in [1, infinity)$ s.t. \
  i. $exists C > 0$ s.t. $norm(f_n)_p < C forall n$, i.e. ${f_n}$ uniformly bounded in $L^p$;\
  ii. $lim_(abs(h) -> 0) norm(f_n - tau_h f_n)_p = 0$ uniformly in $h$, i.e. for every $eta > 0$, there exists $delta > 0$ such that if $abs(h) < delta$, $integral abs(f_n (x) - f_n (x - h))^p dif x < eta^p$ _for every_ $n$;\

  Then, for any $Omega subset.eq RR^d$ with finite measure, there exists a subsequence ${f_n_k}$ such that $f_n_k ->_(L^p (Omega)) f$.
]

#proof[
  Recall that $L^p (Omega)$ is a complete metric space, so TFAE:
  1. sequential compactness;
  2. totally bounded (& complete);
  3. compact.

  Let $cal(F) = {f in L^p (RR^d) "satisfying" "i.", "ii."}$ and fix $Omega subset.eq RR^d$ with finite measure. We aim to show that $cal(F)|_(Omega)$ is sequentially compact in $L^p (Omega)$ (with no regard to whether the limit lives in $cal(F)_Omega$); equivalently, we wish to show $cal(F)|_(Omega)$ is precompact in $L^p (Omega)$ i.e. $overline(cal(F)|_(Omega))$ is compact. Since $overline(cal(F)|_(Omega))$ is a complete metric space, to prove the result it suffices to show that $cal(F)|_(Omega)$ is totally bounded (recall: for every $delta > 0$, $cal(F)|_(Omega) subset.eq union.big_(i=1)^N B_(L^p (Omega)) (g_i, delta)$). We'll do this using mollifiers and AA to do this.

  _Step 1:_ Fix $eta$, $delta$ as in ii. in the statement of the theorem, and let $f in cal(F)$. Then, for every $epsilon < delta$, we claim $
  norm((rho_epsilon convolve f) - f)_(L^p (RR^d)) < eta.
  $ We have $
  abs((rho_epsilon convolve f)(x) - f(x)) &= abs(integral_(B_epsilon) rho_epsilon (y) f(x - y) dif y - f(x) integral rho_epsilon (y) dif y ) \ 
  & <= integral_(B_epsilon) rho_epsilon (y) abs(f(x - y) - f(x)) dif y \
  &= integral_(B_epsilon) rho_epsilon^(1/q) (y) rho_epsilon^(1/p) (y) abs(f(x - y) - f(x)) dif y \ 
  "(Holder's)" wide&<= (integral rho_epsilon (y) abs(f(x - y) - f(x))^p dif y)^(1\/p) underbrace((integral rho_epsilon (y) dif y)^(1\/q), = 1),
  $ and hence $
  integral abs((rho_epsilon convolve f) (x) - f(x))^p dif x &<= integral.double rho_epsilon (y) abs(f(x - y) - f(x))^p dif y dif x \ 
  ("Tonelli's") wide &= integral_(B_epsilon) rho_epsilon (y) underbrace(integral abs(f(x - y) - f(x))^p dif x, epsilon < delta => eta^p) dif y \ 
  &< eta^p underbrace(integral_(B_epsilon) rho_epsilon (y) dif y, = 1) = eta^p,
  $ hence $norm((rho_epsilon convolve f) (x) - f(x))_p < eta$.

  _Step 2:_ We first claim that there exists some $C_epsilon$ such that for any $f in cal(F)$, $
  norm(rho_epsilon convolve f)_infinity <= C_epsilon norm(f)_p, wide (1)
  $ and that for any $x_1, x_2 in RR^d$, $
  abs((rho_epsilon convolve f)(x_1) - (rho_epsilon convolve f) (x_2)) <= C_epsilon norm(f)_p abs(x_1 - x_2). wide (2)
  $ In particular, this shows that _for $epsilon$ fixed_, $(rho_epsilon convolve f)$ satisfy hypothesis of AA. Remark that the first is a uniform boundedness type condition for $rho_epsilon convolve f$, and the second is a uniform Lipschitz bound.

  For the first claim (1), $
  abs((rho_epsilon convolve f) (x)) &= abs(integral rho_epsilon (x - y) f(y) dif y) \ 
  "(Holder's)"wide&<= (integral rho_epsilon^q (x - y) dif y)^(1/q) dot norm(f)_p \ 
  &= norm(rho_epsilon)_q norm(f)_p,
  $ so we have the bound with $C_epsilon := norm(rho_epsilon)_q$ since the bound is independent of $x$.
  #remark[
    One can explicitly compute $norm(rho_epsilon)_q$, and realize that it will in general depend explicitly on $epsilon$.
  ]
  For the second statement (2), we find that $gradient (rho_epsilon convolve f) = (gradient rho_epsilon) convolve f$ since the RHS is finite, because $
  (gradient rho_epsilon convolve f)(x) = integral gradient rho_epsilon (x - y) f(y) dif y <= norm(gradient rho_epsilon)_q norm(f)_p.
  $ So, $
  norm(gradient (rho_epsilon convolve f))_infinity <= underbrace(norm(gradient rho_epsilon)_q, =: C_epsilon) norm(f)_p.
  $ By the mean-value theorem then, we have all together $
  norm((rho_epsilon convolve f)(x_1) - (rho_epsilon convolve f)(x_2)) &<= norm(gradient (rho_epsilon convolve f))_infinity abs(x_1 - x_2) \ 
  &<= C_epsilon norm(f)_p abs(x_1 - x_2).
  $ This proves (2).
  
  _Step 3:_ Next, we claim that for $eta > 0$ and fixed $epsilon < eta$ and $Omega subset.eq RR^d$ with finite measure, there exists $E subset.eq Omega subset.eq RR^d$ such that $E$ is bounded, i.e. $E subset.eq B(0, M)$ where $M$ sufficiently large, and moreover that $norm(f)_(L^p (Omega\\E)) < eta$ for every $f in cal(F)$.

  We have that $
  norm(f)_(L^p (Omega\\E)) <= norm(f - (rho_epsilon convolve f))_(L^p (RR^d)) + norm(rho_epsilon convolve f)_(L^p (Omega\\E)).
  $ By the very first step of the proof, the first term is $< eta$, so this is bounded by $
  &< eta + (integral_(Omega\/E) abs(rho_epsilon convolve f)^p dif x)^(1\/p) \ 
  & < eta + norm(rho_epsilon convolve f)_(infinity) |Omega\\E|^(1/p) \ 
  & < eta + C_epsilon norm(f)_p abs(Omega\\E)^(1/p).
  $ $C_epsilon$ finite and $norm(f)_p$ upper bounded uniformly over $cal(F)$, so it suffices to construct $E$ with the measure of $Omega\\E$ sufficiently small, so we can get $norm(f)_(L^p (Omega\\E)) < 2 eta$.

  _Step 4:_ Fix $eta > 0$. We claim $cal(F)|_(Omega)$ is totally bounded. Let $epsilon < delta$ then let $
  cal(H) := (rho_epsilon convolve cal(F))|_(overline(E)) = {rho_epsilon convolve f|_(E) : f in cal(F)}.
  $ $E subset.eq Omega subset.eq RR^d$ is bounded implies $overline(E)$ is compact. So by Step 2., we showed $(rho_epsilon convolve cal(F))$ satisfies hypotheses of AA on $overline(E)$. Hence, $cal(H)$ is precompact in $C(overline(E))$. Thus, since we have uniform convergence we certainly have $L^p$ convergence thus $cal(H)$ also precompact in $L^p (overline(E))$. Thus, for $eta > 0$, there exists ${overline(g)_i} subset.eq L^p (overline(E))$ such that $
  cal(H) subset.eq union.big_(i=1)^N B_(L^p (overline(E))) (overline(g)_i, eta). wide star.filled
  $ Let $g_i : Omega -> RR$ be given by $
  g_i (x) = cases(overline(g)_i & "on" E, 0 & "on" Omega\\E).
  $ Then, we claim $cal(F)|_(Omega) subset.eq union.big_(i=1)^N B_(L^p (Omega)) (g_i, 3 eta)$. If $f in cal(F)$ by $star.filled$, there is an $i$ such that $norm(rho_epsilon convolve f - overline(g)_i)_(L^p (overline(E))) < eta$. But also, $
  norm(f - g_i)_(L^p (Omega))^p &= integral_(Omega\\E) abs(f)^p dif x + integral_(overline(E)) abs(f - overline(g)_i)^p dif x \ 
  &= norm(f)_(L^p (Omega\\E)) + integral_(overline(E)) abs(f - overline(g)_i)^p dif x\
  "(Step 3.)" wide &<= eta^p + integral_(overline(E)) abs(f - overline(g)_i)^p dif x.
  $ Recall $(a + b)^(1/p) <= a^(1/p )+ b^(1/p)$. Applying this bound to the above, we find $
  norm(f - g_i)_(L^p (Omega)) &<= eta + norm(f - overline(g)_i)_(L^p (overline(E))) \ 
  &<=eta + underbrace(norm(f - f ast rho_epsilon)_(L^p (RR^d)), < eta "by Step 1.") +underbrace(norm((f ast rho_epsilon) - overline(g)_i)_(L^p (overline(E))), < eta "by" star.filled) \ 
  & <= 3 eta.
  $ Hence, $cal(F)|_(Omega) subset.eq union.big_(i=1)^N B(g_i, 3 eta)$, thus $cal(F)|_(Omega)$ is sequentially compact so any sequence in $cal(F)$ has a converging subsequence, which proves the theorem.
]

#remark[
  This can be extended to $L^p (RR^d)$ with some conditions.
]

= Introduction to Fourier Analysis

References are Folland, Chapter 8 and _Fourier Analysis_ by Stein & Sharkarchi.

== Fourier Series

We will denote the torus $TT = [0, 1) tilde.eq RR\/ZZ$ (with $1$ identified back with $0$), and specifically complex-valued functions on the torus $
L^2 (TT) = {f : TT -> CC thin thin thin #vbar(2em) thin thin thin integral_(0)^1 abs(f(x))^2 dif x < infinity},
$ where now $abs(dot)$ the modulus (i.e. $abs(a + b i)^2 = a^2 + b^2$). Equivalently, $f : TT -> CC$ can be identified with $tilde(f) : RR -> CC$ which is periodic.

#proposition[
  The function $L^2 (TT) times L^2 (TT) -> CC$ $
  (f, g) = integral_(0)^1 f(x) overline(g(x)) dif x
  $ is an inner product on $L^2 (TT)$. In particular, $(L^2 (TT), (dot,dot))$ a Hilbert space.
]

#proof[
  For $CC$-valued functions, we need to check: 
  - linearity in the first variable: for $alpha in CC$, $
  (alpha f + h, g) =integral_(0)^1 (alpha f + h) overline(g) dif x = alpha (f, g) + (h, g)
  $ by linearity of the integral;
  - conjugate symmetry: $
  integral_0^1 f(x) overline(g(x)) dif x &= integral_(0)^1 ("Re"(f) + i"Im"(f))("Re"(g) - i"Im"(g)) dif x \ 
  &=: integral_(0)^1 (a  + i b)(c - i d) dif x \ 
  &= integral_(0)^1 (a c + b d) + i (b c -  a d) dif x \
  &= integral_(0)^1 (a c + b d ) - i (a d - b c) dif x\
  &= overline(integral_(0)^1 g overline(f) dif x) = overline((g, f));
  $
  - $f$ inner product with $f$ properties:  $
  (f, f) &= integral_(0)^1 f(x) overline(f(x)) dif x = integral_(0)^1 abs(f(x))^2 dif x = norm(f)_(L^2 (TT))^2 >= 0, = 0 "iff" f equiv 0.
  $
  We know $L^2 (TT)$ is complete, so $L^2 (TT)$ a Hilbert space with this inner product since it induces the same norm as the usual norm $L^2$-norm.
]

#theorem[
  Let $e_n (x) := e^(2 pi i n x)$ for $n in ZZ$. Then, ${e_n}_(n in ZZ)$ is an orthonormal basis of $L^2 (TT)$.
]

#proof[
  For orthonormality, if $n eq.not m$, $
  (e_n, e_m) &= integral_(0)^1 e^(2 pi i n x) e^(- 2 pi i m x) dif x \ 
  &= integral_(0)^1 e^(2 pi i (n - m) x) dif x \ 
  &= 1/(2pi i (n - m)) e^(2 pi i (n - m) x ) thin #vbar(2em)_(thin 0)^(thin 1) \
  &= 1/(2 pi i (n - m)) [e^(2 pi i (n - m)) - 1] \ 
  &= 1/(2 pi i (n - m)) [underbrace(cos (2 pi (n - m)), = 1) + underbrace(i sin (2 pi (n - m)), = 0) - 1] = 0,
  $ and if $n = m$, $
  (e_n, e_n) = integral_(0)^1 abs(e^(2 pi i n x))^2 dif x = integral_(0)^1 1 dif x = 1.
  $ To prove its a basis, we use Stone-Weierstrass. $TT$ is compact; let $
  cal(A) := {sum_(n=-N)^N alpha_n e_n : alpha_n in CC, N in NN}.
  $ Notice $e_n e_m = e^(2 pi i (n + m) x) = e_(n + m)$, and $e_0 = 1$, so this family stays closed under multiplication (and clearly addition and scalar multiplication by definition), so is an algebra which contains constant functions. Also, if $x_1 eq.not x_2$ and $x_1, x_2 in [0, 1)$, then if $n eq.not 0$, $e_n (x_1) = e^(2 pi i n x_1) eq.not e^(2 pi i n x_2) = e_n (x_2)$, so $cal(A)$ separates points. By (complex) Stone-Weierstrass, then we know $cal(A)$ is dense in $C(TT, CC)$ with respect to $norm(dot)_infinity$. We know $C(TT, CC)$ is dense in $L^2 (TT)$ (by some mollifier argument, for example) with respect to $norm(dot)_(L^2 (TT))$. So, $
  f(x) = lim_(N->infinity) sum_(n=-N)^N alpha_n e_n (x),
  $ with the limit taken in the sense of $L^2 (TT)$.
]

Recall that in Hilbert spaces, TFAE:
- ${e_n}$ are a basis, i.e. $f = sum_(n=-infinity)^infinity alpha_n e_n = sum_(n=-infinity)^infinity (f, e_n) e_n$, in $L^2 (TT)$;
- if $(f, e_n) = 0$ for every $n$, $f equiv 0$ (completeness);
- $norm(f)_(L^2 (TT))^2 = sum_(n=-infinity)^infinity abs((f, e_n))^2$ (Parseval's).
With this in mind, we define:

#definition("Fourier Series")[
Let $
hat(f)(n) := (f, e_n) = integral_0^1 f(x) e^(- 2 pi i n x) dif x.
$ Then, the _complex Fourier series_ is defined by $
sum_(n=-infinity)^infinity hat(f)(n) e^(2 pi i n x).
$
]

#remark[
  A Fourier series can be defined for any periodic function, while we only do so for $1$-periodic here. If $f$ were $L$-periodic, we'd define $
  hat(f)_L (n) := 1/L integral_(0)^L f(x) e^((-2 pi i n x)/L) dif x,
  $ with complex Fourier series $sum_(n=-infinity)^infinity hat(f)_L (n) e^((2 pi i n x)/L)$.
]

#remark[
  We can also make Fourier series to be real-valued, with sines and cosines, of the form $
  A_0 + sum_(n=1)^infinity [A_n cos ((2 n pi x)/L) + B_n sin((2 n pi x)/L)],
  $ for some $A_n, B_n$ also given by inner products.
]

What conditions do we need on $f$ to make this series converge? In the general $L^2$-theory, we just need $f in L^2 (TT)$. By Parseval's, $
norm(f)_(L^2 (TT))^2 = sum_(n=-infinity)^infinity abs(hat(f)(n))^2.
$ So, the operator $hat(dot) : L^2 (TT) -> ell^2 (CC)$. Note that this implies $lim_(n->infinity) abs(hat(f)(n))^2 = 0,$ so also $lim_(n->infinity) abs(hat(f)(n)) = 0$. This proves the following proposition:

#proposition("Riemann-Lebesgue Lemma")[
  If $f in L^2 (TT)$, $
  lim_(n->infinity) abs(hat(f)(n)) = 0.
  $
]

#remark[
  This result in _very_ useful, particularly for the real Fourier Series. In particular, it tells us statements such as $
  lim_(n->infinity) integral_(0)^1 f(x) sin(2n pi x) dif x = 0,
  $ with similar for the cosine term. These are so-called "oscillatory integrals".
]

While the $L^2 (TT)$-theory is very useful for Hilbert space interpretation, we are really concerned with the partial sums $
S_N (x) = sum_(n=-N)^N hat(f)(n) e^(2 pi i n x),
$ and ways it might converge. We may rewrite by definition $
S_N (x) &= sum_(n=-N)^N (integral_(0)^1 f(y) e^(- 2pi i n y) dif y) e^(2 pi i n x) \ 
("because finite sum") wide &= integral_(0)^1 f(y) sum_(n=-N)^N e^(2 pi i n (x - y)) dif y \ 
(convolve "just over" [0, 1)) wide &= (f ast D_N) (x), wide D_N (x) := sum_(n=-N)^N e^(2 pi i n x).
$ So in short, $
S_N (x) = (f ast D_N) (x),
$ where $D_N (x)$ is called the _Dirichlet kernel_. Let's look at some of its properties.

$
D_N (x) &= 1 + sum_(n=1)^N [e^(2 pi i n x) + e^(- 2pi i n x)] ,
$ so $
integral_(0)^1 D_N (x) dif x = integral_(0)^1 1 dif x + underbrace(sum_(n=1)^N integral_(0)^1 ("some periodic functions"), = 0) = 1, 
$ by periodicity. However, $D_N (x)$ is not actually a good kernel; one can show that $integral_(0)^1 abs(D_n (x)) dif x >= C log N$ as $N->infinity$.

#theorem("Pointwise Convergence")[
  Let $f in L^2 (TT)$ and suppose $f$ is Lipschitz continuous at $x_0$. Then, $
  S_N (x_0) -> f(x_0).
  $
]
#proof[
  Left as an exercise. 
  
  // !
  // $f$ Lipschitz so in particular it is continuous. Let $epsilon > 0$ and $delta > 0$ such that $abs(x - y_0) < delta => abs(f(x) - f(y_0)) < epsilon$, and let $C$ be a Lipschitz constant. Then,
  // $
  // abs(S_N (x_0) - f(x_0)) &= abs((f ast D_N) (x_0) - f(x_0)) \ 
  // &= abs(integral_(0)^1 D_N (y) f(x_0 - y) dif y - integral_(0)^1 D_N (y) f(x_0) dif y ) wide "since" D_N "integrates to" 1 \ 
  // &= abs(
  //   integral_(0)^1 D_N (y) (f(x_0 - y) - f(x_0)) dif y
  // )\
  // &<= integral_(abs(y) < delta) abs(D_N (y)) abs(f(x_0 - y) - f(x_0)) dif y + C integral_(abs(y) >= delta) abs(D_N (y)) abs(y) dif y\
  // & <= epsilon integral_(abs(y) < delta) abs(D_N (y)) + 2 C integral_(y >= delta) abs(D_N (y)) y dif y\
  // $
] 

Note that $
  D_N (x) &= sum_(n=-N)^N e^(2pi i n x) \
  &= sum_(n=0)^(2 N) e^(2 pi i (n - N) x) \ 
  &= e^( - 2 pi i N x) sum_(n=0)^(2N) (e^(2 pi i x))^n \ 
  &= e^(- 2 pi i N x) ((1 - e^(2 pi i (2N + 1 ))x)/(1 - e^(2 pi i x))) wide "(geometric series)" \ 
  &= (e^(-2 pi i N x) - e^(2 pi i (N + 1) x))/(1 - e^(2 pi i x)) dot (e^(- 2 pi i x/2))/(e^(- 2 pi i x/2))\
  &= (e^(- 2pi i (N + 1/2) x) - e^(2 pi i (N+ 1/2) x))/(e^(- 2 pi i x/2)- e^(2 pi i x/2)) \ 
  &= (sin(2pi (N+ 1/2) x))/(sin(2 pi x/2)).
$

#theorem("Uniform convergence")[
  If $f in C^2 (TT)$, then $S_N (x) -> f(x)$ uniformly on $TT$.
]

#proof[
  Exercise.
]

#remark[
  In fact, we see that $hat(f)(n) = integral_(0)^1 f(x) e^(- 2pi i n x) dif x$ is well-defined whenever $f in L^1 (TT)$. So, we can view $
  hat(dot) : L^1 (TT) -> ell^infinity (CC).
  $
]

#remark[
  All the prior results can be extended to $f in L^1 (TT)$, via density.
]

== Introduction to the Fourier Transform

#definition("Fourier Transform")[
  Let $f : RR -> CC$. Then, for any $zeta in RR$, define $
  hat(f)(zeta) := integral_(RR) f(x) e^(-2 pi i zeta x) dif x.
  $
]

#remark[
  If $f in L^1 (RR)$, $
  abs(hat(f)(zeta)) <= integral_(-infinity)^infinity abs(f(x)) underbrace(abs(e^(-2 pi i zeta x)), =1) dif x = norm(f)_(L^1 (RR))
  $ so in particular, $hat(f) in L^infinity (RR)$. Moreover, $
 abs(hat(f)(zeta + h) - hat(f)(zeta)) &= abs(integral_(RR) f(x) e^(-2 pi i (zeta + h) x) - f(x) e^(-2 pi i zeta x) dif x) \ 
 &= abs(integral_(RR) f(x) e^(-2 pi i zeta x) (e^(-2 pi i h x )-1)) \ 
 &<= integral_(RR) abs(f(x)) abs(e^(-2 pi i h x) - 1) dif x.
  $ We have that $
  lim_(h -> 0) abs(e^(-2 pi i h x) - 1) = 0
  $ for a.e. $x in RR$, and $
  integral_(RR) abs(f(x)) abs(e^(-2 pi i h x - 1)) dif x <= 2 integral_(RR) abs(f(x)) dif x = 2 norm(f)_(L^1 (RR)),
  $ so we can apply dominated convergence theorem to find $
  lim_(h -> 0) abs(hat(f)(zeta + h) - hat(f)(zeta)) <= integral_(RR) abs(f(x)) underbrace(lim_(h -> 0) abs(e^(-2 pi i h x) - 1), = 0) dif x  = 0,
  $ so $hat(f) in C(RR)$.
]

#proposition("Properties of the Fourier Transform")[
  Let $f in L^1 (RR)$ and $g in L^1 (RR)$. Then,\
  a. $hat(tau_y f) (zeta) = e^(-2 pi i zeta y) hat(f)(zeta)$, and $tau_eta hat(f)(zeta) = hat(e^(2pi i eta (dot)) f(dot)) (zeta)$;\
  b. $hat(f convolve g) = hat(f)dot hat(g)$;\
  c. $integral_(RR) f(x) hat(g)(x) dif x = integral_(RR) hat(f)(x) g(x) dif x$.
]

#proof[
a. A change of variables gives $
hat(tau_y f) (zeta) = integral_(RR) f(x - y) e^(-2 pi i zeta x) dif x = e^(-2pi i zeta y) integral_(RR) f(x) e^(-2 pi i zeta x) dif x = e^(-2 pi i zeta y) hat(f)(zeta).
$ Similarly, $
tau_eta hat(f)(zeta) = integral_(RR) f(x) e^(-2 pi i (zeta - eta) x) dif x = integral_(RR) f(x) e^(2 pi i eta x) dot e^(-2 pi i zeta x) dif x = hat(e^(2 pi i eta (dot)) f(dot))(zeta). 
$

b. First, by Young's inequality $f convolve g in L^1 (RR)$ so this makes sense. Moreover, since $f, g in L^1 (RR)$, everything we need to be finite is finite, so we can apply Fubini's theorem to find $
hat(f convolve g)(zeta) &= integral (integral f(x - y) g(y) dif y) e^(-2 pi i zeta x) dif x \
&= integral (integral f(x - y) e^(-2 pi i zeta x) dif x) g(y) dif y \ 
&= integral (integral f(x -y) e^(-2 pi i zeta (x - y)) dif x) e^(- 2 pi zeta y) g(y) dif y \ 
&= (integral f(x) e^(- 2pi i zeta x) dif x) (integral g(y) e^(-2 pi i zeta y) dif y) = hat(f) (zeta) dot hat(g) (zeta),
$ where we "multiply by 1" in the second to last line to change variables in the appropriate way.

c. We can apply Fubini's again, $
integral f(x) hat(g)(x)  dif x &=  integral f(x) (integral g(y) e^(-2 pi i x y) dif y) dif x \
&= integral g(y) (integral f(x) e^(- 2pi i x y) dif x )dif y \ 
&= integral g(y) hat(f)(y) dif y.
$
]

#lemma[
  Let $f(x) = e^(- pi a x^2)$ for $a > 0$. Then, $
  hat(f)(zeta) = 1/sqrt(a) e^(- pi (zeta^2)/a).
  $
]

#proof[
  First, note that $
  hat(dif/(dif x) f) (zeta) &= integral_(-infinity)^infinity f' (x) e^(-2 pi i zeta x) dif x \ 
  &= f(x) e^(- 2pi i zeta x) thin #vbar(2em)_(thin x = -infinity)^(thin infinity)  - integral_(-infinity)^infinity f(x) (- 2 pi i zeta) e^(- 2 pi i zeta x) dif x.
  $ Specifying $f(x) = e^(-2 pi a x^2)$, this becomes $
  &= e^(- pi a x^2) dot e^(- 2pi i zeta x)  thin #vbar(2em)_(thin x = -infinity)^(thin infinity) - integral_(-infinity)^infinity e^(- pi a x^2) (-2 pi i zeta) e^(-2 pi i zeta x) dif x \ 
  &= 2 pi i zeta  dot integral_(-infinity)^infinity e^(- pi a x^2) e^(-2 pi i zeta x) dif x = 2pi i zeta dot hat(f)(zeta).
  $ On the other hand, $
  dif/(dif zeta) hat(f)(zeta) &= dif/(dif zeta) (integral_(-infinity)^infinity f(x) e^(-2 pi i zeta x) dif x)\ 
  &= integral_(-infinity)^infinity f(x) (-2 pi i x) e^(-2 pi i zeta x) dif x,
  $ assuming finiteness; indeed, $
  abs(integral_(-infinity)^infinity e^(- pi a x^2) (- 2 pi x) e^(-2 pi i zeta x) dif x) &<= C integral_(-infinity)^infinity abs(x) e^(- pi a x^2) dif x\
  &= 2 C integral_(0)^infinity x e^(- pi a x^2) dif x = C e^(- pi a x^2) #vbar(2em)_(thin 0)^( thin infinity) < infinity,
  $ so our differentiation was valid. Thus, combining these two, $
  dif/(dif zeta) hat(f)(zeta) &= integral_(-infinity)^infinity - 2 pi i x f(x) e^(-2 pi i zeta x) dif x \
  &= integral_(-infinity)^infinity i (- 2 pi x e^(- pi a x^2)) e^(-2 pi i zeta x) dif x \ 
  &= integral_(-infinity)^infinity i/a f'(x)  e^(- 2 pi i zeta x) dif x \ 
  &= i/a 2 pi i zeta hat(f)(zeta) \
&=> dif/(dif zeta) hat(f)(zeta) = - (2pi)/a zeta hat(f)(zeta). 
  $ Thus, $
  dif/(dif zeta) (e^((pi zeta^2)/a) hat(f)(zeta)) = e^((pi zeta^2)\/a) (-(2 pi)/a zeta hat(f)(zeta)) + (2 pi zeta)/a  e^((pi zeta^2)\/a) hat(f)(zeta) = 0,
  $ and thus $e^((pi zeta^2)/a) hat(f)(zeta)$ is constant in $zeta$ so $e^((pi zeta^2)/a) hat(f)(zeta) = hat(f)(0) = integral_(-infinity)^infinity e^(- pi a x^2) dif x = 1/sqrt(a)$. Thus, $hat(f)(zeta) = 1/sqrt(a) e^(- (pi zeta^2)/a)$.
]

With this, we are ready to define the inverse Fourier transform;

#definition("Inverse Fourier Transform")[
  If $f in L^1 (RR)$, then $
  caron(f)(x) := integral_(RR) f(zeta) e^(2 pi i zeta x) dif zeta = hat(f(- dot))(x).
  $
]

#remark[By similar computations to before, $f in L^1 (RR)$ implies $caron(f) in L^infinity (RR) sect C(RR)$.]

#remark[
  One would hope $caron(hat(f)) = f$. However, if we check, naively, $
  caron(hat(f))(x) &= integral (integral f(x) e^(-2 pi i zeta y) dif y) e^(2 pi i zeta x) dif zeta;
  $ however the integral may not be finite in general, i.e. we cannot switch the integrals for free. We must be more careful, in short.
]

#theorem("Fourier Inversion")[
If $f in L^1 (RR)$ and $hat(f) in L^1 (RR)$, then $f$ agrees almost everywhere with some $f_0in C(RR)$, and $caron(hat(f)) = hat(caron(f)) = f_0$.
]

#proof[
  Let $epsilon > 0$ and $x in RR$. Let $phi(zeta) := e^(2 pi i x zeta) e^(- pi epsilon zeta^2)$. Then, $
  hat(f)(y) &= integral phi(zeta) e^(-2 pi i y zeta) dif zeta\
  &= integral e^(2 pi i x zeta) e^(- pi epsilon zeta^2) e^(- 2 pi i y zeta) dif zeta\
  &= hat(e^(2 pi i x (dot)) e^(-pi epsilon (dot)^2))(y)\
  &= tau_x hat(e^(- pi epsilon (dot)^2)) (y) \
  &= tau_x (1/sqrt(epsilon) e^(- (pi y^2)/epsilon)) \
  &= 1/(sqrt(epsilon)) e^(- pi/epsilon (y - x)^2).
  $ Since $integral f hat(phi) dif y = integral hat(f) phi dif y$, we find $
  integral f(y) 1/sqrt(epsilon) e^(- pi/epsilon (x - y)^2) &= integral hat(f)(y) phi(y) dif y.
  $ Let $K_epsilon (y) := 1/sqrt(epsilon) e^(- pi/epsilon y^2)$. Recall that this is the good kernel that we used in the proof of the Weierstrass Approximation Theorem. In particular, the formula equation above can be written $
  (f ast K_epsilon) (x) = integral hat(f)(y) e^(2 pi i x y) e^(- pi epsilon y^2) dif y. wide ast.circle
  $ Recall that if $f$ is continuous at $x$ and compactly-supported, then $lim_(epsilon -> 0) abs((f ast K_epsilon) (x) - f(x)) = 0$. This implies that for every $f in L^1 (RR)$ $lim_(epsilon -> 0) norm((f ast K_epsilon) - f)_1 = 0$. So, taking $epsilon -> 0$ in $ast.circle$, $f(x) =_(L^1 (RR)) lim_(epsilon -> 0) integral hat(f)(y) e^(2 pi i x y) e^(- pi epsilon y^2) dif y$. $hat(f) in L^1 (RR)$, so by DCT we can pass the limit inside, so $
  f(x) =_(L^1 (RR)) integral hat(f)(y) e^(2 pi i x y) dif y = caron(hat(f)) (x).
  $ This equality in $L^1 (RR)$ thus gives $caron(hat(f)) = f$ a.e.. A similar proof follows for showing $hat(caron(f)) = f$ a.e. by replacing $e^(2 pi i x)$ with $e^(-2 pi i x)$ everywhere it appears. Since $(hat(caron(f))), (caron(hat(f)))$ are continuous by our remarks earlier, it follows that $f$ is equal to a continuous function almost everywhere.
]

So far, all we've worked with is $f in L^1 (RR)$, which results in $hat(f) in L^infinity (RR)$. Really, we'd like to extend the Fourier transform to be $L^2 (RR)$, since this is a nice Hilbert space. To do so, we need the following:

#theorem("Plancherel's Theorem")[
Let $f in L^1 (RR) sect L^2 (RR)$. Then $hat(f) in L^2 (RR)$ and $norm(f)_(L^2 (RR)) = norm(hat(f))_(L^2 (RR))$.
]

#remark[
  One can view Plancherel's Theorem as a type of continuous analog of Parseval's identity for Fourier Series.
]

#proof[
  Let $f(x) in L^1 (RR) sect L^2 (RR)$, and put $g(x) := overline(f(-x))$, noting that then $g in L^1 (RR) sect L^2 (RR)$ as well. Put $
  w(x) := (f ast g)(x).
  $ By Young's, $
  norm(w)_(L^1 (RR)) &<= norm(f)_(L^1 (RR)) norm(g)_(L^1 (RR)) < infinity
  $ so $w in L^1 (RR)$.

  We claim $w$ continuous at $0$. For $h$ sufficiently small, we find $
  abs(w(h) - w(0)) &= abs(integral_(RR) f(h - y) g(y) dif y - integral_RR f(-y) g(y) dif y) \
  &= abs(integral_(RR) (f(h - y) - f(-y)) g(y) dif y) \ 
  &<= norm(f(h - dot) - f(-dot))_(L^2 (RR)) norm(g)_(L^2 (RR))\
  &<= norm(tau_h f - f)_(L^2 (RR)) norm(g)_(L^2 (RR)).
  $ Let $tilde(f) in C_c (RR)$ such that $norm(f - tilde(f))_(L^2 (RR)) < eta$ for some small $eta > 0$. Then we further bound $
  norm(tau_h f - f)_(L^2 (RR)) &<= norm(tau_h f - tau_h tilde(f))_(L^2 (RR)) + norm(tau_h tilde(f) - tilde(f))_(L^2 (RR)) + norm(tilde(f) - f)_(L^2 (RR))\
  "(since norm translation invariant)" wide &= 2norm(tilde(f) - f)_(L^2 (RR)) + norm(tau_h tilde(f) - tilde(f))_(L^2 (RR)) \ 
  &<= 2 eta + norm(tau_h tilde(f) - tilde(f))_(L^2 (RR)).
  $ Now, $tilde(f) in C_c (RR)$ and thus is uniformly continuous hence $abs(tau_h tilde(f) (x) - tilde(f) (x)) -> 0$ uniformly on $RR$ hence $norm(tau_h tilde(f) - tilde(f))_(L^2 (RR)) -> 0$ as well, as $h -> 0$. Finally, since $norm(g)_(L^2 (RR))$ finite, we conclude indeed $w$ continuous at $0$.

  Next, notice that $hat(w) = hat(f)dot hat(g)$, and $
  hat(g)(zeta) = hat(overline(f(-dot)))(zeta) &= integral_RR overline(f(-x)) e^(-2pi i x zeta) dif x\
  &= integral_(RR) overline(f(-x) e^(2 pi i x zeta)) dif x \ 
  &= overline(integral_(RR) f(-x) e^(2pi i x zeta) dif x) \ 
  &= overline(integral_(RR) f(x) e^(-2pi i x zeta) dif x)\
  &= overline(hat(f) (zeta)),
  $ so $
  hat(w) = hat(f) dot overline(hat(f)) = abs(hat(f))^2 >= 0.
  $ Recall our good kernel from the Weierstrass Approximation Theorem, $K_epsilon (y) = 1/(sqrt(epsilon)) e^(-pi/epsilon y^2) = hat(e^(- pi epsilon (dot)^2))$. So, $
  integral hat(w)(y) e^(-pi epsilon y^2) dif y &= integral w(y) 1/sqrt(epsilon) e^(- (pi y^2)\/epsilon) dif y \ 
  &= integral w(y) K_epsilon (y) dif y \ 
  "(by symmetry)"wide&= integral w(y) K_epsilon (-y) dif y \
  &= (w convolve K_epsilon)(0).
  $ On the LHS, $hat(w) >= 0$ so $hat(w) (y) e^(- pi epsilon y^2) arrow.tr_(epsilon -> 0^+) hat(w)(y)$ so by monotone convergence, $integral hat(w) e^(- pi epsilon y^2) ->_(epsilon -> 0) integral hat(w)(y) dif y$. On the other hand, we claim $(w ast K_epsilon)(0) ->_(epsilon -> 0) w(0)$ (this isn't immediate from the fact that $K_epsilon$ is a good kernel because we don't know a priori that $w$ (essentially) bounded). Supposing this claim holds, this implies $integral hat(w)(y) dif y = w(0)$, hence $
  integral hat(w)(y) dif y = integral |hat(f)(y)|^2 dif y &= w(0) \
  &= (f ast g)(0) \ 
  &= integral f(y) overline(f(0-(-y))) dif y\
  &= integral |f(y)|^2 dif y,
  $ which precisely means $norm(hat(f))_(L^2 (RR)) = norm(f)_(L^2 (RR))$.

   To prove the claim of $(K_epsilon ast w)(0)->w(0)$, let $eta > 0$. Since $w$ continuous at $0$, there is a $delta > 0$ such that $|y| < delta => |w(y) - w(0)| < eta$. Then, $
   abs(integral w(0 - y) K_epsilon (y) dif y - w(0)) &= abs(integral (w(-y) - w(0)) K_epsilon (y) dif y) \ 
   &<= eta integral_(abs(y) < delta)  K_epsilon (y) dif y + integral_(abs(y) > delta) abs(w(0)) K_epsilon (y) dif y + integral_(abs(y) > delta) abs(w(-y)) K_epsilon (y) dif y \ 
   &<= eta dot 1 + underbrace(|w(0)|, #stack(spacing: .3em, [$w$ cnts at 0], [so this finite])) dot underbrace(integral_(abs(y) > delta) K_epsilon (y) dif y, ->_(epsilon -> 0) 0 "since good kernel") + integral_(abs(y) > delta) abs(w(-y)) K_epsilon (y) dif y .
   $ It remains to show the last term $->0$. We have $
   integral_(abs(y) > delta) |w(-y)| K_epsilon (y) dif y &<= integral_(|y| > delta) |w(-y)| 1/(sqrt(epsilon)) e^(- pi (delta^2)/epsilon) dif y \ 
   &<= underbrace(1/sqrt(epsilon) e^(-pi (delta^2)/epsilon), -> 0 "as" epsilon -> 0) dot norm(w)_(L^1 (RR)) -> 0.
   $ This completes the proof.
]