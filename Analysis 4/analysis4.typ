// ! external
#import "../typst/notes.typ": *
#import "../typst/shortcuts.typ": *

#import "@preview/cetz:0.2.2"

// ! configuration
#show: doc => conf(
  course_code: "MATH455",
  course_title: "Analysis 4",
  subtitle: "",
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


// #show math.equation: set text(font: "New Computer Modern Math") 
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
  We say $(X, rho)$ _complete_ if every cauchy sequence in $(X, rho)$ converges to a point in $X$.
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
  $(X, rho)$ _sequentially compact_ if every sequence in $X$ has a convergence subsequence whose limit is in $X$.
]

#definition("Relatively/Pre- Compact")[
  $E subset.eq X$ _relatively compact_ if $overline(E)$ compact.
]

#theorem[TFAE: 
- $X$ complete and totally bounded;
- $X$ compact;
- $X$ sequentially compact.
]

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
  Let $X$ separable and let ${f_n} subset.eq C(X)$ be pointwise bounded and equicontinuous. Then, there is a subsequence ${f_n_k}$ and a function $f$ which converges pointwise to $f$ on all of $X$.
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

#theorem("Arzelà-Ascoli")[
  Let $(X, rho)$ a compact metric space and ${f_n} subset.eq C(X)$ be a uniformly bounded and (uniformly) equicontinuous family of functions. Then, ${f_n}$ is pre-compact in $C(X)$, i.e. there exists ${f_n_k} subset.eq {f_n}$ such that $f_n_k$ is uniformly convergent on $X$.
]

#remark[
  If $K subset.eq X$ a compact set, then $K$ bounded and closed.
]

#theorem[Let $(X, rho)$ compact and $cal(F) subset.eq C(X)$. Then, $cal(F)$ a compact subspace of $C(X)$ iff $cal(F)$ closed, uniformly bounded, and (uniformly) equicontinuous.]

== Baire Category Theorem

We'll say a set $E subset.eq X$ _hollow_ if $"int" E = nothing$, or equivalently if $E^c$ dense in $X$.

#theorem[
  Let $X$ be a complete metric space. 

  (a) Let ${F_n}$ a collection of closed hollow sets. Then, $union.big_(n=1)^infinity F_n$ also hollow.

  (b) Let ${O_n}$ a collection of open dense sets. Then, $sect.big_(n=1)^infinity O_n$ also dense.
]

#corollary[Let $X$ complete and ${F_n}$ a sequence of closed sets in $X$. If $X = union.big_(n>=1) F_n$, there is some $n_0$ such that $"int"(F_n_0) eq.not nothing$.]

#corollary[
  Let $X$ complete and ${F_n}$ a sequence of closed sets in $X$. Then, $union.big_(n=1)^infinity partial F_n$ hollow.
]