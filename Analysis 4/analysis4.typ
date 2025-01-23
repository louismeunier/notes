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

#theorem("Baire Category Theorem")[
  Let $X$ be a complete metric space. 

  (a) Let ${F_n}$ a collection of closed hollow sets. Then, $union.big_(n=1)^infinity F_n$ also hollow.

  (b) Let ${O_n}$ a collection of open dense sets. Then, $sect.big_(n=1)^infinity O_n$ also dense.
]

#corollary[Let $X$ complete and ${F_n}$ a sequence of closed sets in $X$. If $X = union.big_(n>=1) F_n$, there is some $n_0$ such that $"int"(F_n_0) eq.not nothing$.]

#corollary[
  Let $X$ complete and ${F_n}$ a sequence of closed sets in $X$. Then, $union.big_(n=1)^infinity partial F_n$ hollow.
]


// ! 01-16
=== Applications of Baire Category Theorem

#theorem[
  Let $cal(F) subset C(X)$ where $X$ complete. Suppose $cal(F)$ pointwise bounded. Then, there exists a nonempty, open set $cal(O) subset.eq X$ such that $cal(F)$ uniformly bounded on $cal(O)$.
]

#theorem[
  Let $X$ complete, and ${f_n} subset.eq C(X)$ such that $f_n -> f$ pointwise on $X$. Then, there exists a dense subset $D subset.eq X$ such that ${f_n}$ equicontinuous on $D$ and $f$ continuous on $D$.
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

#proposition[$E subset.eq X$ open $<=>$ for every $x in X$, there is a neighborhood of $x$ contained $E$.]

#example[
  Every metric space induces a natural topology given by open sets under the metric. The _discrete topology_ is given by $cal(T) = 2^X$ (and is actually induced by the discrete metric), and is the largest topology. The _trivial topology_ ${nothing, X}$ is the smallest.  The _relative topology_ defined on a subset $Y subset.eq X$ is given by $cal(T)_Y := {E sect Y : E in cal(T)}$.
]

#definition("Base")[
  Given a topological space $(X, cal(T))$, let $x in X$. A collection $cal(B)_x$ of neighborhoods of $x$ is called a _base_ of $cal(T)$ at $x$ if for every neighborhood $cal(U)$ of $x$, there is a set $B in cal(B)_x$ siuch that $B subset.eq cal(U)$. 

  We say a collection $cal(B)$ a base for all of $cal(T)$ if for every $x in X$, there is a base for $x, cal(B)_x subset.eq cal(B)$.
]

#proposition[
  If $(X, cal(T))$ a topological space, then $cal(B) subset.eq cal(T)$ a base for $cal(T)$ $<=>$ every nonempty open set $cal(U) in cal(T)$ can be written as a union of elements of $cal(B)$.
]

//  ! 01-21

#proposition[
$cal(B) subset.eq cal(T)$ a base $<=>$ 
- $X = union.big_(B in cal(B)) B$
- If $B_1, B_2 in cal(B)$ and $x in B_1 sect B_2$, then there is a $B in cal(B)$ such that $x in B subset.eq B_1 sect B_2$.
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
  cal(T)(S) = union.big {"finite intersection of elts of" S}.
  $
]

#definition("Point of closure/accumulation point")[
  If $E subset.eq X, x in X$, $x$ is called a _point of closure_ if $forall cal(U)_x$, $cal(U)_x sect E eq.not nothing$. The collection of all such sets is called the _closure_ of $E$, denote $overline(E)$. We say $E$ _closed_ if $E = overline(E)$.
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

#proposition[
  Every metric space normal.
]

// ! 01-23

#proposition[Let $X$ Tychonoff. Then $X$ normal $<=>$ $forall F subset.eq X$ closed and neighborhood $cal(U)$ of $F$, there exists an open set $cal(O)$ such that $
F subset.eq cal(O) subset.eq overline(cal(O)) subset.eq cal(U).
$ This is called the "nested neighborhood property" of normal spaces.]

#definition("Separable")[
  A space $X$ is called _separable_ if it contains a countable dense subset.
]

#definition("1st, 2nd Countable")[
  A topological space $(X, cal(T))$ is called 

  - _1st countable_ if there is a countable base at each point
  - _2nd countable_ if there is a countable base for all of $cal(T)$.
]

#example[Every metric space is first countable.]

#definition("Convergence")[
  Let ${x_n} subset.eq X$. Then, we say $x_n -> x$ in $cal(T)$ if for every neighborhood $cal(U)_x$, there exists an $N$ such that $forall n >= N$, $x_n in cal(U)_x$.
]

#remark[In general spaces, such a limit may not be unique. For instance, under the trivial topology, the only nonempty neighborhood is the whole space, so every sequence converges to every point in the space.]

#proposition[Let $(X, cal(T))$ be Hausdorff. Then, all limits are unique.]

#proposition[Let $X$ be 1st countable and $E subset.eq X$. Then, $x in overline(E)$ $<=>$ there exists ${x_j} subset.eq E$ such that $x_j -> x$.]

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
  cal(B) = {sect.big_(j=1)^n pi^(-1)_(lambda_j) (cal(O_j))} = {product_(lambda in Lambda) cal(U)_lambda : cal(U)_lambda "open" "and all by finitely many " U_lambda's  = X_lambda}.
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
  Let $K$ be contained in a Hausdorff space $X$. Then, $K$ closed in $X$.
]

#definition("Sequential Compactness")[
  We say $(X, cal(T))$ _sequentially compact_ if every sequence in $X$ has a converging subsequence with limit contained in $X$.
]

#proposition[
  Let $(X, cal(T))$ second countable. Then, $X$ compact $<=>$ sequentially compact.
]