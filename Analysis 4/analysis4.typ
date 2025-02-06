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
  Given a topological space $(X, cal(T))$, let $x in X$. A collection $cal(B)_x$ of neighborhoods of $x$ is called a _base_ of $cal(T)$ at $x$ if for every neighborhood $cal(U)$ of $x$, there is a set $B in cal(B)_x$ such that $B subset.eq cal(U)$. 

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
  Let $K$ compact be contained in a Hausdorff space $X$. Then, $K$ closed in $X$.
]

#definition("Sequential Compactness")[
  We say $(X, cal(T))$ _sequentially compact_ if every sequence in $X$ has a converging subsequence with limit contained in $X$.
]

#proposition[
  Let $(X, cal(T))$ second countable. Then, $X$ compact $<=>$ sequentially compact.
]

#theorem[If $X$ compact and Hausdorff, $X$ normal.]

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

#remark[
  On $RR$, $C subset.eq RR$ connected $<=>$ an interval $<=>$ convex.
]

#definition("Intermediate Value Property")[
  We say $X$ has the intermediate value property (IVP) if $forall f in C(X)$, $f(X)$ an interval.
]

#proposition[
  $X$ has IVP $<=>$ $X$ connected.
]

#definition("Arcwise/Path Connected")[
  $X$ _arc connected/path connected_ if $forall x, y in X$, there exists a continuous function $f : [0, 1] -> X$ such that $f(0) = x, f(1) = y$.
]
#proposition[
  Arc connected $=>$ connected.
]

== Urysohn's Lemma and Urysohn's Metrization Theorem

#lemma("Urysohn's")[Let $A, B subset.eq X$ closed and disjoint subsets of a normal space $X$. Then, $forall [a, b] subset.eq RR$, there exists a continuous functions $f : [a, b]-> RR$ such that $f(X) subset.eq [a, b]$, $f|_A = a$ and $f|_B = b$.]

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
]

#lemma[Let $X$ normal, $F subset.eq X$ closed, and $cal(U)$ a neighborhood of $F$. Then, for any $(a, b) subset.eq RR$, there exists a dense subset $Lambda subset.eq (a, b)$ and a normally ascending collection ${cal(O)_lambda}_(lambda in Lambda)$ such that $
F subset.eq cal(O)_lambda subset.eq overline(cal(O))_lambda subset.eq cal(U), wide forall lambda in Lambda.
$]

#remark[
  This is essentially a generalization of the nested neighborhood property, and indeed the proof essentially just uses this property repeatedly to construct the collection ${cal(O)_lambda}$.
]

#proof("Of Urysohn's")[
  Let $F = A$ and $cal(U) = B^c$ as in the previous lemma. Then, there is some dense subset $Lambda subset.eq (a, b)$ and a normally ascending collection ${cal(O)_(lambda)}_(lambda in Lambda)$ such that $A subset.eq cal(O)_lambda subset.eq overline(cal(O))_lambda subset.eq B^c$ for every $lambda in Lambda$. Let $f(x)$ as in the previous previous lemma. Then, if $x in B$, $B subset.eq (union.big_(lambda in Lambda) cal(O)_lambda)^c$ and so $f(x) = b$. Otherwise if $x in A$, then $x in sect.big_(lambda in Lambda) cal(O)_lambda$ and thus $f(x) = inf{lambda in Lambda} = a$. By the first lemma, $f$ continuous, so we are done.
]

#theorem("Urysohn's Metrization Theorem")[
  Let $X$ be a second countable topological space. Then, $X$ is metrizable (that is, there exists a metric on $X$ that induces the topology) if and only if $X$ normal.
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

We tacitly assume the conditions of the theorem in the following lemmas.

#lemma[For every $F subset.eq X$ closed, and every $x_0 in F^c$, there exists a neighborhood $cal(U)(x_0)$ such that $F sect cal(U) = nothing$ and $forall epsilon > 0$ there is some $h in cal(A)$ such that $h < epsilon$ on $cal(U)$, $h > 1 - epsilon$ on $F$, and $0 <= h <= 1$ on $X$.

In particular, $cal(U)$ is _independent_ of choice of $epsilon$.
]

#lemma[
  For every disjoint closed set $A, B$ and $epsilon > 0$, there exists $h in cal(A)$ such that $h|_A < epsilon$, $h|_B > 1 - epsilon$, and $0 <= h <= 1$ on $X$.
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
  $
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