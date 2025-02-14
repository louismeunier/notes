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

We'll say a set $E subset.eq X$ _hollow_ if $"int" E = nothing$, or equivalently if $E^c$ dense in $X$.

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
  If not, violates BCT since $X$ is not hollow in itself.
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

  - _1st countable_ if there is a countable base at each point
  - _2nd countable_ if there is a countable base for all of $cal(T)$.
]

#example[Every metric space is first countable.]

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
  cal(B) = {sect.big_(j=1)^n pi^(-1)_(lambda_j) (cal(O)_j)} = {product_(lambda in Lambda) cal(U)_lambda : cal(U)_lambda "open" "and all by finitely many " U_lambda's  = X_lambda}.
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
Our first claim is that for every $y in F$, there is a $g_y in cal(L)$ such that $g_y (x_0) = 0$ and $g_y (y) > 0$, and moreover $0 <= g_y <= 1$. Since $cal(A)$ separates points, there is an $f in cal(A)$ such that $f(x_0) eq.not f(y)$. Then, let $
g_y (x) := [(f(x) - f(x_0))/(||f - f(x)||_infinity)]^2.
$ Then, every operation used in this new function keeps $g_y in cal(A)$. Moreover one readily verifies it satisfies the desired qualities. In particular since $g_y$ continuous, there is a neighborhood $cal(O)_y$ such that $g_y|_(cal(O)_y) > 0$. Hence, we know that $F subset.eq union.big_(y in F) cal(O)_y$, but $F$ closed and so compact, hence there exists a finite subcover i.e. some $n >= 1$ and finite sequence ${y_i}_(i=1)^n$ such that $F subset.eq union.big_(i=1)^n cal(O)_(y_i)$. Let for each $y_i$ $g_y_i in cal(A)$  with the properties from above, and consider the "averaged" function $
g(x) := 1/n sum_(i=1)^n g_y_i (x) in cal(A).
$ Then, $g(x_0) = 0$, $g > 0$ on $F$ and $0 <= g <= 1$ on all of $X$. Hence, there is some $1 > c > 0$ such that $g >= c$ on $F$, and since $g$ continuous at $x_0$ there exists some $cal(U)(x_0)$ such that $g < c/2$ on $cal(U)$, with $cal(U) sect F = nothing$. So, $0 <= g|_(cal(U)) < c/2$, and $1 >= g|_(F) >= c$. To complete the proof, we need $(0, c/2) <-> (0, epsilon)$ and $(c, 1) <=> (1 - epsilon, 1)$. By the Weierstrass Approximation Theorem, there exists some polynomial $p$ such that $p|_([0, c/2]) < epsilon$ and $p|_([c, 1]) > 1 - epsilon$. Then if we let $h(x) := (p compose g) (x)$, this is just a polynomial of $g$ hence remains if $cal(A)$, and we find $
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
$ Let then $y' in Y$ be such that $
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