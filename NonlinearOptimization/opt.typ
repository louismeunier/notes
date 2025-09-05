// ! external
#import "../typst/notes.typ": *
// #import "../typst/shortcuts.typ": *

#import "@preview/cetz:0.2.2"

// ! configuration
#show: doc => conf(
  course_code: "MATH378",
  course_title: "Nonlinear Optimization",
  // subtitle: "Abstract Metric, Topological Spaces; Functional Analysis.",
  semester: "Fall 2025",
  professor: "Prof. Tim Hoheisel",
  // cute: "../analysis 3/page.png",
  doc,
)

#import "@preview/commute:0.2.0": arr, commutative-diagram, node

#set align(left)

#let impliedby = $arrow.l.double$

#pagebreak()

= Preliminaries
== Terminology
We consider problems of the form $ "minimize" f(x) "subject to" x in X, wide (dagger) $<eqn:problem> with $X subset RR^n$ the _feasible region_ with $x$ a _feasible point_, and $f : X -> RR$ the _objective (function)_; more concisely we simply write $ min_(x in X) f(x). $ When $X = RR^n$, we say the problem $(dagger)$ is _unconstrained_, and conversely _constrained_ when $X subset.neq RR^n$.

#example("Polynomial Fit")[
  Given $y_1, dots, y_m in RR$ measurements taken at $m$ distinct points $x_1, dots, x_m in RR$, the goal is to find a degree $<=n$ polynomial $q : RR -> RR$, of the form $ q(x) =sum_(k=0)^n beta_k x^k, $  "fitting" the data ${(x_i, y_i)}_i$, in the sense that $q(x_i) approx y_i$ for each $i$. In the form of $(dagger)$, we can write this precisely as $ min_(beta in RR^(n+1)) 1/2 sum_(i=0)^n (underbrace(beta_n x_i^n + dots.c + beta_1 x_i + beta_0, q(x_i)) - y_i)^(2); $ namely, we seek to minimize the $ell^2$-distance between $(q(x_i))$ and $(y_i)$. If we write $ X := mat(
    1, x_1, dots, x_1^n; dots.v, dots, dots, dots.v;
    1, x_m, dots, x_m^n
  ) in RR^(m times (n + 1)), wide y := vec(y_1, dots.v, y_m) in RR^m, $ then concisely this problem is equivalent to $ min_(beta in RR^(n + 1)) 1/2 norm(X dot beta - y)_(2)^2, $ a so-called _least-squares problem_.
]

We have two related tasks:
1. Find the optimal value asked for by $(dagger)$, that is what $inf_(X) f$ is;
2. Find a specific point $overline(x)$ such that $f(overline(x)) = inf_(X) f$, i.e. the value of a point $ overline(x) in "argmin"_(X) f := {x in X | f(x) = inf_(X) f}. $ (noting that $"argmin"$ should be viewed as a set-valued function, as there may be multiple admissible minimizers) Notice that if we can accomplish 2., we've accomplished 1. by computing $f(overline(x))$.

Note that $overline(x) in "argmin"_X f => f(overline(x)) = inf_(X) f$, _but_ $inf_X f in RR$ does _not_ necessarily imply $"argmin"_X f eq.not nothing$, that is, there needn't be a feasible minimimum; for instance $inf_(x in RR) e^x = 0$, but $"argmin"_(RR) f = nothing$ (there is no $x$ for which $e^x = 0$).

#definition("Minimizers")[Let $X subset RR^n$ and $f : RR^n -> RR$. Then $overline(x) in X$ is called a
  - _global minimizer (of $f$ over $X$)_ if $f(overline(x)) <= f(x) forall x in X$, or equivalently if $overline(x) in "argmin"_(X) f$;
  - _local minimizer (of $f$ over $X$)_ if $f(overline(x)) <= f(x) forall x in X inter B_epsilon (overline(x))$ for some $epsilon > 0$.

  In addition, we have _strict_ versions of each by replacing "$<=$" with "$<$".
]

#definition("Some Geometric Tools")[
  Let $f : RR^n -> RR$.
  - $"gph" f := {(x, f(x)) | x in RR^n} subset.eq RR^n times RR$
  - $f^(-1) ({c}) := {x | f(x) = c} equiv$ _contour/level set at $c$_
  - $"lev"_c f := f^(-1) ((-infinity, c]) = {x | f(x) <= c}equiv$ _lower level/sublevel set at $c$_
]
#remark[
  - $"lev"_(inf f) f = "argmin" f$
  - assume $f$ continuous; then all (sub)level sets are closed (possibly empty)
]

We recall the following result from calculus/analysis:
#theorem("Weierstrass")[
  Let $f : RR^n -> RR$ be continuous and $X subset RR^n$ compact. Then, $"argmin"_X f eq.not nothing$.
]
From, we immediately have the following:
#proposition[
  Let $f : RR^n -> RR$ continuous. If there exists a $c in RR$ such that $"lev"_c f$ is nonempty and bounded, then $"argmin"_(RR^n) f eq.not nothing$.
]

#proof[
  Since $f$ continuous, $"lev"_c f$ is closed (being the inverse image of a closed set), thus $"lev"_c f$ is compact (and in particular nonempty). By Weierstrass, $f$ takes a minimimum over $"lev"_c f$, namely there is $overline(x) in "lev"_c f$ with $f(overline(x)) <= f(x) <= c$ for each $x in "lev"_c f$. Also, $f(x) > c$ for each $x in.not "lev"_c f$ (by virtue of being a level set), and thus $f(overline(x)) <= f(x)$ for each $x in RR^(n)$. Thus, $overline(x)$ is a global minimizer and so the theorem follows.
]

== Convex Sets and Functions

#definition("Convex Sets")[
  $C subset RR^n$ is _convex_ if for any $x, y in C$ and $lambda in (0, 1)$, $lambda x + (1 - lambda) y in C$; that is, the entire line between $x$ and $y$ remains in $C$.
]


#definition("Convex Fucntions")[
  Let $C subset RR^n$ be convex. Then, $f : C -> RR$ is called
  1. _convex (on $C$)_ if $ f(lambda x + (1 - lambda) y) <= lambda f(x) + (1 - lambda) f(y), $ for every $x, y in C$ and $lambda in (0, 1)$;
  2. _strictly convex (on $C$)_ if the inequality $<=$ is replaced with $<$;
  3. _strongly convex (on $C$)_ if there exists a $mu > 0$ such that $ f(lambda x + (1 - lambda ) y) + mu lambda (1 - lambda) norm(x - y)^2 <= lambda f(x) + (1 - lambda) f(y), $ for every $x, y in C$ and $lambda in (0, 1)$; we call $mu$ the _modulus of strong convexity_.
]

#remark[3\. $=>$ 2. $=>$ 1.]
#remark[A function is convex iff its epigraph is a convex set.]

#example[$exp : RR-> RR$, $log : (0, infinity) -> RR$ are convex. A function $f : RR^n -> RR^m$ of the form $f(x) = A x - b$ for $A in RR^(m times n), b in RR^m$ is called _affine linear_. For $m = 1$, every affine linear function is convex. All norms on $RR^n$ are convex.]

#proposition[
  1. _(Positive combinations)_ Let $f_i$ be convex on $RR^n$ and $lambda_i > 0$ scalars for $i = 1, dots, m$, then $sum_(i=1)^m lambda_i f_i$ is convex; as long as one is strictly (resp. strongly) convex, the sum is strictly (resp. strongly) convex as well.
  2. _(Composition with affine mappings)_ Let $f : RR^n -> RR$ be convex and $G : RR^m -> RR^n$ be affine. Then, $f compose G$ is convex on $RR^m$.
]

= Unconstrained Optimization

== Theoretical Foundations

We focus on the problem $ min_(x in RR^n) f(x), $ where $f : RR^n -> RR$ is continuously differentiable.

#definition("Directional derivative")[
  Let $D subset RR^n$ be open and $f : D -> RR$. We say $f$ _directionally differentiable_ at $overline(x) in D$ in the direction $d in RR^n$ if $ lim_(t -> 0^+) (f(overline(x) + t d) - f(overline(x)))/t $ exists, in which case we denote the limit by $f'(overline(x); d)$.
]

#lemma[Let $D subset RR^n$ be open and $f : D -> RR$ differentiable at $x in D$. Then, $f$ is directionally differentiable at $x$ in every direction $d$, with $ f'(x;d) = gradient f (x)^T d = angle.l gradient f(x), d angle.r. $]

#example("Directional derivatives of the Euclidean norm")[
  Let $f : RR^n -> RR$ by $f(x) = norm(x)$ the usual Euclidean norm. Then, we claim $ f'(x; d) = cases((x^T d)/(norm(x)) wide & x eq.not 0, norm(d) wide & x eq 0). $ For $x eq.not 0$, this follows from the previous lemma and the calculation $gradient f (x) = x/(norm(x))$. For $x = 0$, we look at the limit $ lim_(t -> 0^+) (f(0 + t d) - f(0))/(t) = lim_(t -> 0^+) (t norm(d) - 0)/t = norm(d), $ using homogeneity of the norm.
]

#lemma("Basic Optimality Condition")[
  Let $X subset RR^n$ be open and $f : X -> RR$. If $overline(x)$ is a _local minimizer_ of $f$ over $X$ and $f$ is directionally differentiable at $overline(x)$, then $f'(overline(x);d) >= 0$ for all $d in RR^n$.
]

#proof[
  Assume otherwise, that there is a direciton $d in RR^n$ for which the $f'(overline(x); d) < 0$, i.e. $ lim_(t -> 0^+) (f(overline(x) + t d) - f(overline(x)))/t < 0. $ Then, for all sufficiently small $t > 0$, we must have $ f(overline(x) + t d ) < f(overline(x)). $ Moreover, since $X$ open, then for $t$ even smaller (if necessary), $overline(x) + t d$ remains in $X$, thus $overline(x)$ cannot be a local minimizer.
]

#theorem("Fermat's Rule")[
  In addition to the assumptions of the previous lemma, assume further that $f$ is differentiable at $overline(x)$. Then, $gradient f (overline(x)) = 0$.
]

#proof[
  From the previous, we know $0 <= f'(overline(x);d)$ for any $d$. Take $d = - gradient f(overline(x))$, then using the representation of a directional derivative for a differentiable function, and the fact that norms are nonnegative, $ 0 <= -norm(gradient f (overline(x)))^2 <= 0, $ which can only hold if $norm(gradient f (overline(x))) = 0$ hence $gradient f(overline(x)) = 0$
]

We recall the following from Calculus:
#theorem("Taylor's, Second Order")[
  Let $f : D -> RR^n -> RR$ be twice continuously differentiable, then for each $x, y in D$, there is an $eta$ lying on the line between $x$ and $y$ such that $ f(y) = f(x) + gradient f(x)^T (y - x) + 1/2 (y - x)^T gradient^2 f(eta) (y - x). $
]

#theorem("2nd-order Optimality Conitions")[
  Let $X subset.eq RR^n$ open and $f : X-> RR$ twice continuously differentiable. Then, if $x$ a local minimizer of $f$ over $X$, then the Hessian matrix $gradient^2 f(x)$ is positive semi-definite.
]

#proof[
  Suppose not, then there exists a $d$ such that $d^T gradient^2 f(x) d < 0$. By Taylor's, for every $t > 0$, there is an $eta_t$ on the line between $x$ and $x + t d$ such that $ f(x + t d) & = f(x) + t underbrace(gradient f (x)^T, = 0) d + 1/2 t^2 d^T gradient^2 f(eta_t) d \
             & = f(x) + t^2/d^T gradient^2 f(eta_t) d. $ As $t -> 0^+$, $gradient^2 f(eta_t) -> gradient^2 f(x) < 0$. By continuity, for $t$ sufficiently small, $t^2/2 d^T gradient^2 f(eta_t) d < 0$ for $t$ sufficiently small, whence we find $ f(x + t d) < f(x), $ for sufficiently small $t$, a contradiction.
]

#lemma[
  Let $X subset RR^n$ open, $f : X -> RR$ in $C^2$. If $overline(x) in RR^n$ is such that $gradient^2 f(overline(x)) > 0$ (i.e. is positive definite), then there exists $epsilon, mu > 0$ such that $B_epsilon (overline(x)) subset X$ and $ d^T gradient^2 f(x) d >= mu norm(d)^2, wide forall d in RR^n, x in B_(epsilon) (overline(x)). $
]

Combining this and Taylor's Theorem, we can deduce the following (our first "sufficient" result of this section):

#theorem("Sufficient Optimality Condition")[
  Let $X subset RR^n$ open and $f in C^2 (X)$. Let $overline(x)$ be a stationary point of $f$ such that $gradient^2 f(overline(x)) > 0$. Then, $overline(x)$ is a _strict_ local minimizer of $f$.
]

=== Quadratic Approximation

Let $f : RR^n -> RR$ be $C^2$ and $overline(x) in RR^n$. By Taylor's, we can approximate $ f(y) approx g(y) := f(overline(x)) + gradient f(overline(x))^T (y - overline(x)) + 1/2 (y - overline(x))^T gradient^2 f(overline(x)) (y - overline(x)). $

#example("Quadratic Functions")[
  For $Q in RR^(n times n)$ symmetric, $c in RR^n$ and $gamma in RR$, let $ f : RR^n -> RR, wide f(x) = 1/2 x^T Q x + c^T x + gamma, $ a typical quadratic function. Then, $ gradient f(x) = 1/2 (Q + Q^T) x + c = Q x + c, wide gradient^2 f(x) = Q. $ We find that $f$ has _no_ minimizer if $c in.not "rge"(Q)$ or $Q$ is not positive semi-definite, combining our previous two results. In turn, if $Q$ is positive definite (and thus invertible), there is a unique local minimizer $overline(x) = - Q^(-1) c$ (_and_ global minimizer, as we'll see).
]

== Differentiable Convex Functions

#theorem[
  Let $C subset RR^n$ be open and convex and $f : C -> RR$ differentiable on $C$. Then:
  1. $f$ is convex (on $C$) iff $ f(x) >= f(overline(x)) + gradient f(overline(x))^T (x - overline(x)) wide star_1 $ for every $x, overline(x) in C$;
  2. $f$ is _strictly_ convex iff same inequality as 1. with strict inequality;
  3. $f$ is _strongly_ convex with modulus $sigma > 0$ iff $ f(x) >= f(overline(x)) + gradient f(overline(x))^T (x - overline(x)) + sigma/2 norm(x - overline(x))^2 wide star_2 $ for every $x, overline(x) in C$.
]

#proof[
  (1., $=>$) Let $x, overline(x) in C$ and $lambda in (0, 1)$. Then, $ f(lambda x + (1 - lambda) overline(x)) - f(overline(x)) <= lambda (f(x) - f(overline(x))), $ which implies $ (f(overline(x) + lambda (x - overline(x))) - f(overline(x)))/lambda <= f(x) - f(overline(x)). $ Letting $lambda -> 0^+$, the LHS $->$ the directional derivative of $f$ at $overline(x)$ in the direction $x - overline(x)$, which is equal to, by differentiability of $f$, $gradient f(overline(x))^T (x - overline(x))$, thus the result.

  (1., $impliedby$) Let $x_1, x_2 in C$ and $lambda in (0, 1)$. Let $overline(x) := lambda x_1 + (1 - lambda) x_2$. $star_1$ implies $ f(x_i) >= f(overline(x)) + gradient f(overline(x))^T (x_i - overline(x)), $ for each of $i = 1, 2$. Taking "a convex combination of these inequalities", i.e. multiplying them by $lambda, 1 - lambda$ resp. and adding, we find $ lambda f(x_1) + (1 - lambda) f(x_2) >= f(overline(x)) + gradient f(overline(x))^T (lambda x_1 + (1 - lambda) x_2 - overline(x)) = f(lambda x_1 + (1 - lambda) x_2), $ thus proving convexity.

  (2., $=>$) Let $x eq.not overline(x) in C$ and $lambda in (0, 1)$. Then, by 1., as we've just proven, $ lambda gradient f(overline(x))^T (x - overline(x)) <= f(overline(x) + lambda (x - overline(x))) - f(overline(x)). $ But $f(overline(x) + lambda (x - overline(x))) < lambda f(x) + (1 - lambda) f(overline(x))$ by strict convexity, so we have $ lambda gradient f(overline(x))^T (x - overline(x)) < lambda (f(x) - f(overline(x))), $ and the result follows by dividing both sides by $lambda$.

  (2., $impliedby$) Same as (1., $impliedby$) replacing "$<=$" with "$<$".

  (3.) Apply 1. to $f - sigma/2 norm(dot)^2$, which is still convex if $f$ $sigma$-strongly convex, as one can check.
]

#corollary[
  Let $f : RR^n -> RR$ be convex and differentiable. Then,\
  a) there exists an _affine function_ $g : RR^n -> RR$ such that $g(x) <= f(x)$ everywhere;\
  b) if $f$ strongly convex, then it is coercive, i.e. $lim_(norm(x)->infinity) f(x) = infinity.$
]

#corollary[
  Let $f : RR^n -> RR$ be convex and differentiable, then TFAE:
  1. $overline(x)$ is a global minimizer of $f$;
  2. $overline(x)$ is a local minimizer of $f$;
  3. $overline(x)$ is a stationary point of $f$.
]
#proof[
  $1. => 2.$ is trivial and $2. => 3.$ was already proven and $3. => 1.$ follows from the fact that differentiability gives $ f(x) >= f(overline(x)) + cancel(gradient(f)(overline(x))^T (x - overline(x))) $ for any $x in RR^n$.
]

#corollary[
  (2.2.4)
]

#theorem("Twice Differentiable Convex Functions")[
  Let $Omega subset RR^n$ open and convex and $f in C^2 (Omega)$. Then,
  1. $f$ is convex on $Omega$ iff $gradient^2 f >= 0$;
  2. $f$ is strictly convex on $Omega$ $impliedby$ $gradient^2 f > 0$;
  2. $f$ is $sigma$-strongly convex on $Omega$ $<=>$ $sigma <= lambda_(min) (gradient^2 f(x))$ for all $x in Omega$.
]

#corollary[
  Let $A in RR^(n times n)$ be symmetric, $b in RR^n$ and $f(x) := 1/2 x^T A x + b^T x$. Then,
  1. $f$ convex $<=>$ $A >= 0$;
  2. $f$ strongly convex $<=>$ $A > 0$.
]
