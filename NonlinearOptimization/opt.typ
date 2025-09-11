// ! external
#import "../typst/notes.typ": *
// #import "../typst/shortcuts.typ": *

#import "@preview/cetz:0.2.2"

#import "@preview/algorithmic:1.0.5"
#import algorithmic: algorithm-figure, style-algorithm
#show: style-algorithm

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

#theorem("Convex Optimization")[
  Let $f : RR^n -> RR$ be convex and continuous, $X subset RR^n$ convex (and nonempty), and consider the optimization problem $ min f(x) "s.t." x in X wide (star). $
  Then, the following hold:
  1. $overline(x)$ is a global minimizer of $(star)$ $<=>$ $overline(x)$ is a local minimizer of $(star)$
  2. $"argmin"_X f$ is convex (possibly empty)
  3. $f$ is strictly convex $=> "argmin"_X f$ has at _most_ one element
  4. $f$ is strongly convex and differentiable, and $X$ closed, $=>$ $"argmin"_X f$ has _exactly_ one element
]

#proof[
  (1., $=>$) Trivial. (1., $impliedby$) Let $overline(x)$ be a local minimizer of $f$ over $X$, and suppose towards a contradiction that there exists some $hat(x) in X$ such that $f(hat(x)) < f(overline(x))$. By convexity of $f, X$, we know for $lambda in (0, 1)$, $lambda overline(x) + (1 - lambda) hat(x) in X$ and $ f(lambda overline(x) + (1 - lambda) hat(x)) <= lambda f(overline(x)) + (1 - lambda) f(hat(x)) < f(overline(x)). $ Letting $lambda -> 1^-$, we see that $lambda overline(x) + (1 - lambda) hat(x) -> overline(x)$; in particular, for any neighborhood of $overline(x)$ we can construct a point which strictly lower bounds $f(overline(x))$, which contradicts the assumption that $overline(x)$ a local minimizer.

  (2.) and (3.) are left as an exercise.

  (4.) We know that $f$ is strictly convex and level-bounded. By (3.) we know there is at most one minimizer, so we just need to show there exists one. Take $c in RR$ such that $"lev"_c (f) inter X eq.not nothing$ (which certainly exists by taking, say, $f(x)$ for some $x in X$). Then, notice that $(star)$ and $ min_(x in "lev"_c f inter X) f(x) wide (star star) $ have the same solutions i.e. the same set of global minimizers (noting that this remains a convex problem). Since $f$ continuous and $"lev"_c f inter X$ compact and nonempty, $f$ attains a minimum on $"lev"_c f inter X$, as we needed to show.
]

#remark[
  Note that level sets of convex functions are convex, this is left as an exercise.
]

== Matrix Norms

We denote by $RR^(m times n)$ the space of real-valued $m times n$ matrices (i.e. of linear operators from $RR^n -> RR^m$).

#proposition("Operator Norms")[
  Let $norm(dot)_ast$ be a norm on $RR^m$ and $RR^n$, resp. Then, the map $ RR^(m times n) in.rev A |-> norm(A)_ast := sup_(x in RR^n, \ norm(x)_ast eq.not 0) norm(A x)_(ast)/(norm(x)_ast) in RR $ is a norm on $R^(m times n)$. In addition, $ norm(A)_ast = sup_(norm(x)_ast = 1) norm(A x)_ast = sup_(norm(x)_ast <= 1) norm(A x)_ast. $
]

#proof[
  We first note that all of these $sup$'s are truely $max$'s since they are maximizing continuous functions over compact sets.

  Let $A in RR^(m times n)$. The first "In addition" equality follows from positive homogeneity, since $x/(norm(x)_ast)$ a unit vector. For the second, note that "$<=$" is trivial, since we are supping over a larger (super)set. For "$>=$", we have for any $x$ with $norm(x)_ast <=1$, $ norm(A x)_ast = norm(x)_(ast) norm(A x/(norm(x)_ast))_ast <= norm(A x/(norm(x)_ast)). $ Supping both sides over all such $x$ gives the result.

  We now check that $norm(dot)_ast$ actually a norm on $RR^(m times n)$.
  1. $norm(A)_ast = 0 <=> sup_(norm(x)_ast = 1) norm(A x)_ast = 0 <=> norm(A x)_ast = 0 forall norm(x)_ast = 1 <=> A x = 0 forall norm(x)_ast = 1 <=> A = 0$
  2. For $lambda in RR, A in RR^(m times n)$, $norm(lambda A)_ast = sup norm(lambda A x)_ast = |lambda| dot sup norm(A x)_ast = |lambda| norm(A)_ast$
  3. For $A, B in RR^(m times n)$, $norm(A + B)_ast <= norm(A)_ast + norm(B)_ast$ using properties of sups of sums
]

#proposition[
  Let $A = (a_(i j))_(i=1, dots, m\ j = 1, dots, n) in RR^(m times n)$, then:
  1. $norm(A)_1 = max_(j=1)^n sum_(i=1)^m abs(a_(i j))$
  2. $norm(A)_2 = sqrt(lambda_(max) (A^T A)) = sigma_max (A)$
  3. $norm(A)_infinity = max_(i=1)^m sum_(i=1)^n |a_(i j)|$
]

#proposition[
  Let $norm(dot)_ast$ be a norm on $RR^n, RR^m$, and $RR^p$. For $A in RR^(m times n)$ and $B in RR^(n times p)$,
  1. $norm(A x)_ast <= norm(A)_ast dot norm(x)_ast$
  2. $norm(A B)_ast <= norm(A)_ast dot norm(B)_ast$
]

#proposition("Banach Lemma")[
  Let $C in RR^(n times n)$ with $norm(C) < 1$, where $norm(dot)$ submultiplicative. Then, $I + C$ is invertible, and $ norm((1 + C)^(-1)) <= 1/(1 - norm(C)). $
]

#proof[
  We have for any $m$, $ norm(sum_(i=1)^m (-C)^i) <= sum_(i=1)^m norm(C)^i ->_(m->infinity) 1/(1 - norm(C)). $ Hence, $A_m := sum_(i=1)^m (-C)^i$ a sequence of matrices with bounded norm uniformly in $m$, and thus has a converging subsequence, so wlog $A_m -> A in RR^(n times n)$ (by relabelling). Moreover, observe that $ A_m dot (I + C) = sum_(i=0)^m (-C)^i (I + C) = sum_(i=0)^m [(-C)^i - (-C)^(i + 1)] = (-C)^0 - (-C)^(m + 1) = I - (-C)^(m + 1). $ Now, $norm(C^(m+1)) <= norm(C)^(m +1) -> 0$, since $norm(C) < 1$, thus $C -> 0$. Hence, taking limits in the line above implies $ A (I + C) = lim_(m->infinity) A_m (I + C) = I, $ implying $A$ the inverse of $(I + C)$, proving the proposition.
]

#corollary[
  Let $A, B in RR^(n times n)$ with $norm(I - B A) < 1$ for $norm(dot)$ submultiplicative. Then, $A$ and $B$ are invertible, and $norm(B^(-1)) <= (norm(A))/(1 - norm(I - B A))$.
]

= Descent Methods

== A General Line-Search Method

We deal with the unconstrained problem $ min_(x in RR^n) f(x) wide (star.filled). $
#definition("Descent Direction")[
  Let $f : RR^n -> RR$, $x in RR^n$. $d in RR^n$ is a _descent direction_ of $f$ at $x$ if there exists a $overline(t) > 0$ such that $f(x + t d) < f(x)$ for all $t in (0, overline(t))$.
]

#proposition[If $f : RR^n -> RR$ is directionally differentiable at $x in RR^n$ in the direction $d$ with $f'(x; d) < 0$, then $d$ a descent direction of $f$ at $x$; in particular if $f$ differentiable at $x$, then true for $d$ if $gradient f(x)^T d < 0$.]

#corollary[
  Let $f : RR^n -> RR$ differentiable, $B in RR^(n times n)$ positive definite, and $x in RR^n$. Then $gradient f(x) eq.not 0 => -B gradient f(x)$ is a descent direction of $f$ at $x$.
]

#proof[
  $gradient f(x)^T (-B gradient f(x)) = - gradient f(x)^T B gradient f(x) < 0$.
]

// TODO write as algo.
$(A_1)$
A generic method/strategy for solving $(star.filled)$:
1. (Initialization) Choose $x^0 in RR^n$ and set $k := 0$
2. (Termination) If $x^k$ satisfies a "termination criterion", STOP
3. (Search direction) Determine $d^k$ such that $gradient f(x^k)^T d^k < 0$
4. (Step-size) Determine $t_k > 0$ such that $f(x^k + t_k d^k) < f(x^k)$
5. (Update) Set $x^(k + 1) := x^k + t_k d^k$, iterate $k$, and go back to step 2.

#remark[
  a) The generic choice for $d^k$ in 3. is just $d^k := - B_k gradient f(x^k)$ for some $B_k > 0$. We focus on:
  - $B_k = I$ (_gradient-descent_)
  - $B_k = gradient^2 f(x^k)^(-1)$ (_Newton's method_)
  - $B_k approx gradient^2 f(x^k)^(-1)$ (_quasi Newton's method_)\
  b) Step 4. is called _line-search_, since $t_k > 0$ determined by looking at $ 0 < t |-> f(x^k +t d^k), $ i.e. along the (half)line $t > 0$.\
  c) Executing Step 4. is a trade-off between\
  #h(1em) (i) decreasing $f$ along $x^k + t d^k$ as much as possible; \
  #h(1em) (ii) keeping computational efforts low.\
  For instance, the _exact minimization rule_ $t_k = "argmin"_(t > 0) f(x_k + t d^k)$ overemphasizes (i) over (ii).
]

#definition(
  "Step-size rule",
)[Let $f in C^1(RR^n)$ and $ cal(A)_f := {(x, d) | gradient f(x)^T d < 0}. $ A (possible set-valued) map $ T : (x, d) in cal(A)_f |-> T(x, d) in RR_(+) $ is called a _step-size rule_ for $f$.

  If $T$ is well-defined for all $C^1$-functions, we say $T$ well-defined.
]

=== Global Convergence of $(A_1)$

#definition("Efficient step-size")[
  Let $f in C^1(RR^n)$. The step-size rule $T$ is called _efficient_ for $f$ if there exists $theta > 0$ such that $ f(x + t d) <= f(x) - theta ((gradient f(x)^T d)/norm(d))^2, wide forall t in T(x, d), thin thin (x, d) in cal(A)_f. $
]

#theorem[
  Let $f in C^1 (RR^n)$. Let ${x^k}, {d^k}, {t_k}$ be generated by $(A_1)$. Assume the following:
  1. $exists c> 0$ such that $-(gradient f(x^k)^T d^k)\/(norm(gradient f(x^k))dot norm(d^k)) >= c$ for all $k$ (this is called the _angle condition_), and
  2. there exists $theta > 0$ such that $f(x^k + t_k d^k) <= f(x^k) - theta (gradient f(x^k)^T d^k\/norm(d^k))^2$ for all $k$ (which is satisfied if $t_k in T(x^k, d^k)$ for an efficient $T$).
  Then, every cluster point of ${x^k}$ is a stationary point of $f$.
]
