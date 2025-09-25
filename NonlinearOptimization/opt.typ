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


#set figure(numbering: (..num) => numbering("1.1", counter(heading).get().first(), num.pos().first()))


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
  Let $f : D subset RR^n -> RR$ be twice continuously differentiable, then for each $x, y in D$, there is an $eta$ lying on the line between $x$ and $y$ such that $ f(y) = f(x) + gradient f(x)^T (y - x) + 1/2 (y - x)^T gradient^2 f(eta) (y - x). $
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
\
\
#figure(
  kind: "Code",
  supplement: "Algorithm",
  table(
    columns: 1,
    rows: 2,
    align: left,
    [A generic method/strategy for solving $(star.filled)$:],
    [

      S1. (Initialization) Choose $x^0 in RR^n$ and set $k := 0$\
      S2. (Termination) If $x^k$ satisfies a "termination criterion", STOP\
      S3. (Search direction) Determine $d^k$ such that $gradient f(x^k)^T d^k < 0$\
      S4. (Step-size) Determine $t_k > 0$ such that $f(x^k + t_k d^k) < f(x^k)$\
      S5. (Update) Set $x^(k + 1) := x^k + t_k d^k$, iterate $k$, and go back to step 2.
    ],
  ),
)<tab:A1>

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

=== Global Convergence of @tab:A1

#definition("Efficient step-size")[
  Let $f in C^1(RR^n)$. The step-size rule $T$ is called _efficient_ for $f$ if there exists $theta > 0$ such that $ f(x + t d) <= f(x) - theta ((gradient f(x)^T d)/norm(d))^2, wide forall t in T(x, d), thin thin (x, d) in cal(A)_f. $
]

#theorem[
  Let $f in C^1 (RR^n)$. Let ${x^k}, {d^k}, {t_k}$ be generated by @tab:A1. Assume the following:
  1. $exists c> 0$ such that $-(gradient f(x^k)^T d^k)\/(norm(gradient f(x^k))dot norm(d^k)) >= c$ for all $k$ (this is called the _angle condition_), and
  2. there exists $theta > 0$ such that $f(x^k + t_k d^k) <= f(x^k) - theta dot (gradient f(x^k)^T d^k\/norm(d^k))^2$ for all $k$ (which is satisfied if $t_k in T(x^k, d^k)$ for an efficient $T$).
  Then, every cluster point of ${x^k}$ is a stationary point of $f$.
]

#proof[
  By condition 2., there is $theta > 0$ such that $ f(x^(k + 1)) <= f(x^k) - theta ((gradient f(x^k)^T d^k)/norm(d^k))^2, $ for all $k in NN$.
  By 1., we know $ ((gradient f(x^k)^T d^k)/norm(d^k))^2 >= c^2 norm(gradient f(x^k))^2. $ Put $kappa := theta c^2$, then these two inequalities imply $ f(x^(k + 1)) <= f(x^k) - kappa dot norm(gradient f(x^k))^2. wide (ast) $ Let $overline(x)$ be a cluster point of ${x^k}$. As ${f(x^k)}$ is monotonically decreasing (by construction in the algorithm), and has cluster point $f(overline(x))$ by continuity, it follows that $f(x_k) -> f(overline(x))$ along the whole sequence. In particular, $f(x^(k + 1)) - f(x^k) -> 0$; thus, from $(ast)$, $ 0 <= kappa norm(gradient f(x^k))^2 <= f(x^(k)) - f(x^(k + 1)) -> 0, $ and thus $gradient f(x^k) -> gradient f(overline(x)) = 0$, so indeed $overline(x)$ a stationary point of $f$.
]

== The Gradient Method

We specialize @tab:A1 here. Specifically, we'll take $ d^k := - gradient f(x^k); $ it's know that $ (-gradient f(x^k))/(norm(gradient f(x^k))) = "argmin"_(d : norm(d) <= 1) gradient f(x^k)^T d, $ with $norm(dot)$ the $2$ norm.

We use a step-size rule called "Armijo rule". Choose parameters $beta, sigma in (0, 1)$. For $(x, d) in cal(A)_f$, we define our step-size rule by $ T_A (x, d) := max_(ell in NN_0) {beta^ell | underbrace(f(x + beta^ell d) <= f(x) + beta^ell sigma gradient f(x)^T d, "\"Armijo condition\"")}. $

For instance, consider $f(x) = (x - 1)^2 - 1$. The minimum of this function is $f^ast = -1$. Choose $x^k := 1/k$, then $ f(x^k) = (2k + 1)/k^2 -> 0 eq.not f^ast, $ even though $f(x^(k + 1)) - f(x^k) < 0$; we don't actually reach the right stationary point with our chosen step size.

#example("Illustration of Armijo Rule")[
  For $(x, d) in cal(A)_f$ and $f$ smooth on $RR^n$, defined $phi.alt : RR -> RR, phi.alt(t) := f(x + t d)$.
  The map $t |-> sigma phi'(0) t + phi(0) = sigma t gradient f(x)^T d + phi(0)$
  // TODO maybe picture
]

#proposition[
  Let $f : RR^n -> RR$ be differentiable with $beta, sigma in (0, 1)$. Then for $(x, d) in cal(A)_f$, there exists $ell in NN_0$ such that $ f(x + beta^ell d) <= f(x) + beta^ell sigma gradient f(x)^T d, $ i.e. $T_A (x, d) eq.not nothing$.
]

#proof[
  Suppose not, i.e. $ (f(x + beta^ell d) - f(x))/beta^ell > sigma gradient f(x)^T d, forall ell in NN_0. $ Letting $ell -> infinity$, the left-hand side converges to $gradient f(x)^T d$, so $ gradient f(x)^T d >= sigma gradient f(x)^T d. $ But $(x, d) in cal(A)_f$, so $gradient f(x)^T d < 0$ so dividing both sides of this inequality by this quantity, this implies $sigma <= 0$, which is a contradiction.
]

We now prove convergence of an algorithm based on the Armijo Rule:

#figure(
  kind: "Code",
  supplement: "Algorithm",
  table(
    columns: 1,
    rows: 2,
    align: left,
    [Gradient Descent with Armijo Rule],
    [
      S0. Choose $x^0 in RR^n, sigma, beta in (0, 1), epsilon >= 0,$ and set $k := 0$\
      S1. If $norm(gradient f(x^k)) <= epsilon$, STOP \
      S2. Set $d^k := -gradient f(x^k)$\
      S3. Determine $t_k > 0$ by $ t_k = T_A (x, d) $ as defined above.\
      S4. Set $x^(k + 1) = x^k + t_k d^k$, iterate $k$ and go to S1.
    ],
  ),
)<tab:A2>

#lemma[
  Let $f in C^1 (RR^n)$, $x^k -> x$, $d^k -> d$ and $t_k arrow.b 0$. Then $ lim_(k -> infinity) (f(x^k + t_k d^k) - f(x^k))/t^k = gradient f(x)^T d. $
]

#proof[Left as an exercise.]

#theorem[
  Let $f in C^1 (RR^n)$. Then every cluster point of a sequence ${x^k}$ generated by @tab:A2 is a stationary point of $f$.
]

#proof[
  Let $overline(x)$ be a cluster point of ${x^k}$ and let $x^k ->_(k in K) overline(x)$, $K$ an infinite subset of $NN$. Assume towards a contradiction $gradient f(overline(x)) eq.not 0$. As $f(x^k)$ is monotonically decreasing with cluster point $f(overline(x))$, it must be that $f(x^k) -> f(overline(x))$ along the whole sequence so $f(x^(k + 1)) - f(x^k) -> 0$. Thus, $ 0 <= t_k norm(gradient f(x^k))^2 =^("S2") - t_k gradient f(x^k)^T d^k <=^("S3") (f(x^k) - f(x^(k + 1)))/sigma -> 0. $

  Thus, $0 = lim_(k in K) t_k norm(gradient f(x^k)) = norm(gradient f(overline(x))) lim_(k in K) t_k$. We assumed $overline(x)$ not a stationary point, so it follows that $t_k ->_(k in K) 0$. By S3, for $beta^(ell_k) = t_k$, $ (f(x^k + beta^(ell_k - 1) d^k) - f(x^k))/(beta^(ell_k - 1)) > sigma gradient f(x^k)^T d^k. $ Letting $k -> infinity$ along $K$,the LHS converges to, by the previous lemma, to $ gradient f (overline(x))^T d = - gradient f(overline(x))^T gradient f(overline(x)) = - norm(gradient f(overline(x)))^2, $ and the RHS converges to $sigma norm(gradient f(overline(x)))^2$, which implies $ - norm(gradient f(overline(x)))^2 >= sigma norm(gradient f(overline(x)))^2, $ which implies $sigma$ negative, a contradiction.
]

#remark[
  The proof above shows, the following: Let ${x^k}$ such that $x^(k + 1) := x^k + t_k d^k$ for $d^k in RR^n, t_k > 0$, and let $f(x^(k + 1)) <= f(x^k)$ and $x^k ->^K overline(x)$ such that $d^k = - gradient f(x^k)$, $t_k = T_A (x^k, d^k)$ for all $k in K$. Then $gradient f(overline(x)) = 0$; i.e., all of the "focus" is on the subsequence along $K$. The only time we needed the whole sequence was to use the fact that $f(x^k) -> f(overline(x))$ along the whole sequence.
]

== Newton-Type Methods

=== Convergence Rates and Landau Notation


#definition[
  Let ${x^k in RR^n}$ converge to $overline(x)$. Then, ${x^k}$ converges:
  1. _linearly_ to $overline(x)$ if there exists $c in (0, 1)$ such that $ norm(x^(k + 1) - overline(x)) <= c norm(x^k - overline(x)), forall k; $
  2. _superlinearly_ to $overline(x)$ if $ lim_(k -> infinity) (norm(x^(k + 1) - overline(x)))/(norm(x^k - overline(x))) = 0; $
  3. _quadratically_ to $overline(x)$ if there exists $C > 0$ such that $ norm(x^(k+1) - overline(x)) <= C norm(x^k - overline(x))^2, forall k. $
]

#remark[\3. $=>$ 2. $=>$ 1.]

#remark[We needn't assume $x^k -> overline(x)$ for the first two definitions; their statements alone imply convergence. However, the last does not; there exists sequences with this property that do not converge.]


#definition("Landau Notation")[
  Let ${a_k}, {b_k}$ be positive sequences $arrow.b 0$. Then,
  1. $a_k = cal(o)(b_k) <=> lim_(k -> infinity) a_k/b_k = 0$;
  2. $a_k = cal(O)(b_k) <=> exists C > 0 : a_k <= C b_k$ for all $k$ (sufficiently large).
]

#remark[
  If $x^k -> overline(x)$, then
  1. the convergence is superlinear $<=>$ $norm(x^(k + 1) - overline(x)) = cal(o)(norm(x^k - overline(x)))$;
  2. the convergence is quadratic $<=>$ $norm(x^(k + 1) - overline(x)) = cal(O)(norm(x^k- overline(x))^2)$.
]

=== Newton's Method for Nonlinear Equations

We consider the nonlinear equation $ F(x) = 0, wide (ast) $ where $F : RR^n -> RR^n$ is smooth (continuously differentiable). Our goal is to find a numerical scheme that can determine approximate zeros of $F$, i.e. solutions to $(ast)$. The idea of Newton's method for such a problem, is, given $x^k in RR^n$, to consider the (affine) linear approximation of $F$ about $x^k$, $ F_k : x |-> F(x^k) + F' (x^k) (x - x^k), $ where $F'$ the Jacobian of $F$. Then, we compute $x^(k + 1)$ as a solution of $F_k (x) = 0$. Namely, if $F'(x^k)$ invertible, then solving for $F_k (x^(k + 1)) = 0$, we find $ x^(k + 1) = x^k - F' (x^k)^(-1) F(x^k). $ More generally, one solves $F'(x^k) d = - F(x^k)$ and sets $x^(k + 1) := x^k + d^k$.
\

Specifically, we have the following algorithm:
#figure(
  kind: "Code",
  supplement: "Algorithm",
  table(
    columns: 1,
    rows: 2,
    align: left,
    [#align(center, "Newton's Method (Local Version)")],
    [
      S0. Choose $x^0 in RR^n, epsilon > 0$, and set $k := 0$.\
      S1. If $norm(F(x^k)) < epsilon$, STOP.\
      S2. Compute $d^k$ as a solution of _Newton's equation_ $ F'(x^k) d = - F(x^k). $
      S3. Set $x^(k + 1) := x^k + d^k$, increment $k$ and go to S1.
    ],
  ),
)<tab:newtonslocal>

#lemma[Let $F: RR^n -> RR^n$ be $C^1$, and $overline(x) in RR^n$ such that $F'(overline(x))$ is invertible. Then, there exists $epsilon > 0$ such that $F'(x)$ remains invertible for all $x in B_epsilon (overline(x))$, and there exists $C > 0$ such that $ norm(F'(x)^(-1)) <= C, wide forall x in B_epsilon (overline(x)). $]

#proof[
  Since $F'$ continuous at $overline(x)$, there exists $epsilon > 0$ such that $norm(F' (overline(x)) - F'(x)) <= 1/(2 norm(F' (overline(x))^(-1)))$ for all $x in B_epsilon (overline(x))$. Then, for all $x in B_epsilon (overline(x))$, $ norm(I - F' (x) F'(overline(x))^(-1)) & = norm((F' (overline(x)) - F'(x)) F'(overline(x))^(-1)) \
                                        & <= norm(F'(overline(x)) - F'(x)) norm(F'(overline(x))^(-1)) <=1/2 < 1. $
  By a corollary of the Banach lemma, $F'(x)$ invertible over $B_epsilon (overline(x))$, and $ norm(F'(x)^(-1)) <= norm(F'(overline(x))^(-1))/(1 - norm(I - F'(x) F'(overline(x))^(-1))) <= 2 norm(F'(overline(x))^(-1)) =: C. $
]

#remark[
  Observe $F : RR^n -> RR^m$ is differentiable at $overline(x)$ if and only if $norm(F(x^k) - F(overline(x)) - F'(overline(x)) (x^k - overline(x))) = cal(o)(norm(x^k - overline(x)))$ for every $x^k -> overline(x)$.

  This can be sharpened if $F'$ is continuous or even locally Lipschitz.
]

#lemma[
  Let $F : RR^n -> RR$ be continuously differentiable and $x^k -> overline(x)$, then:
  1. $norm(F(x^k) - F(overline(x)) - F'(x^k) (x^k - overline(x))) = cal(o)(norm(x^k - overline(x)))$;
  2. if $F'$ locally Lipschitz at $overline(x)$, then $norm(F(x^k) - F(overline(x)) - F'(x^k) (x^k - overline(x))) = cal(O)(norm(x^k - overline(x))^2)$.
]

#proof[
  1. Observe that $ norm(F(x^k) - F(overline(x)) - F'(x^k) (x^k - overline(x))) \
    <=
    norm(F(x^k) - F(overline(x)) - F(overline(x))(x^k - overline(x))) + norm(F'(x^k) (x^k - overline(x)) - F'(overline(x)) (x^k - overline(x))) \
    <=norm(F(x^k) - F(overline(x)) - F(overline(x))(x^k - overline(x))) + norm(F'(x^k) - F(overline(x))) norm(x^k - overline(x)). $ The left-hand term is $cal(o)(norm(x^k - overline(x)))$ by our observations previously, and the right-hand term is as well by continuity of $F'$, thus so is the sum.

  2. Let $L> 0$ be a local Lipschitz constant of $F'$ at $overline(x)$. Then, $ norm(F(x^k) - F(overline(x)) - F'(x^k) (x^k - overline(x))) &= norm(integral_(0)^1 F'(overline(x) + t (x^k - overline(x))) dif t (x^k - overline(x)) - F'(x^k) (x^k - overline(x))) \
    &<= integral_0^1 norm(F'(overline(x) + t (x^k - overline(x))) - F'(x^k)) dif t dot norm(x^k - overline(x))\
    &<= L integral_0^1 abs(1 - t) norm(x^k - overline(x)) dif t dot norm(x^k - overline(x)) \
    &= L norm(x^k - overline(x))^2 integral_(0)^1 (1 - t) dif t = L/2 norm(x^k - overline(x))^2, $ which implies the result.
]

#theorem[
  Let $F : RR^n -> RR^n$ be continuously differentiable, $overline(x) in RR^n$ such that $F(overline(x)) = 0$ and $F'(overline(x))$ is invertible. Then, there exists an $epsilon > 0$ such that for every $x^0 in B_epsilon (overline(x))$, we have:
  1. @tab:newtonslocal is well-defined and generates a sequence ${x^k}$ which converges to $overline(x)$;
  2. the rate of convergence is (at least) linear;
  3. if $F'$ is locally Lipschitz at $overline(x)$, then the rate is quadratic.
]

#proof[
  1. By the previous lemma, we know there is $epsilon_1, c > 0$ such that $norm(F'(x)^(-1)) <= c$ for all $x in B_epsilon_1 (x)$. Further, there exists an $epsilon_2 > 0$ such that $norm(F(x) - F(overline(x)) - F'(x)(x - overline(x))) <= 1/(2c) norm(x - overline(x))$ for all $x in B_(epsilon_2) (overline(x))$. Take $epsilon = min{epsilon_1, epsilon_2}$ and pick $x^0 in B_epsilon (overline(x))$. Then, $x^1$ is well-defined, since $F'(x^0)$ is invertible, and so $ norm(x^1 - overline(x)) & = norm(x^0 - F'(x^0)^(-1) F(x^0) - overline(x)) \
                            & = norm(F'(x^0)^(-1) (F(x^0) - underbrace(F(overline(x)), = 0) - F'(x^0) (x^0 - overline(x)))) \
                            & <= norm(F'(x^0)^(-1)) norm(F(x^0) - F(overline(x)) - F'(x^0) (x^0 - overline(x))) \
                            & <= c dot 1/(2 c) norm(x^0 - overline(x)) \
                            & = 1/2 norm(x^0 - overline(x)) < epsilon/2, $ so in particular, $x^1 in B_(epsilon\/2) (overline(x)) subset B_epsilon (overline(x))$. Inductively, $ norm(x^k - overline(x)) <= (1/2)^(k) norm(x^0 - overline(x)), $ for every $k in NN$. Thus, $x^k$ well-defined and converges to $overline(x)$.

    2., 3. Analogous to 1., $ norm(x^(k + 1) - overline(x)) & = norm(x^k - d^k - overline(x)) \
                                  & = norm(x^k - F'(x^k)^(-1) F(x^k) - overline(x)) \
                                  & <= norm(F'(x^k)^(-1)) norm(F(x^k) - F(overline(x)) - F'(x^k)(x^k - overline(x))) \
                                  & <= c norm(F(x^k) - F(overline(x)) - F'(x^k)(x^k - overline(x))). $ This final line is little $cal(o)$ of $norm(x^k - overline(x))$ or this quantity squared by the previous lemma, which proves the result depending on the assumptions of 2., 3..
]

=== Newton's Method for Optimization Problem

Consider $ min_(x in RR^n) f(x), $ with $f : RR^n -> RR$ twice continuously differentiable. Recall that if $overline(x)$ a local minimizer of $f$, $gradient f(overline(x)) = 0$. We'll now specialize Newton's to $F := gradient f$:
#figure(
  kind: "Code",
  supplement: "Algorithm",
  table(
    columns: 1,
    rows: 2,
    align: left,
    [#align(center, "Newton's Method for Optimization (Local Version)")],
    [
      S0. Choose $x^0 in RR^n, epsilon > 0$, and set $k := 0$.\
      S1. If $norm(gradient f(x^k)) < epsilon$, STOP.\
      S2. Compute $d^k$ as a solution of _Newton's equation_ $ gradient^2 f (x^k) d= - gradient f(x^k). $
      S3. Set $x^(k + 1) := x^k + d^k$, increment $k$ and go to S1.
    ],
  ),
)<tab:newtonsopt>


We then have an analogous convergence result to the previous theorem by simply applying $F := gradient f$; in particular, if $f$ thrice continuously differentiable, we have quadratic convergence.

#example[
  Let $f(x) := sqrt(x^2 + 1)$. Then $f'(x) = x/(sqrt(x^2 + 1))$, $f''(x) = 1/(x^2 + 1)^(3\/2)$. Newton's equation (i.e. @tab:newtonsopt, S2) reads in this case: $ 1/(x_k^2 + 1)^(3\/2) d = - (x_k)/(sqrt(x_k^2 + 1)). $ This gives solution $d_k = -(x_k^2 + 1)x_k,$ so $x_(k + 1) = - x_k^(3)$. Then, notice that if: $ abs(x_0) < 1 & => x_k -> 0, "quadratically" \
     |x_0| > 1 & => x_k "diverges" \
     |x_0| = 1 & => abs(x_k) = 1 forall k, $ so the convergence is truly local; if we start too far from $0$, we'll never have convergence.
]

We can see from this example that this truly a local algorithm. A general globalization strategy is to:
- if Newton's equation has no solution, or doesn't provide sufficient decay, set $d^k := - gradient f(x^k)$;
- introduce a step-size.


#figure(
  kind: "Code",
  supplement: "Algorithm",
  table(
    columns: 1,
    rows: 2,
    align: left,
    [#align(center, "Newton's Method (Global Version)")],
    [
      S0. Choose $x^0 in RR^n, epsilon >0, rho > 0, p > 2, beta in (0, 1), sigma in (0, 1\/2)$ and set $k := 0$\
      S1. If $norm(gradient f(x^k)) < epsilon$, STOP\
      S2. Determine $d^k$ as a solution of $ gradient^2 f(x^k) d = - gradient f(x^k). $ If no solution exists, or if $gradient f(x^k)^T d^k <= - rho norm(d^k)^p$, is violated, set $d^k := - gradient f(x^k)$\
      S3. Determine $t_k > 0$ by the Armijo back-tracking rule, i.e. $ t_k := max_(ell in NN_0) {beta^ell | f(x^k + beta^ell d^k) <= f(x^k) + beta^ell sigma gradient f(x^k)^T d^k} $
      S4. Set $x^(k + 1) := x^k + t_k d^k$, increment $k$ to $k + 1$, and go back to S1.
    ],
  ),
)<tab:newtonsglob>

#remark[S3. well-defined since in either choice of $d^k$ in S2., we will have a descent direction so the choice of $t_k$ in S3. is valid; i.e. $(x^k, d^k) in cal(A)_f$ for every $k$.]

#theorem([Global convergence of @tab:newtonsglob])[
  Let $f : RR^n -> RR$ be twice continuously differentiable. Then every cluster point of ${x^k}$ generated by @tab:newtonsglob is a stationary point of $f$.
]

#remark[Note that we didn't impose any invertibility condition on the Hessian of $f$; indeed, if say the hessian was nowhere invertible, then @tab:newtonsglob just becomes the gradient method with Armijo back-tracking, for which have already established this result. ]
#proof[
  Let ${x^k}$ be generated by @tab:newtonsglob, with ${x^k}_K -> overline(x)$. If $d^k := -gradient f(x^k)$ for infinitely many $k in K$ (i.e. along a subsubsequence of ${x^k}$), then we have nothing to prove by the previous remark.

  Otherwise, assume wlog (by passing to a subsubsequence again if necessary) that $d^k$ is determined by the Newton equation for all $k in K$. Suppose towards a contradiction that $gradient f(overline(x)) eq.not 0$. By Newton's equation, $ norm(gradient f(x^k)) = norm(gradient^2 f(x^k) d^k) <= norm(gradient^2 f(x^k)) norm(d^k), wide forall k in K. $ By assumption $norm(gradient^2 f(x^k)) eq.not 0$; if it were, then by assumption $gradient f(x^k) = 0$, i.e. we'd have already reached our stationary point, which we assumed doesn't happen. So, we may write $norm(gradient f(x^k))/(norm(gradient^2 f(x^k))) <= norm(d^k)$ for all $k in K$. We claim that there exists $c_1, c_2 > 0$ such that $ 0 < c_1 <= norm(d^k) <= c_2, wide forall k in K. $ We have existence of $c_1$ since, if it didn't, we could find a subsequence of the $d^k$'s such that $d^k -> 0$ along this subsequence; but by our bound above and the fact that $norm(gradient^2 f(x^k))$ uniformly bounded (by continuity), then $norm(gradient f(x^k))$ would converge to zero along the subsequence too, a contradiction.

  The existence of $c_2$ follows from the sufficient decrease condition. Indeed, suppose such a $c_2$ didn't exist; by the condition $ gradient f(x^k)^T (d^k)/(norm(d^k)) <= -rho norm(d^k)^(p - 1); $ the left-hand side is bounded (since $gradient f(x^k) -> gradient f(overline(x))$ and $d^k/(norm(d^k))$ lives on the unit sphere). Since $c_2$ assumed not to exist, there is a subsequence $norm(d^k) -> infinity$, but then $-rho norm(d^k)^(p - 1) -> - infinity$, contradicting the fact that the LHS is bounded. Hence, there also exists such a $c_2$ as claimed.

  As ${f(x^k)}$ is monotonically decreasing (by construction in S3) and converges along a subsequence $K$ to $f(overline(x))$, then $f(x^k)$ converges along the whole sequence to $f(overline(x))$. In particular, $f(x^(k + 1)) - f(x^k) -> 0$. Then, $ (f(x^(k + 1)) - f(x^k))/sigma
  <= t_k gradient f(x^k)^T d^k <= - rho t_k norm(d^k)^p <= 0. $ Taking $k -> infinity$ along $K$, we see that $t_k norm(d^k)^p -> 0$ along $K$ as well. We show now that ${t_k}_K$ actually uniformly bounded away from zero. Suppose not. Then, along a sub(sub)sequence, $t_k -> 0$. By the Armijo rule, $t_k = beta^(ell_k)$, for $ell_k in NN_0$, uniquely determined. Since $t_k -> 0$, then $ell_k -> infinity$. On the other hand, by S3,$ (f(x^k + beta^(ell_k - 1) d^k) - f(x^k))/beta^(ell_k - 1) > sigma gradient f(x^k)^T d^k. $ Suppose $d^k -> overline(d) eq.not 0$ (by again passing to a subsequence if necessary), which we may assume by boundedness. Taking $k -> infinity$, the LHS converges to $gradient f(overline(x))^T overline(d)$ and the RHS converges to $sigma gradient f(overline(x))^T overline(d)$ so $gradient f(overline(x))^T overline(d) >= sigma gradient f(overline(x))^T overline(d)$, which implies since $sigma in (0, 1/2)$ that $gradient f(overline(x))^T overline(d) >= 0$. Taking $k -> infinity$ in the sufficient decrease condition statement shows that this is a contradiction. Hence, $t_k$ uniformly bounded away from 0. Hence, there exists a $overline(t) > 0$ such that $t_k >= overline(t)$ for all $k in K$. But we had that $t^k gradient f(x^k)^T d^k -> 0$, so by boundedness of $t_k$ it must be that $gradient f(x^k)^T d^k -> 0$ along the subsequence; by the sufficient decrease condition again, it must be that $d^k -> 0$, which it can't, as we showed it was uniformly bounded away, and thus we have a contradiction.
]

#theorem([Fast local convergence of @tab:newtonsglob])[
  Let $f : RR^n -> RR$ be twice continuously differentiable, ${x^k}$ generated by @tab:newtonsglob. If $overline(x)$ is a cluster point of ${x^k}$ with $gradient^2 f(overline(x)) > 0$. Then:
  1. ${x^k} -> overline(x)$ along the _whole_ sequence, so $overline(x)$ is a strict local minimizer of $f$;
  2. for $k in NN$ sufficiently large, $d^k$ wil be determined by the Newton equation in S2;
  3. ${x^k} -> overline(x)$ at least superlinearly;
  4. if $gradient^2 f$ locally Lipschitz, ${x^k} -> overline(x)$ quadratically.
]

== Quasi-Newton Methods


In Newton's, in general we need to find $ d^k "solving" gradient^2 f(x^k) d = - gradient f(x^k). $ Advantages/disadvantages:\
(+) Global convergence with fast local convergence\
(-) Evaluating $gradient^2 f$ can be expensive/impossible.\
Dealing with the second, there are two general approaches:\
- _Direct Methods:_ replace $gradient^2 f(x^k)$ with some matrix $H_k$ approximating it;
- _Indirect Methods:_ replace $gradient^2 f(x^k)^(-1)$ by $B_k$ approximating it;
where $H_k, B_k$ reasonably computational, and other convergence results are preserved.

=== Direct Methods
The typical conditions we put on $H_(k + 1)$ as described above are:
1. $H_(k + 1)$ symmetric
2. $H_(k + 1)$ satisfies the _Quasi-Newton equation_ (QNE) $ H_(k + 1) s^k = y^k, wide wide s^k := x^(k + 1) - x^k, wide y^k := gradient f(x^(k + 1)) - gradient f(x^k) $
3. $H_(k + 1)$ can be achieved from $H_k$ "efficiently"
4. The result method has strong local convergence properties

#remark[
  Suppose $x^k$ a current iterate for an algorithm to minimize $f : RR^n -> RR$ for $f in C^2$.
  1. $gradient^2 f(x^k)$ does not generally satisfy QNE;
  2. condition 1 above is motivated by the fact that Hessians are symmetric;
  3. the QNE is motivated by the mean-value theorem for vector-valued functions, $ gradient f(x^(k + 1)) - gradient f(x^k) = integral_0^1 gradient^2 f(x^k + t (x^(k + 1) - x^k)) dif t dot (x^(k + 1) - x^k); $ we can think of the integrated term as an averaging of the Hessian along the line between $x^(k),x^(k + 1)$.
]

We follow a so-called _symmetric rank-2 approach_; given $H_(k)$, we update $ H_(k + 1) = H_k + gamma u u^T + delta v v^T, wide gamma, delta in RR; u, v in RR^n. $ Note that if we put $S := u u^T$ for $u eq.not 0$, $"rank"(S) = 1$ and $S^T = S$.
