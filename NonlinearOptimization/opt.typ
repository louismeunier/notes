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

// TODO
#set heading(numbering: "I.1")

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
  Since $f$ continuous, $"lev"_c f$ is closed (being the inverse image of a closed set), thus $"lev"_c f$ is compact (and in particular nonempty). By Weierstrass, $f$ takes a minimum over $"lev"_c f$, namely there is $overline(x) in "lev"_c f$ with $f(overline(x)) <= f(x) <= c$ for each $x in "lev"_c f$. Also, $f(x) > c$ for each $x in.not "lev"_c f$ (by virtue of being a level set), and thus $f(overline(x)) <= f(x)$ for each $x in RR^(n)$. Thus, $overline(x)$ is a global minimizer and so the theorem follows.
]

== Convex Sets and Functions

#definition("Convex Sets")[
  $C subset RR^n$ is _convex_ if for any $x, y in C$ and $lambda in (0, 1)$, $lambda x + (1 - lambda) y in C$; that is, the entire line between $x$ and $y$ remains in $C$.
]


#definition("Convex Functions")[
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
  Assume otherwise, that there is a direction $d in RR^n$ for which the $f'(overline(x); d) < 0$, i.e. $ lim_(t -> 0^+) (f(overline(x) + t d) - f(overline(x)))/t < 0. $ Then, for all sufficiently small $t > 0$, we must have $ f(overline(x) + t d ) < f(overline(x)). $ Moreover, since $X$ open, then for $t$ even smaller (if necessary), $overline(x) + t d$ remains in $X$, thus $overline(x)$ cannot be a local minimizer.
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

#theorem("2nd-order Optimality Conditions")[
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
  We first note that all of these $sup$'s are truly $max$'s since they are maximizing continuous functions over compact sets.

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

== Descent Methods

=== A General Line-Search Method

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

==== Global Convergence of @tab:A1

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

=== The Gradient Method

We specialize @tab:A1 here. Specifically, we'll take $ d^k := - gradient f(x^k); $ it's known that $ (-gradient f(x^k))/(norm(gradient f(x^k))) = "argmin"_(d : norm(d) <= 1) gradient f(x^k)^T d, $ with $norm(dot)$ the $2$ norm.

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

=== Newton-Type Methods

==== Convergence Rates and Landau Notation


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

==== Newton's Method for Nonlinear Equations

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

==== Newton's Method for Optimization Problem

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

=== Quasi-Newton Methods


In Newton's, in general we need to find $ d^k "solving" gradient^2 f(x^k) d = - gradient f(x^k). $ Advantages/disadvantages:\
(+) Global convergence with fast local convergence\
(-) Evaluating $gradient^2 f$ can be expensive/impossible.\
Dealing with the second, there are two general approaches:\
- _Direct Methods:_ replace $gradient^2 f(x^k)$ with some matrix $H_k$ approximating it;
- _Indirect Methods:_ replace $gradient^2 f(x^k)^(-1)$ by $B_k$ approximating it;
where $H_k, B_k$ reasonably computational, and other convergence results are preserved.

==== Direct Methods
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

We follow a so-called _symmetric rank-2 approach_; given $H_(k)$, we update $ H_(k + 1) = H_k + gamma u u^T + delta v v^T, wide gamma, delta in RR; u, v in RR^n. wide (1) $ Note that if we put $S := u u^T$ for $u eq.not 0$, $"rank"(S) = 1$ and $S^T = S$.

So, the ansatz we take is $ y^k = H_(k + 1) s^k = H_k s^k + gamma u u^T s^k + delta v v^T s^k. wide (2) $
If $H_k > 0$ and $(y^k)^T s^k eq.not 0$, then taking $u := y^k, v:= H_k s^k,$  $gamma := 1/((y^k)^T s^k)$ and $delta := - 1/((s^k)^T H_k s^k)$ will solve (2), and gives the formula $ H^"BFGS"_(k + 1) := H_k - ((H_k s^k)(H_k s^k)^T)/((s^k)^T H_k s^k) + (y^k (y^k)^T)/((y^k)^T s^k) wide (3), $ the so-called "BFGS" formula. Another update formula that can be obtained that solves (2) is $ H_(k + 1)^("DFP") := H_k + ((y^k - H_k s^k) (y^k)^T + y^k (y^k - H_k s^k)^T)/((y^k)^T s^k) - ((y^k - H_k s^k)^T s^k)/([(h^k)^T s^k]^2) y^k (y^k)^T. $ Note that any convex combination of formulas that satisfy (2) also satisfy (2); thus, we define the so-called _Broyden class_ by the family of convex combinations of the above two formula, $ H^lambda_(k +1 ):= (1 -lambda) H_(k + 1)^"DFP" + lambda H_(k + 1)^"BFGS", wide forall lambda in [0, 1]. $

Algorithmically, for $f in C^1$;
#figure(
  kind: "Code",
  supplement: "Algorithm",
  table(
    columns: 1,
    rows: 2,
    align: left,
    [#align(center, "Globalized BFGS Method")],
    [
      S0. Choose $x^0 in RR^n$, $H_0 in RR^(n times n)$ symmetric positive definite, $sigma in (0, 1/2)$, $rho in (sigma, 1)$, $epsilon >= 0$ and set $k := 0$.\
      S1. If $norm(gradient f(x^k)) <= epsilon$, STOP.\
      S2. Determine $d^k$ as a solution to the QNE, $ H_k d = - gradient f(x^k). $
      S3. Determine $t_k>0$ such that $ f(x^k + t_k d^k) <= f(x^k) + sigma t_k gradient f(x^k)^T d^k, $ (this is just the Armijo condition), AND $ gradient f(x^k + t_k d^k)^T d^k >= rho gradient f(x^k)^T d^k, $ call the _Wolfe-Powell rule_.\
      S4. Set $ x^(k + 1) & := x^k + t_k d^k, \
            s^k & := x^(k + 1) - x^k, \
            y^k & := gradient f(x^(k + 1)) - gradient f(x^k), \
      H_(k + 1) & := H_(k + 1)^"BFGS". $
      S5. Increment $k$ and go to S1.
    ],
  ),
)<tab:BFGS>

We use the _Wolfe-Powell rule_; i.e., for $f : RR^n -> RR$ differentiable, $sigma in (0, 1/2), rho in (sigma, 1)$, $ T_("WP") : cal(A)_f in.rev (x, d) |-> {t > 0 | #stack(spacing: .7em, $f(x + t d) <= f(x) + sigma t gradient f(x)^T d$, $gradient f(x + t d)^T d >= rho gradient f(x)^T d$)} subset RR_+. $

#lemma[
  For $f in C^1$ and $(x, d) in cal(A)_f$, assume that $f$ is bounded from below on ${x + t d | t > 0}$. Then, $T_"WP" (x, d) eq.not nothing$.
]<lem:raybounded>
#remark[Note that we didn't need any boundedness restriction for the well-definedness of the Armijo rule.]

#lemma[
  For $f in C^1$, bounded from below with $gradient f$ Lipschitz continuous on $cal(L) := "lev"_(f(x^0)) f$. Then, $T_"WP"$ restricted to $cal(A)_f sect (cal(L) times RR^n)$ is _efficient_, i.e. there exists a $theta > 0$ such that $f(x + t d) <= f(x) - theta ((gradient f(x)^T d)/(norm(gradient f(x)) norm(d)))^2$ for every $(x, d) in cal(A)_f sect (cal(L) times RR^n)$ and $t in T_("WP") (x, d)$.
]<lem:bfgstwpefficiency>
#remark[
  Note that, generally $x^k$ will be in the level set at $f(x^0)$ for every $k >= 0$ when $x^k$ defined by a descent method. So in the context of this lemma, we will have the efficient bound at every iterate.
]

We turn to analyze @tab:BFGS.
#lemma[
  Let $y^k, s^k in RR^n$ such that $(y^k)^T s^k > 0$ and $H_k > 0$. Then, $ H_(k+1)^("BFGS") > 0. $
]<lem:bfgspositiveness>

#proof[
  For fixed $k$, set $H_+ := H_(k + 1)$, $H := H_k$, $s := s^k$ and $y := y^k$ for notational convenience. As $H > 0$, there exists a $W > 0$ such that $W^2 = H$. Let $d in RR^n minus {0}$ and set $z := W s$, $v := W d$. Then $ d^T H_+ d & = d^T (H + (y y^T)/(y^T s) - (H s s^T H)/(s^T H s)) d \
            & = d^T H d + d^T (y y^T)/(y^T s) d - d^t (H s s^T H)/(s^T H s)) d \
            & = d^T H d + ((y^T d)^2)/(y^T s) - ((d^T H s)^2)/(s^T H s) \
            & = norm(v)^2 + ((y^T d)^2)/(y^T s) - ((v^T z)^2)/(norm(z)^2) \
            & >= norm(v)^2 + ((y^T d)^2)/(y^T s) - norm(v)^2 \
            & = ((y^T d)^2)/(y^T s) >= 0, $ using Cauchy-Schwarz. In particular, equality (to zero) holds throughout iff $v$ and $z$ are linearly dependent and $y^T d = 0$. Suppose this is the case. In particular, there is an $alpha in RR$ for which $v = alpha z$. Then, $d = W^(-1) v = alpha W^(-1) z = alpha s$, thus $0 = d^T y = alpha s^T y$, hence $alpha$ must equal zero, since we assumed $y^T s > 0$. Thus, $d = 0$, which we also assumed wasn't the case. Thus, we can never have equality here, and thus $d^T H_+ d > 0$, and so $H_+ > 0$.
]

#lemma[
  If in the $k$th iteration of @tab:BFGS we have $H_k > 0$ and there exists $t_k in T_"WP" (x^k, d^k)$, then $(s^k)^T y^k > 0$.
]<lem:bfgspositivesy>

#proof[
  We have $ (s^k)^T y^k & = (x^(k + 1) - x^k)^T (gradient f(x^(k + 1)) - gradient f(x^k)) \
  & = t_k (d^k)^T (gradient f(x^(k + 1)) - gradient f(x^k)) \
  & >=^"WP" t_k (rho - 1) gradient f(x^k)^T d^k \
  & = underbrace(t_k (1 - rho), > 0) underbrace((underbrace(gradient f(x^k), eq.not 0))^T H_k^(-1) gradient f(x^k), > 0) \
  & > 0, $ since $H_k^(-1) > 0$ and $t_k > 0$ and $0< rho < 1$.
]

#theorem[
  Let $f in C^1 (RR^n)$ and bounded from below. Then, the following hold for the iterates generated by @tab:BFGS:
  1. $(s^k)^T y^k > 0$;
  2. $H_k > 0$;
  3. thus, @tab:BFGS is well-defined, i.e. at each iteration, each step generates a valid value.
]

#proof[
  We prove inductively on $k$, with the fact that $H_0 > 0$ already establishing 2. for the base step. $H_k > 0$ implies the existence of a unique solution $d^k = - H_k^(-1) gradient f(x^k)$ to QNE. Because $gradient f(x^k) eq.not 0$, $gradient f(x^k)^T d^k < 0$ so $(x^k, d^k) in cal(A)_f$. By @lem:raybounded, there exists a $t_k in T_"WP" (x^k, d^k)$. Thus, by @lem:bfgspositivesy, $(y^k)^T s^k > 0$ and so by @lem:bfgspositiveness $H_(k + 1) > 0$. Since this holds for any $k$ this proves the result.
]
#theorem[Let $f : RR^n -> RR$ be continuously differentiable, and ${x^k}, {d^k}, {t_k}$ be generated by @tab:BFGS. assume that $gradient f$ is Lipschitz on $cal(L) := "lev"_(f(x^0)) f$, and that there exists a $c > 0$ such that $"cond"(H_k) := (lambda_max (H_k))/(lambda_min (H_k)) <= 1/c$ for all $k in NN$. Then every cluster point of ${x^k}$ is a stationary point of $f$.
]

#proof[
  For all $k in NN$, $ - gradient f(x^k)^T d^k = (d^k)^T H_k d^k & >= lambda_min (H_k) norm(d^k)^2 \
  & = lambda_min (H_k) norm(H^(-1)_k nabla f(x^k)) norm(d^k) \
  & = (lambda_min (H_k))/(norm(H_k)) norm(H_k) norm(H^(-1)_k nabla f(x^k)) norm(d^k) \
  &>= (lambda_min (H_k))/(lambda_max (H_k)) norm(gradient f(x^k)) norm(d^k) \
  &= 1/("cond"(H_k)) norm(gradient f(x^k)) norm(d^k) \
  &>= c norm(gradient f(x^k)) norm(d^k), $ and thus $- (gradient f(x^k)^T d^k)/(norm(gradient f(x^k)) norm(d^k)) >= c$ for all $k in NN$ (this is the so-called "angle condition"). Moreover, under the assumptions on $f$, the Wolfe-Powell rule (restricted to $cal(A)_f sect cal(L) times RR^n$, in which we always stay) is efficient, so by the previously established global convergence of @tab:A1, we have convergence of this algorithm as well.
]
#remark[We cited the convergence of @tab:A1, which we couldn't do when proving convergence of the gradient, since the step size in that case was _not_ efficient.]

#remark[
  1. The assumption that $gradient f$ is Lipschitz on $"lev"_(f(x^0)) f$ is satisfied under either of the following conditions,\
    (i) $f in C^2$ and $norm(gradient^2 f (x))$ bounded on a convex superset of $cal(L);$\
    (ii) $f in C^2$ and $cal(L)$ is bounded (hence compact).\
  An example of a $C^1$ function that is not $C^2$ but still globally Lipschitz is $f(x) := 1/2 "dist"^2_C (x)$ where $C$ a convex set, and $gradient f(x) = x - P_C (x)$ where $P_C$ the projection onto $C$.
  2. The BFGS method is regarded as one of the most robust methods for smooth, unconstrained optimization up to medium scale. For large-scale, there is a method called "limited memory BFGS". Surprisingly, BFGS can be modified to work well for nonsmooth functions with a special line search method.
]

==== Inexact Methods

The local Newton's method involves finding $d^k$ such that $gradient^2 f (x^k) d^k = - gradient f(x^k)$. Quasi-Newton methods replace the Hessian with an approximation, and indirect methods further allow the flexibility to let $d^k$ approximately solve this equation (since solving this equation exactly can be costly). The goal is to find $d^k$ such that $ norm(gradient^2 f(x^k) d + gradient f(x^k))/(norm(gradient f(x^k))) <= eta_k $ for a prescribed tolerance $eta_k$. This is called the _inexact Newton's equation_.

#remark[Dividing by $norm(gradient f(x^k))$ here enforces the idea that the closer $x^k$ is to a stationary point, the higher accuracy we require.]
#figure(
  kind: "Code",
  supplement: "Algorithm",
  table(
    columns: 1,
    rows: 2,
    align: left,
    [#align(center, "Local Inexact Newton's Method")],
    [
      S0. Choose $x^0 in RR^n, epsilon >= 0$ and set $k := 0$.\
      S1. If $norm(gradient f(x^k)) <= epsilon$, STOP.\
      S2. Choose $eta_k >= 0$ and determine $d^k$ such that $ norm(gradient^2 f(x^k) d + gradient f(x^k))/(norm(gradient f(x^k))) <= eta_k. $
      S3. Set $x^(k + 1) = x^k + d^k$, increment $k$ and go to S1.
    ],
  ),
)<tab:inexactnewton>

#theorem[
  Let $f : RR^n -> RR$ be $C^2$, let $overline(x)$ be a stationary point of $f$ such that $gradient^2 f(overline(x))$ is invertible. Then there exists $epsilon > 0$ such that for all $x^0 in B_epsilon (overline(x))$:
  1. If $eta_k <= overline(eta)$ for all $k in NN$ for some $overline(eta) > 0$ sufficiently small, then @tab:inexactnewton is well-defined and generates a sequence that converges at least linearly to $overline(x)$.
  2. If $eta_k arrow.b 0$, the rate of convergence is superlinear.
  3. If $gradient^2 f$ is locally Lipschitz (for instance, if $f in C^3$) and $eta_k = cal(O)(norm(gradient f(x^k)))$, then the rate is quadratic.
]
#remark[For $eta_k = 0$, we just recover the local Newton's method. 2. and 3. strongly point their fingers at how to choose $eta_k$. 1. is theoretically important, but practically useless since $overline(eta)$ is generally unknown.]




#figure(
  kind: "Code",
  supplement: "Algorithm",
  table(
    columns: 1,
    rows: 2,
    align: left,
    [#align(center, "Globalized Inexact Newton's Method")],
    [
      S0. Choose $x^0 in RR^n, epsilon >= 0$, $rho > 0, p > 2$, $beta in (0, 1)$, $sigma in (0, 1/2)$ and set $k := 0$.\
      S1. If $norm(gradient f(x^k)) <= epsilon$ STOP.\
      S2. Choose $eta_k >= 0$ and determine $d^k$ by $ norm(gradient^2 f(x^k) d + gradient f(x^k)) <= eta_k norm(gradient f(x^k)). $ If this is not possible, or not feasible, i.e. $gradient f(x^k)^T d^k <= - rho norm(d^k)^p$ is violated, then set $d^k := - gradient f(x^k)$.\
      S3. Determine $t_k > 0$ by Armijo, $t_k := max_{ell in NN_0} {beta^ell | f(x^k + beta^ell d^k) <= f(x^k) + beta^ell sigma gradient f(x^k)^T d^k}$.\
      S4. Set $x^(k + 1) = x^k + t_k d^k$, increment $k$ and go to S1.
    ],
  ),
)<tab:inexactnewtonglobal>

#theorem[
  Let $f : RR^n -> RR$ be $C^2$ and let ${x^k}$ be generated by @tab:inexactnewtonglobal with $eta_k arrow.b 0$. If $overline(x)$ is a cluster point of ${x^k}$ with $gradient^2 f (overline(x)) > 0$, then the following hold:
  1. ${x^k}$ converges along the whole sequence to $overline(x)$, which is a strict locally minimizer of $f$.
  2. For all $k$ sufficiently large, $d^k$ will be given by the inexact Newton equation.
  3. For all $k$ sufficiently large, the full step-size $t_k = 1$ will be accepted.
  4. The convergence is at least superlinear.
]

=== Conjugate Gradient Methods for Nonlinear Optimization

==== Prelude: Linear Systems

Remark that, for $A > 0$ and $b in RR^n$, $ A x = b wide <=> wide x "minimizes" f(x):=1/2 x^T A x - b^T x. $

#definition([$A$-conjugate vectors])[
  Let $A > 0$ and $x, y in RR^n \\ {0}$ are called _$A$-conjugate_ if $ x^T A y = 0 $ (i.e. $x, y$ are orthogonal in the inner product induced by $A$, denoted $angle.l dot, dot angle.r_A$).
]

#lemma[
  Let $A> 0, b in RR^n$, and $f(x) := 1/2 x^T A x - b^T x$. Let $d^0, d^1, dots, d^(n - 1)$ be (pairwise) $A$-conjugate. Let ${x^k}$ be generated by $x^(k + 1) = x^k + t_k d^k, x^0 in RR^n$, where $t_k := "argmin"_(t > 0) f(x^k + t_k d^k)$. Then, after _at most_ $n$ iterations, $x^n$ is the (unique) global minimizer $overline(x)$ ($= A^(-1) b$) of $f$. Moreover, with $g^k := gradient f(x^k)$ ($= A x^k - b$), we have $ t_k = - ((g^k)^T d^k)/((d^k)^T A d^k) > 0, $ and $(g^(k + 1))^T d^j = 0$ for all $j = 0, dots, k$.
]

#proof[
  The formula for $t_k$ was proven in an exercise. To prove the latter statement, note that $ (g^(k + 1))^T d^k & = (A x^(k + 1) - b)^T d^k \
                    & = (A x^k - b + t_k A d^k)^T d^k \
                    & = (g^k)^T d^k + t_k (d^k)^T A d^k \
                    & = (g^k)^T d^k - (g^k)^T d^k = 0. $

  Moreover, for all $i, j = 0, dots, k$ with $i eq.not j$, we have that $ (g^(i + 1) - g^i)^T d^j = (A x^(i + 1) - A x^(i))^T d^j = t_i (d^i)^T A d^j = 0, $ hence for all $j = 0, dots, k$, $ (g^(k + 1))^T d^j = (g^(j+1))^T d^j + sum_(i=j+1)^k (g^(i+1) - g^i)^T d^j = 0. $ Thus, $g^n$ is orthogonal to the $n$ linearly independent vectors ${d^0, dots, d^(n+1)}$, which implies $g^n = 0$, thus proving the conclusion.
]

We want to obtain these $A$-conjugate vectors, while simultaneously ensuring that they are descent directions at each step, i.e. that $gradient f(x^k)^T d^k < 0$ for all $k = 0, dots, n - 1$. We do this algorithmically.

Assume $gradient f(x^0) eq.not 0$ (else we are done), and take $d^0 := - gradient f(x^0)$. Suppose then we have $l + 1$ $A$-conjugate vectors $d^0, dots, d^l$ with $gradient f(x^i)^T d^i < 0$ for each $i$. Suppose $ d^(l+ 1) := - g^(l + 1) + sum_(i=0)^l beta_(i l) d^i, $ where $g^(l + 1)$ is "valid" to be used since it is not in the span of ${d^0, dots, d^l}$, and ${beta_(i l)}$ are scalars to be determined. The condition $(d^(l + 1))^T A d^j = 0$ readily implies that $ beta_(j l) := ((g^(l + 1))^T A d^j)/((d^j)^T A d^j), quad j = 0, dots, l. $ Then, it follows that $(g^(l+1))^T d^(l+1) = - norm(g^(l+1))^2 < 0$, and since $g^(l+1) = gradient f(x^(l+1))$ by definition, it follows $d^(l+1)$ a descent direction. Thus, it must be that $ g^(j + 1) - g^j = A x^(j + 1) - A x^j = t_j A d^j, $ and so with $t_j > 0$, $ (g^(l+1))^T A d^j = 1/t_j (g^(l+1))^T (g^(j+1) - g^j), $ and thus $ beta_(j l) = cases(
  0 & j = 0\, dots\, l - 1,
  (norm(g^(j + 1))^2)/(norm(g^l)^2) & j = l
), $ and thus our update of $d^(l+1)$ reduces to $ d^(l+1) := - g^(l+1) + beta_l d^l, wide beta_l := beta_(l l). $ In summary, this gives the following algorithm.


#figure(
  kind: "Code",
  supplement: "Algorithm",
  table(
    columns: 1,
    rows: 2,
    align: left,
    [#align(center, "CG method for linear equations")],
    [
      S0. Choose $x^0 in RR^n$ and $epsilon >= 0$, set $g^0 := A x^0 - b$, $d^0 := - g^0$ and initiate $k = 0$.\
      S1. If $norm(g^k) <= epsilon$, STOP.\
      S2. Put $ t_k := (norm(g^k)^2)/((d^k)^T A d^k). $
      S3. Set $ x^(k + 1) & = x^k + t_k d^k \
      g^(k + 1) & = g^k + t_k A d^k \
         beta_k & = norm(g^(k + 1))^2/(norm(g^k)^2) \
      d^(k + 1) & = - g^(k + 1) + beta_k d^k. $
      S4. Increment $k$ and go to S1.

    ],
  ),
)<tab:CGlinear>

#theorem("Convergence of CG Method")[
  Let $A in RR^(n times n)$  be symmetric positive definite, $b in RR^n$ and $f(x) := 1/2 x^T A x - b^T x$. Then, @tab:CGlinear will produce the global miniumum $overline(x)$ of $f$ after at most $n$ interations. If $m in {0, dots, n}$ is the smallest number such that $x^m = overline(x)$, then the following hold as well:
  $
    (d^k)^T A d^j = 0, (g^k)^T g^j = 0, (g^k)^T d^j = 0, wide (k = 1, dots, m, j = 0, dots, k - 1),\
    (g^k)^T d^k = - norm(g^k)^2 wide (k = 0, dots, m).
  $
]

=== The Fletcher-Reeves Method

We want to apply the same method as the previous section for non-quadratic and non-convex functions. The isue we need to resolve, though, is that the step-size rule in S2. of @tab:CGlinear is no longer appropriate. To resolve, we introduce the _Strong Wolfe-Powell rule._ Choose $sigma in (0, 1), rho in (sigma, 1)$. The strong WP rule for a differentiable $f : RR^n -> RR$ reads $ T_("SWP") : (x, d) in cal(A)_f |-> {t > 0 quad #line(angle: 90deg) quad#stack(
    spacing: 1em,
    [$f(x + t d) <= f(x) + sigma t gradient f(x)^T d$],
    [$|gradient f(x + t d)^T d| <= - rho gradient f(x)^T d$],
  )}, $ noting that clearly $T_"SWP" (x, d) subset T_"WP" (x, d)$.


#figure(
  kind: "Code",
  supplement: "Algorithm",
  table(
    columns: 1,
    rows: 2,
    align: left,
    [#align(center, "Fletcher-Reeves")],
    [
      S0. Choose $x^0 in RR^n$, $epsilon >= 0$, $0 < sigma < rho < 1/2$, set $d^0 := - gradient f(x^0)$ and $k = 0$.\
      S1. If $norm(gradient f(x^k)) <= epsilon$, STOP.\
      S2. Determine $t_k > 0$ such that $ f(x^k + t_k d^k) <= f(x^k) + sigma t_k gradient f(x^k)^T d^k, \
      |gradient f(x^k + t_k d^k)^T d^k| <= - rho gradient f(x^k)^T d^k. $
      S3. Set $   x^(k + 1) & = x^k + t_k d^k \
      beta_k^"FR" & = norm(gradient f(x^(k+1)))^2/norm(gradient f(x^k))^2 \
        d^(k + 1) & = - gradient f(x^(k + 1)) + beta_k^"FR" d^k. $
      S4. Increment $k$ and go to S1.
    ],
  ),
)<tab:fletcherreeves>

#lemma[
  Let $f : RR^n -> RR$ be $C^1$ and bounded from below and $(x, d) in cal(A)_f$. Then $T_"SWP" (x, d) eq.not nothing$.
]
#proof[
  Define $phi, psi : RR -> RR$ by $ phi(t) := f(x + t d), wide psi(t) = f(x) + sigma t gradient f(x)^T d, $ noting that $psi$ affine linear with negative slope. We need to show, then, that $phi(t) <= psi(t)$ and $|phi'(t)| <= -rho phi'(0)$ for some $t > 0$. Now, $phi(0) = psi(0)$, and $phi'(0) < psi'(0)$. By Taylor's theorem, $phi(t) < psi(t)$ for all $t > 0$ sufficiently small. Define $ t^ast = min{t > 0 | phi(t) = psi(t)}. $ This exists, since $psi(t) -> - infinity$ as $t -> infinity$, and $phi(t)$ is bounded from below; for small $t$, $phi(t) < psi(t)$, so by continuity there must exist $t > 0$ for which $phi(t) = psi(t)$, so $t^ast$ well-defined. Moreover, we have then that $phi'(t^ast) >= psi'(t^ast)$, which we can see by Taylor/graphically.

  Now, we consider two cases. Suppose first that $phi'(t^ast) < 0$. Then, $ |phi'(t^ast)| = - phi'(t^ast) <=- psi'(t^ast) = - sigma gradient f(x)^T d. $
  We know $sigma < rho$, so we're done, so this is further upper bounded by $- rho gradient f(x)^T d = -rho phi'(0)$, so we're done in this case with $t^ast$.

  Next, suppose $phi'(t^ast) >= 0$. $t^ast$ won't cut it in this case, but we can see that there exists $t^(ast ast) in (0, t^ast]$, by intermediate value theorem, for which $phi'(t^(ast ast)) = 0$. Since $t^ast$ the _first_ time $phi, psi$ are equal (being the minimum) and $t^(ast ast) <= t^ast$, it follows that we have $phi(t^(ast ast)) < psi(t^(ast ast))$. Also trivially, $ |phi'(t^(ast ast))| = 0 <= - rho phi'(0), $ since $phi'(0) < 0$, and thus $t^(ast ast)$ provides the appropriate $t$ value for the claims, so we're done.
]

#remark[In particular, this immediately gives the well-definedness of @tab:fletcherreeves, assuming ${x^k} times {d^k} in cal(A)_f$.]

#lemma[
  Let $f : RR^n -> RR$ be $C^1$ and bounded from below. Let ${x^k}, {d^k}$ be generated by @tab:fletcherreeves. Then, $ - sum_(j=0)^k rho^j <= (gradient f(x^k)^T d^k)/(norm(gradient f(x^k))^2) <= -2 + sum_(j=0)^k rho^j, $ for all $k in NN$.
]

#proof[
  We induct on $k$. For $k = 0$, the claim reads $ - 1 <= - 1 <= -2 + (1) = -1, $ since $d^0 = - gradient f(x^0)$, so it holds trivially.

  Suppose the claim for some fixed $k in NN$. We have $ rho gradient f(x^k)^T d^k <= gradient f(x^(k+1))^T d^k <= - rho gradient f(x^k)^T d^k $ by (S2), which implies by a little algebraic manipulation $ -1 + rho (gradient f(x^k)^T d^k)/(norm(gradient f(x^k))^2) <= -1 + (gradient f(x^(k+1))^T d^k)/(norm(gradient f(x^k))^2) <= -1 - rho (gradient f(x^k)^T d^k)/(norm(gradient f(x^k))^2). wide (star) $ In addition, by (S3), we know $ (gradient f(x^(k+1))^T d^(k + 1))/(norm(gradient f(x^(k+1)))^2) &= (gradient f(x^(k+1))^T (- gradient f(x^(k+1)) + beta_k d^k))/(norm(gradient f(x^(k+1)))^2)\
  &= -(gradient f(x^(k+1))^T gradient f(x^(k+1)))/(norm(gradient f(x^(k+1)))^2) + beta_k (gradient f(x^(k+1))^T d^k)/(norm(gradient f(x^(k+1)))^2) \
  &= -1 + (gradient f(x^(k + 1))^T d^k)/(norm(gradient f(x^k))^2), $ thus $
    (gradient f(x^(k+1))^T d^(k + 1))/(norm(gradient f(x^(k+1)))^2) = -1 + (gradient f(x^(k + 1))^T d^k)/(norm(gradient f(x^k))^2) wide (star star) // ?
  $
  thus $  - sum_(j = 0)^(k + 1) rho^j & = -1 - sum_(j=1)^(k + 1) rho^j \
                               & = -1 + rho (-sum_(j=0)^(k) rho^j) \
  ("induction hypothesis")wide & <= -1 + rho (gradient f(x^(k))^T d^k)/(norm(gradient f(x^k))^2) \
                   (star) wide & <= -1 + (gradient f(x^(k + 1))^T d^k)/(norm(gradient f(x^k))^2) wide (dagger) \
                   (star) wide & <= -1 - rho (gradient f(x^k)^T d^k)/(norm(gradient f(x^k))^2) \
  ("induction hypothesis")wide & <= -1 + rho sum_(j=0)^k rho^j = -2 + sum_(j=0)^(k + 1) rho^j. $
  But by $(ast ast)$, the line $(dagger) = (gradient f(x^(k+1))^T d^(k+1))/(norm(gradient f(x^(k+1)))^2)$, so we've shown the claim.
]

#theorem[
  Let $f : RR^n -> RR$ be $C^1$ and bounded from below, and let ${x^k}, {d^k}$ be generated by @tab:fletcherreeves. Then,
  1. @tab:fletcherreeves is well-defined,
  2. $gradient f(x^k)^T d^k < 0$ for all $k in NN$ (it is a descent method).
]

#proof[
  By the previous lemma, $ (gradient f(x^k)^T d^k)/(norm(gradient f(x^k))^2) <= -2 + sum_(j=0)^k rho^j <= -2 + sum_(j=0)^infinity rho^j = -2 + 1/(1 - rho) = (2 rho - 1)/(1 - rho) < 0, $ since $rho < 1/2$. Multiplying both sides by $norm(gradient f(x^k))^2$ gives 2. Combining 2. with the previous previous lemma and the accompanying remarks, 1. follows.
]

#theorem("Al-Baali")[
  Let $f : RR^n -> RR$ be $C^1$ and bounded from below, such that $f$ is Lipschitz on $"lev"_(f(x_0)) f$, and let ${x^k}, {d^k}$ be generated by @tab:fletcherreeves. Then, $ lim_(k -> infinity) norm(gradient f(x^k)) = 0. $
]

== Least-Squares Problems

Supposing we wish to find the root of a function $F : RR^n -> RR^m$, we know that when $m = n$, then Newton's method is applicable. More generally, though, for $m eq.not n$, such methods are not available. However, we can approach this by equivalently considering the optimization problem $ min_x 1/2 ||F(x)||^2. $ Such a problem, i.e. "minimizing the square of the norm", will be considered here. Naturally, since this is now a real-valued objective function, we could just apply Newton's method to it, but we'll do things a little more interesting.

=== Linear Least-Squares

Suppose $F(x) = A x - b$ an affine linear function for $A in RR^(m times n), b in RR^m$; the least-squares problem just becomes $ min_x 1/2 norm(A x - b)^2. wide (dagger) $

#theorem[
  1. $overline(x)$ solves $(dagger)$ $<=>$ $overline(x)$ solves $A^T A x = A^T b$.
  2. $(dagger)$ always has a solution.
  3. $(dagger)$ has a unique solution $<=>$ $"rank"(A) = n$.
]

#proof[
  1. With $f(x) := 1/2 norm(A x - b)^2$ the function of interest, one readily checks $gradient f(x) = A^T A x - A^T b$ (by chain rule, or by expanding $f$ as a "proper" quadratic) and $gradient^2 f(x) = A^T A$. Thus, since $A^T A >= 0$ always, $f$ is convex so stationary points are equivalent to minimization points, and thus we need $gradient f(x) = 0 <=> A^T A x = A^T b$.
  2. By 1., we have a solution $<=>$ $A^T b$ in the image of $A^T A$; but this is equal to the image of $A^T$, and obviously $A^T b$ in the image of $A^T$.
  3. Similarly to the previous, we will have a unique solution to $A^T A x = A^T b$ iff $A^T A$ has full rank $<=>$ $A$ has full rank.
]

=== Gauss-Newton for Nonlinear Least-Squares

Suppose $F in C^1$. Inspired by Newton's method, we will, instead of linearizing $f(x) := 1/2 norm(F(x))^2$, we will linearize $F(x)$; plugging this linearization back into the norm squared, we expect a quadratic function. Indeed, suppose we have an iterate $x^k in RR^n$; then, the linearization of $F$ about $x^k$ is given by $ F_k (x) = F(x^k) + F'(x^k) (x - x^k). $ Then, $ q(x) := 1/2 norm(F_k (x))^2 = dots.c = 1/2 x^T (F'(x^k)^T F'(x^k)) x + [F'(x^k)^T F(x^k) - F'(x^k)^T F'(x^k) x^k]^T x + "const", $ where $"const"$ independent of $x$. Assume $F'(x^k)$ of full rank $n$. Then, $F'(x^k)^T F'(x^k) > 0$, and so by the previous section, $ x^+ in "argmin"(q) & <=> gradient q(x^+) = 0 \
                   & <=> F'(x^k)^T F'(x^k) x^+ + F'(x^k)^T F(x^k) - F'(x^k)^T F'(x^k) x^k = 0 \
                   & <=> x^+ = x^k underbrace(- (F'(x^k)^T F'(x^k))^(-1) F'(x^k)^T F(x^k), := d^k). $
Thus, this inspires the Gauss-Newton Method; supposing we can find $d$ as a solution to the _Gauss-Newton Equations_ (GNE), $ F'(x^k)^T F(x^k) d = - F'(x^k)^T F(x^k), $ then we update $x^(k + 1) = x^k + d^k$. In particular, with this choice, $ gradient f(x)^T d^k = -(underbrace(F'(x^k)^T F(x)^k, = u))^T underbrace((F'(x^k)^T F'(x^k))^(-1), >= 0) (underbrace(F'(x^k)^T F(x^k), = u)) < 0, $ i.e., if $gradient f(x^k) eq.not 0$ and $F'(x^k)$ of rank $n$, then $d^k$ a descent direction.

The Newton's Equation for the same function $f$ would read $ (F'(x^k)^T F'(x^k) + S(x^k)) d = - F'(x^k)^T F(x^k), $ where $ S(x^k) = sum_(i=1)^m F_i (x^k) gradient^2 F_i (x^k); $ if $S$ were zero, then this the same as the GNE (though of course, this will not hold in general).

= Constrained Optimization

== Optimality Conditions for Constrained Problems

Consider $ min f(x) "s.t." #stack(spacing: 1em, $g_i (x) <= 0 forall i = 1, dots, m,$, $h_j (x) = 0 forall j = 1, dots, p$), $ where we will assume $f, g_i, h_j : RR^n -> RR$ are continuously differentiable. We call such a problem a _nonlinear program_. We put as before the _feasible set_ $ X := {x | g_i (x) <= 0 forall_(i=1)^m, h_j (x) = 0 forall_(j=1)^p}. $
We'll also define the index sets $ I := {1, dots, m}, wide J := {1, dots, p}, $ and the _active indices_ for a point $overline(x)$ by $ I(overline(x)) := {i in I | g_i (overline(x)) = 0} subset I. $

=== First-Order Optimality Conditions

Consider the slightly more abstract problem $ min_x f(x) "s.t." x in S wide (dagger), $ with $f : RR^n -> RR$ in $C^1$ and $S subset RR^n$ closed and nonempty.

#definition("Cones")[
  A nonempty set $K subset RR^n$ is said to be a _cone_ if $ lambda v in K quad forall v in K, lambda >= 0, $ i.e. $K$ is closed under positive scalings of vectors in $K$.
]

#remark[
  We can in fact replace $RR^n$ with any real vector space $V$, for a cone living in $V$.
]

We have that
- any vector space;
- the nonnegative reals;
- $Lambda := {(x, y)^T | x, y in K, x^T y = 0}$, where $K$ a given cone;
- and  $S_+^n := {A in RR^(n times n) | A >= 0}$ (embedded in an appropriate space of matrices)
are all cones, for instance.

#definition[
  Let $S subset RR^n$, $overline(x) in S$. Then $ T_s (overline(x)) := {d in R^n | exists {x^k in S} -> overline(x), {t_k} arrow.b 0 "s.t." (x^k - overline(x))/(t_k) ->d} $ is called the _tangent cone of $S$ at $overline(x)$_.
]

#proposition[
  Let $S subset RR^n$, $x in S$. Then $T_S (x)$ is a closed cone.
]

#theorem("Basic First-Order Optimality Conditions")[
  Let $overline(x)$ be a local minimizer of $(dagger)$. Then,
  1. $gradient f(overline(x))^T d >= 0$ for all $d in T_S (overline(x))$;
  2. if $S$ is convex, then $gradient f(overline(x))^T (x - overline(x)) >= 0$ for all $x in S$.
]

#proof[
  1. Let $d in T_S (overline(x))$. By definition, there exists ${x^k} subset S$ and ${t_k}arrow.b 0$ for which $(x^k - overline(x))/(t_k) -> d$. As $x^k$ feasible and $overline(x)$ a local minimizer of $f$ over $S$, $ f(x^k) - f(overline(x)) >= 0 $ for all $k$ sufficiently large. By the mean value theorem, there is for each $k$ sufficiently large a $theta_k$ on the line between $x^k$ and $overline(x)$ for which $ f(x^k) - f(overline(x)) = gradient f(theta_k)^T (x^k - overline(x)), $ so $ 0 <= (f(x^k) - f(overline(x)))/(t_k) = (gradient f(theta_k)^T (x^k - overline(x)))/(t_k) ->_k gradient f(overline(x))^T d. $
  2. Suppose not. Then, there exists a $hat(x) in S$ such that $gradient f(overline(x))^T (hat(x) - overline(x)) < 0$. By convexity, $overline(x) + lambda (hat(x) - overline(x)) in S$ for $lambda in (0, 1)$. By mean value theorem, for every such $lambda$ there exists a $theta_lambda$ on the line between $overline(x) + lambda (hat(x) - overline(x))$ and $overline(x)$ for which $ f(overline(x) + lambda(hat(x) - overline(x))) - f(overline(x)) = lambda gradient f(theta_lambda)^T (hat(x) - overline(x)). $ By supposition, for $lambda$ sufficiently close to $0$, the right-hand side will remain negative (since $gradient f(theta_lambda) ->_(lambda -> 0) gradient f(overline(x))$), so for sufficiently small $lambda$, $ f(overline(x) + lambda (hat(x) - overline(x))) < f(overline(x)), $ and since $overline(x) + lambda (hat(x) - overline(x))$ remains feasible for all $lambda$ by covexity, this contradicts minimality.
]

#set quote(block: true)
#show quote: set align(center)
#show quote: set pad(x: 5em)

#remark[
  Computationally, this isn't very helpful - in practice, i.e. in trying to compute local minimizers, we'd need to compute $gradient f(overline(x))^T d$ for every $d$ in the tangent cone of a given $S$ at a given point $overline(x)$. In general, we don't know what this set looks like, and even if we did, this isn't a feasible condition to check for every such point, since it isn't easy to interpret computationally.
  #quote(block: true, attribution: "Tim H", "You can never tell the computer what the fucking set looks like")
]

=== Farkas' Lemma

#definition("Projection")[
  Let $S subset RR^n$ be nonempty, $x in RR^n$. The _projection_ of $x$ onto $S$ is given by $ P_S (x) := "argmin"_(y in S) 1/2 norm(x - y)^2. $
]
#remark[
  This is, in general, a set-valued function; it could even be empty (for instance, if $S = [0, 1)$ and $x = 2$.)
]

#proposition[
  Let $x in RR^n, S subset RR^n$ nonempty, closed and convex. Then,
  1. $P_S (x)$ has exactly one element, so $P_S$ can be viewed $RR^n -> S$;
  2. $P_S (x) = x <=> x in S$;
  3. (The Projection Theorem) $(P_S (x) - x)^T (y - P_S (x)) >= 0$ for all $y in S$.
]

#proof[

  1. This follows from the fact that $S in.rev y |-> norm(x - y)_2^2$ a strongly convex function.
  2. Clear.
  3. Take $f(y) = 1/2 norm(x - y)^2$ in the last theorem.
]

#lemma[
  Let $B in RR^(ell times n)$. Then, ${B x | x in RR^n_+}$ is a nonempty, closed, convex cone.
]

#proof[
  Convexity and cone properties are clear. Closed? // TODO better proof?
]

#theorem("Farkas' Lemma")[
  Let $B in RR^(ell times n)$, $h in RR^n$. Then, the following are equivalent:
  1. The system $ B^T x = h, x >= 0 $ has a solution.
  2. $h^T d >= 0$ for all $d$ such that $B d >= 0$.
]

#remark[
  $x >= 0$ should be understood component-wise, i.e. each component of $x$ is nonnegative.
]

#proof[
  $(1. => 2.)$ Let $x >= 0$ such that $B^T x = h$. Then, if $d$ such that $B d >= 0$, $ h^T d = (B^T x)^T d = x^T B d >= 0. $

  $(2. => 1.)$ Suppose 1. doesn't hold, i.e. $ h in.not K = {B^T x | x >= 0}, $ where $K$ a closed, convex cone as the previous lemma. Set $overline(s) = P_K (h) in K$, which is well-defined since $K$ closed and convex. Set $overline(d) = overline(s) - h eq.not 0$. Thus, by the rojection theorem, $ overline(d)^T (s - overline(s)) >= 0 $ for all $s in K$.

  By taking $s = 2 overline(s) in K$, we see then that $overline(d)^T overline(s) >= 0$. Also, taking $overline(s) = 0$, this implies $-overline(d)^T overline(s) >= 0$, by which we must have $overline(d)^T overline(s) = 0$ and thus $overline(d)^T s >= 0$ for all $s in K$. By definition of $K$, $(B overline(d))^T x = overline(d)^T B^T x >= 0$ for all $x >= 0$. This implies $B overline(d) >= 0$, by taking $x$ to be each standard unit vector $e_i$.

  OTOH, $ h^T overline(d) = (overline(s) - overline(d))^T overline(d) = underbrace(overline(s)^T overline(d), = 0) - norm(overline(d))^2 < 0, $ since $overline(d) eq.not 0$. This contradicts 2.
]

=== Karush-Kuhn-Tucker Conditions


#definition("KKT Conditions")[
  Consider the standard nonlinear program $ min f(x) "s.t." #stack(spacing: 1em, $g_i (x) <= 0 forall i = 1, dots, m,$, $h_j (x) = 0 forall j = 1, dots, p$). wide (star) $

  1. The function $L : RR^n times RR^m times RR^p -> RR$ defined by $ L(x, lambda, mu) & = f(x) + sum_(i=1)^m lambda_i g_i (x) + sum_(j=1)^p mu_j h_j (x) \
                     & = f(x) + lambda^T g(x) + mu^T h(x), $ where $lambda := (lambda_1, dots, lambda_m), g = (g_1, dots, g_m)$, $mu = (mu_1, dots, mu_p)$, $h = (h_1, dots, h_p)$, is called the _Lagrangian_ of the problem $(star)$.

  2. The set of conditions $ gradient L_x (x, lambda, mu) = 0, \ h(x) = 0,\ lambda >= 0, g(x) <= 0, lambda^T g(x) = 0 $ are called the _KKT Condition_ of $(star)$.
  3. A triple $(overline(x), overline(lambda), overline(mu))$ that satisfies the KKT conditions is called a _KKT point_ of $(star)$.
  4. Given $overline(x)$ feasible for $(star)$, define $ M(overline(x)) = {(lambda, mu) | (overline(x), lambda, mu) "is a KKT point of" (star)}. $
]

#definition("Linearized Cone")[
  Let $X$ be the feasible set of $(star)$ and $overline(x) in X$. The _linearized cone (of $X$) at $overline(x)$_ is given by the set $ cal(L)_X (overline(x)) := {d | #stack(spacing: .7em, $gradient g_i (overline(x))^T d <= 0 forall i in I(overline(x))$, $gradient h_j (overline(x))^T d = 0 forall j in J$) }. $
]

#definition("Abadie Constraint Qualification")[
  Let $overline(x) in X$. We say that the _Abadie constraint qualification (ACQ)_ holds at $overline(x)$ if $T_X (overline(x)) = cal(L)_X (overline(x))$.
]
#remark[
  We may represent the constraints that lead to $X$ in different ways. These different representations may lead to different linearized cones $cal(L)_X (overline(x))$, but will NOT change $T_X (overline(x))$. So, the ACQ may hold/not hold depending on how we represent $X$ for a fixed problem.
]

#theorem("KKT Conditions Under ACQ")[
  Let $overline(x)$ be a local minimizer of $(star)$ such that ACQ holds at $overline(x)$. Then, there exist $(overline(lambda), overline(mu)) in RR^m times RR^p$ such that $(overline(x), overline(lambda), overline(mu))$ a KKT point.
]

#proof[
  $overline(x)$ a local minimizer implies by the basic first-order optimality conditions for $(star)$ that $gradient f(overline(x))^T d >= 0$ for all $d in T_X (overline(x))$. Set $ B = mat(
    - gradient g_i (x)^T quad (i in I(overline(x)));
    - gradient h_j (x)^T quad (j in J);
    gradient h_j (x)^T quad (j in J);
  ) in RR^((|I(overline(x))| + 2 p)times n). $ Note that $d in cal(L)_X (overline(x))$ iff $B d >= 0$. By the ACQ, $gradient f(overline(x))^T d >= 0$ for all $d in cal(L)_X (overline(x))$, hence $gradient f(overline(x))^T d >= 0$ for all $d$ such that $B d >= 0$. By Farkas' Lemma (taking $B$ as defined, $h = gradient f(overline(x))$), there exists a $y = (y^1, y^2, y^3) in RR^(|I(overline(x))|) times RR^p times RR^p$ such that $B^T y = gradient f(overline(x))$ and $y >= 0$. Define $ overline(lambda) := cases(
    y_i^1 quad & i in I(overline(x)) \
             0 & "else"
  ), wide overline(mu) := y^2 - y^3. $ Then, $(overline(x), overline(lambda), overline(mu))$ is a KKT point.
]

#example[
  Consider $ min x_1^2 + x_2^2 quad "s.t." quad x_1, x_2 >= 0, x_1 x_2 = 0, $
  with $X = {x in RR^2 | x_1, x_2 >= 0, x_1 x_2 = 0}$. Let $overline(x) = (0, 0)^T in X$. We find that $ T_X (overline(x)) = X, wide cal(L)_X (overline(x)) = RR_+^2. $ So, ACQ does not hold. However, with $overline(lambda) = 0$ and $overline(mu) = 1$, we find $nabla f(overline(x)) + overline(lambda)_1 nabla g_1(overline(x)) + overline(lambda)_2 nabla g_2 (overline(x)) + overline(mu) nabla h(overline(x)) = 0$, and we find $(overline(x), overline(lambda), overline(mu))$ is a KKT point.
]

=== Constraint Qualifications

#definition[
  Let $overline(x)$ be a feasible point of the generic nonlinear program. We say that:
  1. the _linear independence constraint qualification (LICQ)_ holds at $overline(x)$ if the vectors $ gradient g_i (overline(x)), i in I(overline(x)), gradient h_j (overline(x)), j in J, $ are linearly independent;
  2. the _Mangasarian-Fromovitz CQ (MFCQ)_ holds at $overline(x)$ if the gradients $ gradient h_j (overline(x)), j in J $ are linearly independent, and there exists a $d in RR^n$ such that $ gradient g_i (overline(x))^T d < 0, i in I(overline(x)), \
    gradient h_j (overline(x))^T d = 0, j in J. $
]

#proposition([$"LICQ" => "MFCQ"$])[
  Let $overline(x)$ be feasible and such that LICQ holds at $overline(x)$. Then MFCQ holds at $overline(x)$.
]
#proof[
  Left as an exercise.
]

#theorem("Implicit Function Theorem")[
  Let $U subset RR^p, V subset RR^m$ open and $F : U times V -> RR^b$ continuous differentiable such that for $(overline(x), overline(y)) in U times V$, $F(overline(y), overline(z)) = 0$ and $D_y F(overline(y), overline(z)) in RR^(p times b)$ invertible. Then, there exist neighborhoods $hat(U) subset U$ and $hat(V) subset V$ and $g : hat(V) -> hat(U)$ continuously differentiable such that $ F(g(z), z) = 0
  , forall z in hat(V), $ and $ D g(z) = -[D_y F(g(z), z)]^(-1) D_z F(g(z), z), $ and for all $(y, z) in hat(U) times hat(V)$ such that $F(y, z) = 0$, then $y = g(z)$.
]

#lemma[
  Let $overline(x)$ be feasible such that $gradient h_j (overline(x)), j in J$ are linearly independent, and there exists $d$ such that $gradient g_i (overline(x))^T d < 0$ for $i in I(overline(x))$ and $gradient h_j (overline(x))^T d = 0$ for $j in J$. Then, there exists an $epsilon > 0$ and a $C^1$-curve $x : (- epsilon, epsilon) -> RR^n$ such that $x(t)$ feasible for all $t in [0, epsilon)$, $x(0) = overline(x)$, and $x'(0) = d$.
]

#proof[
  Define $H : RR^p times RR -> RR^p$ by $ H_j (y, t) := h_j (overline(x) + t d + h'(overline(x))^T y), quad j = 1, dots, p. $ The equation $H(y, t) = 0$ has as solution $(overline(y), overline(t)) = (0, 0)$, as $h_j (overline(x)) = 0$ by feasibility. Moreover, $ D_y H(overline(y), overline(t)) = h'(overline(x)) h'(overline(x))^T in RR^(p times p), $ with $h'(overline(x))^T$ having linearly independent columns, hence being invertible, so all of $D_y H(overline(y), overline(t))$ is invertible. By the implicit function theorem, there exists an $epsilon > 0$ and a $C^1$-curve $y :(-epsilon, epsilon) -> RR^p$ for which $y(0) = 0$, $H(y(t), t) = 0$ for all $t in (-epsilon, epsilon)$, and $y'(t) = - [D_y H(y(t), t)]^(-1) D_t H(y(t), t)$ for all $t in (-epsilon, epsilon)$. In particular, $ y'(0) = -[D_y H(0,0)]^(-1) h'(overline(x))d = 0, $ since $h'(overline(x)) = [gradient h_j (overline(x))^T] = 0$ by assumption. Set now $x(t) = overline(x) + t d + h'(overline(x))^T y(t)$. Making $epsilon$ smaller if necessary, we see that $x : (-epsilon, epsilon) -> RR^n$ has all the desired properties:
  - $x in C^1$ since $y in C^1$
  - $x(0) = overline(x)$
  - $x'(0) = d$
  - $x(t)$ is feasible: by construction, for $t in [0, epsilon)$, $h_j (x(t)) = H_j (y(t), t) = 0$; for $i in I\\I(overline(x))$, then $g_i (overline(x))= g_i (x(0)) < 0$, then by continuity $g_i (x(t))$ will remain negative for all sufficiently small $t$; for $i in I(overline(x))$, $g_i (overline(x)) = g_i (x(0)) = 0$, and $dif/(dif t) g_i (x(0)) = gradient g_i (overline(x))^T d < 0$, which implies $g_i (x(t)) < 0$ for all $t$ sufficiently small.
]

#proposition($"MFCQ" => "ACQ"$)[
  Let $overline(x)$ be a feasible point such that MFCQ holds at $overline(x)$; then ACQ holds.
]

#proof[
  We only need to show $cal(L)_X (overline(x)) subset T_X (overline(x))$. Let $d in cal(L)_X (overline(x))$. By MFCQ there exists $hat(d)$ such that $gradient g_i (overline(x))^T hat(d) < 0$ for $i in I(overline(x))$ and $gradient h_j (overline(x))^T hat(d) = 0$ for all $j in J$. Set $d(delta) = d + delta hat(d)$ for all $delta > 0$. Then, $ gradient g_i (overline(x))^T d(delta) < 0, forall i in I(overline(x)), wide gradient h_j (overline(x))^T d(delta) = 0 forall j in J. $ Applying the previous lemma to $d(delta)$ yields a $C^1$-curve $x : (-epsilon, epsilon) -> RR^n$ such that $x(0) = overline(x)$, $x'(0) = d(delta)$, and $x(t)$ feasible for all $t in [0, epsilon)$. Let $t_k arrow.b 0$ and set $x^k := x(t_k)$, then $x^k$ feasible and $x^k -> overline(x)$. We see that $ d(delta) = x'(0) = lim_(k -> infinity) (x(t_k) - x(0))/(t_k) = lim_(k -> infinity) (x^k - overline(x))/(t_k) in T_X (overline(x)), $ hence for all $delta > 0$, $d(delta) in T_X (overline(x))$. Letting $delta -> 0$, $d(delta) -> d$ and thus $d in T_X (overline(x))$ as well, since $T_X (overline(x))$ closed.
]

#corollary[
  Let $overline(x)$ be a local min of the generic nonlinear program such that MFCQ holds at $overline(x)$. Then the following hold:
  1. $M(overline(x)) eq.not nothing$;
  2. $M(overline(x))$ is bounded.
]
#proof[
  \1. follows from the previous proposition and the related theorem for ACQ. For 2., suppose otherwise, then there exists ${(lambda^k, mu^k)} subset M(overline(x))$ for which $norm((lambda^k, mu^k)) -> infinity$. Without loss of generality, we may assume $(lambda^k, mu^k)/(norm((lambda^k, mu^k))) -> (tilde(lambda), tilde(mu)) eq.not 0$. Since $(overline(x), lambda^k, mu^k)$ is a KKT point, we have $ 0 = (gradient f(overline(x)) + sum_(i in I(overline(x))) lambda_i^k gradient g_i (overline(x)) + sum_(j in J) mu_j^k gradient h_j (overline(x)))/(norm((lambda^k, mu^k))) -> sum_(i in I(overline(x))) tilde(lambda)_i gradient g_i (overline(x)) + sum_(j in J) tilde(mu)_j gradient h_j (overline(x)). $ If $tilde(lambda) = 0$, $tilde(mu) eq.not 0$ and thus $0 = sum_(j) tilde(mu)_j gradient h_j (overline(x))$ contradicts the linear independence of ${gradient h_j (overline(x))}$ of MFCQ.\ If $tilde(lambda) eq.not 0$, then there exists $i_0 in I(overline(x))$ such that $tilde(lambda)_(i_0) > 0$. Multiplying the above expression by $d$ from MFCQ yields $ 0 = sum_(i in I(overline(x))) overbrace(tilde(lambda)_i, >= 0) underbrace(gradient g_i (overline(x))^T d, < 0) + sum_(i in J) tilde(mu)_j overbrace(gradient h_j (overline(x))^T d, = 0) <= tilde(lambda)_(i_0) gradient g_(i_0) (overline(x))^T d < 0, $ a contradiction.
]

#corollary[
  Let $overline(x)$ be a local minimimum of the generic nonlinear program such that LICQ holds. Then, $M(overline(x))$ is a singleton.
]
// TODO better?
In summary, we have
#align(center, table(
  columns: 6,
  stroke: none,
  [], [LICQ], [$=>$], [MFCQ], [$=>$], [ACQ ],
  [], [#rotate(90deg, $=>$)], [], [#rotate(90deg, $=>$)], [], [#rotate(90deg, $=>$)],
  [$M(overline(x))$ is:], [a singleton], [], [nonempty,\ bounded], [], [nonempty],
))
=== Affine constraints

#definition("Affine CQ")[
  We say that the _affine CQ_ holds if all constraints are affine, i.e. there exists $a_i in RR^n, alpha_i in RR (i in I)$, $b_j in RR^n, beta_j in RR (j in J)$ such that $ g_i (x) = a_i^T x - alpha_i, wide h_j (x) = b_j^T x - beta_j. $
]


#proposition[
  Let the affine CQ hold. Then, ACQ holds at every feasible point.
]

#proof[
  Let $overline(x) in X$. As before, we only need to show $cal(L)_X (overline(x)) subset T_X (overline(x))$, then apply the previous lemma. Pick $d in cal(L)_X (overline(x))$, i.e. $a_i^T d <= 0, b_j^T d = 0$ for $i in I(overline(x)), j in J$. Let now $t_k arrow.b 0$ and $x^k := overline(x) + t_k d$. Then, $x^k -> overline(x)$ as $t_k -> 0$ and $(x^k - overline(x))/(t_k) -> d$. It remains to show that $x^k in X$ for all $k$ sufficiently large. We check the conditions for $x^k$ to be sufficient.

  If $i in.not I(overline(x))$, $a_i^T overline(x) < alpha_i$, so by continuity this strict inequalities remains true replacing $overline(x)$ by $x^k$ for $k$ sufficiently large.

  If $i in I(overline(x))$, $a_i^T overline(x) = alpha_i$ thus $ a_i^T x^k = a_i^T overline(x) + t_k a_i^T d <= alpha_i. $ Similar work follows for $j in J$, i.e. $b_j^T x^k = b_j^T overline(x) + t_k b_j^T d = beta_j + 0$.
]

=== Convex Problems

We consider $ min f(x) "s.t." #stack(spacing: 1em, $g_i (x) <= 0, i in I$, $b_j^T x = beta_j, j in J$), $ where now we assume $f, g_i : RR^n -> RR$ are $C^1$ and convex. The feasible set $ X = {x | g_i (x) <= 0 (i in I), b_j^T x = beta_j (j in J)} $ is then convex (as per a midterm question).

#theorem("KKT for Convex NLP")[
  Let $overline(x)$ be feasible for the convex NLP above and consider the following statements:
  1. there exists $(overline(lambda), overline(mu)) in M(overline(x))$ (i.e., $(overline(x), overline(lambda), overline(mu))$ is a KKT point);
  2. $overline(x)$ is a (global) minimizer;
  then, always 1. $=>$ 2., and hence if a constraint qualification holds at $overline(x)$, then 1. and 2. are equivalent.
]

#proof[
  Let $(overline(x), overline(lambda), overline(mu))$ be a KKT point. Then for any $x in X$, $ f(x) & >=^("convexity") f(overline(x)) + gradient f(overline(x))^T (x -overline(x)) \
  & =^("KKT") f(overline(x)) + (- sum_(i in I(overline(x))) overline(lambda)_i gradient g_i (overline(x)) - sum_(j in J) overline(mu)_j gradient h_j (overline(x)))^T (x - overline(x)) \
  &= f(overline(x)) - sum_(i in I(overline(x))) overline(lambda)_i underbrace(gradient g_i (overline(x))^T (x - overline(x)), <= g_i (x) - g_i (overline(x)) = g_i (x)) - sum_(j in J) overline(mu)_j underbrace(gradient h_j (overline(x))^T (x - overline(x)), "= 0, feasibility") \
  &>= f(overline(x)) - underbrace(sum_(i in I(overline(x))) overline(lambda)_i g_i (x), <= 0) >= f(overline(x)), $ which gives $overline(x)$ indeed a local min, so 2. holds. The reverse implication holding under a CQ is the very definition of a CQ.
]

#definition("Slater CQ")[
  We say the _Slater CQ (SCQ)_ holds for the convex NLP if there exists a $hat(x)$ such that $ g_i (hat(x)) < 0, (i in I), h_j (hat(x)) = 0 (j in J). $ We call such a point a _Slater point_.
]


#proposition([SCQ $=>$ ACQ])[
  Let SCQ hold for the convex NLP. Then, ACQ holds at every feasible point.
]

#proof[
  Let $overline(x) in X$ and set $ F(overline(x)) := {d | gradient g_i (overline(x))^T d < 0, i in I, b_j^T d = 0, j in J}. $ Then, $F(overline(x)) subset T_X (overline(x))$ (_exercise_). As $T_X (overline(x))$ is closed, it follows that $overline(F(overline(x))) subset T_X (overline(x))$. We know show that $cal(L)_X (overline(x)) subset overline(F(overline(x)))$, from whence we'll be done. So, let $d in cal(L)_X (overline(x))$ and let $hat(x)$ be a Slater point. Put $hat(d) = hat(x) - overline(x)$. Then, $ gradient g_i (overline(x))^T hat(d) <= g_i (hat(x)) - g_i (overline(x)) < 0 $ for $i in I(overline(x))$, and moreover, $gradient h_j (overline(x))^T hat(d) = 0$. Define for $delta > 0$, $d(delta) := d + delta hat(d)$.  Then, $d(delta) in F(overline(x))$ for all $delta > 0$ (CHECK THIS). Let $delta -> 0$; then $d(delta) -> d in overline(F(overline(x)))$.
]


== Lagrangian Duality


Consider as before the standard NLP $ min f(x) "s.t." #stack(spacing: 1em, $g_i (x) <= 0 forall i = 1, dots, m,$, $h_j (x) = 0 forall j = 1, dots, p$), wide (P) $ with $f, g_i, h_j : RR^n -> RR$ with $X = {x | g(x) <= 0, h(x) = 0} != nothing$ (we don't make smoothness assumptions just yet). The _Lagrangian_ of the problem $(P)$ is given by $ L : RR^n times RR^m times RR^p -> RR, wide L(x, lambda, mu) = f(x) + lambda^T g(x) + mu^T h(x). $

=== The Dual Problem

Observe that $ sup_(lambda, mu) L(x, lambda, mu) = cases(f(x) & "if" x in X, infinity & "else"). $ Then, the problem $(P)$ is really equivalent to the problem $ min_(x in RR^n) sup_(lambda in RR^m_+,\ mu in RR^p) L(x, lambda, mu) = inf_x p(x), $ where we call $p(x)$ the _primal objective_.
A question of interest is when can we switch the order of the min and the sup?

#definition("Lagrangian Dual")[
  The _(Lagrangian) dual_ of $(P)$ is given by $ max d(lambda, mu) "s.t." lambda >= 0 wide (D) $ where $ d: RR^m times RR^p -> RR union {infinity}, wide d(lambda, mu) := inf_x L(x, lambda, mu). $ The latter is called the _dual objective_.
]

#example("LP")[
  Consider the stanard linear program (LP) $ min_x c^T x | A x= b, x >= 0, $ with $A in RR^(m times n), b in RR^m, c in RR^n$. The Lagrangian for this problem reads $ L(x, lambda, mu) & = c^T x - lambda^T x + mu^T (b - A x) \
                   & = (c - lambda - A^T mu)^T x + b^T mu. $ We see that $gradient_x L(x, lambda, mu) = c - lambda - A^T mu$. Note that the function $x |-> L(x, lambda, mu)$ an affine function, which takes its minimum iff $c - lambda - A^T mu = 0$, in which case $ inf_(x in RR^n) L(x, lambda, mu) = b^T mu. $ Otherwise, $ inf_(x in RR^n) L(x, lambda, mu) = - infinity. $ Thus, the dual objective in this case just reads $ d(lambda, mu) = cases(
    b^T mu wide & c = lambda A^T mu,
    - infinity & "else"
  ). $ Maximizing this function is thusly equivalent to $ max_x b^T mu "s.t." A^T mu + lambda = c, lambda >= 0. $ We can incorporate $lambda$ directly into the first constraint, and get the one-variable problem $ max_mu b^T mu "s.t." A^T mu <= c. $
]

=== Weak snd Strong Duality

#theorem("Weak Duality")[
  Let $hat(x)$ be feasible for $(P)$ and $(hat(lambda), hat(mu))$ be feasible for $(D)$. Then, $p(hat(x)) >= d(hat(lambda), hat(mu))$.
]

#proof[
  We have $ p(hat(x)) & = f(hat(x)) \
            & >= f(hat(x)) + underbrace(hat(lambda)^T g(hat(x)), <= 0) + underbrace(mu^T h(hat(x)), = 0) \
            & = L(hat(x), hat(lambda), hat(mu)) >= inf_(x in RR^n) L(x, hat(lambda), hat(mu)) = d(hat(lambda), hat(mu)). $
]

From weak duality, $overline(p) := inf_(x in X) p(x) >= sup_(lambda >= 0) d(lambda, mu) =: overline(d)$, we have the _duality gap_ $overline(p) - overline(d) >= 0$ (taking by convetion $+infinity - infinity := + infinity$.)

#example("Nonzero Duality Gap")[
  Consider $ min f(x) := cases(x^2 - 2 x wide &x >= 0, x & "else"), $ such that $g(x) := - x <= 0$. The Lagrangian reads $ L(x, lambda) := cases(
    x^2 - (2 + lambda) x wide & x >= 0,
    (1 - lambda) x & "else"
  ). $ A short computation gives $ d(lambda) = cases(
    - (2 + lambda)^2/4 wide & lambda >= 1,
    -infinity & "else"
  ), $ and thus $overline(d) = d(1) = -9/4$. On the other hand, the optimal value of the primal is $f(1) = -1$.
]

#theorem("Strong Duality")[
  Consider the convex NLP $ min f(x) "s.t." g_i (x) <= 0 forall_(i=1)^m, h_j (x) = 0 forall_(j=1)^p, $ with $f, g_i : R^n -> RR$ convex and $h_j : RR^n -> RR$ affine. If Slater CQ holds, then $overline(p) = overline(d)$.
]
#proof[
  This one's TOO hard :-(.
]

=== The Saddle Point Theorem

#definition("Saddle Point of a Lagrangian")[
  Let $L : RR^n times RR^m times RR^p -> RR$ be the Lagrangian of $(P)$. Then, $(overline(x), overline(lambda), overline(mu))$ is called a _saddle-point_ of $L$ if the following inequalities hold: $ L(overline(x), lambda, mu) <= L(overline(x), overline(lambda), overline(mu)) <= L(x, overline(lambda), overline(mu)), quad forall (x, lambda, mu) in RR^n times RR^m_+ times RR^p. $
]

#theorem("Saddle Point Theorem")[
  Let $(overline(x), overline(lambda), overline(mu)) in RR^n times RR^m_+ times RR^p$. TFAE:
  1. $(overline(x), overline(lambda), overline(mu))$ a saddle point of $L$ for $(P)$;
  2. $overline(x)$ solves $(P)$, $(overline(lambda), overline(mu))$ solves $(D)$ and $f(overline(x)) = d(overline(lambda), overline(mu))$, i.e. the duality gap is zero.
]

#proof[
  (1. $=>$ 2.) We see that $ L(overline(x), overline(lambda), overline(mu)) = underbrace(inf_(x in RR^n) L(x, overline(lambda), overline(mu)), = d(overline(lambda), overline(mu))) &<= sup_(lambda in RR^m_+ \ mu in RR^p) inf_(x in RR^n) L(x, overline(lambda), overline(mu)) \
  &<= inf_(x in RR^n) sup_(lambda in RR^m_+ \ mu in RR^p) L(x, lambda, mu) \
  &<= underbrace(sup_(lambda in RR^m_+ \ mu in RR^p) L(overline(x), lambda, mu), = p(overline(x))) = L(overline(x), overline(lambda), overline(mu)), $ using the saddle point properties in the first, last equalities. Thus equality must hold throughout, so in particular, $d(overline(lambda), overline(mu)) = p(overline(x))$; moreover $p(overline(x)) < infinity$ by the same chain of equalities so $overline(x)$ feasible for $(P)$. By definition ($overline(lambda) >= 0$) too, $(overline(lambda), overline(mu))$ feasible for $(D)$. Moreover, by weak duality, $overline(x)$ solves $(P)$ and $(overline(lambda), overline(mu))$ solves $(D)$.

  (2. $=>$ 1.) Observe $ underbrace(L(overline(x), overline(lambda), overline(mu)), (a)) & <= f(overline(x)) ( = d(overline(lambda), overline(mu))) \
  & = p(overline(x)) \
  & = overbrace(sup_(lambda >= 0, mu) L(overline(x), lambda, mu), (c)) \
  & = d(overline(lambda), overline(mu)) = underbrace(inf_(x) L(x, overline(lambda), overline(mu)), (b)) <= overbrace(L(overline(x), overline(lambda), overline(mu)), (d)). $ The inequalities $(b) <= (d) = (a) <= (c)$ gives the desired result.
]

== Penalty Methods

Consider $ min f(x) "s.t." x in X wide (1). $ Replace $(1)$ with a sequence of unconstrained problems $ min f(x) + alpha_k r(x), wide forall k in NN, $ where $alpha_k > 0$ a _penalty parameter_, $r(x) : RR^n -> RR$ such that $r(x) >= 0$ and $r(x) = 0 <=> x in X$. The sum $f + alpha_k r$ is called the _penalty function_.

=== The Quadratic Penalty Function

Consider a special instance of $(1)$ given by $ min f(x) "s.t." h_j (x) = 0 forall_(j=1)^p, $ for $f, h_j : RR^n -> RR$ at least continuous. The _quadratic penalty function_ for the problem is given by $ P_alpha (x) = f(x) + alpha/2 norm(h(x))^2. $

This readily gives rise to the (abstract) algorithm @tab:quadpenaltymeth.

#figure(
  kind: "Code",
  supplement: "Algorithm",
  table(
    columns: 1,
    rows: 2,
    align: left,
    [#align(center, "Quadratic Penalty Method")],
    [
      S0. Choose $alpha_0 > 0$, set $k = 0$\
      S1. Determine $x^k in RR^n$ as a solution of $min P_(alpha_k) (x)$\
      S2. If $h(x^k) = 0$, STOP \
      S3. Choose $alpha_(k + 1) > alpha_k$, increment $k$ and go to S.
    ],
  ),
)<tab:quadpenaltymeth>

#theorem[
  Suppose $f, h$ continuous such that the feasible set $X eq.not nothing$. Let $alpha_k arrow.t infinity$ and ${x^k}$ generated by @tab:quadpenaltymeth. Then, the following hold:
  1. ${P_(alpha_k) (x^k)}$ is monotonically increasing;
  2. ${norm(h(x^k))}$ is monotonically decreasing;
  3. ${f(x^k)}$ is monotonically increasing;
  4. $lim_k h(x^k) = 0$;
  5. Every cluster point of ${x^k}$ is a solution of the constrained optimization problem.
]

#proof[
  1. $P_(alpha_k) (x^k) <= P_(alpha_(k)) (x^(k+1))$ since $x^k$ minimizes $P_(alpha_k)$, and $P_(alpha_(k)) (x^(k+1))<= P_(alpha_(k+1)) (x^(k+1))$ since $alpha_(k + 1) > alpha_k$.
  2. We have similarly that $P_(alpha_k) (x^k) <= P_(alpha_(k)) (x^(k+1))$ and $P_(alpha_(k+1)) (x^(k+1)) <= P_(alpha_(k+1)) (x^k)$, so adding these gives us $ P_(alpha_k) (x^k) + P_(alpha_(k+1)) (x^(k+1)) <= P_(alpha_k) (x^(k+1)) + P_(alpha_(k+1)) (x^k). $ Both sides of this inequality contain $f(x^k) + f(x^(k+1))$; cancelling these and multiplying by 2, we get  $ alpha_(k) norm(h(x^k))^2 + alpha_(k+1) norm(h(x^(k+1)))^2 <= alpha_(k) norm(h(x^(k+1)))^2 + alpha_(k+1) norm(h(x^(k)))^2. $ Rearraning, we get $ (alpha_k - alpha_(k+1)) (norm(h(x^k))^2 - norm(h(x^(k+1)))^2) <= 0. $ Since $alpha_k - alpha_(k+1) < 0$, we get the result.
  3. From $P_(alpha_k) (x^k) <= P_(alpha_(k)) (x^(k+1))$, we get $ f(x^k) + alpha_k/2 norm(h(x^k))^2 <= f(x^(k+1)) + alpha_(k)/2 norm(h(x^(k+1)))^2. $ Using $norm(h(x^(k+1)))^2 <= norm(h(x^k))^2$ (from 2.) and cancelling gives $f(x^k) <= f(x^(k+1))$, as needed.
  4. Observe that $P_(alpha_k) (x^k) = inf_(x in RR^n) P_(alpha_k) (x) <= inf_(x in X) P_(alpha_k) (x)$
  #quote(
    block: true,
    attribution: "Tim H",
    "You can't get worse from picking from a bigger set; that's what the Quebec government doesn't understand.",
  )
  But if $x in X$, $P_(alpha_k) (x) = f(x)$ so further $P_(alpha_k) (x^k) <= inf_X f(x) < infinity$ (since $X eq.not nothing$). Thus, we have that $ f(x^0) + alpha_k/2 norm(h(x^k))^2 <= P_(alpha_k) (x^k) < infinity. $ Letting $k -> infinity$, $alpha_k -> infinity$; but the whole sequence must be bounded, and thus $norm(h(x^k))^2$ must go to zero (so in particular $h(x^k) -> 0$).
  5. Let $overline(x)$ a cluster point of $x^k$, supposing it converges along the whole sequence wlog. Thus, $h(overline(x)) = 0$ by continuity and 4., so in particular $overline(x) in X$. Moreover, $f(overline(x)) = lim_(k) f(x^k) <= lim_(k) P_(alpha_k) (x^k)<= inf_(X) f$ (using the bound we used in 4.). Thus, $overline(x)$ indeed a solution of the corresponding optimization problem.
]

#remark[
  1. We used often the fact $f(x^k) <= P_(alpha_k) (x^k) <= inf_X f$; in particular if $x^k in X$, then $x^k$ solves the problem (hence why our stopping criterion is appropriate).
  2. @tab:quadpenaltymeth, and the corresponding theorem, also apply to the more general problem $min f$ with both $h(x) = 0$ _and_ $g(x) <= 0$ (with the components of $h, g$ continuous) because this problem is equivalent to the equality-constraint problem $ min f(x) "s.t." quad h_j (x) = 0, max{g_i (x), 0} = 0. $ The corresponding (quadratic) penalty function would then be $ P_alpha (x) = f(x) + alpha/2 norm(h(x))^2 + alpha/2 sum_(i=1)^p max{g_i (x), 0}^2. $ Then, $P_alpha$ remains continuous. In fact, if $f, g_i, h_j in C^1$, so is $P_alpha$; the only stick point is in whether the function $tau mapsto max{tau, 0}^2$ is $C^1$ (indeed, without the square this is not true).
]

Our goal now is, assuming $f, h_j in C^1$ and given ${x^k}$ generated by @tab:quadpenaltymeth, to find ${mu^k}$ such that ${(x^k, mu^k)}$ converges to a KKT point.

Observe that $x^k in "argmin"_X P_alpha => 0 = gradient P_(alpha_k) (x^k) = gradient f(x^k) + sum_(j=1)^p alpha_j h_j (x^k) gradient h_j (x^k)$. Put $mu_j^k := alpha_j h_j (x^k)$; these needn't be a KKT point, since we don't know if $x^k$ feasible hence we don't know if $h_j (x^k) = 0$. But it seems like $mu_j^k$ seems like a good choice.

#theorem[
  With the hypotheses of the previous remarks, let ${x^k}$ be generated by @tab:quadpenaltymeth and assume $x^k -> overline(x)$, and that LICQ holds at $overline(x)$. For $mu^k_j = alpha_j h_j (x^k)$, we have $mu^k$ converges to some $overline(mu)$ and $overline(mu) in M(overline(x))$.
]

#proof[
  Define $A_k = h'(x^k) in RR^(p times n)$. We see that $A_k -> h'(overline(x)) =: overline(A)$ by continuity. By LICQ, $overline(A) dot overline(A)^T in RR^(p times p)$ is invertible. Thus, $A_k dot A_k^T$ is also invertible for $k$ sufficiently large, so $(A_k dot A_k^T)^(-1) -> (overline(A) dot overline(A)^T)^(-1)$ as well. Thus, $ gradient f(x^k) + sum_(j=1)^p mu_j^k gradient h_j (x^k) = 0 <=> A_k^T mu_k = - gradient f(x^k), $ and thus $ mu_k = - (A_k A_k^T)^(-1) A_k gradient f(x^k) -> - (overline(A) overline(A)^T)^(-1) overline(A) gradient f(overline(x)) =: overline(mu). $ This completes the proof, since $overline(x)$ feasible as well.
]

=== Exact Penalty Functions

Consider a penalty function $P_alpha^r = f + alpha r, alpha > 0$ where $r >= 0$ and $r(x) = 0 <=> x in X$.

#definition("Exactness")[
  The penalty function $P_alpha^r$ is called _exact_ at a local minimum if there exists an $overline(alpha) > 0$ such that $overline(x)$ also a local minimum of $P_alpha^r$ for any $alpha > overline(alpha)$.
]

Consider now the standard NLP $ min f(x) "s.t." #stack(spacing: 1em, $g_i (x) <= 0 forall i = 1, dots, m,$, $h_j (x) = 0 forall j = 1, dots, p$). $ A whole class of penalty functions in the above form for the above problem is defined via $ r_q (x) = norm((max(g(x), 0), h(x)))_q, $ where for $y in RR^m$, $max(y, 0) = [max {y_i, 0}]_(i=1)^m$, i.e. component-wise maxima, $norm(dot)_q$ the usual $q$-norm, and we're writing $(x, y) in RR^(m times p)$ for shorthand. We focus on $q = 1$, which gives rise to the penalty function $ P_alpha^1 (x) = f(x) + alpha sum_(j=1)^p |h_j (x)| + alpha sum_(i=1)^m max{g_i (x), 0}. $

#theorem[
  Let $(overline(x), overline(lambda), overline(mu))$ be a KKT point for the typical convex NLP, where $f, g_i$ convex and $h_j$ affine. Then, $overline(x) in "argmin"_X P_alpha^1(x)$ for any $alpha >= norm((overline(lambda), overline(mu)))_infinity$. In particular, $P_alpha^1$ is exact if a constraint qualification holds at $overline(x)$.
  #text(fill: red, "might need to add some constraint")
]

#proof[
  By the KKT theorem for convex problems, $overline(x)$ is a (global) minimizer. Therefore, by the saddle-point theorem, $overline(x)$ is a global minimizer of $L(dot, overline(lambda), overline(mu))$. Thus, for all $x in RR^n, alpha >= norm((overline(lambda), overline(mu)))_infinity$, $ P_alpha^1 (overline(x)) &= f(overline(x)) + alpha underbrace(sum_(j) abs(h_j (overline(x))), = 0) + alpha sum_(j) underbrace(max(g_i (x), 0), = 0) \
  &= f(overline(x)) \
  &= f(overline(x)) + overline(lambda)^T g(overline(x)) + overline(mu)^T h(overline(x)) \
  &= L(overline(x), overline(lambda), overline(mu)) \
  & <= L(x, overline(lambda), overline(mu)) \
  &= f(x) + sum_(i=1)^m overline(lambda)_i g_i (x) + sum_(j=1)^p overline(mu)_j h_j (x) \
  & <= f(x) + sum_(i=1)^m overline(lambda)_i max(g_i (x), 0) + sum_(j=1)^p abs(overline(mu)_j) abs(h_j (x)) \
  & <= f(x) + norm((overline(lambda), overline(mu)))_infinity (sum_(i=1)^m max(g_i (x), 0) + sum_(j=1)^p abs(h_j (x))) \
  & <= f(x) + alpha (sum_(i=1)^m max(g_i (x), 0) + sum_(j=1)^p abs(h_j (x))) \
  &= P_alpha^1 (x). $
]

#theorem[
  Let $overline(x)$ be an isolated minimum such that MFCQ holds at $overline(x)$. Then for all $q in [1, infinity)$, there exists an $alpha_q > 0$ such that for any $alpha >= alpha_q$, then the point $overline(x)$ is a local minimimum of $P_alpha^q$, i.e. $P_alpha^q$ is exact at $overline(x)$.
]

$theta$ convex and increasing, $g : RR^n -> RR$ convex implies $theta(g)$ convex.

$g(lambda x + (1 - lambda) y) <= lambda g(x) + (1 - lambda) g(y)$. $theta$ increasing thus $ theta(g(lambda x + (1 - lambda) y)) <= theta(lambda g(x) + (1 - lambda) g(y)), $ then we just apply convexity to $lambda dot g(x), (1 - lambda) dot g(y)$.

== SQP Methods

=== The Lagrange-Newton Method

Consider $ min f(x) "s.t." h_j (x) = 0, forall_(j=1)^p, $ with $f, h_j : RR^n -> RR$ in $C^2$. Define $ Phi : RR^n times RR^p -> RR^n times RR^p, wide Phi(x, mu) = vec(gradient_x L(x, mu), h(x)), $ where $L$ the Lagrangian of the problem. Then, $(x, mu)$ a KKT point iff $Phi(x, mu) = 0$. So, we can just throw Newton methods at $Phi$ to find KKT points (note that we couldn't work with inequality constraints, since this would result in $max$'s showing up in $Phi$, which aren't differentiable). This leads to the following algorithm, which is just Newton's specialized to $Phi$.

#figure(
  kind: "Code",
  supplement: "Algorithm",
  table(
    columns: 1,
    rows: 2,
    align: left,
    [#align(center, "Lagrange-Newton")],
    [
      S0. Choose $(x^0, mu^0) in RR^n times RR^p$, set $k := 0$ \
      S1. If $Phi(x^k, mu^k) = 0$, STOP\
      S2. Determine $vec(Delta x^k, Delta mu^k)$ as a solution $ Phi'(x^k, mu^k) (Delta x, Delta mu) = - Phi(x^k, mu^k) $
      S3. Set $(x^(k+1), mu^(k+1)) = (x^k, mu^k) + (Delta x^k, Delta mu^k)$, increment $k$ and go to S1.
    ],
  ),
)<tab:lagrangenewton>

Recall that the crucial condition for the convergence of the Newton's algorithm we discussed was invertibility of the Jacobian at the critical point.

#theorem[Let $(overline(x), overline(mu)) in RR^n times RR^p$ be a KKT point, such that
  1. LICQ holds ($gradient h_j (overline(x))$ are linearly independent), and
  2. we have $d^T gradient_(x x)^2 L(overline(x), overline(mu)) d > 0$ for all $d eq.not 0$ such that $gradient h_j (overline(x))^T d =0, j in J$
  Then, $Phi'(overline(x), overline(mu))$ is invertible.
]

#proof[
  Observe that $ Phi'(x, mu) = mat(
    gradient_(x x)^2 L(x, mu), h'(x)^T;
    h'(x), 0
  ). $ Let $(q, r)$ s.t. $Phi'(overline(x), overline(mu)) vec(q, r) = 0$. Then, $ gradient^2_(x x) L(overline(x), overline(mu)) q + h'(overline(x))^T r = 0, \
  h'(overline(x))q = 0. $ Thus, $ 0 = q^T gradient_(x x) L(overline(x), overline(mu)) q + underbrace(q^T h'(overline(x))^T, = (h'(overline(x) q))^T = 0) r = q^T gradient_(x x) L(overline(x), overline(mu)) q. $ Moreover, we see that $gradient h_j (overline(x))^T q = 0$ for all $j in J$. Thus, by our second assumption, it must be that, if $q$ nonzero, $q^T gradient_(x x) L(overline(x), overline(mu)) q > 0$; this isn't the case thus it must be $q = 0$. This implies $h'(overline(x))^T r = 0$, but by MFCQ, $h'(overline(x))^T$ has linearly independent columns (the gradients of $h_j$), thus a trivial kernel so $r = 0$. So, $vec(q, r) = 0$, and thus $Phi'(overline(x), overline(mu))$ has trivial kernel so invertible.
]

#remark[
  As in the proof above, we see that the update in S2. is equivalent to the equation (putting $H_k := gradient_(x x)^2 L(x^k, mu^k)$) $ H_k Delta x + h'(x^k)^T Delta mu & = - gradient_x L(x^k, mu^k), \
                 h'(x^k)^T Delta x & = - h(x^k) $ In particular, if we put $mu^+ := mu^k + Delta mu$, then since $gradient_x L(x, mu) = gradient f(x) + h'(x)^T mu$, equivalently $ H_k Delta x + h'(x^k)^T mu^+ & = - gradient f(x^k), \
  gradient h_j (x^k)^T Delta x & = - h_j (x^k), quad j in J. $

  Also, consider the following (quadratic objective, affine constraint) problem:
  $
    wide min_(Delta x) 1/2 (Delta x)^T H_k Delta x + gradient f(x^k)^T Delta x quad "s.t." quad gradient h_j (x^k)^T Delta x + h_j (x^k) = 0, j in J.
  $
  The KKT conditions in this case read,
  $ H_k Delta x + gradient f(x^k) + h'(x^k)^T mu = 0, \
  gradient h_j (x^k)^T Delta x + h_j (x^k) = 0, j in J, $ which are precisely the conditions we wrote out above, with $mu$ (here) equal to $mu^+$ (above).
]

We want to consider the general NLPs, i.e. with inequality constraints; we'll assume our objective and constraints are $C^2$;
$
  (dagger) quad min f(x) "s.t." g_i (x) <= 0, i in I, quad h_j (x) = 0, j in J.
$
Given $(x^k, lambda^k, mu^k)$, consider $ min 1/2 (Delta x)^T H_k Delta x + gradient f(x^k)^T Delta x quad "s.t." quad gradient g_i (x^k)^T Delta x + g_i (x^k) <= 0, i in I, quad gradient h_j (x^k)^T Delta x + h_j (x^k) = 0, j in J. $ This leads to the following:

#figure(
  kind: "Code",
  supplement: "Algorithm",
  table(
    columns: 1,
    rows: 2,
    align: left,
    [#align(center, "Local SQP Method")],
    [
      S0. Choose $(x^0,lambda^0, mu^0) in RR^n times RR^m times RR^p$, set $k := 0$, and choose $H_0 in RR^(n times n)$ symmetric \
      S1. If $(x^k, lambda^k, mu^k)$ a KKT point of the underlying NLP $(dagger)$, STOP\
      S2. Determine $(x^(k+1), lambda^(k+1), mu^(k+1))$ of the quadratic program $ min_(x in RR^n) 1/2 (x - x^k)^T H_k (x - x^k) + gradient f(x^k)^T (x - x^k),\
      "s.t."\ gradient g_i (x^k)^T (x - x^k) + g_i (x^k) <= 0, i in I, gradient h_j (x^k)^T (x - x^k) + h_j (x^k) = 0, j in J. $
      S3. Choose $H_(k + 1) in RR^(n times n)$ symmetric, increment $k$, and go to S1.
    ],
  ),
)<tab:sqplocal>

#remark[
  Instead of the exact choice $H_k = gradient_(x x)^2 L(x^k, lambda^k, mu^k)$, as in our derivation, one can update $H_k$ using some (modified) Newton techniques.
]

#theorem([Convergence of @tab:sqplocal])[
  Let $(overline(x), overline(lambda), overline(mu))$ be a KKT point of $(dagger)$ such that\
  i. (strict complementarity) $g_i (overline(x)) = 0 => overline(lambda)_i > 0$, for all $i in I$,\
  ii. (LICQ) $gradient g_i (overline(x)), i in I(overline(x)), gradient h_j (overline(x)), j in J$ are linearly independent, and\
  iii. (2nd order sufficient conditions) $d^T gradient_(x x)^2 L(overline(x), overline(lambda), overline(mu)) d > 0, forall d in cal(L)_X (overline(x)) \\{0}$.\
  Then, there exists $epsilon > 0$ such that for all $(x^0, lambda^0, mu^0) in B_epsilon (overline(x), overline(lambda), overline(mu))$ such that the following hold for any sequence ${x^k, lambda^k, mu^k}$ generated by @tab:sqplocal with update $H_k := gradient_(x x)^2 L(x^k, lambda^k, mu^k)$ and such that in S2., one choose the KKT point closest to the previous iterate $(x^k, lambda^k, mu^k)$:
  1. ${(x^k, lambda^k, mu^k)}$ well-defined and converges to $(overline(x), overline(lambda), overline(mu))$ superlinearly, and
  2. if $gradient^2 f, gradient^2 g_i, gradient^2 h_j$ are locally Lipschitz, then the rate is quadratic.
]
The natural next generalization is globalizing this method, as we globalized Newton's method.

=== A Globalized SQP Method

Recall that globalization of the Newton's method involving introducing a step-size based on the Armijo rule. For SQP, we will introduce a step-size based on the (exact) $ell_1$-penalty function $ P_alpha^1 (x) = f(x) + alpha sum_(j=1)^p |h_j (x)| + alpha sum_(i=1)^m max{g_i (x), 0}. $
Note $P_alpha^1$ is not generally differentiable, hence we use the directional derivative to detect descent directions.

#theorem("Chain Rule for Directional Derivatives")[
  Let $H : RR^n -> RR^m$, $G: RR^m -> RR^p$, and set $F := G compose H$. Assume that for $x in RR^m$,
  1. $H$ is directionally differentiable at $x$,
  2. $G$ is directionally differentiable at $H(x)$, and
  3. $G$ is locally Lipschitz at $H(x)$.
  Then, $F$ is directionally differentiable at $x$, and $ F'(x; d) = G'(H(x); H'(x; d)), $ for all $d in RR^n$.
]

#proof[
  Let $d in RR^n$ and let $L > 0$ be the (local) Lipschitz constant of $G$ around $H(x)$. For $t > 0$ sufficiently small, we have $ norm((F(x + t d) - cancel(F(x)))/t - (G(H(x) + t H'(x; d)) - cancel(G(H(x))))/(t)) \
  = norm((G(H(x + t d)) - G(H(x) + t H'(x; d)))/t) \
  <= L norm((H(x + t d) - H(x))/t - H'(x; d)) -> 0. $ Since the term on the RHS of the first line converges to $G'(H(x); H'(x; d))$, we're done.\
]

#corollary([Directional derivative of $ell_1$-penalty])[
  For any $alpha > 0$, the $ell_1$-penalty function is directionally differentiable, with $ (P^1_alpha)'(x; d) &= gradient f(x)^T d \
  &wide + alpha sum_(j : h_j (x) > 0) gradient h_j (x)^T d - alpha sum_(j : h_j (x) < 0) gradient h_j (x)^T d + alpha sum_(j: h_j (x) = 0) abs(gradient h_j (x)^T d) \
  & wide + alpha sum_(i : g_i (x) > 0) gradient g_i (x)^T d + alpha sum_(i : g_i (x) = 0) max{gradient g_i (x)^T d, 0}. $
]
