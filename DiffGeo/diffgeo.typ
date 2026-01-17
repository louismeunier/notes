// ! external
#import "../typst/notes.typ": *
// #import "../typst/shortcuts.typ": *

#import "@preview/cetz:0.2.2"

// ! configuration
#show: doc => conf(
  course_code: "MATH458",
  course_title: "Differential Geometry",
  subtitle: "",
  semester: "Winter 2026",
  professor: "Prof. Jean-Pierre Mutanguha",
  // cute: "../analysis 3/page.png",
  doc,
)

#import "@preview/commute:0.2.0": arr, commutative-diagram, node

#set align(left)
#let boxit(arg) = box(stroke: 0.75pt, outset: 8pt, arg)

#pagebreak()

= Some Review
We will work in $RR^n$, usually with $n = 2, 3$. For vectors $v = (v_1, dots, v_n), w = (w_1, dots, w_n) in RR^n$, we denote the dot product $ v dot w = sum_(i =1)^n v_i w_i. $ More generally, an _inner product_ on $RR^n$ is any function $b : RR^n times RR^n -> RR$ that is symmetric, bilinear and positive definite. For instance, if $T : RR^n -> RR^n$ is linear and invertible $b_T (v, w) := T(v) dot T(w)$ a new inner product. In fact, it turns out every inner product on $RR^n$ is of this form; this implies that every inner product is just a coordinate-change away from the dot product.

We will say a linear transformation $T : RR^n -> RR^n$ is _orthogonal_ if it is inner product preserving, i.e. $T(v) dot T(w) = v dot w$ for every $v, w in RR^n$.

#exercise[Show that $T$ is inner product preserving iff it is norm preserving ($norm(T v) = norm(v)$) iff it is distance preserving ($norm(T(v - w)) = norm(v - w)$).]

#exercise[
  Show that if $T$ orthogonal, it is a bijection with determinant $plus.minus 1$.
]

We say $T : RR^n -> RR^n$, linear, is _orientation preserving_ if $det(T) > 0$.

#definition("Rigid Motion")[
  A function $M : RR^n -> RR^n$ is called a _rigid motion_ if there exists an $a in RR^n$ and $T : RR^n -> RR^n$ orthogonal and orientation preserving such that $ M(v) = a + T v, quad forall v in RR^n. $
]

We view the space $EE^n$ as $RR^n$ equipped with the Euclidean distance, which we'll denote $d_EE$ or $d$ if no confusion arises, _up to rigid motions_. In practice, this means working in $EE^n$ has no distinguished origin point or coordinate axes. However, also in practice, we will make the identification $EE^n tilde.eq RR^n$ by picking an origin and axes, as we will see.

However, working in $EE^n$, abstractly, still preserves orientation and distance, since these are both preserved under rigid motions.

For $r > 0$ and $rho in EE^n$, we write $DD_r (rho)$ for the open unit disk, and $DD^n := DD_1 (0) subset RR^n$.

#theorem("Heine-Borel")[
  $C subset EE^n$ compact iff closed and bounded.
]

#exercise[Let $r' > r > 0$ and $rho in EE^n$. Let $f : DD_(r') (rho) -> EE^n$ be continuous. Show that $f|_(DD_r (rho))$ uniformly continuous.]

We'll denote the derivative of a function $f : cal(U) subset RR^n -> RR^m$ at a point $a$ by $D_a f : RR^n -> RR^m$, which is represented by the Jacobian $m times n$ matrix $J(f)_a = ((partial f)/(partial x_1)|_a, dots, (partial f)/(partial x_n)|_a)$.

#definition[We will say $f : cal(U) -> RR^m$ is $C^k$ on $cal(U)$ if all the $k$th order partial derivatives of all of the component functions of $f$ are continuous. We say $f$ in $C^infinity$ if it is in $C^k$ for every $k >= 1$. We write $C^0$ for the space of continuous functions.]

#remark[
  $C^(k + 1) => C^k$
]

= Curves

#definition("Parametrized curve/path")[
  A _parametrized curve/path_ in $EE^n$ is a continuous function $ gamma : I -> EE^n, $ where $I subset RR$ an interval. We say $gamma$ _compact_ if $I$ is compact.
]

#definition([(Regular) $C^k$ parametrized curve])[
  Fix coordinates in $EE^n$. Then, a (regular) $C^k$ parametrized curve is a parametrized curve in which $gamma in C^k (I)$ (and for which $(dif gamma )/(dif t) (t) eq.not 0 forall t in I$).
]

#exercise[Regularity and differentiability is preserved under rigid motion, i.e. if $gamma$ a (regular) $C^k$ parametrized curve and $M$ a rigid motion on $RR^n$, then $tilde(gamma) := M compose gamma$ also (regular) $C^k$.]

#definition[
  Given a curve $gamma$, we define
  - the _velocity_, $nu = (dif gamma)/(dif t) : I -> RR^n$
  - the _acceleration,_ $alpha = (dif^2 gamma)/(dif t^2) : I -> RR^n$
  - the _speed_, $sigma = norm(nu) = norm((dif gamma)/(dif t)) : I -> RR$,
  whenever each of these quantities all exist.
]

#exercise[
  Speed is preserved by rigid motions.
]

#definition[
  Let $gamma$ be a $C^1$ curve. The _arclength_ of $gamma$ is defined by $ ell(gamma) := integral_I sigma(t) dif t. $
]

#example[
  Let $p, q in EE^2$ with $d_EE (p, q) = 3$. Suppose $gamma : [a, b] -> EE^2$ is a $C^1$-path with $gamma(a) = p, gamma(b) = q$. Prove that $ell(gamma) >= 3$, with equality holding iff $gamma(I)$ is a line segment, with no change of direction.

  _(Hint: pick coordinates so that $p = 0$ and the $x$-axis passes through $q$ to simplify computations.)_
  // TODO Add picture
]

#definition("Curve")[
  A set $cal(C) subset EE^n$ is a _curve_ if it is connected, and for every $p in cal(C)$, there exists a compact neighborhood $N_p$ of $p$ and a one-to-one, compact, parametrized curve $gamma : I -> EE^n$ such that $gamma(I) = cal(C) sect N_p$.

  A curve is called $C^k$ if there exists $gamma$ as in the definition which are now required to be $C^k$.

  I.e., a general curve is everywhere locally a compact parametrized curve.
  // TODO Add picture
]

#remark[
  One can relax the one-to-one/compact conditions to obtain either a global compact parametrization (which may not be one-to-one) or a parametrized curve with $I = RR$ with $gamma(I) = cal(C)$ and $gamma$ is periodic.
]

== Classification Theorem for Curves
#theorem("Classification Theorem for Curves")[
  Let $cal(C) subset EE^n$ a connected subset. Then, $cal(C)$ is a (regular) [$C^k$] curve iff it is the image of a (regular) [$C^k$] path $gamma : I -> EE^n$ satisfying either
  1. $gamma$ is one-to-one with [$C^k$] continuous inverse
  2. $I = RR$ and $gamma$ is periodic, and the restriction of $gamma$ to any interval $I'$ shorter than the period is one-to-one.

  If $gamma$ satisfies 1. or 2., we'll call it a _global parametrization_ of $cal(C)$.
]

#remark[
  This means we just need _one_ path to describe a curve; but it may, in 2., loop back onto itself.
]

== Reparametrizations of Curves

#definition("Reparametrization")[
  Let $I, tilde(I) subset RR$ be intervals and $t : tilde(I) -> I$ a continuous bijection (we'll call it a _change of parameters_). Then, the _reparametrization_ of $gamma : I -> EE^n$ using $t$ is the composition $tilde(gamma) := gamma compose t : tilde(I) -> EE^n$.

  Suppose $gamma$ a regular $C^k$ path and $t : tilde(I) -> I$ a $C^k$ bijection with a $C^k$ inverse. Then $tilde(gamma)$ is a $C^k$-reparametrization of $gamma$.

  We say $t$ is _orientation-preserving (-reversing)_ if it is monotone increasing (decreasing).
]

#remark[
  $gamma$ also a reparametrization of $tilde(gamma)$ using the inverse $s := t^(-1)$.
]

#theorem[
  Suppose $gamma : I -> RR^n$ is $C^1$ and $tilde(gamma) : tilde(I) -> RR^n$ a $C^1$ reparametrization of $gamma$. Then $ell(gamma) = ell(tilde(gamma))$, that is, arclength is invariant under change of parameters.
]

#theorem("Arc-Length Parametrization")[
  Let $gamma : I -> EE^n$ be a regular $C^k$ path. Then, there exists an orientation-preserving $C^k$ reparametrization of $gamma$, $tilde(gamma) : tilde(I) -> EE^n$, with unit speed, i.e. $norm(dot(tilde(gamma))) equiv 1$.
]

#proof[
  Pick $t_0 in I$ and definte $ s : I -> RR, quad s(t) := integral_(t_0)^t norm(dot(gamma)(r)) dif r. $
  This integral exists and is bounded, and moreover, $ (dif s)/(dif t) = norm(dot(gamma)(t)) > 0, $ since $gamma$ regular. In particular, we see that $s$ is invertible on its image $tilde(I) := s(I)$, and increasing. Then, $s : I -> tilde(I)$ an orientation-preserving, $C^1$ bijection with $s' > 0$. By the inverse function theorem, $t := s^(-1) : tilde(I) -> I$ exists and has the same desired properties. Moreover, $ t'(s) = 1/(s'(t(s))) = 1/(norm(dot(gamma)(t(s)))). $ Letting $tilde(gamma) := gamma compose t$, then we see that $ norm(dot(tilde(gamma))(s)) = norm(dot(gamma) compose t(s) dot t' (s)) = 1/(norm(dot(gamma)(t(s)))) norm(dot(gamma)(t(s))) equiv 1. $
]

With this, we can try to define the length of a general curve $cal(C)$. Suppose $cal(C) subset EE^n$ a compact curve with boundary ${p, q}$ (so satisfies the first point of the classification theorem).

1. If $cal(C)$ a line segment, then we just define $ cal(L)_1 (cal(C)) := d_(EE) (p, q). $
2. If $cal(C)$ regular, then we define $ cal(L)_2 (cal(C)) := ell(gamma), $ where $gamma$ is any parametrization of $cal(C)$.

#exercise[
  This definition of $cal(L)_2$ is well-defined, i.e. independent of choice of parametrization.
]

#definition("Rectifiable")[
  Let $cal(C)$ be a compact curve with boundary ${p, q}$. An _inscribed polygon_ in $cal(C)$ is a finite increasing sequence of points $cal(P) = {p_i}_(i=0)^N$ of points in $cal(C)$ with endpoints $p_0 = p, p_N = q$.// TODO add picture
  We write $ L(cal(P)) := sum_(i=0)^(N-1) d_EE (p_i, p_(i + 1)) $ for the length of $cal(P)$, and $ abs(cal(P)) := max_(i=0)^(N - 1) d_EE (p_i, p_(i + 1)) $ for the size of $cal(P)$.

  A curve $cal(C)$ is said to be _rectifiable_ if there exists a real number $cal(L)_3 (cal(C)) >= 0$ such that for all sequence ${cal(P)_m}$ of inscribed polygons in $cal(C)$ with $abs(cal(P)_m) ->_(m -> infinity) 0$, we have $ lim_(m -> infinity) L(cal(P)_m) = cal(L)_3 (cal(C)). $
]

#proposition[
  A unit-speed reparametrization is essentially unique, up to a shift in the domain $I$.
]

#exercise[
  Compute the arc-length parametrization of $gamma(t) := (t, t^2)$.
]

#lemma[
  Let $tilde(gamma) : tilde(I) -> RR^n$ be a regular $C^2$ path with constant speed. Then, $dot.double(tilde(gamma))$ will always be orthogonal to $dot(tilde(gamma))$.
]

#proof[
  Suppose $norm(dot(tilde(gamma))) equiv c$. We apply the product rule for dot products, to obtain $ 0 = dif/(dif t) (c^2) & = dif/(dif t) norm(dot(tilde(gamma)))^2 \
                        & = dif/(dif t) dot(tilde(gamma)) dot dot(tilde(gamma)) \
                        & = 2 dot.double(tilde(gamma)) dot (dot(tilde(gamma))), $ which gives the proof.
]

== Curvature

Let $gamma$ be a regular $C^2$-path $gamma : I -> RR^n$, there exists an orientation-preserving change of parameters $t : tilde(I) -> I$ such that $tilde(gamma) := gamma compose t : tilde(I) -> RR$ has unit speed. Let $s := t^(-1) : I -> tilde(I)$.


#definition("Curvature of a parametrized curve")[
  Define the curvature of $gamma$ as above at some time $t in I$ to be $ kappa_(gamma) : I -> RR_+, quad kappa_(gamma) (t) := norm((dot.double(tilde(gamma))compose s)(t)). $
]

#exercise[
  Show that this definition is well-defined, i.e. independent of choice of unit-speed parametrization.
]

#definition("Curvature of a curve")[
  Given a regular $C^2$ curve $cal(C) subset RR^n$, there exists (by the classification theorem) a global, regular, $C^2$ parametrization of $cal(C)$, $gamma : I -> RR^n$. For a point $p in cal(C)$, then, there exists some $t in I$ such that $gamma(t) = p$. Define, then, the curvature of $cal(C)$ at $p$, then, to be the curvature of $gamma$ at time $t$.
]

#exercise[
  Show that this definition is well-defined, i.e., independent of choice of regular global parametrization. One will need to appeal to the inverse function theorem, to show that any two such parametrizations differ by an orientation-preserving change of parameters.
  // TODO picture?
]

#exercise[
  Show that curvature of preserved by rigid motions of $RR^n$, i.e. given $M$ a rigid motion of $RR^n$ and a regular $C^2$ curve $gamma$, then $ kappa_(M compose gamma) = kappa_(gamma). $
]

#remark[
  In particular, this exercise gives the curvature is an _inherit property_ of curves in $EE^n$, not just in $RR^n$.
]

#remark[
  The definition of $kappa_gamma$ is a little bothersome in the sense that it requires computing an arc-length parametrization. The follow result shows how we can compute it regardless.
]
#proposition[
  $ kappa_(gamma) = 1/(norm(dot(gamma))^2) norm(dot.double(gamma) - (dot.double(gamma) dot dot(gamma))/(dot(gamma) dot dot(gamma)) dot(gamma)) = norm(dot.double(gamma)^perp)/norm(dot(gamma))^2, $ where we use the "$perp$" notation to indicate the orthogonal complement of $dot.double(gamma)$ with respect to $dot(gamma)$.
]

#proof[
  I'll add it later. It's just repeated application of the chain rule and product rule.

  // TODO
]

#exercise[
  Compute the curvature of parabola $cal(C) := {(x, y) | y = x^2} subset RR^2$ at any point.
]
