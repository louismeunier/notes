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
#let ddot(a) = $dot.double(#a)$
#let dddot(a) = $dot.triple(#a)$

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
#exercise[
  Any two arc-length parametrizations differ by some shifting in the domain, i.e. if $gamma_i : I_i -> RR$ are two arc-length reparametrizations of a regular path $gamma : I -> RR^n$ using a change of parameters $t_i : I_i -> I$ for $i = 1, 2$, then $h := t_2^(-1) compose t_2 : I_2 -> I_1$ is a restriction of a rigid motion of $RR$; specifically $h' equiv 1$.
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


#theorem[
  The quantity $norm(dot.double(gamma)^perp)/norm(dot(gamma))^2$ is preserved under reparametrization.
]

#remark[
  This is really more of a corollary of the previous proposition. Moreover, this implies that our definition of curvature is "correct" as a property of curves in $EE^n$ rather than just $RR^n$.
]

#definition[
  Let $gamma : I -> RR^n$ a regular path. We define
  - $T(t) := (dot(gamma)(t))/(norm(dot(gamma(t))))$, then _unit tangent_ at time $t$
  If $gamma in C^2$,
  - $N(t) := (dot.double(gamma)(t)^perp)/(norm(dot.double(gamma)(t)^perp))$, the _unit normal_ at time $t$
  - the _osculating plane_ at time is the plane in $RR^n$ that contains the point $gamma(t)$ and is spanned by ${dot(gamma)(t), dot.double(gamma)(t)}$ (supposing $kappa_gamma eq.not 0$)
  - the _osculating circle_ at time $t$ as the circle laying in the osculating plane of radius $1/(kappa(t))$ and centered at $gamma(t) + N(t)/(kappa(t))$
  - the _evolute_ of $gamma$ is the map $ t in I |-> gamma(t) + (N(t))/(kappa(t)) = "center of oscualting circle at" t $
]

#remark[$dot.double(gamma)^perp eq.not 0 <=> kappa_gamma eq.not 0 <=> {dot(gamma), dot.double(gamma)}$ a linearly independent set.]

#exercise[
  A circle of radius $r$, i.e. the curve defined implicitly by ${x^2 + y^2 = r^2}$, has curvature $1/r$.
]

This exercise shows that the osculating circle at a point on a curve has the same curvature as the curve at that point.

#exercise[
  Suppose $n = 2$ and a curve is given _explicitly_ by $y = f(x)$ where $f : RR -> RR$ sufficiently differentiable. Compute the curvature in terms of $f$ and its derivatives. Do the same if the curve is given _implicitly_ as the set of $(x, y) in RR^2$ such that $g (x, y) = 0$ where $g : RR^2 -> RR$ sufficiently differentiable.
]

Fix now $n = 2$. Let $gamma : I -> RR^2$ be a regular $C^2$ curve and fix $t in I$. Let us assume (by changing coordinates if necessary) that $gamma(t) = 0$ and the $x$-axis is parallel to $T(t)$, i.e. $T(t) = (1, 0)$. Then, we see that we may write $ (dot.double(gamma)(t)^perp)/(norm(dot(gamma)(t))^2) = "constant" times (0,1). $ Specifically, the "constant" here is what we call the _signed curvature_ of $gamma$ at time $t$, and is computed as :
#definition("Signed curvature")[Let $gamma$ as in the above, then the _signed curvature_ is the quantity
  $ kappa_(gamma)^(plus.minus) (t) = 1/(norm(dot(gamma)(t))^2) (dot.double(gamma)(t) dot dot(gamma)(t)^ast)/(norm(dot(gamma)(t))), $ where we use the notation $v^ast$ as a rotation of $v = (v_1, v_2)$ by an angle of $pi/2$, counter-clockwise, i.e. $v^ast = (-v_2, v_1)$.]

#exercise[
  $kappa_(gamma)^(plus.minus) (-t) = - kappa_(gamma)^(plus.minus)(t)$.
]

#exercise[
  Suppose $gamma(t) = (x(t), y(t))$, then show $ kappa_(gamma) = (dot(x) dot.double(y) - dot.double(x) dot(y))/((dot(x)^2 + dot(y)^2)^(3\/2)). $
]

#definition("Angle function")[
  Let $gamma : I -> RR^2$ be a regular $C^2$ curve parametrized by arc length with basepoint $s_0 in I$. We assume wlog $s_0 = 0$ (by translating if necessary) and that $dot(gamma)(0) = (1, 0)$ (by changing coordinates). We define the _angle function_ of $gamma$ by $ theta : I -> RR, quad theta(0) = 0, theta(s) := integral_(0)^s kappa_(gamma)^(plus.minus) (u) dif u. $

  In particular, $(dif theta)/(dif s) = kappa_(gamma)^(plus.minus) (s)$.
]

#remark[
  We can view $s |-> dot(gamma)(s)$ as a new $C^1$-parametrized curve, in which case its arc length is given by $ integral_(0)^s norm(dot.double(gamma)(u)) dif u = integral_(0)^s kappa_(gamma)(u) dif u. $ So, in a sense, the $theta$ angle function is the "signed arc-length" of $dot(gamma)$, i.e. it accounts for backtracking.

  Moreover, since we have an arc length parametrization, we know $dot(gamma)$ a unit vector, hence we can view the map $t |-> dot(gamma)(t)$ as a map from $I$ to the unit circle in $RR^2$. Hence, $theta$ is meant to capture the angle of this unit vector for any $t$, i.e. $dot(gamma) = (cos, sin) compose theta$.
]

#theorem("Fundamental Theorem of Plane Paths")[
  Let $s_0 in I$ be a given base point and let $kappa : I -> RR$ be a $C^(k - 2)$ function ($2 <= k <= infinity$). Then, for each $p in RR^2$ and $theta_0 in RR$, there is a unique regular $C^k$ path $gamma : I -> RR^2$, parametrized by arc-length, such that
  1. $kappa_(gamma)^(plus.minus) = kappa$,
  2. $dot(gamma)(s_0) = (cos(theta_0), sin(theta_0))$,
  3. $gamma(s_0) = p$.
]

#remark[
  The choice of $p, theta_0$ just correspond to a translation, rotation (resp.) of $RR^2$ of our curve, i.e. this means our curve is uniquely determined up to rigid motion.
]

#remark[
  This essentially says that, given the curvature of a curve in the plane, we can reconstruct the curve.
]

#proof[
  We seek to find $gamma : I -> RR^2$ and $theta : I -> RR$ such that $ (dif gamma)/(dif s) = (cos theta, sin theta), gamma(s_0) = p $ and $ (dif theta)/(dif s) = kappa, theta(s_0) = theta_0. $
  By the fundamental theorem of calculus, we know $ theta(s) = integral_(s_0)^s kappa(u) dif u + theta_0 $ is the unique solution for $theta(s)$ with the given properties, which in turn implies $ gamma(s) = (integral_(s_0)^s cos(theta(u)) dif u, integral_(s_0)^s sin(theta(u)) dif u) + p, $ which is again unique by FTC.
]

// TODO add graphic from beginning of lecture 1/22
#remark[
  This theorem essentially says that a curve is uniquely determined by its signed curvature. However, the same is not true if we just take the curvature. For instance, the curves given explicitly by $y = x^3$, $y = |x|^3$ have the same curvature everywhere but clearly do not described the same curves.
]

A more abstract manner of characterizing the angle function for a more general curve is as follows.
If $gamma : I -> RR^2$ a regular, $C^2$ curve, then the angle function $theta : I -> I'$ where $I'$ some other interval of $RR$, is such that $ T = rho compose theta, $ where $rho : I' -> RR^2$ is the standard parametrization of the circle given by $rho(theta) := (cos(theta), sin(theta))$ and $T$ the unit tangent vector viewed as a map $I -> RR^2$.

#exercise[
  Show that the signed curvature of $gamma$ is preserved under rigid motion, hence is well-defined as a property of a curve in $EE^n$. (Note that the signed curvature is the derivative of the $theta$ function, hence it suffices to prove this property for $theta$)
]

== 3-Dimensional Space Paths

We wish to derive an analogous "fundamental" result for curves in $RR^3$. However, we have no notion of "signed curvature" in this case. Moreover, as we'll see, we actually need a second "intrinsic" (called _torsion_) of the curve to uniquely identify it.

Fix $gamma : I -> RR^3$ regular and $C^2$ and with strictly positive curvature (turns out, there's not much we can say when the curvature is 0).

Define as before $ T := (dot(gamma))/(norm(dot(gamma))), quad N := (dot.double(gamma)^perp)/(norm(dot.double(gamma)^perp)) $ the unit tangent and normal vectors. Remark that $T dot N = 0$. Since we are in $RR^3$, there exists a unique third vector, which we denote $B$ and call it the _binormal_ such that ${T, N, B}$ is an orthonormal, positively oriented basis (in the sense that the matrix consisting of columns $T, N, B$ in that order is orthogonal with determinant 1) of $RR^3$, i.e. $ B := T times N. $
The basis ${T, N, B} subset RR^3$ is called the _Frenet frame_ associated to $gamma$.

We'll be interested in the dynamics of this frame, i.e. how $T, N, B$ resp. change in time. We need to additionally assume $gamma in C^3$ for this, so that we may take derivatives of $N$. We'll also assume $gamma$ is parametrized by arc-length for convenience. We find that with these assumptions, $ T = dot(gamma) \
=> dot(T) = dot.double(gamma) = norm(dot.double(gamma)) N = kappa N. $ In addition, $ norm(B) = 1 => dot(B) dot B = 0 $ and $ B = T times N => dot(B) = dot(T) times N + T times dot(N) = kappa underbrace(N times N, = 0) + T times dot(N) => dot(B) dot T = 0, $
hence $dot(B)$ is simultaneously orthogonal to $B$ and $T$, hence $ dot(B) = "const"(-N). $ We call this constant the _torsion_ $tau$ of $gamma$ at time $s$, which is given by $ tau := - dot(B) dot N. $
Finally, to compute $dot(N)$, we have that $ norm(N) = 1 => dot(N) dot N = 0 \
T dot N = 0 => 0 = dot(T) dot N + T dot dot(N) = kappa underbrace(norm(N)^2, = 1) + T dot dot(N) => T dot dot(N) = - kappa \
B dot N = 0 => 0 = dot(B) dot N + B dot(N) = -tau + B dot dot(N) => B dot dot(N) = tau. $ This implies $ dot(N) = - kappa T + tau B. $ In summary, we can succinctly write $ vec(dot(T), dot(N), dot(B)) = mat(0, kappa, 0; - kappa, 0, tau; 0, - tau, 0) vec(T, N, B) quad quad ("The Frenet equations"). $

#theorem("Fundamental Theorem of Space Paths")[
  Let $I subset RR$ be an interval with basepoint $s_0 in I$. Suppose $tau : I -> RR$ is a $C^(k - 3)$ function and $kappa : I-> RR_(>0)$ is a $C^(k - 2)$ function (where $3 <= k <= infinity$). Then, for any initial point $p_0 in RR^3$, initial velocity $v_0 in RR^3$, and initial normal direction $n_0 in RR^3$ such that $norm(v_0) = norm(n_0) = 1$ and $v_0 dot n_0 = 1$, there is a _unique_ regular $C^k$ path $gamma : I -> RR^3$ parametrized by arc length and satisfying:
  1. $kappa_gamma = kappa$,
  2. $tau_gamma = tau$,
  3. $gamma(s_0) = p_0$,
  4. $dot(gamma)(s_0) = v_0$,
  5. $dot.double(gamma)(s_0)/(norm(dot.double(gamma)(s_0))) = n_0$.
]

#remark[
  The last three requirements say that this curve is uniquely defined up to rigid motion, hence unique in $EE^3$; translations will simply change the initial point $p_0$, and rotations will change the angles of $v_0, n_0$.
]

#proof[
  Remark that the Frenet equations are a system of (9) first order ODEs with given initial condition. The Picard-Lindelhoff theorem from ODEs says that there exist unique function $T, N, B : I -> RR^3$ satisfying the equations with $T(s_0) = v_0, N(s_0) = n_0, B(s_0) = v_0 times n_0$. We need to show that these are the Frenet frame of some curve.

  First, we show they are a positively oriented orthogonal basis. Indeed, remark that, using the Frenet equations, $ (dif)/(dif s) (T dot N) & = kappa (N dot N) - kappa (T dot T) + tau (T dot B) \
  (dif)/(dif s) (T dot B) & = kappa (N dot B) - tau (T dot N) \
  (dif)/(dif s) (N dot B) & = - kappa (T dot B) + tau (B dot B) - tau (N dot N) \
  (dif)/(dif s) (T dot T) & = 2 kappa (T dot N) \
  (dif)/(dif s) (N dot N) & = - 2 kappa (T dot N) + 2 tau (N dot B) \
  (dif)/(dif s) (B dot B) & = -2 tau (N dot B). $ These are a system of ODEs for the quantities $T dot N, T dot B,$ etc with initial conditions $0,0,0, 1,1,1$. However, the system can also be solved by $T dot N equiv 0$, $T dot B equiv 0$, etc, and so by uniqueness of solutions to linear ODEs, it follows that $T dot N = 0$, etc, which proves the orthonormality. To show positive orientation, it suffices to show that $(T times N) dot B equiv 1$. This is true at the basepoint of time by choice of initial conditions, and if we take the derivative, we find $ (dif)/(dif s) ((T times N) dot B) = kappa (N times N) dot B + [(T times (- kappa T)) + T times (tau B)] dot B + (T times N) dot (- tau N), $ which we see to be equal to zero by our orthonormality proof from above. Thus, ${T, N, B}$ is indeed a positively-oriented orthonormal basis.

  Finally, we need to show that there exists a unique curve with $T$ as its unit tangent (from which the remainder of the quantities $N$, etc will follow); indeed, we have $ gamma : I -> RR^3, quad gamma(s) = p_0 + integral_(s_0)^s T(u) dif u $ is the unique curve with $dot(gamma) = T$; the fact that $gamma in C^k$ follows from $T in C^(k - 1)$.
]

#exercise[
  With the same assumptions as above, also assume $sigma : I -> RR_(> 0) in C^(k - 1)$. Then, there exists a unique $C^k$ regular path $gamma in EE^3$ such that $ norm(dot(gamma)) = sigma, quad kappa_(gamma) = kappa, quad tau_gamma = tau. $
]

We're interested in defining the torsion for more general paths in a consistent way. Let $gamma$ a regular $C^3$ curve in $RR^3$ with $kappa > 0$. Let $tilde(gamma) : tilde(I) -> RR^3$ be a arc-length reparametrization using $t: tilde(I) -> I$, and let $s = t^(-1)$, and define $ tau := tilde(tau) compose s, $ where $tilde(tau)$ the torsion of $tilde(gamma)$, as defined above.

#proposition[
  Let $gamma$ be as above. Then, $ kappa = norm(dot(gamma) times dot.double(gamma))/(norm(dot(gamma))^3), quad tau = ((dot(gamma) times ddot(gamma))/(norm(dot(gamma) times ddot(gamma))^2)) dot dddot(gamma) $
]
#proof[
  We know $kappa = norm(ddot(gamma)^perp)/(norm(dot(gamma))^2)$. In $RR^3$, $norm(dot(gamma) times ddot(gamma))$ is the area of the parallelogram with sides $dot(gamma), ddot(gamma)$, or equivalently, twice the area of the triangle with base $dot(gamma)$ and height $ddot(gamma)^perp$ (the perpendicular to the base $dot(gamma)$), i.e. $ norm(dot(gamma) times ddot(gamma)) = norm(dot(gamma)) norm(ddot(gamma)^perp), $ which proves the first claim. The second claim follows from lots of careful chain rules.
]


#exercise[
  Is torsion preserved by reversals? i.e., if $overline(gamma) := gamma compose overline(t)$ where $overline(t)(t) = - t$, is $tau_(overline(gamma)) (overline(t)) = tau_gamma (t)$?
]
// TODO the answer is yes
#exercise[(Twisted Cubic)
  Let $gamma : RR -> RR^3$ be given by $gamma(t) = (t, t^2, t^3)$. Show that $kappa(0) = 2, tau(0) = 3$.
]

#exercise[(Helix) Let $gamma(t) = (cos(t), sin(t), t)$. Show that $kappa equiv 1/2, tau equiv 1/2$.]
#exercise[Find an example where $kappa equiv 1/2, tau equiv -1/2$.]

== Global Theorems/Properties of Plane Curves
Let $SS^1$ denote the unit circle in $RR^2$ centered at the origin, with global periodic parametrization $rho(t) = (cos(t), sin(t))$. Given a $C^0$ curve in $SS^1$ by $g : I -> SS^1$, a function $theta : I -> RR$ is called a _lift_ of $g$ via $rho$ if
1. it is $C^0$
2. $g = rho compose theta$

#theorem[
  Fix $t_0 in RR, theta_0 in RR$ such that $g(t_0) = (cos theta_0, sin theta_0)$. Then, there exists a unique lift $theta$ of $g$ such that $theta(t_0) = theta_0$.
]

If $g : RR -> SS^1$ a periodic path with period $[a, b]$, then for any lift $theta$ of $g$, $ abs(theta(b) - theta(a)) = 2 pi n, quad n in ZZ_(+), $ where $n$ the number of times the curve "goes around" $SS^1$.

#theorem("Hopf's Umlanfasatz")[
  If $cal(C) subset RR^2$ a regular closed curve periodic (with period $[a, b]$) parametrization $gamma : R -> RR^2$, then for any lift $theta$ of its tangent vector $T$ (i.e., $theta$ is an angle function), $abs(theta(b) - theta(a)) = 2 pi$.
]

We say $gamma$ is _positively/ccw oriented_ if $theta(b) - theta(a) = 2 pi$, and _negatively/cw oriented_ if $theta(b) - theta(a) = - 2 pi$.

#theorem("Jordan Curve Theorem")[
  Let $cal(C) subset RR^2$ a regular closed curve. Then, $RR^2 \\ cal(C)$ has two connected components; one bounded ("inside" of $cal(C)$) and one unbounded ("outside" of $cal(C)$).
]

We can then say $gamma$ is _positively oriented_ if $T^ast$ points inside $cal(C)$, and _negatively oriented_ if $T^ast$ points outside $cal(C)$. It turns out these different notions of orientation are equivalent.

#theorem("Isoperimetric Inequality")[
  Let $cal(C) subset RR^2$ a regular closed curve. Let $ell =$ length of $cal(C)$ and $A =$ area of inside of $cal(C)$. Then, $ 4 pi A <= ell^2, $ with equality iff $cal(C)$ is a circle.
]

#proof[(Sketch of Hopf's)
  // TODO
]


= Appendix


#proposition[
  For $u, v in RR^3$, $norm(u times v)$ is the area of the parallelogram with side $u$, $v$.
]

#proposition[
  // The one about permutations of matrix columns and their determinant.
]

#proposition[

]
