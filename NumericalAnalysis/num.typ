// ! external
#import "../typst/notes.typ": *
// #import "../typst/shortcuts.typ": *

#import "@preview/cetz:0.2.2"

// ! configuration
#show: doc => conf(
  course_code: "MATH578",
  course_title: "Numerical Analysis 1",
  // subtitle: "Abstract Metric, Topological Spaces; Functional Analysis.",
  semester: "Fall 2025",
  professor: "Prof. J.C. Nave",
  // cute: "../analysis 3/page.png",
  doc,
)

#import "@preview/commute:0.2.0": arr, commutative-diagram, node

#set align(left)

#pagebreak()

= Polynomial Interpolation

In general, the goal of interpolation is, given a function $f(x)$ on $[a, b]$ and a series of distinct ordered points (often called _nodes_ or _collocation points_) ${x_j}_(j=1)^(n) subset.eq [a, b]$, to find a polynomial $P(x)$ such that $f(x_j) = P(x_j)$ for each $j$.

#theorem("Existence and Uniqueness of Lagrange Polynomial")[
  Let $f in C[a, b]$ and ${x_j}$ a set of $n$ distinct points. Then, there exists a unique $P(x) in PP_(n-1)$, the space of $n-1$-degree polynomials, such that $P(x_j) = f(x_j)$ for each $j$.

  We call such a $P$ the _Lagrange polynomial_ associated to the points ${x_j}$ for $f$.
]

#proof[
  We define the following $n-1$ degree "fundamental polynomials" associated to ${x_j}$, $ ell_j (x) equiv product_(1 <= i <= n \ i eq.not j) (x - x_i)/(x_j - x_i), wide j = 1, dots, n. $ Then, one readily verifes $ell_j (x_i) = delta_(i j)$, and that the distinctness of the nodes guarantees the denominator in each term of the product is nonzero. Define $ P(x) = sum_(j = 1)^n f(x_j) ell_j (x), $ which, being a linear combination of $n-1$ degree polynomials is also in $PP_(n-1)$. Moreover, $ P(x_i) = sum f(x_j) delta_(i, j) = f(x_i), $ as desired.

  For uniqueness, suppose $overline(P)$ another $n-1$ degree polynomial satisfying the conditions of the theorem. Then, $q(x) equiv P(x) - overline(P)(x)$ is also a degree $n-1$ polynomial with $q(x_i) = 0$ for each $i = 1, dots n$. Hence, $q$ a polynomial with more distinct roots than its degree, and thus it must be identically zero, hence $P = overline(P)$, proving uniqueness.
]

#theorem("Interpolation Error")[
  Suppose $f in C^n [a, b]$, and let $P(x)$ be the Lagrange polynomial for a set of $n$ points ${x_j}$, with $x_1 = a, x_n = b$. Then, for each $x in [a, b]$, there is a $xi in [a, b]$ such that $ f(x) - P(x) = (f^((n)) (xi))/n! (x - x_1) dots.c (x - x_n). $ Moreover, if we put $h := max_i (x_(i+1) - x_i)$, then $ norm(f - P)_infinity <= (h^n)/(4n) norm(f^((n)))_infinity. $
]

#proof[
  We prove the first identity, and leave the second "Moreover" as a homework problem. Notice that it holds trivially for $x = x_j$ for any $j$, so assume $x eq.not x_j$ for any $j$, and define the function $ g(t) := f(t) - P(t) - omega(t) (f(x) - P(x))/(omega(x)), wide omega(t) := (t - x_1) dots (t - x_n) in PP_n [t]. $ Then, we observe the following:
  - $g in C^n [a, b]$
  - $g(x) = 0$
  - $g(t = x_j) = 0$ for each $j$
  Recall that by Rolle's Theorem, if a $C^1$ function has $>= m$ roots, then its derivative has $>= m - 1$ roots. Thus, applying this principle inductively to $g(t)$, we conclude that $g^((n)) (t)$ has at least one root. Take $xi$ to be such a root. Then, one readily verifies that $P^((n)) equiv 0$ and $omega^((n)) equiv n!$ (using polynomial properties), from which we may use the fact that $g^((n)) (xi) = 0$ to simplify to the required identity.
]

#remark[
  In general, larger $n$ leads to smaller maximum step size $h$. However, it is _not_ true that $n->infinity$ implies $P -> f$ in $L^infinity$. From the previous theorem, one would need to guarantee $norm(f^((n)))-> 0$ (or at least, doesn't grow faster than $(h^n)/(4n)$), which certainly won't hold in general; we have no control on the $n$th-derivative of an arbitrarily given function. However, we can try to optimize our choice of points ${x_j}$ for a given $j$.
]


We switch notation for convention's sake to $n + 1$ points $x_j$. Our goal is the optimization problem $ min_(x_j) max_(x in [a, b]) abs(product_(j) (x - x_j)), $ the only term in the error bound above that we have control over. Remark that we can expand the product term: $ product_(j) (x - x_j) = x^(n+1) - r(x), $ where $r(x) in PP_(n)$. So, really, we equivalently want to solve the problem $ min_(r in PP_(n)) norm(x^(n + 1) - r(x))_infinity, $ namely, what $n$-degree polynomial minimizes the max difference between $x^(n + 1)$?


#theorem("De la Vallé-Poussin Oscillation Theorem")[
  Let $f in C([a, b])$, and suppose $r in PP_n$ for which there exists $n + 2$ distinct points ${x_j}$ such that $a <= x_0 < dots.c < x_(n + 1) <= b$ at which the error $f(x) - r(x)$ "oscillate" sign, i.e. $ "sign"(f(x_j) - r(x_j)) = - "sign"(f(x_(j + 1)) - r(x_(j + 1))). $ Then, $ min_(P in PP_n) norm(f - P)_(infinity) >= min_(0 <= j <= n + 1) |f(x_j) - r(x_j)|. $

]

#definition("Chebyshev Polynomial")[
  The _degree $n$ Chebyshev polynomial_, defined on $[-1, 1]$, is defined by $ T_n (x) := cos(n cos^(-1) (x)). $
]

#remark[The fact that $T_n$ actually is a polynomial follows from the double angle formula for $cos$, which says $ cos((n + 1) theta) = 2 cos(theta) cos(n theta) - cos((n - 1) theta). $ In the context of $T_n$, this implies that for any $n >= 1$, the recursive formula $ T_(n + 1) (x) = 2 x T_n (x) - T_(n - 1) (x). $ This formula with a simple induction argument proves that each $T_n$ a polynomial, with for instance $T_0 (x) = 1, T_1 (x) = x, T_2 (x) = 2x^2 - 1$ and so on.]

#proposition[
  ${T_n}$ are orthogonal with respect to the inner product given by $ (f, g) := integral_(-1)^1 f(x) g(x) omega_2 (x) dif x, $ where $omega_2 (x) := (1 - x^2)^(1\/2)$.
]

#remark[
  Defining similar _weight_ functions by $omega_n (x) := (1 - x^n)^(1\/n)$, one can derive a more general class of polynomials called _Geigenbauer polynomials_, which are respectively orthogonal with respect to $integral dot dot omega_n$.
]

#proposition([Some Properties of $T_n$])[
  - $abs(T_n (x)) <= 1$ on $[-1, 1]$
  - The roots of $T_n (x)$ are the $n$ points $ xi_j := cos(((2 j - 1) pi)/(2n)), wide j = 1, dots, n. $
  - For $n >= 1$, $abs(T_n (x))$ is maximal on $[-1, 1]$ at the $n + 1$ points $ eta_j := cos((j pi)/n), wide j = 0, dots, n, $ with $T_n (eta_j) = (-1)^j$.
]

Note too that $T_(n + 1) (x)$ has leading coefficient $2^(n)$, which can be seen by the recursive formula above; define the _normalized_ Chebyshev polynomials by $hat(T)_(n+1) (x) := 2^(-n) T_(n + 1) (x)$. Thus, we may write $ hat(T)_(n + 1) (x) = x^(n + 1) - r_n (x), $ with $r_n (x) in PP_n$. It follows for one that $ max_(x in [-1, 1]) |x^(n + 1) - r_n (x)| = 2^(-n). $ Moreover, we know that at the $n + 2$ points $eta_j$, we have $ hat(T)_(n + 1) (eta_j) = 2^(-j) (-1)^j = eta_j^(n + 1) - r_n (eta_j). $ Namely, because of the inclusion of $(-1)^j$ term, this means that $hat(T)_(n + 1) (x)$ oscillates sign between the $eta_j$ points, which fulfils the condition stated in the Oscillation Theorem. Thus, these observations readily imply the following result, settling our original question on optimizing locations of interpolation points for Lagrange interpolation:
#theorem([Optimal Approximation of $x^(n + 1)$ in $PP_n$])[
  The optimal approximation of $x^(n + 1)$ in $PP_n$ on $[-1, 1]$ with respect to the $L^infinity$ norm is given by $ r_n (x) := x^(n + 1) - 2^(-n) T_(n + 1) (x). $ Thus, the optimal Lagrange interpolation points are the $n + 1$ roots of $x^(n + 1) - r_n (x)$, namely $xi_j = cos(((2j + 1) pi)/(2n + 2))$ for $j = 0, dots, n$.
]

#remark[
  This, and previous results, were stated over $[-1, 1]$. A linear change of coordinates transforming any closed interval to $[-1, 1]$ readily leads to analgous results.
]

= Fourier Transform

Recall that the Fourier transform of a (Lebesgue) measurable function $u(x)$ on $RR$ is defined $ (cal(F)u )(xi) = hat(u)(xi) = integral_RR e^(-i xi x) u(x) dif x. $

#theorem[
  Let $u in L^2 (RR)$. Then,
  1. $hat(u) in L^2$
  2. the _inversion_ formula holds, ie $u(x) = integral_RR hat(u) (xi) e^(i xi x) dif x = (cal(F)^{-1} u) (x)$
  3. $norm(hat(u))_2 = sqrt(2 pi) norm(u)_2$
  4. for $u in L^2, v in L^1$, $u convolve v in L^2$, and $hat(u convolve v) = hat(u) hat(v)$.
]

#theorem("Further Properties of Fourier Transform")[
  Let $u, v in L^2$. Then,
  1. $cal(F)$ is linear over $RR$
  2. $cal(F)(u (dot + x_0)) (xi) = e^(i xi x_0) hat(u) (x_0)$
  3. $cal(F)(e^(i xi_0 x) u(x)) (xi) = hat(u) (xi - x_0)$
  4. If $c eq.not 0$, $cal(F)(u (c dot)) (xi) = (hat(u) (xi/c))/c$
  5. $cal(F)(overline(u)) (xi) = overline(hat(u)(-xi))$
  6. if $u_x$ exists and is in $L^2$, then $ cal(F)(u_x) (xi) = i xi hat(u)(xi). $ By extension, if $partial_alpha u in L^2$, then $hat(partial_alpha u) (xi) = (i xi)^alpha hat(u) (xi)$
  7. $(cal(F)^(-1) u) (xi) = 1/(2pi) hat(u)(-xi)$.
]

In a sense, 6. implies a duality between the smoothness of $u(x)$ and rapid decay (as $abs(xi) -> infinity$) of $hat(u)(x)$; 7. indicates that the same analogy holds switching the roles of $u$ and $hat(u)$. We make this more precise.
#definition("Bounded Variation")[
  We say a function $u$ on $RR$ is of _bounded variation_ or write $in "BV"$ if there exists a constant $M$ such that for any finite integer $m$ and collection of points $x_0 < x_1 < dots < x_m$, $ sum_(j=1)^m |u(x_j) - u(x_(j-1))| <= M. $
]
In a sense, this notion of $"BV"$ captures a notion of "limited oscillation".

#theorem[
  Let $u in L^2$. Then:
  1. If $u$ has $p - 1$ continuous derivatives in $L^2$ and its $p$th derivative is in BV, then $ hat(u)(xi) = cal(O)(|xi|^(- p - 1)). $
  2. If $u$ has infinitely many derivatives all in $L^2$, then $ hat(u)(xi) = cal(O)(|xi|^(-M)), wide forall M >= 1. $
]

== Discrete Fourier Transform

Let $h > 0$ be a _step size_. Let $x_j = j h$ for $j in ZZ$. We write $v = {v_j}_(j in ZZ)$ for discrete approximations of a function $u$ on the grid ${x_j}_(j in ZZ)$, i.e. $v_j approx u(x_j)$.

The $ell^2_h$ norm is defined for such $v$ by $ norm(v)_2 := [h sum_(j in ZZ) |v_j|^2]^(1\/2). $
Then, $ell^2_h$ is defined as the space of such sequences $v$ such that this norm is finite. analogous definitions hold for other $ell^p_h$ spaces and norms.

#proposition("Nesting")[
  $ell^p_h subset ell^q_h$ for each $q >= p$.
]

#remark[
  Note that the analogous result to this does _not_ hold for $L^p$ spaces (unless restricted to a compact domain).
]

We define the convolution of two sequences $v, w$ by the new sequence $v convolve w$ with entries $ (v convolve w)_m = h sum_(j in ZZ) v_j w_(m - j) = h sum_(j in ZZ) v_(m - j) w_j. $ For any $v in ell^2_h$, we define too the _semi-discrete Fourier transform_ of $v$ by $ hat(v) (xi) = (cal(F)_h v)(xi) = h sum_(j in ZZ) e^(-i xi x_j) v_j, wide xi in [-pi/h, pi/h], $ where we remark that $hat(v)(xi)$ $(2pi)/h$-periodic (hence the domain restriction) and continuous.

We define the norm of $hat(v)$ by the usual $L^2$-norm, restricted to the appropriate domain: $ norm(hat(v))_2 := (integral_(-pi\/h)^(pi\/h) |hat(v)(xi)|^2 dif xi)^(1\/2), $ and $L^2_h$ the space of such functions with finite norm.

#theorem[
  If $v in ell_h^2$, then $hat(v) in L^2_h$, and we can recover $v$ from $hat(v)$ by the "inverse semi-discrete Fourier transform", i.e. $ v_j = 1/(2pi) integral_(-pi\/h)^(pi\/h) e^(i xi x_j) hat(v) (xi) dif xi. $ Also, Parseval's identity holds, i.e. $norm(hat(v))_2 = sqrt(2 pi) norm(v)_2$, as does the expected convolution identity (for $v in ell^2_h, w in ell^1_h$ for instance).
]


#remark[
  Note that each wave number $xi$ is indistinguishable from $xi + (2pi j)/h$ for $j in ZZ$ on $h ZZ$; this is called _aliasing_. The cutoff $pi/h$ is called the _Nyquist Wave Number_.
]



#theorem[
  Let $u in L^2$, sufficiently smooth, with $v in ell^2_h$ be a restriction of $u$ to $h ZZ$. Then, $ hat(v)(xi) = sum_(j in ZZ) hat(u)(xi + (2pi j)/h), wide xi in [-pi/h, pi/h]. $
]


== Wavelet Transform


The heuristic idea of the wavelet transform is to construct a basis of functions which effectively compromise between localization in space and frequency; indeed, the issues related to aliasing in the discrete case are linked to the fact that localization of a function simultaneously in physical and fourier space is impossible except for the zero function.

More precisely, we dictate that a wavelet $psi$ should have:
1. non-negligible values in a limited range of space _and_ frequency;
2. finite energy, by which we mean $ integral_(0)^infinity |hat(psi) (omega)|^2 (dif omega)/(abs(omega)) < infinity. $
3. zero mean, i.e. $integral_(-infinity)^infinity psi(t) dif t = 0$.

Note that 2., 3., imply that $psi$ has actual "frequency content" and zero mean, so $psi$ satisfying these properties must oscillate.

We call such a $psi$ a the _model wavelet_, from which we will generate our desired basis by translating and scaling: $ psi_(s, tau) (t) := 1/(sqrt(s)) psi((t - tau)/s). $

From this, we define $ gamma(s, tau) = integral f(t) psi_(s, tau)^(ast) (t) dif t. $ Then, one can retrieve $f$ (with appropriate properties) by the _inverse wavelet transform_ $ f(t) = integral_(RR^+) integral_(RR) gamma(s, tau) psi_(s, tau) (t) dif tau dif s. $

In a sense, $gamma(s, t)$ provides a _compromise_ between space (i.e. $tau$) and frequency/scale (i.e. $s$) and energy localization.

More precisely, we'd like a quantitative decay of $gamma(s, t)$ for small $s$, i.e. small frequencies, which are the problematic range. If we Taylor expand $f$ in the definition of $gamma(s, tau)$ about $s = 0$ (and taking $tau = 0$ for convenience), one notices that $ gamma(s, 0) = 1/(sqrt(s)) [sum_(p=0)^n f^((p))(0) integral t^p/(p!) psi(t\/s) dif t + cal(O)(n + 1)]. $ If we define $M_p := integral t^p psi(t) dif t$ to be the $p$th moment of $psi$, then one clearly sees that if the first $n$ moments of $psi$ are identically 0, then $ psi(s, tau) = cal(O)(s^(n + 2)), $ those providing a qualitative decay rate for these coefficients. Thus, we generally want such vanishing moments in designing "good" wavelets.
