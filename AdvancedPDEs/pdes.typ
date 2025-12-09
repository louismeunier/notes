// ! external
#import "../typst/notes.typ": *
// #import "../typst/shortcuts.typ": *

#import "@preview/cetz:0.2.2"

// ! configuration
#show: doc => conf(
  course_code: "MATH580",
  course_title: "Advanced PDEs 1",
  subtitle: "Local existence theory, first order quasilinear equations; Laplace's equation; the wave equation; the heat equation.",
  semester: "Fall 2025",
  professor: "Prof. Niky Kamran",
  // cute: "../analysis 3/page.png",
  doc,
)

#import "@preview/commute:0.2.0": arr, commutative-diagram, node

#set align(left)
#let boxit(arg) = box(stroke: 0.75pt, outset: 8pt, arg)

#pagebreak()

= Local Existence Theory

== Terminology

#definition("Multiindex")[
  We'll use _multiindex_ notation throughout; if working in $RR^n$, we have a multiindex $ alpha equiv (alpha_1, dots, alpha_n), wide alpha_i in ZZ_+. $ The _length_ of a multiindex is given $ |alpha| equiv sum_(i) alpha_i, $ and we'll also write, for $x in RR^n$, $ x^alpha equiv x_1^(alpha_1) dots.c x_n^(alpha_n). $
  Finally, we'll write $ partial^alpha equiv partial_(x_1)^(alpha_1) compose dots.c compose partial_(x_n)^(alpha_n) $ for higher-order partial derivatives in mixed directions.
]

Thus, the most general form of a $k$-th order PDE in independent variables $x in Omega subset RR^n$ can be written succinctly by $ F(x, (partial^(alpha) u)_(|alpha| <= k))) = 0, wide F : Omega times RR^(N(k)) -> RR, wide (dagger) $ with $N(k) equiv hash {alpha | |alpha| <= k}$.

#definition("Solution")[
  We'll define a _(classical/strong) solution_ to $(dagger)$ to be a $C^k$-map $u : Omega -> RR$ for which $(dagger)$ is satisfied for all $x in Omega$.
]

#definition("Linearity/Quasilinearity")[
  We say $(dagger)$ is _linear_ if $F$ is affine-linear in $partial^(alpha) u$ for each multiindex, i.e. we may write equivalently $ L[u] := sum_(|alpha|<= k) a_alpha (x) partial^alpha u = f(x), $ where $L[u] = f(x) <=> F[x, u] = 0$. Similarly, $(dagger)$ is said to be _quasilinear_ if $F$ is affine-linear in the highest order derivatives, i.e. $partial^alpha u$ for $|alpha| = k$. An equivalent form is given by $ sum_(|alpha|= k) a_alpha (x, (partial^beta u)_(|beta| <= k - 1)) partial^alpha u = b(x, (partial^beta u)_(|beta| <= k - 1)). $
]

#definition("Weak Solution")[
  A _weak solution_ to a linear PDE $L[u] = f$ is a function $u : Omega -> RR$ such that $ sum_(|alpha|<= k) (-1)^(|alpha|) angle.l u, partial^(alpha) a_alpha phi angle.r = angle.l f, phi angle.r wide forall phi in C^infinity_c (Omega), $ with $angle.l dot, dot angle.r$ the regular $L^2 (Omega)$-inner product.
]

#remark[
  Such a notation allows for non-$C^k$ "solutions" to $(dagger)$ which still have certain properties akin to those described by $F$. For a motivation of the definition, one need only integrate by parts $L[u] = f$ multiple times, hitting against $phi in C^infinity_c (Omega)$; if $u$ were a strong solution, one would find the above equation as a result.
]

#definition("Characteristics")[
  Let $L$ be a linear operator associated to a $k$th-order linear PDE. The _characteristic form_ of $L$ is the $k$th degree homogeneous polynomial defined by $ chi_L (x, xi) := sum_(|alpha| = k) a_alpha (x) xi^alpha. $ The _characteristic variety_ is defined, for a fixed $x$, as the set of $xi$ for which $chi_L$ vanishes, i.e. $ "char"_x (L) := {xi eq.not 0 | chi_L (x, xi) = 0}. $
]
#remark[
  Suppose $overline(xi) = xi_j e_j eq.not 0 in "char"_x (L)$; then since $ chi_L (x, overline(xi)) = a_(overline(alpha)) partial_(x_j)^k xi_j, wide overline(alpha) equiv k e_j, $ then it must be that $a_(overline(alpha)) = 0$ at $x$. Heuristically, one has that $L$ is not "genuinely" $k$th order in the direction of $overline(xi)$.
]
#definition("Elliptic")[We say $L$ is _elliptic_ at $x$ if $"char"_x (L) = nothing$.]

#proposition[$"char"_x (L)$ is independent of choice of coordinates.]

== First Order Scalar PDEs

We consider the quasilinear first-order PDE of the form $ sum_(i=1)^n a_i (x, u) partial_i u = b(x, u), wide (ast) $ subject to the initial condition $u|_S = phi$ where $S subset.eq RR^n$ some hypersurface with $phi$ given. We assume $a_i, b$ $C^1$ in all arguments.

#theorem[
  Let $A(x) = (a_1 (x, u), dots, a_n (x, u), b(x, u))$ and $S^ast = {(x, phi(x)) : x in S} subset.eq RR^(n+1)$. Then, if $A$ nowhere tangent to $S^ast$, then for any sufficiently small neighborhood $Omega$ on $S$, there exists a unique solution to $(ast)$ on $Omega$.
]

#proof[
  Locally, $S$ can be parametrized by $ (s_1, dots, s_(n-1)) |-> g(s) = (g_1 (s), dots, g_n (s)). $ Then, the "transversality condition" (about the tangency of $A$) can equivalently be written as $ det mat(partial g_1\/partial s_1, dots, partial g_1\/partial s_(n-1), a_1 (g(s)); dots.v, "", dots.v, dots.v; partial g_n\/partial s_1, dots, partial g_n\/partial s_(n-1), a_n (g(s))) eq.not 0. $
  #remark[In the linear case, one sees that this equivalently means that the normal $nu$ of $S$ is not in $"char"_x (L)$; in particular, it is independent of the choice of initial data, _in this case_.]
  Remark that if we write coordinates $(x_1, dots, x_n, y) in RR^(n+1)$ and define $F(x, y) = u(x) - y$, then the PDE can be written succinctly as the statement $A dot gradient F = 0$, and that the zero set $F = 0$ gives the graph of the solution $u$; hence, we essentially need that the vector field $A$ everywhere tangent to the graph of any solution. The idea of our solution is to consider $A$ "originating" at $S^ast$, and "flowing" our solution along the integral curves defined by $A$ to obtain a solution locally.

  The integral curves of $A$ are defined by the system of ODEs $ cases((dif x_j)/(dif t) = a_j (x, y)\, (dif y)/(dif t) = b(x, y) & ""\ x_j (s, 0) = g_j (s)\, y(s, 0) = phi(g(s))) wide j = 1, dots, n. $
  By existence/uniqueness theory of ODEs, there is a local solution to this ODE, viewing $s$ as a parameter, inducing a map $ (s, t) |-> (x_1 (s, t), dots, x_n (s, t)), $ which is at least $C^1$ in $s, t$ by smooth dependence on initial data. By the transversality condition, we may apply inverse function theorem to this mapping to find $C^1$-inverses $s = s(x), t = t(x)$ with $t(x) = 0$ and $g(s(x)) = 0$ whenever $x in S$. Define now $ u(x) := y(t(x), s(x)). $ We claim this a solution. By the inverse function theorem argument, it certainly satisfies the initial condition, and repeated application of the chain rule shows that the solution satisfies the PDE.
]

We briefly discuss, but don't prove in detail, the fully nonlinear case, i.e. $ F(x, u, partial u) = 0, $ where we assume $F in C^2$. We approach by analogy. Putting $xi_i := (partial u)/(partial x_i)$, then we see $F$ as a function $RR^(2n + 1) -> RR$. We seek "characteristic" ODEs akin to those found for the integral curves in the quasilinear case. We naturally take, as in the previous, $(dif x_i)/(dif t) = (partial F)/(partial xi_i)$. Applying chain rule, we find that $ (dif y)/(dif t) = sum_i (partial u)/(partial x_i) (dif x_i)/(dif t) = sum_(i) xi_i (partial F)/(partial xi_i). $ Finally, if we differentiate $F = 0$ w.r.t. $x_j$, we find $ 0 = (partial F)/(partial x_j) + xi_j (partial F)/(partial y) + sum_(k) (partial F)/(partial xi_k) (partial xi_k)/(partial x_j) $ whence $ (dif xi_j)/(dif t) = sum_k (partial xi_j)/(partial x_k) (partial x_k)/(partial t) = - (partial F)/(partial x_j) - xi_j (partial F)/(partial y). $ In summary, this gives a system of $2 n +1$ ODEs in $(x, y, xi)$ variables $ (dif x_j)/(dif t) = (partial F)/(partial xi_j), wide (dif y)/(dif t) = sum_(i) xi_i (partial F)/(partial xi_i) \
(dif xi_j)/(dif t) = -(partial F)/(partial x_j) - xi_j (partial F)/(partial y). $ After imposing a similar (but slightly more complex) transversality requirement, one can similarly obtain a solution from this system by an inverse function theorem argument.

In terms of initial conditions, if $u$ is specified on some hypersurface $S$, we need to lift it to $S^(ast ast) subset.eq RR^(2n + 1)$ to "encode" the information of the initial values of $u$ and its derivatives on $u$.

#example[
  Show that $ partial_1 u partial_2 u = u, wide u(0, x_2) = x_2^2 $ has solution $ u(x_1, x_2) = (x_1 + 4 x_2)^2/16. $
]

#example("Geodesics")[
  For an invertible matrix $g = (g^(i j))$, solve $ sum_(i j) g^(i j) (partial u)/(partial x_i) (partial u)/(partial x_j) = 0. $
]<ex:geo>

#solution([(To @ex:geo)])[

]

== Cauchy-Kovaleskaya

We discuss the essential existence and uniqueness theorem related to the following general $k$-order Cauchy problem: $ (ast') wide cases(F(x, u, partial^alpha u) = 0 & wide abs(alpha) <= k, partial_(nu)^j u|_(S) = phi_j & wide 0 <= j <= k - 1), $ in which $S$ a given hypersurface with normal $nu$, and we assume $F$ and $phi_j$ to be analytic, for which we write that they are in $C^omega$. We aim to show that, for $x_0 in S$, there exists a neighborhood of $x_0$ and unique solution to $(ast')$ on that neighborhood.

We begin to rewriting $(ast')$ in several ways to simplify things. First, since we are working locally, we can always change coordinates to $(x, t) in RR^(n - 1) times RR$ such that $S$ is locally given by the zero set $t = 0$, in which case our problem becomes $ (ast) wide cases(
  F(x, t, partial_x^alpha partial_t^j u) = 0 & wide abs(alpha) + j <= k,
  partial_t^j u(x,0) = phi_j (x) & wide 0 <= j <= k - 1
), $ where now of course $alpha = (alpha_1, dots, alpha_(n-1))$ a $n - 1$ length multiindex.

Remark that if $u$ were a $C^r$ solution for $r >= k$, we can compute $ partial_(x)^alpha partial_t^j u(x, 0) = partial_x^alpha phi_j (x) $ for any $0 <= j <= k - 1$ and $abs(alpha) <= r$. I.e., we can compute the mixed partial derivatives of $u$ up to order $k - 1$ in $t$ along $S$ in this way. To find those related to the $k$th order in $t$, we'd need to be able to use the equation $F = 0$ directly to solve for $partial_t^k u(x, 0)$ in terms of the other variables. However, this is not always possible, for arbitrary Cauchy data:

#example[
  1. $partial_x partial_t u = 0$, $u(x, 0) = phi_0 (x)$, $partial_t u(x, 0) = phi_1 (x)$ does not have unique solutions, and in fact the initial conditions dictate that $phi_1$ must be constant (which is already problematical). Moreover, $u(x, t) := phi_0 (x) + f(t)$, with $f$ any $C^1$ function with $f(0) = phi_1$, is a valid solution.
  2. $partial_x^2 u - partial_t u = 0$ dictates that $phi_0 '' (x) = phi_1 (x)$, so we can't choose arbitrary initial conditions again.
]

We enforce then this condition in the following:
#definition("Characteristic")[
  We say $S$ given by $t = 0$ is _non-characteristic_ for $(ast)$ if one can solve for $partial_t^k u$ from the equation directly.
]

In this case, we may rewrite our equation as $ (1) wide cases(
  partial_t^k u = G(x, t, (partial_x^alpha partial_t^j u)_(abs(alpha) + j <= k\ 1 <= j <= k - 1)) & \
                                                                  partial_t^j u(x, 0) = phi_j (x) & wide 0 <= j <= k - 1
). $ Moreover, we assume $x_0 = (0, 0)$ in $(x, t)$ space by translating. We write, for notational convenience, $y_(alpha j) := partial_x^alpha partial_t^j u$, noting that we will use this both as a separate coordinate system and for shorthand distinctly, so one should be careful with interpreting notation to follow.

Now, by differentiating $(1)$ repeatedly with respect to $t$ and evaluating when $t = 0$ (so on $S$), we can thus solve for the higher-order derivatives of $partial_t^(j) u$ in terms of lower-order, known terms. For instance, $ partial_t^(k + 1) u = (partial G)/(partial t) + sum_(|alpha| + j <= k \ 0 <= j <= k - 1) (partial G)/(partial y_(alpha j)) partial_x^alpha partial_t^(j + 1) u. $ On $S$, everything on the right-hand side is determined, and so thus we know what $partial_t^(k + 1) u$ is as well here. We can repeat this process for any order derivative of $u$. This proves our first result:

#proposition[$(1)$ has at most 1 analytic solution.]

#proof[
  If $(1)$ has an analytic solution $u$, then the discussion above demonstrates how to compute all of its derivatives at a specific point, i.e. on $S$. But these then just form the coefficients of a local power series representation of $u$, which must be unique, and hence $u$ is unique as well, being determined by such coefficients.
]

#theorem("Cauchy-Kovaleskaya")[
  (1) has a unique analytic solution.
]

The proof of the theorem is fairly constructive. Using similar ideas to above, we find the Taylor series coefficients of a solution. Then, we show that such a series actually converges with strictly positive radius of convergence, thus proving in turn existence and analyticity of the solution. The previous proposition give the uniqueness once this existence has been established.

First, we can rewrite $(1)$ a couple of times:

#lemma[(1) is equivalent to $ cases(
    partial_t Y = sum_(j=1)^(n - 1) A_j (x, t, Y) partial_j Y + B(t, x, Y), Y(x, 0) = Phi(x)
  ), $
  where $Y$ a vector $(y_(alpha j))_(|alpha| + j <= k)$, $A_j (x, t, Y)$ matrix-valued, $B(t, x, Y)$ vector valued, $partial_j equiv partial_(x_j)$, and $Phi$ determined by $phi_j$.
]
The proof is notationally difficult, but not conceptually; one need just to show that if $y_00$ the first (lexicographically) component of a solution $Y$ to this system, then $y_00$ satisfies the original PDE.

We can do even better:
#lemma[
  The problem (1) is equivalent to one in the same form as the previous lemma, but with $A_j$ and $B$ independent of $t$ (and $Y$ now of 1 higher dimension).
]

This last one is easy; we just introduce an additional component to $Y$ such that $partial_t Y = 1$, and subtract the initial conditions from our original $B$.

#example("Transforming a PDE into \"Cauchy form\" ")[
  Consider the special case of a PDE $ u_(t t) = f(u_(x x), u_(x t)), \
  u(x, 0) = phi_0 (x), wide u_t (x, 0) = phi_1 (x), $ where we assume $f, phi_0, phi_1 in C^infinity$ for convenience of notation. In the notation of the previous two lemmas, we have $ Y = (y_00, y_10, y_01, y_20, y_11, y_02). $ Computing the partials of each of these entries: $ partial_t y_00 = \"partial_t u\" = y_01, wide partial_t y_10 = y_11, wide partial_t y_01 = y_02, \
  partial_t y_20 = \"y_21\" = partial_x y_11, wide partial_t y_11 = partial_x y_02, wide partial_t y_02 = f_1 partial_x y_11 + f_2 partial_x y_02, $ noting that in the second line, we used the assumed smoothness of the solutions to interchange the order of the derivatives, and for the last partial, we directly used the statement of the PDE. The initial conditions follow similarly, $ y_00 (x, 0) = phi_0 (x), wide y_10 (x, 0) = phi'_0 (x), wide y_01 (x, 0) = phi_1 (x) \
  y_20 (x, 0) = phi''_0 (x), wide y_11 (x, 0) = phi'_1 (x), wide y_02 (x, 0) = f(phi''_1 (x), phi'_1 (x)), $ where we again use the PDE directly to compute the final initial condition.
]

We recall/state several facts on $C^omega$ functions of multiple variables we'll need.

#proposition("i")[
  We say $f in C^omega$ near $x_0$ if there exists a cube $Omega := {x in RR^n : |x_j - x_j^0| < r, 1 <= j <= n}$, $r > 0$, such that the series $ sum_(alpha) 1/(alpha!) (partial^alpha f)(x_0) (x - x_0)^alpha $ converges to $f(x)$ for all $x in Omega$.

  On compact subsets of $Omega$, convergence is absolute and uniform; in particular, we can differentiate the summation term-by-term.
]

#proposition("ii")[
  Let $f(x) = sum a_alpha (x - x_0)^alpha$ converge near $x_0$, and suppose $x$ a $C^omega$ function of $xi$, i.e. $x = sum b_beta (xi - xi_0)^beta$, $x(xi_0) = x_0$. Then, $F(xi) := f(x(xi))$ will be analytic near $xi_0$, and moreover, the power series for $F$ is obtained by substitution, and can be written $ F(xi) = sum_(gamma) c_gamma (xi - xi_0)^gamma, $ where the coefficients $c_gamma = c_gamma (a_alpha, b_beta)$ are polynomials in $a_alpha, b_beta$, with non-negative coefficients.
]

#proposition("iii")[
  Given $M > 0, r > 0$, the function $ f(x) := (M r)/(r - (x_1 + dots + x_n)) $ is analytic on the rectangle ${x | max_j |x_j| < r/n}$, and moreover $ f(x) = M sum_(k=0)^infinity (x_1 + dots.c + x_n)^k/(r^k) = M sum_(alpha) (|alpha|! x^alpha)/(alpha! r^(|alpha|)). $
]

#remark[This is just a geometric series, with the second equality just a rewriting using the multinomial theorem.]

#proposition("iv")[
  We say that $A := sum a_alpha (x - x_0)^alpha$ _majorizes_ $B := sum b_alpha (x - x_0)^alpha$ if $a_alpha > |b_alpha|$ for all $alpha$. In this case, if $A$ converges absolutely at some $x$, then so does $B$.
]

#remark[
  This is just the comparison test in several variables.
]

#proposition("v")[
  Suppose $sum_alpha a_alpha x^alpha$ converges in some rectangle ${x | max_j |x_j| < R}$. Then, there exists a geometric series, as in (iii), that majorizes $sum_alpha a_alpha x^alpha$.
]

#proof[
  Let $0 < r < R$ fixed. Then, $sum a_alpha r^(|alpha|)$ converges, and thus there exists $M > 0$ such that $|a_alpha r^(|alpha|)| <= M$ for all $alpha$. Rearranging, this implies $ |a_alpha| <= M/(r^(|alpha|)) <= (M |alpha|!)/(r^(|alpha|) alpha!), $ where we used the fact that $|alpha|! >= alpha!$.
]

We return to the proof of Cauchy-Kovaleskaya. Using our lemmas, we are reduced to solving the system $ (1) wide partial_t y_m = sum_(i=1)^(n - 1) sum_(ell=1)^N a^i_(m, ell) (x, Y) partial_i y_ell + b_m (x, Y), wide 1 <= m <= N, \
Y(x, 0) = 0. $

In particular, we will construct a power series for each $y_m$ component, and prove that it converges. Namely, we write $ y_m = sum_(alpha, j) c_m^(alpha j) x^alpha t^j. $ Substituting this form into (1), the right-hand side becomes $ sum_(i, j, alpha) P_m^(alpha j) ((c_k^(beta k))_(k <= j), "coeff. of" A_i, B) x^alpha t^j, $ where $P_m^(alpha j)$ are polynomials with nonnegative coefficients, as in (ii). The left-hand side becomes $ sum_(alpha, j) (j + 1) c_m^(alpha, j + 1) x^alpha t^j. $ Matching coefficients, this gives the recursive formula $ c_(m)^(alpha j + 1) = 1/(j + 1) P_(m)^(alpha j) ((c_k^(beta k))_(k <= j), "coeff. of" A_i, B). $ This can be solved explicitly, giving $ c_m^(alpha j) = Q_m^(alpha j) ("coeff. of" A_i, B), $ where $Q_m^(alpha j)$ a polynomial with nonnegative coefficients.

This defines, assuming convergence, the power series of each $y_m$. The key-step to proving convergence is the following; we construct another Cauchy problem $ (1') wide partial_t tilde(Y) = sum_(j=1)^(n - 1) tilde(A)_j (x, tilde(Y)) partial_j tilde(Y) + tilde(B)(x, tilde(Y)),\
tilde(Y)(x, 0) = 0, $ with $tilde(A)_j, tilde(B)$ chosen such that \
$tilde(("i"))$: $(1')$ has a $C^omega$ solution near $(x, t) = (0, 0)$;\
$tilde(("ii"))$: the Taylor series of $tilde(A)_i$, $tilde(B)$ majorize those of $A_i, B$ respectively.

Assuming we can do this we'll be done. We claim that a solution to $(1')$ will majorize our constructed solution to $(1)$, which would imply our desired result (namely, that this solution converges). Indeed, we have that since each $Q_(m)^(alpha j)$ has nonnegative coefficients, $ |c_m^(alpha j)| = |Q_m^(alpha j) ("coeff." A_i, B)| <= Q_m^(alpha j) ("coeff." tilde(A)_i, tilde(B))= tilde(c)_m^(alpha j), $ and thus $sum tilde(c)_m^(alpha j) x^alpha t^j$ majorizes $sum c_m^(alpha j) x^(alpha) t^alpha$, and thus the latter converges near the origin.

We proceed then to construction $tilde(A)_j, tilde(B)$ for $(1')$ and its conditions to hold. By (v) above, there exists $M > 0$ and $r > 0$ such that the series for each $A_i$ and $B$ are majorized by the (geometric) series for $ (M r)/(r - (x_1 + dots.c + x_(n - 1) - (y_1 + dots.c + y_N))). $ Thus, chosen in this way, consider our candidate $(1')$ as $ partial_t y_m = (M r)/(r - sum_(i=1)^(n - 1) x_i - sum_(j=1)^N y_j) (sum_(i=1)^(n - 1) sum_(j=1)^N partial_i y_(j) + 1), wide y_m (x, 0) = 0, $ for each $1 <= m <= N$, noting that by choice of $M, r$, $tilde("(ii)")$is satisfied, so we just need to show that this has a $C^omega$ solution.

Remark that this system is completely symmetric under permutation of the $x_j, y_m$ variables, and thus if we find a solution $u = u(s, t)$ to the system $ (1'') wide partial_t u = (M r)/(r - s - N u) (N (n - 1) partial_(s) u + 1 ), wide u(s, 0) = 0, $ where $(s, t) in RR^2$, then setting $ y_j = u(x_1 + dots.c + x_n, t), wide j = 1, dots, N, $ gives a solution to $(1')$. But $(1'')$ is just a quasilinear system, in $RR^2$, which we know how to handle. Indeed, it has characteristic equations (using $tau$ as our "characteristic" parameter) $ (dif t)/(dif tau) = n - s - N u, wide (dif s)/(dif tau) = - M r (N - 1), wide (dif u)/(dif tau) = M r\
t(0) = 0, s(0) = sigma, u(0) = 0, $ using $sigma$ as our parametrization variable along $tau = 0$. Solving this system, one readily finds $ t(tau) = 1/2 M r N (n - 2) tau^2 + alpha tau, wide s(tau) = -M r (N - 1) tau + sigma, wide u(tau) = M r tau, $ where $alpha$ an arbitrary constant. Inverting these to solve for $tau(s, t), sigma(s, t)$ and plugging into $u$ (indeed, $u$ only depends on $tau$ so it suffices to solve for this parameter), readily yields $ u(s, t) = (r - s - sqrt((r - s)^2 - 2 M r N t))/(M n). $ This is analytic in $(s, t)$ near the origin (indeed, we can avoid any blow-ups in the higher derivatives of $sqrt(dots)$), and thus $u in C^(omega)$. "Changing variables" to $u(x_1 + dots + x_n, t)$ will not change this analyticity, and so we have finished our proof. #h(1fr) $square.filled$

#remark[
  This theorem gives absolutely _no_ description as to how solutions to a given PDE behave with respect to their initial Cauchy data. For ODEs, under mild assumptions, we can guarantee continuous dependence on solution on initial conditions; we have no such result for PDEs under the current assumptions, for any reasonable notion of "continuity" for spaces of functions.
]

#example("from Hadamard")[
  Consider Laplace's equation in $RR^2$ with specified initial conditions on a line: $ partial_1^2 u + partial_2^2 u = 0,\
  u(x_1, 0) = 0, wide partial_2 u(x_1, 0) = phi_k (x_1) := k e^(-sqrt(k)) sin(k x_1), $ with $k in NN$. The line $x_2 = 0$ is clearly non-characteristic for the PDE. The unique $C^omega$ solution is given by (which can be found using characteristics) $ u_k (x_1, x_2) = e^(-sqrt(k)) sin(k x_1) sinh(k x_2). $

  Now, remark that as $k -> infinity$, the initial data $phi_k -> 0$ uniformly in $x_1$. However, the solution, for $x_2 eq.not 0$, as $k -> infinity$
  - grows in amplitude (because of the $sin$ term)
  - oscillates increasingly rapidly (because of the $sinh$ term),
  so in particular, $u_k$ will diverge for $x_2 eq.not 0$. The unique solution for the limiting initial data $lim_(k -> infinity) phi_k (x_1) = 0$, though, is the trivial solution. So, there is clearly no "continuity" (in some vague, heuristic sense) in this situation.
]

= The Laplacian/Laplace's Equation

== Preliminaries: Review of the Fourier Transform, Distributions

=== Fourier Transform

Recall that the Fourier transform of a function $f in L^1 (RR^n)$ (which we'll write as $L^1$ when the underlying space is clear) is defined by $ hat(f) (xi) := integral_(RR^n) e^(-2 pi i x dot xi) f(x) dif x. $
We'll state some properties of $hat(f)$ here, mostly without proof. Note first that by passing absolute values under the integral, we have the trivial bound $norm(hat(f))_infinity <= norm(f)_1$, so in general the Fourier transform will live in $L^infinity$. We'll see some isntances below where we can do better.

#theorem[For $f, g in L^1$, $hat(f convolve g) = hat(f) dot hat(g)$.]

#proposition[
  Let $f in L^1$. Then:
  1. if we define $f_a (dot) := f(dot + a)$ as the translate of $f$ by a vector $a in RR^n$, then $ hat(f_a) (xi) = e^(2 pi a dot xi) hat(f) (xi); $
  2. if $T$ a linear invertible map on $RR^n$, then $ hat(f compose T) (xi) = |det T|^(-1) hat(f)((T^(-1))^ast xi); $
  in particular, the Fourier transform commutes with orthogonal linear transformations.
]

#definition("Schwartz Class")[
  The _Schwartz Class_ of functions is defined $ cal(S) = cal(S)(RR^n) := {u in C^infinity (RR^n) | sup_(x in RR^n) |x^(beta) partial^alpha u| < infinity, forall "multiindices" beta, alpha}. $
  In other words, it is the space of smooth functions decay faster at infinity than any polynomial can grow.
]


#theorem[$cal(S)$ is dense in $L^1$, and functions in $cal(S)$ are uniformly continuous.]

#proposition[
  Let $f in cal(S)$. Then:
  1. $hat(f) in C^infinity$ and $partial^beta hat(f) = hat((-2 pi i x )^beta f)$;
  2. $hat(partial^beta f) (xi) = (2pi i xi)^beta hat(f) (xi)$.
]

#corollary[
  $f in cal(S) => hat(f) in cal(S)$
]

#theorem("Riemann-Lebesgue Lemma")[
  Let $f in L^1$; then, $hat(f)$ is continuous and $hat(f) (xi) -> 0$ as $norm(xi) -> infinity$.
]

#theorem("Gaussian to Gaussian")[
  Let $f(x) = e^(-pi a |x|^2)$, then $hat(f)(xi) = a^(-n\/2) e^(-pi |xi|^2\/a)$.
]

#theorem[If $f, g in cal(S)$, then $integral f hat(g) = integral hat(f) g$.]

#theorem("Fourier Inversion")[
  Define the inverse Fourier transform by $ caron(f)(x) := integral e^(2pi i xi dot x) f(xi) dif xi. $ Then, if $f in cal(S)$, $(hat(f))^caron = f$.
]

#proof("(Sketch)")[
  For $epsilon > 0$ and $x in RR^n$, define $phi(xi) := e^(2pi i x dot xi - pi epsilon^2 |xi|^2)$. One can check that $phi in cal(S)$, and $hat(phi)(y) = g_epsilon (x - y)$, where $g_epsilon (z) := epsilon^(-n) g(z/epsilon)$ where $g(z) := e^(-pi |x|^2)$. In particular, one checks that $g_epsilon$ a "good kernel", i.e. $ g_epsilon convolve f ->_(epsilon -> 0) f $ for all $f in cal(S)$, where the convergence is uniform. Thus, $ integral e^(-pi epsilon^2 |xi|^2) e^(2pi i x dot xi) hat(f)(xi) dif xi integral phi(xi) hat(f)(xi) dif x = integral hat(phi)(xi) f(xi) dif x = g_epsilon convolve f(x). $ Taking $epsilon -> 0$ on both sides gives the result.
]

#theorem(
  "Plancherel",
)[The Fourier transform extends to an isometry of $L^2$ to itself, i.e. $norm(f)_2^2 = norm(hat(f))_2^2$ for all $f in cal(S)$.]

#proof("(Sketch)")[
  Define $g(x) := overline(f(-x))$, and compute $hat(g)$.
]
=== Distributions

Let $Omega subset RR^n$ open.

#definition[
  Let ${phi_j} subset C^infinity_c (Omega)$. We will say that $phi_j -> phi$ in $C^infinity_c (Omega)$ if there exists $K subset Omega$ such that $"supp"(phi_j) subset K$ for all $j$ and $partial^alpha phi_j -> partial^alpha phi$ for all multiindices $alpha$, uniformly.
]

This defines, then, a topology on the space $C^infinity_c (Omega)$.

#definition[A _distribution_ $u$ on $Omega$ is a continuous linear function on $C^infinity_c (Omega).$ I.e., $u$ continuous iff for each $phi_j -> phi$ in $C^infinity_c (Omega)$, $angle.l u, phi_j angle.r -> angle.l u, phi angle.r$, as a sequence of real numbers (where we use the bracket notation to indicate evaluation of the functional $u$ to differentiate from function evaluation).



]

We write $cal(D)' (Omega)$ or just $cal(D)'$ for the space of distributions on $cal(D)'$. We endow the space with the weak topology, i.e. a sequence $u_j in cal(D)'$ converges in $cal(D)'$ to another distribution $u in cal(D)'$ if $angle.l u_j, phi angle.r -> angle.l u, phi angle.r$ for every $phi in C^infinity_c (RR^n)$.

#example[
  1. Every $u in L_"loc"^1 (Omega)$ is naturally a distribution, by defining $angle.l u, phi angle.r := integral_(Omega) u phi$ (one can check continuity holds by DOM).
  2. The _Dirac measure_, denoted $delta$, and defined by $angle.l delta, phi angle.r = phi(0)$.
]

Next, we show a fairly natural way to extend operations on functions to act on distributions. Suppose $T : C^infinity_c -> C^infinity_c$
is continuous, and admits a "transpose" $T'$, in the sense that for any $phi, psi in C^infinity_c$, $ integral (T phi) psi = integral phi (T' psi). $ Then, the natural way to make $T$ act on distributions is by, given $u in cal(D)'$, $ angle.l T u, phi angle.r := angle.l u, T'phi angle.r. $ Then, one can verify $T: cal(D)' -> cal(D)'$ is continuous whenever $T : C^infinity_c -> C^infinity_c$ is. We discuss some particular $T$'s of interest to follow:

1. $T =$ multiplication by $f in C^infinity (Omega)$; then, $T' = T$.
2. $T = partial^alpha$; by integration by parts (boundary terms vanish since $phi$ compactly supported), $T' = (-1)^(|alpha|) partial^alpha$.
3. If $T = sum_(|alpha| <= k) a_alpha (x) partial^alpha$ some linear differential operator, one has $T' = sum_(|alpha| <= k) (-1)^(|alpha|) partial^alpha (a^alpha dot)$.

#example[The derivative of the heaviside function $H(x) := cases(0 & x < 0, 1 & x >= 0)$, as a distribution, equals the delta distribution; the $alpha$-th derivative of the $delta$  is given by $ delta^(alpha) phi = (-1)^alpha partial^alpha phi (0). $]

4. (Translation) For $x in RR^n$, define $(T phi) (y) := phi_x (y) := phi(y + x)$. One checks $T' phi(y) = phi_(-x) (y)$.
5. (Reflection) Define $(T phi) (x) := phi(-x) equiv tilde(phi).$
6. (Convolution Product) For $u in cal(D)'; psi, phi in C^infinity_c$, define $ T_psi phi = phi convolve psi. $ Then one can check $T_psi' phi = phi convolve tilde(psi)$ (one needs to apply Fubini after changing variables in the appropriate integrals). We thus define $(u convolve psi) phi = angle.l u, tilde(psi) convolve phi angle.r$. Note that we can extend this definition to convolve $u$ with $psi$ not necessarily compactly supported, but we need some additional constraint on $u$, which we'll describe here.

#definition[
  Let $u, v in cal(D)'(Omega)$.
  1. We say $u = v$ on $V subset.eq Omega$, open, if $angle.l u, phi angle.r = angle.l v, phi angle.r$ for every $phi in C^infinity_c (V)$.
  2. We define $ "supp"(u) := "complement of largest subset of" Omega "on which" u = 0, $ where "$0$" the 0 functional which acts trivially. Denote by $cal(E)' (Omega) subset.neq cal(D)'(Omega)$ the set of compactly supported distributions.
]

#example[The support of the $delta$ distribution, as one would expect, ${0}$.]

6'. For $u in cal(E)'$, $psi in C^infinity$ (not necessarily with compact support!) and $phi in C^infinity_c$, define then $ angle.l u convolve psi, phi angle.r := angle.l u, tilde(psi) convolve phi angle.r. $ Now that $u$ compactly supported, the expression on the right makes sense.

#example("Exercises")[
  1. Show $delta convolve psi = delta$
  2. Show that, given $u in cal(E)'$ and $v in cal(D)'$, we can define the convolution of $u$ with $v$ by $ angle.l u convolve v, phi angle.r := angle.l v, tilde(u) convolve phi angle.r, $ i.e. this is a continuous operation.
]

7. (Tempered Distributions) Our goal here is define the Fourier transform of distributions. Recalling the "self-adjointness" of the Fourier transform we proved for Schwartz functions (that is, $integral hat(phi) psi = integral phi hat(psi)$), a natural definition would be "$angle.l hat(u), phi angle.r = angle.l u, hat(phi) angle.r$". However, this definition does not make sense if we simply assume $phi in C^infinity_c$, since $hat(phi)$ will not generally have compact support either (indeed, one can show that $phi, hat(phi)$ both have compact support only if $phi equiv 0$, but that's besides the point), so writing $u$ as acting on $hat(phi)$ doesn't make sense, since $u$ acts on $C^infinity_c$. Thus, our idea is to enlarge our space of functions upon which admissible $u$'s will act on to $cal(S)$, and put an appropriate topology on this space which will be stronger than that we've put on $C^infinity_c$. This will remedy our issue from above since $cal(S)$ stable under Fourier transform.

More precisely, define a topology on $cal(S)$ by $ phi_j ->_(cal(S)) phi <=> sup_(x in RR^n) |x^alpha partial^beta (phi_j - phi) (x)| ->_(j->infinity) 0, wide forall alpha, beta, $ noting that this is stronger than the $C^infinity_c$ topology for such functions since taking $alpha equiv 0$ recovers the convergence requirement on that space. Then, define $ cal(S)' := {u : cal(S) -> RR | u "continuous"}. $
Then, $u in cal(S)' => u|_(C^infinity_c) in cal(D)'$.

#definition[
  For $u in cal(S)'$, denote the Fourier transform of $u$ by $hat(u)$, defined by $ angle.l hat(u), phi angle.r := angle.l u, hat(phi) angle.r, $ for $phi in cal(S)$.
]

#example[
  Show $hat(delta) = 1$; show $(partial^alpha delta)^hat = (2pi i)^(|alpha|) xi^alpha$.
]

== The Laplacian

Recall $ #boxit($ laplace := sum_(i=1)^n partial_i^2 = gradient dot gradient = "tr"(gradient^2) $) $ is the _Laplacian_ or _Laplace operator_. Functions for which $laplace u = 0$ are called _harmonic._

The Laplacian is a very symmetric operator, as we'll demonstrate more precisely.
#definition[
  We say a linear differential operator $L := sum_(|alpha| <= k) a_alpha (x) partial^alpha$ commutes with $T : RR^n -> RR^n$ if $ (L u) compose T = L(u compose T), $ for every function $u$.
]

#theorem[
  Suppose $L$ as above commutes with all translations and rotations in $RR^n$. Then, $ L = sum_(j) b_j laplace^j, wide b_j in RR, $ that is, $L$ is a polynomial in powers of $laplace$ with constant coefficients. In particular, $laplace$ generates the ring of all linear differential operators invariant under the Euclidean group.
]

#proof[
  First, we know that each $a_alpha$ coefficient must be constant, by translation. Indeed, for each index $alpha$, let $u$ be a function such $partial^alpha u = 1$, then if $T$ is a translation by $y in RR^n$, $ (a_alpha (x) partial^alpha u(x)) compose T = a_alpha (x + y), $ while $ a_(alpha) (x) partial^alpha (u compose T)= a_alpha (x), $ so $a_alpha (x) = a_alpha (x + y)$ for all $y$, implying constancy.

  Next, notice that if we take $u in cal(S)$, then $ hat(L u) (xi) = P(xi) hat(u)(xi), $ where $P(xi)$ a polynomial in $xi$, $ P(xi) = sum_(|alpha| <= k) c_alpha (2pi i xi)^(alpha), $ using properties of derivatives interacting with $hat$. But the Fourier transform also commutes with rotations, so it must be also that $P(xi)$ rotationally invariant, i.e. $ P(xi) = P(|xi|) = sum_(j) c_j (2pi i |xi|)^j. $ Moreover, we know only even powers of $j$ are admissible since $P$ still a polynomial and $|xi| = sqrt(xi_1^2 + dots + xi_n^2)$. But remark $(2pi i |xi|)^(2 j) hat(u) = hat(laplace^j u)$, thus completing the proof.
]

To further our discussion of the Laplacian, we recall some results from calculus.

#theorem("Green's Identities")[
  Let $Omega subset.eq RR^n$ have $S := partial Omega$ orientable and smooth, with outward unit normal given by $nu$. Denote the directional derivative in the direction $nu$ by $partial_nu$ and $dif sigma$ the induced surface measure on $S$. Let $u, v in C^2 (overline(Omega))$. Then,
  $
    "(G1)" & wide integral_(S) v partial_nu u dif sigma = integral_(Omega) (v laplace u - gradient u dot gradient v) dif x,\
    "(G2)" & wide integral_(S) (v partial_nu u - u partial_nu v) dif sigma = integral_(Omega) (v laplace u - u laplace v) dif x.
  $
]
#proof[
  (G2) follows from (G1) by taking swapping the roles of $u, v$ and subtracting the results. (G1) follows from the divergence theorem applied to the vector field $v gradient u$.
]

#corollary[
  If $u$ harmonic in $Omega$, then $ integral_(S) partial_nu u dif sigma = 0. $
]<cor:fluxlaplace>

#proof[
  Take $v = 1$ in (G1).
]

We denote in what follows $omega_n = (2 pi^(n\/2))/(Gamma(n\/2))$ the surface area of the unit sphere $S^(n - 1)$ in $RR^n$.


#lemma[
  Suppose $u(x) = phi(r)$ where $r = abs(x)$, i.e. $u$ is radially symmetric. If $u$ is harmonic on $RR^n minus {0}$, then $ phi(r) = cases(
    a + b r^(2 - n) & wide n >= 3,
    a + b log(r) & wide n = 2,
  ) $ for some constants $a, b$.
]

#proof[
  Applying the chain rule, one verifies that, in polar coordinates, $ laplace u(x) = phi''(r) + (n - 1)/r phi'(r). $ Indeed, this gives rise to the so-called _radial Laplacian operator_, or more nominally, the _Euler-Poisson operator (EP)_
  $
    #boxit($ (dif^2)/(dif r^2) + (n - 1)/r (dif)/(dif r). $)
  $
  This is just an ODE in $r$, which has general solution as in the lemma.
]

#theorem("Mean Value Property of Harmonic Functions")[
  Suppose $laplace u = 0$ in $Omega$ and for $x in Omega, r > 0$ sufficiently small such that $overline(B)_r (x) subset Omega$. Then, $u(x)$ is equal to the average of $u$ over the sphere of radius $r$ centered at $x$, i.e. $ u(x) = 1/(r^(n - 1) omega_n) integral_(S_r (x)) u(x + r y) dif sigma (y), $ where $S_r (x)$ the sphere of radius $r$ centered at $x$.
]<thm:mvp>

#proof[
  We assume $x = 0$ by translating if necessary (which is valid since $laplace$ invariant under translations). We prove in the case $n >= 3$, and leave the two dimensional case as an exercise. Let $Omega_epsilon := B_r (0) minus B_epsilon (0)$ with $epsilon > 0$ sufficiently small. Apply (G2) to $u$ as given and $v = phi(r)$ as in the previous lemma, normalized with $a = 0, b = 1$. Then, since both $u, v$ harmonic, the RHS of (G2) is identically zero, so we are left with $ integral_(partial Omega_epsilon) v partial_nu u - u partial_nu v dif sigma = 0. $ The outward unit normal to a sphere $S_r (0)$ is given by $y/r$, so $partial_nu = 1/r sum y_i partial/(partial y_i)$. Computing the outward unit normal of $phi(r)$, we readily see $partial_nu phi (r) = (2 - n) r^(1 -n)$ on $S_r (0)$. Now, notice that $partial Omega_epsilon = S_r (0) union S^-_epsilon (0)$ (i.e. the second component of surface has opposite orientation). Splitting the integral above along both components, we get $ integral_(S_r (0)) v partial_nu u dif sigma - integral_(S_epsilon (0)) v partial_nu u dif sigma - integral_(S_r (0))u partial_nu v dif sigma + integral_(S_epsilon (0)) u partial_nu v dif sigma. $ In the two left-most integrals, since $v$ is radially symmetric, it is constant along $S_r, S_epsilon$, so we can "pull out" $v$ from each integrals; but then since $u$ harmonic, each of these integrals is identically zero from @cor:fluxlaplace. Plugging in what we computed for $partial_nu v$ and rearranging, we find what's left gives $ (2 - n) r^(1 - n) integral_(S_r (0)) u dif sigma = (2 - n) epsilon^(1-n) integral_(S_epsilon (0)) u dif sigma. $ Dividing both sides by $omega_n$, both sides form perfect averages of $u$ over their respective domains; taking $epsilon -> 0$ on the RHS, then by continuity of $epsilon$, we have convergence to $u(0)$. What's left on the LHS is precisely what we aimed to show.
]

#corollary[
  With the same notations, hypotheses as @thm:mvp, $ n/(omega_n r^n) integral_(B_r (x)) u dif y = u(x), $ i.e. $u(x)$ is given by the average of $u$ over the _ball_ $B_r (x)$.
]

#proof[
  This follows from writing the integral over the ball as an integral over spherical shells, and applying the theorem to each shell; the remaining terms form the normalizing constant in the ball average.
]

== The Fundamental Solution to Laplace's Equation

Our goal to follow is to find a distribution $u in cal(D)'$ such that $ laplace u = delta wide "on" Omega. $


#theorem[
  The solution to the above problem is given by $ N(x) := cases(
    abs(x)^(2 - n)/(omega_(n) (2 - n)) & wide n >= 3,
    1/(2pi) log(abs(x)) & wide n = 2
  ). $
]
Note that this is the same radially symmetric function "$phi$" we saw in the previous section, with $b = 0$, $a = 1/(omega_n (2 - n))$, $1/(2pi)$ for $n >=3, n = 2$ resp.. We know this function is harmonic away from the origin, so really what we have to focus on is the blow-up at the origin.
#proof[
  We'll prove for $n >= 3$. Our idea will be to regularize $N$ by shifting the pole at the origin, take derivatives of our regularization, and show that what results converges to $delta$. For $epsilon > 0$, define $ N^epsilon (x) := (abs(x)^2 + epsilon^2)^((2 - n)/2)/(omega_n (2 - n)). $
  It's clear $N^epsilon -> N$ point-wise everywhere. Indeed, associating $N^epsilon, N$ with distributions in the typical sense (which is valid since they are both locally integrable), we have $N^epsilon -> N$ in $cal(D)'$ (one can see this by the fact that $|N^epsilon phi| <= |N| |phi|$, so we can apply dominated convergence to any test function $phi in C^infinity_c$). Next, one verifies $ laplace N^epsilon (x) = n/(omega_n) epsilon^2 (abs(x)^2 + epsilon^2)^(-(n + 2)/2). $ Let $psi(x) := n/omega_n (abs(x)^2 + 1)^(- (n + 2)/2)$; then one verifies $laplace N^epsilon (x) = psi_epsilon (x) := epsilon^(-n) psi(x/epsilon)$. Thus, for $phi in C^infinity_c$, we find $ angle.l laplace N^epsilon, phi angle.r = integral psi_epsilon (-x) phi(x) dif x = psi_epsilon convolve phi (0), $ using the radial symmetry of $psi$ to write as a reflection across the origin. By the following lemma:
  #lemma[
    Let $g in L^1$ with $a := integral g dif x$. Let $f in L^p$, $p >= 1$ (resp. $f in L^infinity$, uniformly continuous on some $V subset RR^n$). Then, $f convolve g_epsilon ->_(epsilon -> 0) a f$ in $L^p$ (resp. uniformly on $V$), where $g_epsilon (x) := epsilon^(-n) g(x/epsilon).$
  ]<lemma:goodkernel>
  Using this with $g = psi$, $f = phi$, for which clearly $f$ of the "second kind", we find that $angle.l laplace N^epsilon, phi angle.r -> a phi(0).$; so, it suffices to show that the value of $a = integral psi$ is $1$. This follows by some calculus: $ integral psi(x) dif x & = integral n/omega_n (abs(x)^2 + 1)^(-(n + 2)/2) dif x \
  & = n integral_(0)^infinity r^(n - 1)(r^2 + 1)^(- (n + 2)/2) dif r \
  & = n/2 integral_0^infinity ((r^2)/(r^2 + 1))^((n - 2)/2) (2 r)/(r^2 + 1)^2 dif r, wide s := r^2/(r^2 + 1) \
  &= n/2 integral_(0)^1 s^((n - 2)/2) dif s = 1. $
]

#theorem("Maximum Principle")[
  Let $Omega subset RR^n$ open and connected. Suppose $u$ is harmonic in $Omega$, and $sup_Omega u = A < infinity$. Then, either
  - $u(x) < A$ everywhere on $Omega$, or
  - $u(x) = A$ everywhere on $Omega$.
]

#proof[
  Let $S = {x in Omega | u(x) = A}$. We'll show that $S$ is both open and closed, from which it follows that $S = Omega$ or $nothing$, since $Omega$ connected, and thus the theorem follows. $S$ clearly closed, since it is equal to $u^(-1)({A})$ and $u$ continuous. For openness, let $x in S$, so $u(x) = A$. We want to show that there exists a ball $B$ centered at $x$ such that $u(x) = u(y) = A$ for all $y in B$. Suppose otherwise, that no such ball exists. Then in particular, there exists a sufficiently small $r > 0$ for which $u$ remains strictly less than $A$ on all of $B(x, r)$. But then, by the mean-value property, $ A = u(x) = n/(omega_n r^n) integral_(B(x, r)) u(y) dif y > A n/(omega_n r^n) integral_(B(x, r)) dif y = A, $ a contradiction. Thus, there exists a ball $A$ on which $u$ is constantly equal to $A$, thus $B subset S$, and so $S$ also open.
]

#corollary[With the same assumptions, suppose further $overline(Omega)$ compact, and $u$ is continuous up on $overline(Omega)$. Then, $max_(overline(Omega)) u = max_(x in partial Omega) u$.]

#corollary[Suppose $overline(Omega)$ compact and $u_1, u_2$ are harmonic and equal on $partial Omega$. Then $u_1, u_2$ are equal on all of $Omega$.]

#theorem("Liouville's")[
  If $u$ is harmonic and bounded on all of $RR^n$, then $u$ is constant.
]

#proof[
  Let $x in RR^n$ and $R > norm(x)$. By the mean-value property, $ abs(u(x) - u(0)) &= n/(R^n omega_n) abs(integral_(B(x, r)) u(y) dif y - integral_(B(0, r)) u(y) dif y) <= n/(R^n omega_n) norm(u)_infinity "vol"(D), $ where $D := B(x, R) triangle.t B(0, R)$. One verifies that $ D subset {y | R - abs(x) < abs(y) < R + abs(x)}, $ and thus $ "vol"(D) <= omega_n/n ((R + abs(x))^n - (R - abs(x))^n) = cal(O)(R^(n-1)). $ Thus, it follows that $ abs(u(x) - u(0)) <= c dot norm(u)_infinity/(R), $ where $c$ some constant independent of $R$. Thus, letting $R -> infinity$, we find that it must be that $u(x) = u(0)$, and since this holds for all $x$, $u$ must be constant.
]

== Dirichlet and Neumann Problems

#let D = $#rect("D", inset: 0.2em)$
#let N = $#rect("N", inset: 0.2em)$
#let box(a) = $#rect(a, inset: 0.2em)$

We assume that $Omega subset RR^n$ bounded and $S = partial Omega$ is $C^infinity$ (and sufficiently nice to be able to apply Green's identities). We consider the _Dirichlet problem_, $ #rect("D", inset: 0.2em) wide laplace u = f "on" Omega, u|_S = g, $ where $f, g$ are given functions, and the _Neumann problem_, $ #rect("N", inset: 0.2em) wide laplace u = f "on" Omega, u|_S = partial_nu g, $ where $nu$ the exterior outward normal to $S$.

#remark[If #D has a solution it must be unique (if two solutions exist, their difference solves the equation $laplace u = 0, u|_S = 0$ which implies by the maximum principle $u =0$).]

#remark[Solutions to #N are not unique, for any solution plus a constant is another solution. Moreover, solutions do not exist for arbitrary $f, g$; applying Green's identities, we find that (we assume that $Omega$ connected, but this work applies to any connected component of $Omega$) $ integral_Omega f dif x = integral_Omega laplace u dif x = integral_(S) partial_nu u dif sigma = integral_(S) g dif sigma, $ and thus $f$, $g$ must obey the integral identity that $integral_Omega f dif x = integral_S g dif sigma$.]

We can reduce the study of #D to one of the following related problems, where we take either $f$ or $g$ identically zero (a similar reasoning works for #N, but we restrict our attention to the Dirichlet problem here), $ #box("D1")wide laplace v = f, v|_S = 0, wide wide #box("D2") wide laplace w = 0, v|_S = g. $

Indeed, if $v, w$ solve #box("D1"), #box("D2") resp., then $u = v + w$ solves #D. Moreover, it turns out that the two are essentially equivalent.

Suppose we can solve #box("D1"), and suppose $g$ has a $C^2$-extension $tilde(g)$ to $overline(Omega)$. Then, let $v$ solve $ laplace v = laplace tilde(g), v|_S = 0. $ Then, one checks $w = tilde(g) - v$ solves #box("D2").

Conversely, suppose we can solve #box("D2"). Extend $f$ to be identically zero outside of $Omega$, and let $v' = f convolve N$, where $N$ the fundamental solution to the Laplacian we found earlier. Let $w$ solve $ laplace w = 0, w|_(S) = v', $ and let $v = v' - w$. Then, $ laplace v = laplace v' - laplace w = f convolve laplace N = f, $ since $laplace N = delta$ in the sense of distributions. Also, $v|_S = v'|_S - w|_(S) = v' - v' = 0$.

== Green's Function for the Laplacian

We assume throughout $n >= 3$ for simplicity of notation. We abuse notation to write $N(x, y) := N(x - y)$.

#definition("Green's Functions")[
  A function $G: Omega times overline(Omega) -> RR$ is called a _Green's function_ for $laplace$ on $Omega$ if
  1. $G(x, dot) - N(x, dot)$ harmonic on $Omega$ for all $x$, and $C^0$ on $overline(Omega)$, and
  2. $G(x, y) = 0$ for all $x in Omega, y in S$.
]

#remark[If $G$ exists, it is unique, for it solves the Dirichlet problem $laplace_y w (y) = 0$, $w|_S (y) = - N(x, y)$ for every $x in Omega$.]

#theorem[If $Omega$ bounded and $S$ smooth, then $G$ exists, and for all $x in Omega$, $G$ is $C^infinity (Omega minus {x})$ as a function of $y$.]

#proposition[$G(x, y) = G(y, x)$.]

#proof[
  For $x, y in Omega$, define $ u(z)= G(x, z), wide v(z) = G(y, z). $ One checks $laplace_z u = delta(x - z), laplace_z v = delta(y - z)$; applying Green's identities (which we only do formally, but can be made rigorous through proper treatment of the distributions implicitly being used), $ G(x, y) - G(y, x) & = integral_(Omega) G(x, z) delta(y - z) - G(y, z) delta(x - z) dif z \
                    & = integral_S G(x, z) partial_nu_z G(y, z) - G(y, z) partial_(nu_z) G(x, z) dif z = 0, $ appealing to 2. in the definition of Green's functions for the final line.
]

Now, assume $G$ exists for some $Omega$, and consider again #box("D1"). Extend $G$ to $overline(Omega) times overline(Omega)$ to be zero on $partial Omega times Omega$, and extend $f$ to be zero outside of $Omega$. We claim that $ v(x) := integral_(Omega) G(x, y) f(y) dif y $ solves #box("D1"). Indeed, we may rewrite $ v(x) = integral_(Omega) N(x - y) f(y) dif y + integral_(Omega) [G(x, y) - N(x, y)] f(y) dif y, $ so $ laplace v(x) = f convolve laplace N + integral_Omega (underbrace(laplace_x (G - N), = 0)) f dif y=f convolve delta(x) = f(x), $ and clearly $v(x) = 0$ whenever $x in partial Omega$.

A similar formula holds for #box("D2"), indeed $ w(x) = integral_S g(y) partial_(nu_y) G(x, y) dif y. $
This can be shown using the previous integral formula and the remarks of the previous section linking solutions of #box("D1") and #box("D2"). The function $partial_nu_y G(x, y)$ is called the _Poisson kernel_ of $Omega$.

=== Green's Function for the Half-Space
We let $ RR^(n+1)_+ := {(x, t) : x in RR^n, t > 0} $ denote the half-space in $RR^(n + 1)$, where we note $partial RR^(n+1)_+ = RR^(n+1) times {0}$ and where we will distinguish coordinates as $(x, t) in RR^n times RR_+$. We will show that $ G((x, t), (y, s)) := N(x - y, t - s) - N(x - y, -t - s) $ is a Green's function for $RR^(n+1)_+$. Indeed, its easy to see that $G$ harmonic in $x$, since it is a sum of harmonic functions in $x$, and also $ G((x, t), (y, 0)) = N(x - y, t) - N(x - y, -t) = 0, $ so the two properties of a Green's function are fulfilled. Indeed, one readily checks that $ u(x, t) := integral_0^infinity integral_(RR^n) G((x, t), (y, s)) f(y, s) dif y dif s $ solves the Dirichlet problem #box("D1").

For the #box("D2"), we know that the outer normal derivative of $RR^(n+1)_+$ is just $- s$, and we readily compute $ - partial_s G((x, t), (y, s))thin #line(angle: 90deg, length: 2em) _(thin s = 0) = (2t)/(omega_(n + 1)) 1/(|x - y|^2 + t^2)^((n + 1)/2), $ which gives as candidate solution to #box("D2") $ u(x, t) = integral_(RR^(n)) (2 t)/(omega_(n + 1) (|x - y|^2 + t^2)^((n + 1)/2)) g(y) dif y, $ which we notice can be written as the convolution product $g convolve P_t (x)$, where $P_t (x) := (2t)/(omega_(n + 1) (|x|^2 + t^2)^((n + 1)/2))$.

#theorem[
  Suppose $g in L^p (RR^n)$, $1 <= p <= infinity$. Then $u(x, t) = g convolve P_t (x)$ is well-defined and harmonic in $Omega = RR^(n + 1)_+$. Further, if $g$ continuous and bounded, then $u$ is continuous on all of $overline(RR^(n+1)_+)$, and $u(x, 0) = g(x)$. If $g$ simply in $L^p$ for $1 <= p < infinity$, then $u(dot, t) -> g$ in $L^p$ as $t -> 0$.
]

#proof[
  One readily checks $P_t in L^q$ for all $1 <= q<= infinity$, which implies $g convolve P_t$ absolutely convergent; this moreover also holds by applying $laplace_x, partial_t^2$ under the integral sign, since this will only make the integral decay faster. Hence, since $G$ harmonic, it follows that $ (laplace_x + partial_t^2)u = g convolve (laplace_x + partial_t^2) P_t = 0, $ and so we indeed have a solution.

  For the boundary behaviour, notice that $P_t (x) = t^(-n) P_1 (x/t)$, and so we are in position to apply @lemma:goodkernel (which directly implies the remaining results), assuming $integral P_1 (x) dif x = 1$, which we check: $ integral P_1 (x) dif x & = 2/(omega_(n + 1)) integral_0^infinity r^(n - 1)/(r^2 + 1)^((n + 1)/2) dif r \
                         & = 1/(pi^(1/2)) (Gamma((n + 1)/2))/(Gamma(n/2)) integral_(0)^1 s^(n/2 - 1) (1 - s)^(-1/2) dif s \
                         & = 1/(Gamma(1/2)) (Gamma((n + 1)/2))/(Gamma(n/2)) B(n/2, 1/2) = 1, $  where $B$ the Beta function, and the final simplification follows from the identity $B(s, t) = (Gamma(s) Gamma(t))/(Gamma(s + t))$.
]

#remark[This certainly does not prove uniqueness of solutions; indeed, adding $c t$ to $u$ for any constant $c$ gives another solution to #box("D2"). However, this does not contradict our earlier uniqueness theorem since $Omega$ is not bounded. However, we can sometimes guarantee uniqueness.]

#theorem[
  If $g$ continuous and vanishes at $infinity$ in $RR^(n+1)_+$, then $g convolve P_t$ is the unique solution to $#box("D2")$, and tends to zero at $infinity$ as well.
]

#proof[
  We prove first if $g$ compactly supported, then conclude for general $g$ by an approximation argument.

  Let $g$ have compact support, i.e. $g = 0$ if $|x| > a$. In particular, then, $g in L^1$, so by Young's inequality, $ norm(g convolve P_t)_infinity <= norm(g)_1 norm(P_t)_infinity <= C t^(-n), $ where $C$ some (clearly independent of $x$) constant and the final upper bound follows by direct inspection of $P_t$; thus, we see $g convolve P_t -> 0$ uniformly as $t -> 0$. This proves the result in the $t$ direction. For $0 <= t <= R$ and $|x| >2 a$, say, we see $ |u(x, t)| <= norm(g)_1 sup_(|y| < a) |P_t (x - y)| <= C R |x|^(- n - 1) ->_(|x| -> infinity) 0, $ again by inspection of $P_t$. This proves the result for $g$ compact.

  For general $g in C^0$ vanishing at infinity, choose a sequence ${g_n}$ of compactly supporting functions converging uniformly to $g$. Let $u_n := g_n convolve P_t$, which we know by the previous paragraph vanishes at infinity in $overline(Omega)$. Furthermore, $ underbrace(norm(u_n - u)_infinity, "norm in" Omega) <= sup_t underbrace(norm((g_n - g) convolve P_t)_infinity, "norm in" RR^n) <= sup_t norm(g_n - g)_infinity underbrace(norm(P_t)_1, = 1) = norm(g_n - g)_infinity ->_n 0. $

  To prove uniqueness, apply the maximum principle to $w = v - u$ for any two solutions $v, u$, and on rectangles of the form ${|x| < R, |t| < t_0}$. We have uniqueness in each rectangle, from which, by "growing the rectangles to infinity", we can conclude global uniqueness (in $Omega$). We leave the details as an exercise.
]

=== Green's Function for the Unit Ball

Put $Omega = B = B_1 (0), S = partial B = S_1 (0)$. We will analogously construct a Green's function for the Laplacian on $Omega$ by imagining a point charge "inverted" outside the sphere for each $x in Omega$. First, an algebraic lemma;

#lemma[
  For $x, y in RR^n$, $x eq.not 0$ and $|y| = 1$, $|x - y| = ||x|^(-1) x - |x| y|$.
]

#proof[
  $
    |x - y|^2 & = (x - y) dot (x - y) \
              & = |x|^2 - 2 x dot y - underbrace(|y|^2, = 1) \
              & = ||x| y|^2 - 2 (|x|^(-1) x) dot (|x| y) + ||x|^(-1) x|^2 \
              & = ||x|^(-1) x - |x| y|^2.
  $
]

Recall $N(x) = (|x|^(2-n))/(omega_n (2 - n))$. Define $ G(x, y) = N(x - y) - |x|^(2 -n) N (x/(|x|^2) - y), $  which one readily sees simplifies to $ G(x, y) = 1/(omega_n (2 - n)) [ |x - y|^(2 - n) - |x/(|x|) - |x| y|^(2 -n)]. $
From the lemma, we automatically have $G(x, y) = 0$ for any $y in S$, for then $|y| = 1$. Moreover, it's clear that $G(x, y) - N(x, y)$ harmonic, as long as $y eq.not x/(|x|^2)$, so this indeed a Green's function.

We compute next the Poisson's kernel; the outward normal vector to $Omega$ is just $y$, so we compute, for $y in S$, $ P(x, y) = partial_(y) G(x, y) & = y dot gradient_y G(x, y) \
                              & = - 1/(omega_n)[ (y dot (x - y))/(|x-y|^n) - (y dot (x - |x|^2 y))/(|x - y|^n) ] \
                              & = 1/omega_n (1 - |x|^2)/(|x - y|^n). $

#theorem[If $f in L^1(S)$ with $P$ as given, then $u(x) = integral_(S) P(x, y) f(y) dif sigma(y)$ is harmonic in $B_1(0)$.

  If $f in C^0$, $u$ extends continuously to $overline(B_1(0))$ and $u|_S = f$. If $f in L^p$, then $u_r := u(r dot) ->^(r->1^-)_(L^p) f$ (i.e., $u$ converges to $f$ along "rays" to the boundary).
]

#proof[
  We first claim the following: $ (ast) wide integral_S P(x, y) dif sigma (y) = 1 quad forall x in B \
  (ast ast) wide lim_(r arrow.t 1) integral_(S\\V) P(r y_0, y) dif sigma(y) = 0, quad forall y_0 in S, V subset.eq S "nbhd of" y_0. $ $(ast)$ follows from the fact that $P(x, y)$ harmonic in $x$, so by the mean-value theorem, $ integral_(S) P(x, y) dif sigma(y) = omega_n P(0, y) = 1, $ by direction computation. For $(ast ast)$, note that $ P(r y_0, y) = (1 - r^2|y_0|^2)/(|r y_0 - y|^n). $ Since $y in S\\V$, $|y - y_0|$ bounded away by zero uniformly in $y$, say, $|y - y_0| > delta > 0$. Then, $ abs(r y_0 - y) >= abs(abs(y_0 - y) - |r y - y|) = |y_0 - y| + r - 1 > delta + r - 1. $ Thus, $ P(r y_0, y) <= (1 - r^2)/(delta + r - 1) ->_(r arrow.t 1) 0. $ We can pass the limit under the integral by DOM, since $S$ compact, which gives the result. Moreover, note that this limit was independent of $y_0$ and depended only on the quantity $delta$.

  With this in place, suppose first $f in C^0$, so since $S$ compact, $f$ uniformly continuous, hence for all $epsilon > 0$ there exists a $delta > 0$ such that $|x - y| < delta => |f(x) - f(y)| < epsilon$. Let $V_x := {y in S | |y - x| < delta}$. Then, using $(star)$, we can bring functions independent of $y$ under the integral premultiplied by $P(x, y)$  for free, hence for any $x in S, 0 < r< 1$, $ |f(x) - u_r (x)| & = |integral_S P(r x, y) [f(x) - f(y)] dif sigma(y)| \
  & <= abs(integral_(V_x) P(r x, y) underbrace(|f(x) - f(y)|, < epsilon) dif sigma(y)) + 2 norm(f)_infinity integral_(S\\V_x) P(r x, y) dif sigma(y) \
  &<= epsilon + 2 norm(f)_infinity integral_(S\\V_x) P(r x, y) dif sigma(y). $ By $(ast ast)$, the last integral $-> 0$ as $r -> 1$. But recall that we showed that this limit was uniform in choice of $x$, and only depends on the size of the neighborhood $V_x$. But this was chosen by construction to be $delta$, so we can bound this latter term by $epsilon$ by taking $r$ sufficiently large, with such a choice independent of $x$. Thus, we've shown $u_r -> f$ uniformly, and since each $u_r$ continuous, $f$ must be continuous as well.

  Next, suppose $f in L^p$. We'll proceed by an approximation argument by a continuous function, appealing to the previous case, and then tying everything together with generalized Youngs. Let $epsilon > 0$ and $g in C^0 (S)$ with $norm(f - g)_p <= epsilon/3$, and define $ v(x) := integral_S P(x, y) g(y) dif sigma(y). $ Then, we see that for $r$ sufficiently small, $ norm(f - u_r)_p & <= norm(f - g)_p + norm(g - v_r)_p + norm(v_r - u_r)_p \
                  & < epsilon/3 + epsilon/3 + norm(v_r - u_r)_p, $ with the first bound clear, the second following from the previous case (uniform convergence on a compact set implies convergence in $L^p$). For the last, notice that we may write $ v_r (x) - u_r (x) & = integral P(r x, y) (f(y) - g(y)) dif y. $ The kernel $(x, y) |-> P(r x, y)$ satisfies the criteria of Young's generalized inequality for the measure space $(B, sigma)$, by $(ast ast)$ and the symmetry of the Green's function., with constant $C = 1$. Thus, we know that $norm(v_r - u_r)_p <= norm(f - g)_p <= epsilon/3$, so we are done.
]

== A Short Introduction to the Dirichlet Principle

Let $Omega$ bounded, $S = partial Omega$ smooth, $u : Omega -> CC$, $u in C^1 (overline(Omega))$, and define the Dirichlet Hermitian product $ D(u, v) := integral_Omega gradient u dot overline(gradient v) dif x. $ This defines a semi-norm $D(u, u)$ (for any constant function has semi-norm 0). However, the following is a norm: $ norm(u)_((1)) := norm(u)_(H_1 (Omega)) := (D(u, u) + norm(u)_2^2)^(1/2). $  Define the space $H_1 (Omega)$ as the completion of $C^1 (overline(Omega))$ under this norm.

#proposition[
  $H_1 (Omega)$ is complete, and is the subspace of $L^2 (Omega)$ consisting of functions who's distributional derivatives are in $L^2$.
]

#proposition[
  There exists a $C > 0$, depending on $Omega$, such that $ integral_S abs(u)^2 dif sigma <= C norm(u)_((1))^2, $ for all $u in C^1 (overline(Omega))$.
]
As a direct corollary of this, this implies that functions in $H_1 (Omega)$ have well-defined boundary values on $S$, and are in $L^2 (S)$.

#proof[
  #table(
    stroke: 0pt,
    columns: 2,
    [Denote by $nu$ the exterior normal of $S$. Let us extend $nu$ to a constant vector field within a small neighborhood of $S$ within $Omega$, and multiply it by a cut-off function such that it is extended to a (bounded) vector field on all of $Omega$.],
    [
      #image("pdesvectorfield.png", width: 40%)
    ],
  )


  By the divergence theorem, we may write $ integral_S abs(u)^2 dif sigma &= integral_S abs(u)^2 nu dot nu dif sigma \
  &= integral_Omega sum_(j=1)^n (partial_j abs(u)^2 nu_j) dif x \
  &<= sum_(j) integral_Omega [ |u partial_j overline(u) nu_j| + |overline(u) partial_j u nu_j| + abs(u)^2 abs(partial_j nu_j)] dif x \
  &<= C' sum_(j) integral_(Omega) [ |u partial_j overline(u)| + |overline(u) partial_j u| + abs(u)^2 abs(partial_j)] , wide C' := sup_(Omega) sum_(j=1)^n (abs(nu_j) + abs(partial_j nu_j)) \
  "(Cauchy-Schwarz)"quad &<= C' [sum_(j=1)^n 2 norm(u)_2 norm(partial_j u)_2 + n norm(u)_2^2 ] \
  "(AM-GM)" quad &<= 2n C' norm(u)_2^2 + C' sum_(j=1)^n integral_Omega abs(partial_j u)^2 dif x \
  &= 2n C' norm(u)^2_2 + C' D(u, u), $ hence taking $C = 2 n C'$ gives the result.
]

#definition[We further define $H_1^0 (Omega)$ to be the closure of $C_c^infinity (Omega)$ in $H_1 (Omega)$, so in particular, $f in H_1^0 (Omega) => f|_S equiv 0$ (the converse is _not_ true).]

Note that the kernel of $D(u, v)$ is the set of locally constant functions; if we mod out by this kernel, we get a complete normed space under $sqrt(D(dot, dot))$, namely $ H_1 (Omega)\/{"loc. constant functions"} $ is a Banach space.

We can now restate the Dirichlet problem in the context of the function spaces we've introduced. Let $g$ be a function on $S$ which is the restriction to $S$ of some function $f H_1 (Omega)$. Then, the Dirichlet problem can be formulated by finding $w$ such that $w$ is harmonic in $Omega$ and $w - f$ is in $H_1^0 (Omega)$ (namely, $(w - f)|_S equiv 0$, so $w, f$ are equal on $S$).

#theorem[
  Suppose $w in H_1 (Omega)$. Then $w$ is harmonic in $Omega$ iff it is orthogonal to $H_1^0 (Omega)$ with respect to $D(dot, dot)$.
]

#proof[
  By one of Green's identities, for $w in C^1 (overline(Omega))$ and $v in C^infinity_c (Omega)$, $ integral_(Omega) w overline(laplace v) dif x = - integral_Omega nabla w dot overline(nabla v) dif x = - D(w, v). $ Using the fact that $C^1 (overline(Omega))$ dense in $H_1 (Omega)$ and passing limits under integrals (which is fine since $v$ compactly supported), we conclude the same statement for general $w in H_1 (Omega)$. Using the other Green's identity, we can swap the Laplacian on the first term and find that $ integral_Omega laplace w overline(v) dif x = - D(w, v). $
  In particular, $laplace w = 0$ in the distributional sense iff $D(w, v) = 0$ for all $v in C^infinity_c (Omega)$.
  #lemma[
    $laplace$ is _hypo-elliptic_, i.e. if $laplace T in C^infinity$ for $T in cal(D)' (Omega)$, then $T$ is $C^infinity$.
  ]
  Using now that $H^0_1 (Omega)$ is the closure of $C^infinity_c (Omega)$ in $H_1 (Omega)$, and the lemma, which we won't prove, we can conclude by taking limits that $w$ harmonic in $Omega$ iff $D(w, v) = 0$ for all $v in H_1^0 (Omega)$.
]

#corollary[
  $ H_1 (Omega)\/{"loc. constant functions"} = "Harm"(Omega) plus.circle H_1^0 (Omega), $ under $D(dot, dot)$, where $"Harm"(Omega)$ the space of harmonic functions in $H_1 (Omega)$ (mod loc. constant functions).
]

Thus, to solve the Dirichlet problem as stated is equivalent to projecting $f$ onto the space $"Harm"(Omega)$.

= The Wave Equation

== The Cauchy Problem - Uniqueness

We study the non-elliptic linear operator $ square u = partial_t^2 u - laplace_x u, $ where $u = u(x, t)$ and $square$ is called the _D'Alembertian operator_, or simply "box". The general Cauchy problem we will study is $ cases(
  square u = 0,
  u(x, 0) = f(x)\, u_t (x, 0) = g(x)
), $ for $x in RR^n$ and $0 <= t <= T$. Notice that $square$ is invariant under time reflection, so there is no loss of generality in restricting to studying $t >= 0$.

For $n = 1$, one checks that a solution, for sufficiently nice $f, g$ is given by $ u(x, t) = 1/2 (f(x + t) + f(x - t)) + 1/2 integral_(x + t)^(x - t) g(z) dif z. $
For $n >= 2$, we also have such solution representations, but they have more complicated formulations, which we will discuss later.

First, we present a uniqueness theorem for general dimensions.

#theorem[
  Suppose $u in C^2$ for $0 <= t <= T$, $x in RR^n$. Suppose $u = 0 = partial_t u$ on the "ball" $ B = {(x, 0) | |x - x_0| <= t_0}, $ for some $t_0 in [0, T]$.
  #table(
    stroke: none,
    columns: 2,
    [Then, if $square u = 0$, then $u = 0$ in the region $ Omega := {(x, t) | #stack(spacing: 1em, $0 <= t <= t_0,$, $|x - x_0| <= t_0 - t$)}, $ which is a cone of height $t_0$ and circular base given by $B$ (see right).],
    [#image("cone.png", width: 90%)],
  )
  // TODO I can make this image better...
]

#proof[
  For $0 <= t <= t_0$, define $ B(t) := {x | |x - x_0| <= t_0 - t},\
  E(t) := 1/2 integral_(B_t) [((partial u)/(partial t))^2 + |gradient_x u|^2] dif x. $
  Remark that $E(t) >= 0$. Let us compute $(dif E)/(dif t)$ assuming $square u = 0$. Everything is sufficiently nice for us to take derivatives under the integral sign, so we find $ (dif E)/(dif t) = integral_(B_t) (partial u)/(partial t) (partial^2 u)/(partial t^2) + sum_j (partial u)/(partial x_j) (partial^2 u)/(partial t partial x_j) dif t - 1/2 integral_(partial B_t) |gradient_(x, t) u|^2 dif sigma. $ We can integrate by parts and apply the divergence theorem, to conclude $ (dif E)/(dif t) &= integral_(B_t) (partial u)/(partial t) underbrace([(partial^2 u)/(partial t^2) - sum_j (partial^2 u)/(partial x_j^2)], = square u = 0) dif x\
  & wide + integral_(partial B_t) sum_j (partial u)/(partial x_j) (partial u)/(partial t) nu_j dif sigma \
  & wide - 1/2 integral_(partial B_t) |gradient_(x, t) u|^2 dif sigma. \
  &= integral_(partial B_t) sum_j (partial u)/(partial x_j) (partial u)/(partial t) nu_j dif sigma - 1/2 integral_(partial B_t) |gradient_(x, t) u|^2 dif sigma. $ We can bound the integrand in the first integral by Cauchy-Schwarz followed by AM-GM, using $|nu| = 1$: $ sum_j (partial u)/(partial x_j) (partial u)/(partial t) nu_j <= |(partial u)/(partial t)| (sum_j ((partial u)/(partial x_j))^2)^(1/2) |nu| <= 1/2 (abs((partial u)/(partial t))^2 + sum_j abs((partial u)/(partial x_j))^2) = 1/2 |gradient_(x, t) u|^2. $ But this is precisely the integrand of the second remaining integral, from which we find $(dif E)/(dif t) <= 0$. But one sees that $E(0) = 0$ and $E(t) >= 0$, so it must be that $E(t)$ identically 0 for all $t in [0, t_0]$. Again, the integrand in $E(t)$ is positive, so it follows that $gradient_(x, t) u = 0$ over for $x in B_t$ for each $t in [0, t_0]$, hence $u$ a constant, thus equal to the initial Cauchy data of 0; we see that $Omega = union.big_(t = 0)^(t_0) B_t times {t}$, so we are done.
]

#remark[
  If we consider the time-rescaled equation $c^2 partial_t^2 u - laplace_x u = 0$, we obtain similar results, with the slope of the cone $Omega$ being $c$.
]

#remark[
  This theorem says then that if initial data is given on $B$, then this information will "propagate" throughout the cone $Omega$, at finite speed. In particular, if we specify additional data outside of the ball $B$, the function $u$ will not "see" this data while within the cone $Omega$.
]

== Solution of the Cauchy Problem via Spherical Means

Our goal to follow is to find a closed-form solution for the solution to the equation $ cases(
  square u = 0,
  u(x, 0) = f(x)\, quad partial_t u (x, 0) = g(x)
), $ where $f, g$ are of a certain regularity class that we will determine in our work, and with spatial dimension $n >= 2$. The idea will be to transform the purported solution $u$ via a series of differential, integral operators; the resulting equation will obey, in a sense, the 1-dimensional wave equation. From there, we can simplify and achieve a closed form of the solution $u$ in terms of the initial datum $f, g$ by appealing to d'Alembert's formula in 1 dimension.

#definition("Spherical Mean Operator")[
  For $phi$ on $RR^n$, define $ M_phi (x, r) := 1/(r^(n - 1) omega_n) integral_(|z - x| = r) phi(z) dif sigma (z) = 1/(omega_n) integral_(|y| = 1) phi(x + r y) dif sigma(y). $
]

#remark[
  The second formulation is still valid for negative $r$; in particular, we see that $M_phi (x, r)$ even in $r$, i.e. $M_phi (x, r) = M_phi (x, -r)$. In addition, it's easy to check that $M_phi (x, 0) = phi(x)$, and $phi in C^k => M_phi (dot, r) in C^k$ (by direct computation, dominated convergence resp.).
]

We recall the Euler-Poisson (EP) operator; given $u(x) = phi(r)$ for $r = |x|$, then $ laplace u(x) = [dif^2/(dif r^2) + (n - 1)/r (dif)/(dif r)] phi (r), $ the bracketed term being the EP operator in question.

#proposition[
  For $phi in C^2$, $laplace_x M_phi = [dif^2/(dif r^2) + (n - 1)/r (dif)/(dif r)] M_phi$.
]

#proof[
  Differentiating under the integral sign and applying the divergence theorem, we find that
  $ partial_r M_phi & = 1/(omega_n) integral_(|y| = 1) sum_(i=1)^n y^i partial_(y_i) phi(x + r y) dif sigma(y) \
  & = 1/(omega_n) integral_(|y| <= 1) r dot laplace_y phi(x + r y) dif y = 1/(r^(n-1) omega_n) integral_(|z| <= r) laplace phi(x + z) dif z. $ Thus, passing to hyperspherical coordinates, $ r^(n - 1) partial_r M_phi = 1/(omega_n) integral_0^r integral_(|y| = 1) laplace phi(x + rho y) rho^(n - 1) dif sigma(y) dif rho. $ Taking an additional derivative of this expression in $r$ then 'kills' the other integral by FTC, and what remains is $ partial_r (r^(n - 1) partial_r M_phi ) = r^(n-1) laplace M_phi (x, r). $ But the LHS is also equal to $(n - 1) r^(n - 2) partial_r M_phi + r^(n - 1) partial_r M_phi$; simplifying this equation gives the result.
]

#corollary[
  Suppose $u in C^2$ on $RR^n times RR$, and let $M_u (x, r, t)$ be the spherical mean of $u$ in $x$ with $t$ fixed. Then, $ square u = 0 => (partial_r^2 + (n - 1)/r partial_r) M_u (x, r, t) = partial_t^2 M_u (x, r, t). $
]<cor:squareimpliesepeqpartialt>

#remark[
  The expression here is _almost_ a wave equation in 1D, treating $r$ as a new spatial variable, if it wasn't for that pesky first derivative in $r$ term. We'll proceed now to apply an operator to $M_u$ to get rid of this term. Namely, introduce a differential operator $T = T_k$ with the property that $partial_r^2 T M_u = partial_t^2 T M_u$.
]

#lemma[
  If $k >= 1$ and $phi in C^(k + 1) (RR)$, $ partial_r^2 (r^(-1) partial_r)^(k - 1) [r^(2k - 1) phi(r)] = (r^(-1) partial_r)^(k) [r^(2k) phi'(r)]. $
]<lem:annoyingsquareexp>

Remark that the RHS here can be written as $ (r^(-1) partial_r)^(k -1) [2 r^(2k - 2) phi'(r) + r^(2k - 1) phi''(r)], $ which looks a lot like the EP operator up to scaling by $r$. With this as motivation, define, for $k >= 1$, $ T_k phi(r) := (r^(-1) partial_r)^(k - 1) [r^(2k - 1) phi(r)], $ so that @lem:annoyingsquareexp reads $partial_r^2 T_k phi = T_k [phi'' + (2k)/r phi']$. Thus, remark that if we could pick $k$ such that $2k = n - 1$, we'd be in business; of course, this is only possible when $n$ is odd; this represents a dichotomy in our solution approach. For the remainder we assume that $n = 2k + 1$ is an odd space dimension.

Combining @lem:annoyingsquareexp and @cor:squareimpliesepeqpartialt, then, yields the equation $ partial_t^2 T_k M_u - partial_r^2 T_k M_u = 0, $ namely, a 1D wave equation for the expression $T_k M_u$, which we know how to solve. In what proceeds, we demonstrate how we can simplify this expression to get a closed-form for $u$ itself, and moreover show that what results is actually a solution to the $n$ dimensional wave equation.

#lemma[
  $T_k phi = sum_(j=0)^(k - 1) c_j r^(j + 1) phi^((j)) (r)$, for some constants $c_j$, with in particular $ c_0 = (2k - 1) (2 k - 3) dots.c 3 dot 1. $
]<lem:Tkexpansion>
#proof[
  Follows from direct computation.
]

Putting now $tilde(u) = T_((n - 1)/2) M_u$, then we find that $tilde(u)(x, r, 0) = tilde(f)(x, r) := T_((n-1)/2) M_f$ and $partial_t tilde(u)(x, r, 0) = tilde(g)(x, r) := T_((n-1)/2) M_g$ to have a fully-defined Cauchy problem for $tilde(u)$ in the $(r, t)$ variables. By D'Alembert's, $ tilde(u)(x, r, t) = 1/2 [tilde(f)(x, r + t) + tilde(f)(x, r - t)] + 1/2 integral_(r-t)^(r + t) tilde(g)(x, s) dif s. $

#lemma[
  $u(x, t) = lim_(r -> 0) (tilde(u)(x, r, t))/(c_0 r)$.
]<lem:limitofusquare>
#proof[
  By @lem:Tkexpansion, $tilde(u) = c_0 r M_u + c_1 r^2 M'_u + dots.c = c_0 r M_u + cal(O)(r^2)$. But also, we know that $u(x, t) = M_u (x, 0, t)$, so that dividing both sides of $tilde(u)$ by $c_0 r$ and sending $r -> 0$, everything vanishes except the $cal(O)(r)$ term, which is equal to $M_u (x, 0, t) = u(x, t)$.
]
Next, we compute the RHS in this lemma by L'Hopital's and the expression we have above by D'Alembert's.

First, recall that $M_phi (x, r)$ even in $r$, so $ tilde(f) = T_((n - 1)/2) M_f = underbrace((r^(-1) partial_r)^(k -1), "even in" r) [underbrace(r^(2k - 1), "odd in" r) underbrace(M_f, "even in" r)], $ which we see $tilde(f)$ odd in $r$; hence, in particular, $partial_r tilde(f)$ even in $r$. Similarly, we see that $tilde(g)$ is odd in $r$. Thus, combining the lemma, our formula, and expanding definitions $ u(x, t) &= lim_(r -> 0) 1/(2 c_0 r) 1/2 [tilde(f)(x, r + t) + tilde(f)(x, r - t)] + 1/2 integral_(r-t)^(r + t) tilde(g)(x, s) dif s \
&= 1/(2c_0) [partial_r tilde(f)(x, r)|_(r = t) + partial_r tilde(f)(x, r)|_(r = -t) + tilde(g)(x, t) - tilde(g)(x, - t)] \
&= 1/(c_0) [partial_r tilde(f)(x, r)|_(r = t) + tilde(g)(x, t)] \
&= 1/(1 dot 3 dots.c (n - 2) omega_n) [partial_t (t^(-1) partial_t)^((n -3)/2) (t^(n - 2) integral_(|y| = 1) f(x + t y) dif sigma(y)) \
  & wide wide + (t^(-1) partial_t)^((n - 3)/2) (t^(n-2) integral_(|y| = 1) g(x + t y) dif sigma(y)) ]. $

Note that the RHS only depends on $f, g$ (and their derivatives), in a very explicit manner.

#theorem[
  Suppose $n$ odd and $>= 3$, and $f in C^((n + 3)/2) (RR^n),$ $g in C^((n+1)/2) (RR^n)$. Then,  $u(x, t)$ defined by $ u(x, t) = 1/(1 dot 3 dots.c (n - 2) omega_n) [partial_t (t^(-1) partial_t)^((n -3)/2) (t^(n - 2) integral_(|y| = 1) f(x + t y) dif sigma(y)) \
    + (t^(-1) partial_t)^((n - 3)/2) (t^(n-2) integral_(|y| = 1) g(x + t y) dif sigma(y)) ] $ is a $C^2$ solution of the Cauchy problem.
]

#remark[
  Counting derivatives in the solution formula, we readily see where the smoothness assumptions on $f, g$ come from; namely, there are $(n - 1)/2$ (resp. $(n- 3)/2$) derivatives of $f$ (resp. $g$) taken in the formula, so we'll need to take two more for $u$ to have any chance of being $C^2$, yielding the numbers stated.
]

#proof[
  The fact that $u$ satisfies $square u = 0$ just follows by direct computation. For the boundary data, recall that $ u(x, t) = lim_(r -> 0) (tilde(u)(x, r, t))/(c_0 r) = 1/c_0 [partial_r (T_((n-1)/2) M_f)|_(r = t) + T_((n-1)/2) M_g|_(r = t)]. $ Recall that $T_k phi = sum_(j=0)^(k - 1) c_j t^(j + 1) phi^(j) (t)$, from which we see that $ u(x, t) & = partial_t [t M_f+ (c_1)/c_0 t^2 partial_t M_f + cal(O)(t^3) ] + t M_g + cal(O)(t^2) \
          & = M_f + t partial_t M_f + c_1/(c_0) 2 t partial_t M_f + t M_g + cal(O)(t^2). $ In particular, at $t = 0$, all terms vanish except $M_f (x, 0)$, which is equal to $f(x)$, as required. Similarly, taking a derivative in $t$, we find $ partial_t u(x, t) = partial_t M_f + (1 + 2 (c_1)/c_0) partial_t M_g + M_g + cal(O)(t). $ Recalling that $M_phi$ even in $t$ and thus its derivative is odd in $t$, the terms involving $partial_t M_f, partial_t M_g$ vanish, so all that is left is $M_g (x, 0) = g(x)$.
]


=== Even Space Dimensions
The key observation to derive an analogous formula for even space dimension is the so-called _Hadamard's Method of Descent_. Namely, if $n$ even and $u : RR^(n + 1) times RR$ is such that $square u = 0$ but $u$ independent of the final coordinate $x_(n + 1)$, then $square u$ will also be zero in $RR^(n) times RR$. Thus, we can just use the representation formula for odd dimensions, and simplify accordingly.


#theorem[
  Suppose $n$ even, $f in C^((n + 4)/2) (RR^n), g in C^((n + 2)/2) (RR^n)$. Then, if $u$ solves the Cauchy problem corresponding to $square$ in $RR^n$, $ u(x, t) &= 2/(1 dot 3 dots.c (n-1) omega_(n+1)) [partial_t (t^(-1) partial_t)^((n-2)/2) (t^(n-1) integral_(|y| <= 1) (f(x + t y))/(sqrt(1 - |y|^2)) dif y) \
    & wide wide + (t^(-1) partial_t)^((n-2)/2) (t^(n-1) integral_(|y| <= 1) (g(x + t y))/(sqrt(1 - |y|^2))) dif y
  ]. $
]

#proof[
  By our remarks above, it suffices to show that the representation formula with our given stipulations on the dependence on $x_(n + 1)$ simplifies as given.

  Namely, if we write $(y, y_(n+1)) in RR^(n + 1)$, then the integrals of interest become (splitting into two integrals over the northern/southern hemispheres, and adding together), $ integral_(|y|^2 + y_(n + 1)^2 = 1) f(x + t y) dif sigma(y, y_(n + 1)) &= 2 integral_(|y|^2 <= 1) (f(x + t y))/(sqrt(1 - |y|^2)) dif y. $ Same holds for $g$.
]

Remark that our solution formula can be interpreted in the distributional sense. Namely, if we define the distribution $Sigma_t$ by $angle.l Sigma_t, psi angle.r := 1/(omega_n) integral_(|y| = 1) psi(t y) dif sigma(y)$ and $Phi_t := 1/(omega_n) (t^(-1) partial_t)^((n-3)/2) (t^(n-2) Sigma_t)$, then $u(dot, t) = f convolve partial_t Phi_t + g convolve Phi_t$, in a distributional sense (using the evenness of the integrals in $t$).


== Cauchy Problem for the Inhomogeneous Wave Equation

Here, we study $ (star) wide cases(
  square u = w(x, t),
  u(x, 0) = f(x),
  partial_t u(x, 0) = g(x)
). $
WLOG, we can take $f = g = 0$, since if $u_1$ solves $(star)$ with $w = 0$ and $u_2$ solves $(star)$ with $w$ given and $f = g = 0$, then $u_1 + u_2$ will solve the general problem.

#theorem("Duhamel's Principle")[
  Let $w in C^([n/2] + 1) (RR^n times RR)$ and for each $s in RR$, let $v(x, t, s)$ solve $ cases(
    square v = 0,
    v(x, 0, s) = 0,
    partial_t v(x, 0, s) = w(x, s)
  ). $ Then, $ u(x, t) = integral_(0)^t v(x, t - s, s) dif s $ solves $(star)$ with $f = g = 0$.
]

#proof[
  Follows by direct computation.
]

== The Cauchy Problem via Fourier Transform

One should review the Preliminaries on Fourier transform and distributions, and especially on Fourier transforms of tempered distributions, before proceeding.


We work formally for now; consider as before the Cauchy problem for the wave equation $ cases(
  square u = 0,
  u(x, 0) = f(x)\, quad partial_t u (x, 0) = g(x)
), $ where we do not prescribe the regularity of $f, g$ yet. Assuming it is possible to do so, take the Fourier transform of $u$ in just the spatial variables. Using derivative properties of the Fourier transform, and assuming we may integrate (in $t$) under the integral, we obtain the equation $ partial_t^2 hat(u)(xi, t) + 4pi^2 abs(xi)^2 hat(u)(xi, t) = 0, $ with initial data $hat(u)(xi, 0) = hat(f)(xi), partial_t hat(u)(xi, 0) = hat(g)(xi)$ (again assuming this makes sense). But this is just an ODE in $t$, and a simple one at that; we obtain the solution $ hat(u)(xi, t) = hat(f)(xi) cos(2 pi |xi| t) + hat(g)(xi) (sin(2 pi |xi| t))/(2 pi |xi|). $ To recuperate the original solution, we need to apply the inverse Fourier transform; the products become convolutions, and we obtain the formula $ u(dot, t) = f convolve Psi_t + g convolve Phi_t, $ where $Psi_t$ the inverse Fourier transform of $cos(dots)$, similar for $Phi$; not that (again under assumptions of being able to take derivatives under integrals) $partial_t Phi_t = Psi$. Remark the similarity of this formula with the expression we wrote down at the very end of the chapter on spherical means.

However, there is a quite big technical problem; the trig. functions $hat(Phi)_t, hat(Psi)_t$ are _not_ in $L^1$, so it doesn't make sense to take their inverse Fourier transforms. We'll deal with this via distributions, and approximation. Namely, put $ hat(Phi)_t^epsilon (xi) := e^(- 2 pi |xi| epsilon) (sin(2 pi |xi| t))/(2 pi |xi|), $ for $epsilon > 0$, with similar for $hat(Psi)_t$; these are now in $L^1$, and converge uniformly to their respective functions. We will compute the inverse fourier transforms of these functions. First, note that we can rewrite $ hat(Phi)_t^epsilon (xi) = 1/(4pi i |xi|) (e^(-2 pi (epsilon - i t) |xi|) - e^(- 2pi (epsilon + i t) |xi|)) = 1/(2 i) integral_(epsilon - i t)^(epsilon + i t) e^(- 2pi s |xi|), $ so that we need to compute
$
  Phi^epsilon_t (x) = 1/(2 i) integral_(epsilon - i t)^(epsilon + i t) integral_(RR^n) e^(2 pi i xi dot x) e^(- 2pi s |xi|) dif xi dif s.
$

#lemma[
  $ integral_(RR^n) e^(2 pi i xi dot x) e^(- 2pi s |xi|) dif xi = (Gamma((n+1)/2))/(pi^((n+1)/2)) s/((s^2 + |x|^2)^((n+1)/2)) $ for any $s in CC$ with positive real part.
]<lem:annoying>

Assuming this lemma, we obtain $ Phi_t^(epsilon) (x) &= (Gamma((n + 1)/2))/(pi^((n+1)/2)) 1/(2 i) integral_(epsilon - i t)^(epsilon + i t) s/((s^2 + abs(x)^2)^((n+1)/2)) dif s \
&= (Gamma((n+1)/2))/(pi^((n+1)/2)) 1/(2 i) 1/(1 - n) [1/([(epsilon + i t)^2 + |x|^2]^((n-1)/2)) - 1/([(epsilon - i t)^2 + |x|^2]^((n-1)/2))]. $ In particular, we see that for $|t| < |x|$, that $lim_(epsilon -> 0) Phi_t^epsilon (x) -> 0$. However, we get a dichotomy in the dimension when $|t| > |x|$. Namely, if $n$ odd, we again have limiting value zero. However, if $n$ even, the parity of the denominator gives that $ Phi_t (x) & = lim_(epsilon) Phi_t^epsilon (x) \
          & = ("sgn"(t) Gamma((n+1)/2))/(i (1 - n) pi^((n+1)/2)) 1/((-t^2 + |x|^2)^((n-1)/2)) \
          & = ((Gamma(n+1)/2) "sgn"(t) (-1)^((n-1)/2))/((1 - n) pi^((n+1)/2)) 1/((t^2 - |x|^2)^((n-1)/2)). $ One can check by induction on $n$ that then $ Phi_t (x) = (2 "sgn"(t))/(1 dot 3 dots.c (n - 1) omega_(n+1)) (t^(-1) partial_t)^((n/2) - 1) [t^2 - |x|^2]^(-1/2), $ as we expected from the spherical means approach. Thus, we see that $ u(dot, t) = f convolve partial_t Phi_t + g convolve Phi_t, wide Phi_t = 1/(1 dot 3 dots.c (n-1)) (t^(-1) partial_t)^((n-2)/2) (t^(n-1) Gamma_t), $ where $Gamma_t$, as a distribution, is given by $ angle.l Gamma_t, phi angle.r = 1/(omega_(n+ 1)) integral_(|y| <= 1) (psi(t y))/(sqrt(1 - |y|^2)) dif y. $

#proposition[If $f, g in L^2 (RR^n)$, then $u(dot, t) in L^2 (RR^n)$]

#proof[
  By Plancherel's, $hat(f), hat(g) in L^2$ as well. Thus, with $t$ fixed, $ norm(hat(u))_2 <= norm(hat(f) cos(2 pi abs(dot) t))_2 + norm(hat(g) (sin(2 pi abs(dot) t))/(2pi abs(dot)))_2 < infinity, $ thus $hat(u) in L^2$, so $u in L^2$.
]
We can even control the (weak) derivatives of solutions.
#definition[
  Put $ H_k (Omega) := {f in L^2 (Omega) | partial^alpha f in L^2 (Omega) forall |alpha| <= k}. $ Note that, using the identity $hat(partial^alpha f)(xi) = (2 pi i xi)^(alpha) hat(f) (xi)$ and Plancherel's, $ f in H_k (RR^n) <=> xi^alpha hat(f)(xi) in L^2 (RR^n) forall |alpha| <= k <=> (1 + |xi|)^k hat(f)(xi) in L^2 (RR^n). $
]

#proposition[If $f in H_k (RR^n), g in H_(k-1)(RR^n)$, then $u in H_k (RR^n times [t_0, t_1])$.]

#proof[
  Same as the previous proof, only applied to the Fourier transform of mixed partials of $u$.
]

Finally, with the interesting things out of the way, we prove the lemma we took for granted, @lem:annoying:

#proof[
  (Of @lem:annoying) First, we claim that for $beta >= 0$, $ e^(-beta) = integral_(0)^infinity (e^(-tau))/(sqrt(pi tau)) e^(-beta^2/(4 tau)) dif tau quad (dagger). $ Indeed, using the residue theorem, we see that $ integral_(-infinity)^(infinity) (e^(i beta s))/(1 + s^2) dif s = 2 pi i "Res"_(s = i) ((e^(i beta s))/(1 + s^2)) = pi e^(-beta), $ and $integral_(0)^infinity e^(- (1 + s^2) tau) dif tau = 1/(1 + s^2)$, so combining these two results, we get $ e^(-beta) & = 1/pi integral_(-infinity)^(infinity) integral_(0)^infinity e^(- (1 + s^2) tau) e^(i beta s) dif tau dif s \
  & =^"Fubini" 1/(pi) integral_(0)^infinity integral_(-infinity)^infinity (dots.c) dif s dif tau \
  & =^(s = 2 pi sigma) 2 integral_(0)^infinity underbrace(integral_(-infinity)^(infinity) e^(i beta 2 pi sigma) e^(-4 pi^2 sigma^2 tau) e^(- tau) dif sigma, = "i.f.t of a Gausian") dif tau \
  &= 2 integral_(0)^infinity (4 pi tau)^(-1/2) e^(- beta^2/(4 tau)) e^(- tau) dif tau\
  &= integral_(0)^infinity (e^(-tau))/sqrt(pi tau) e^(-beta^2/(4 tau)) dif tau, $ as claimed in $(dagger)$. Next, we may rewrite the integral of interest as follows $ integral_(RR^n) e^(2 pi i x dot xi) e^(-2 pi |xi| t) dif xi & =^((dagger)) integral_(RR^n) e^(2pi i x dot xi) integral_(0)^infinity (e^(-tau))/(sqrt(pi tau)) e^(- (pi^2 |xi|^2 t^2)/(tau)) dif tau dif xi \
  &=^"Fubini" integral_(0)^infinity (e^(- tau))/(sqrt(pi tau)) underbrace(integral_(RR^n) e^(2pi i x dot xi) e^(-(pi^2 |xi|^2 t^2)/tau) dif xi, = "i.f.t. of Gaussian") dif tau \
  &= integral_0^infinity (e^(-tau))/(sqrt(pi tau)) (tau/(pi t^2))^(n/2) e^(- tau/t^2 |x|^2) dif tau \
  &= 1/(pi^((n+1)/2)) 1/(t^n) integral_(0)^infinity e^(- tau(1 + (|x|^2)/t^2)) tau^((n-1)/2) dif tau \
  &=^(sigma = (1 + (|x|^2)/t^2) tau) 1/(pi^((n+1)/2)) t/((t^2 + |x|^2)^((n+1)/2)) underbrace(integral_(0)^infinity e^(-sigma) sigma^((1-n)/2), = Gamma((n+1)/2)) dif sigma, $ which completes the proof upon simplification.
]
== The Fundamental Solution
We seek to find a distribution $u$ such that $ square u = delta(x) delta(t) $ as a distribution. Taking the Fourier transform in $x$, we get an inhomogeneous ODE for $hat(u)(xi, t)$: $ partial_t^2 hat(u)(xi, t) + 4 pi^2 |xi|^2 hat(u)(xi, t) = delta(t), $ since $hat(delta) = 1$. We can solve this by solving the homogeneous problem for $t < 0, t > 0$, and imposing proper conditions at $t = 0$ such that the inhomogeneous problem holds. Namely, we know that $ hat(u)(xi, t) = cases(
  a(xi) cos(2pi abs(xi) t) + b(xi) sin(2pi abs(xi) t) quad t < 0,
  c(xi) cos(2 pi abs(xi) t) + d(xi) sin(2 pi abs(xi) t) quad t > 0.
) $
In order for the dirac distribution to appear in the second derivative of $u$, we know that we need there to be a discontinuity jump of 1 at the origin in $partial_t hat(u)$; since $ partial_t hat(u)(xi, t) = cases(
  - 2pi abs(xi) a(xi) sin(dots) + 2pi abs(xi) b(xi) cos(dots) quad & t < 0,
  -2pi abs(xi) c(xi) sin(dots) + 2pi abs(xi) d(xi) cos(dots) & t > 0
), $ we need $ 1 = lim_(t -> 0^+) partial_t hat(u) - lim_(t -> 0^-) partial_t hat(u) = 2 pi abs(xi) (d(xi) - b(xi)) => 2 pi abs(xi) (d(xi) - b(xi)) = 1 quad "(i)". $ In addition, we need continuity at $0$ in $hat(u)$ so that our first derivative is only discontinuous, not a dirac itself. Namely, we need $ lim_(t -> 0^+) hat(u) = lim_(t -> 0^-) hat(u) <=> a(xi) = c(xi) quad "(ii)". $ (i), (ii) give two conditions on the coefficients $a, b, c, d$, so we need two more to determine a solution for all time. Let's just say $hat(u)$ identically zero for $t < 0$ (so that $a equiv b equiv 0$), and thus (i), (ii) imply $c(xi) equiv 0, d(xi) = 1/(2 pi abs(xi))$. In this way, we get solution $ hat(u)(xi, t) = cases(
  0 quad & t > 0,
  (sin(2 pi abs(xi) t))/(2 pi abs(xi)) & t < 0
), $ which one should recognize (for $t > 0$) as our $hat(Phi)_t$ from above. Taking one more Fourier transform (which needs to be computed via a regularization, since the function above not in $L^1$), in $t$, we get $ hat(u)(xi, tau) = 1/(4 pi^2) 1/(|xi|^2 - tau^2), $ which one remarks is singular on the cone $abs(xi)^2 = tau^2$; just as before, only now we are in Fourier space. With this, we can solve, for sufficiently nice $w$, the inhomogeneous problem $square v = w$, via $ v = u convolve w, $ where $u$ the inverse Fourier transform of what we wrote above.

== An Introduction to the Radon Transform
The idea here is, akin to the method of spherical means, to reduce the $n$-dimensional wave equation to a 1-dimensional wave equation; however, this time we'll use a different integral transform, namely the Radon transform. We'll (largely formally) discuss properties of the transform relevant to our purposes first.

#definition[
  Put $cal(S)_n := {omega in RR^n : abs(omega)= 1}$. For $f in cal(S)(RR^n)$ and $(s, omega) in RR times cal(S)_n$, define the _Radon transform_ of $f$ by $ (R f)(s, omega) := integral_(x dot omega = s) f(x) dif x, $ where $dif x$ the induced hypersurface measure on the plane defined by $x dot omega = s$.
]
// ! motivations?

#proposition[
  For $f in cal(S)$, $rho in RR, omega in cal(S)_n$, then $ hat(R f)(rho, omega) = hat(f)(rho omega), $ where the first Fourier transform a one-dimensional Fourier transform (with $rho$ the Fourier dual of $s$) with $omega$ fixed, and the second a $n$-dimensional Fourier transform.
]

#proof[
  This essentially boils down to the observation that we may write integration over $RR^n$ as the tensor product of integration over planes $x dot omega = s$ and integration over $s in RR$;
  $
    hat(f)(rho omega) & = integral_(RR^n) e^(- 2 pi i rho omega dot x) f(x) dif x \
                      & = integral_(RR) integral_(x dot omega = s) e^(-2 pi i rho s) f(x) dif x dif s \
                      & = integral_(RR) e^(- 2pi i rho s) R f (s, omega) dif s = hat(R f)(rho, omega).
  $
]

#corollary[
  For $f in cal(S)$, $R f (s, omega) = integral_(RR) e^(2 pi i s rho) hat(f)(rho omega) dif rho$.
]
#proof[
  Follows immediately by Fourier inversion.
]

#proposition("Inverse Radon Transform")[
  For $f in cal(S)$, $ f(x) = integral_(cal(S)_n) (tilde(R) f)(s, omega) dif sigma(omega), $ where the operator $tilde(R)$ defined by $ (tilde(R)f)(s, omega) := 1/2 integral_(RR) e^(2 pi i rho x dot omega) (hat(R f))(rho, omega) abs(rho)^(n - 1) dif rho. $
]

#proof[
  By Fourier inversion, hyperspherical coordinates, and the previous proposition, we may write $ f(x) &= integral_(RR^n) e^(2 pi i x dot xi) hat(f)(xi) dif x \
  &= integral_(cal(S)_n) integral_(RR_+) e^(2 pi i rho omega dot x) hat(f)(rho omega) rho^(n-1) dif rho dif sigma(omega) \
  &= integral_(cal(S)_n) underbrace(integral_(0)^infinity e^(2 pi i rho x dot omega) hat(R f)(rho, omega) rho^(n - 1) dif rho dif sigma(omega), =: h(x dot omega, omega)). $ We can decompose $h$ into a sum of a symmetric and antisymmetric function (in $omega$ under the flip $omega mapsto - omega$), by $ h(x dot omega, omega) = underbrace(1/2 [h(x dot omega, omega) + h(x dot (-omega), - omega)], "symmetric") + underbrace(1/2 [h(x dot omega, omega) - h(x dot (-omega), - omega)], "antisymmetric"). $
  Since our integration is over the sphere $cal(S)_n$, the antisymmetric term will vanish, and we are therefore left to deal with the symmetric term, which we may rewrite $ 1/2 [h(x dot omega, omega) + h(x dot (-omega), - omega)] &= 1/2 [integral_0^infinity e^(2 pi i rho x dot omega) hat(R f)(rho, omega) rho^(n-1) dif rho - integral_(0)^(-infinity) e^(2 pi i rho x dot omega) hat(R f)(rho, omega) rho^(n-1) (-rho)^(n-1)] \
  &= 1/2 integral_(RR) e^(2 pi i rho x dot omega) hat(R f)(rho, omega) abs(rho)^(n-1) dif rho = (tilde(R)f)(s, omega), $ where we change variables in second integral $rho -> - rho$. This completes the proof.
]

Finally, we can see the connection back to the wave equation.
#proposition[
  For $f in cal(S)$, $R(partial_i f)(s, omega) = omega_i partial_s (R f)(s, omega)$. In particular, we see that $ R (laplace f) = partial_s^2 (R f)(s, omega), $ and moreover, if $square u = 0$, then, treating $t$ as a parameter, $ 0 = R(square u)(s, omega; t) = (partial_t^2 - partial_s^2)(R u)(s, omega; t), $ i.e., $(R u)(s, omega; t)$ satisfies a wave equation in the $t, s$ variables.
]

#proof[
  The "In particular" statement follows by applying the main result twice in each coordinate and summing over the result. To prove the result, denote the translation $f_t (x) := f(x + t)$ for $t in RR^n$. Then, by changing coordinates, one finds that $ (R f_t)(s, omega) = (R f)(s + t dot omega, omega). $ So, since $ partial_j f (x) = lim_(t_j -> 0) 1/(t_j) [f(x + t_j e_j) - f(x)], $ then applying the Radon transform to both sides, and passing limits under integrals (valid since $f in cal(S)$), we obtain $ R (partial_j f) (s, omega) = lim_(t_j -> 0) [R(s + t_j omega_j, omega) - R f(s dot omega, omega)] = omega_j partial_s R f(s, omega). $
]

#theorem[
  The solution to the problem $ cases(
    square u = 0,
    u(0, x) = f(x)\, quad partial_t u(0, x) = g(x)
  ) $ is given by $ u(x, t) = 1/2 integral_(cal(S)_n) [(tilde(R) f) (x dot omega + t, omega) + (tilde(R) f) (x dot omega - t, omega) + integral_(x dot omega - t)^(x dot omega + t) (tilde(R) g)(s, omega) dif s] dif sigma(omega). $
]

#remark[
  As we'll see in the proof, we need some regularity of $f, g$ for this result to hold, but we'll not focus on them here.
]

#proof[
  Per the previous lemma, $partial_s^2 R u = partial_t^2 R u$ for all $omega in cal(S)_n$, i.e. $R u$ satisfies a 1-dimensional wave equation, with $F(s, omega) := R u (s, omega, 0), G(s, omega) := R partial_t u(s, omega, 0)$ (treating $t$ as a parameter in the Radon transform). Hence, $ (R u) (s, omega, t) = 1/2 [F(s + t, omega) + F(s - t, omega) + integral_(s - t)^(s + t) G(s, omega) dif s], $ by D'Alembert's formula. Moreover, one has that $ F(s, omega) = R f (s, omega), wide G(s, omega) = R g (s, omega), $ where in the second equality we need to take a derivative outside of an integral sign (see our remark above; if, say, $f, g$ have compact support, then this is fine, for instance). Applying the inversion theorem for the Radon transform to the expression above, we obtain the expression stated.
]

A natural question is how this relates to the solution we found via Fourier transforms? Note that we can, as in that case, see a dichotomy in the behaviour of solutions with our solution formula too.

Suppose first that $n$ odd; then, remember that there is a term $abs(rho)^(n - 1)$ in the definition of $tilde(R) f$; since $n$ odd, $n - 1$ even so $abs(rho)^(n - 1) = rho^(n-1)$, and we may rewrite the relevant expression in terms of the inverse Fourier transform of a perfect derivative: $ tilde(R) f (s, omega) & = 1/2 integral_(RR) e^(2 pi i rho s) hat(R f)(rho, omega) rho^(n- 1) dif rho \
& = 1/2 ((-1)^((n-1)/2))/((2 pi)^(n-1)) integral_(RR) e^(2 pi i rho s) hat(partial_s^(n-1) R f) (rho, omega) dif rho \
&= 1/2 ((-1)^((n-1)/2))/((2 pi)^(n-1)) partial_s^(n - 1) R f (omega, rho). $ Remark that this is a purely local expression on the initial data $f$.

On the other hand, if $n$ even, then $abs(rho)^(n - 1) = "sgn"(rho) rho^(n - 1)$, and the analogous expression we get is $ tilde(R f)(s, omega) = 1/2 ((-1)^((n-2)/2))/((2 pi)^(n-1)) integral_(RR) e^(2 pi i rho s) (2 pi i rho)^(n - 1) (-i) "sgn"(rho) hat(R f) (rho, omega) dif rho, $ which isn't quite the perfect derivative term we had above. However, we can rewrite it as follows, by use of the _Hilbert transform_:

#lemma[
  For a real-valued function of one variable $phi$, define the _Hilbert transform_ of $phi$ by the Cauchy principal-valued integral transform $ (H phi) (s) := lim_(epsilon -> 0) 1/pi integral_(|t| > epsilon) (phi(s - t))/t dif t. $ Then, we have that $ hat(H phi)(rho) = - i "sgn"(rho) hat(phi)(rho). $
]

#proof[
  // maybe
]

Assuming this, we can hence rewrite our expression above for $tilde(R f)$ by $ tilde(R f) (s, omega) = 1/2 ((-1)^((n-2)/2))/((2 pi)^(n-1)) H(partial_s^(n-1) R f)(s, omega), $ where we see now the non-locality (w.r.t. intial data) of the even-dimensional solution, for the Hilbert transform is clearly far from local.

= The Heat Equation

The _heat equation_ is given by $ partial_t u = laplace_x u, $ where $x in RR^n$ and $t in [0, + infinity)$. Traditionally, $u$ represents the temperature at $x in Omega subset RR^n$ at some time $t$. Namely, we would have that, physically, the rate of change in time of the total temperature in a domain $Omega$ is given by the incoming heat flux across the boundary:
$ partial/(partial t) integral_(Omega) u(x, t) dif x &= integral_(partial Omega) arrow(J) dot (- arrow(nu)) dif sigma \
&=^("Divergence"\ "Theorem") - integral_(Omega) arrow(gradient) dot arrow(J) dif x. $ The so-called Fourier's Law says that $arrow(J) = - c gradient u$; i.e., heat flows from warm to cold (we'll take $c = 1$). Plugging this in, this says that $ (partial)/(partial t) integral_(Omega) u(x, t) dif x = integral_Omega laplace_x u(x, t) dif x, $ which gives the heat equation upon integrating under the integral.

We'll be interested in the initial value problem $ partial_t u = laplace_x u, wide u(x, 0) = f(x). $ We'll approach this via Fourier transform. Suppose $f in cal(S)(RR^n)$. Writing $hat(u)(xi, t)$ for the Fourier transform of a solution $u$ in just the spatial variable. Using derivative properties of the Fourier transform and assuming for now $u in cal(S)$, we obtain a first-order ODE for $u$, $ partial_t hat(u)(xi, t) + 4 pi^2 abs(xi)^2 hat(u)(xi, t) = 0, wide hat(u)(xi, 0) = hat(f)(xi), $ which readily has solution $ hat(u)(xi, t) = hat(f)(xi) e^(-4 pi^2 abs(xi)^2 t), $ which we see is in $cal(S)$ for all $t > 0$. Applying the inverse Fourier transform, we find $ u(x, t) = f convolve K_t (x), wide hat(K_t)(xi) := e^(- 4pi^2 abs(xi)^2 t). $ We see that $hat(K)_t (xi)$ a Gaussian, so using the stability of Gaussians under the Fourier transform, we see that $ K_t (xi) = (4 pi t)^(-n/2) e^(- abs(x)^2/(4 t)), $ a so-called Gaussian kernel. Remark that as $t -> infinity$, the graph of such a function "flattens" (symmetrically) about $x = 0$.

#remark[
  We have the properties
  $ K_t (x) = t^(-n/2) K_1 (x/(t^(1/2))), $ and $ integral_(RR^n) K_t (x) dif x = hat(K)_t (0) = 1. $
]

Using the above remark and the the proof given for boundary behaviours for solutions of the Dirichlet problem for $laplace$, we obtain the following result.


#theorem[
  Suppose $f in L^p (RR^n), 1 <= p <= infinity$. Then, $ u(x, t) = f convolve K_t (x) $ solves the heat equation on $RR^(n) times (0, infinity)$. Furthermore, if $f$ is continuous and bounded, then $u$ is continuous on $RR^n times [0, infinity)$ and furthermore $u(x, 0) = f(x)$. If $f in L^p (RR^n)$, $1 <= p < infinity$, $ u(dot, t) ->^(t -> 0)_(L^p) f(dot). $
]
#remark[
  Remark the similarities in this theorem and the analogue for the Dirichlet problem for the Laplacian.
]
#remark[$K_t (x)$ and all of its $x$ derivatives decay rapidly, so we can take derivatives under the integral sign in $u = f convolve K_t$; thus, $u in C^infinity$ for all $t > 0$; the heat flow "regularizes" initial data.]

#remark[
  Uniqueness does _not_ hold in general for the initial value problem of the heat equation; we need some conditions at infinity. This is already apparent in $n = 1$. Take any one-variable $C^infinity$ function $g(t)$, and let $ u(x, t) = sum_(k=0)^infinity (g^(k)(t))/((2k)!) x^(2 k). $ We claim $u$ solves $partial_t u - partial_x^2 u = 0$. Indeed, $ partial_t u = sum_(k=0)^infinity (g^((k+1))(t))/((2k)!) x^(2k), wide laplace u = sum_(k=0)^infinity g^((k)) (t) (x^(2k - 1))/((2 k - 2)!), $ which we see are equal by shifting indices.

  Then, if we take, say, $ g(t) = cases(
    0 quad & t = 0,
    e^(-t^(-2)) quad & t eq.not 0
  ), $ then one can see that $g^((k))(0) = 0$ for all $k >= 0$, so that with this $g$, $u(0, x) = 0$. So, this $u$ gives a nontrivial solution to the heat equation with $f equiv 0$ initial data, which gives a second solution to the trivial constant $0$ solution.

  There are some uniqueness-related results with additional restrictions. For instance, Widder's Theorem says that if $f >= 0$, then $f convolve K_t (x)$ is the unique, nonnegative solution to the initial value problem.
]

== The Gaussian Kernel as a Fundamental Solution

Again, we seek the fundamental solution to the heat equation, in order to solve the inhomogeneous equation $ partial_t u - laplace u = g. $

#theorem[
  $ K(x, t) = cases(1/(4 pi t)^(n\/2) e^(- (abs(x)^2)/(4 t)) quad & t > 0, 0 & t <= 0) $ is a fundamental solution for the heat operator.
]

#proof[
  We know $K in L^1_"loc" (RR^n times RR)$, so given $epsilon > 0$, let $K_epsilon (x, t) = K(x, t)$ for $t > epsilon$, and 0 otherwise. By dominated convergence, $K_epsilon -> K$ in $cal(D)'$. So, all we have to show is that, for $phi in C^infinity_c (RR^n times RR)$, $ angle.l K_epsilon, - partial_t phi - laplace phi angle.r -> phi(0, 0) $ as $epsilon -> 0$. We see that $ angle.l K_epsilon, - partial_t phi - laplace phi angle.r &= integral_(epsilon)^infinity integral_(RR^n) K(x, t) [-partial_t phi - laplace phi] dif x dif t \
  &= integral_(epsilon)^infinity integral_(RR^n) underbrace((partial_t K - laplace K), = 0 "for " t > 0) phi(x, t) dif x dif t + integral_(RR^n) K(x, epsilon) phi(epsilon, x) dif x \
  &=^(K "even in" x) integral_(RR^n) K(-x, epsilon) phi(x, epsilon) dif x \
  &= [K_epsilon convolve phi(dot, epsilon)](0) \
  &= [K_epsilon convolve phi(dot, 0)](0) + [K_epsilon convolve (phi(dot, epsilon - phi(dot, 0)))](0). $ The first term $-> phi(0)$ as $epsilon -> 0$, using previous theorem, and by Young's inequality, $ [K_epsilon convolve (phi(dot, epsilon - phi(dot, 0)))](0) & <= sup_x |phi(x, epsilon) - phi(x, 0)| norm(K_epsilon)_(L^1) ->_(epsilon -> 0) 0, $ thus completing the proof.
]

#theorem("Inhomogeneous Heat Equation")[
  If $g in L^1 (RR^n times RR)$, then $u = g convolve K$ is defined almost everywhere and is a distributional solution of $partial_t u - laplace u = g$.
]


== The Heat Equation in Bounded Domains

#theorem[
  Let $Omega subset RR^n$ be a bounded domain and $0 < T < infinity$. Suppose that $u$ is continuous on $overline(Omega) times [0, T]$ and that it satisfies $partial_t u - laplace u = 0$ on $Omega times (0, T).$ Then, $u$ assumes its maximum either on $Omega times {0}$ or on $partial Omega times [0, T]$.
]

#proof[
  For $epsilon > 0$, set $ v(x, t) = u(x, t) + epsilon abs(x)^2. $ We have $ partial_t v - laplace v = partial_t (epsilon abs(x)^2) - laplace (epsilon abs(x)^2) = - epsilon 2 n < 0. $ Let $0 < T' < T$. If the max of $v$ occurs on $overline(Omega) times [0, T']$, then $partial_j v = partial_t v = 0$ and $partial_(j)^2 v <= 0$, but this contradicts the fact that $(partial_t - laplace)v < 0$. Therefore, $ max_(overline(Omega) times [0, T']) u <= max_(overline(Omega) times [0, T']) v &= max_(overline(Omega) times {0} union (partial Omega times [0, T'])) v \
  &<= max_(Omega times {0} union (partial Omega times [0, T'])) u + epsilon max_(overline(Omega)) norm(x)^2. $
  Letting $epsilon -> 0$ and $T' -> T$ gives the result.
]
