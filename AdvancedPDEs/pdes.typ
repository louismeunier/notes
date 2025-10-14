// ! external
#import "../typst/notes.typ": *
// #import "../typst/shortcuts.typ": *

#import "@preview/cetz:0.2.2"

// ! configuration
#show: doc => conf(
  course_code: "MATH580",
  course_title: "Advanced PDEs 1",
  // subtitle: "Abstract Metric, Topological Spaces; Functional Analysis.",
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
  Let $L$ be a linear operator associated to a $k$th-order linear PDE. The _characteristic form_ of $L$ is the $k$th degree homogeneous polynomial defined by $ chi_L (x, xi) := sum_(|alpha| = k) a_alpha (x) xi^alpha. $ The _characteristic variety_ is defined, for a fixed $x$, as the set of $xi$ for whcih $chi_L$ vanishes, i.e. $ "char"_x (L) := {xi eq.not 0 | chi_L (x, xi) = 0}. $
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
  #remark[In the linear case, one sees that this equivalently means that the normal $nu$ of $S$ is not in $"char"_x (L)$; in particular, it is independent of the choice of initial data.]
  Remark that if we write coordinates $(x_1, dots, x_n, y) in RR^(n+1)$ and define $F(x, y) = u(x) - y$, then the PDE can be written succinctly as the statement $A dot gradient F = 0$, and that the zero set $F = 0$ gives the graph of the solution $u$; hence, we essentially need that the vector field $A$ everywhere tangent to the graph of any solution. The idea of our solution is to consider $A$ "originating" at $S^ast$, and "flowing" our solution along the integral curves defined by $A$ to obtain a solution locally.

  The integral curves of $A$ are defined by the system of ODEs $ cases((dif x_j)/(dif t) = a_j (x, y)\, (dif y)/(dif t) = b(x, y) & ""\ x_j (s, 0) = g_j (s)\, y(s, 0) = phi(g(s))) wide j = 1, dots, n. $
  By existence/uniqueness theory of ODEs, there is a local solution to this ODE, viewing $s$ as a parameter, inducing a map $ (s, t) |-> (x_1 (s, t), dots, x_n (s, t)), $ which is at least $C^1$ in $s, t$ by smooth dependence on initial data. By the transversality condition, we may apply inverse function theorem to this mapping to find $C^1$-inverses $s = s(x), t = t(x)$ with $t(x) = 0$ and $g(s(x)) = 0$ whenever $x in S$. Define now $ u(x) := y(t(x), s(x)). $ We claim this a solution. By the inverse function theorem argument, it certainly satisfies the initial condition, and repeated application of the chain rule shows that the solution satisfies the PDE.
]

We briefly discuss, but don't prove in detail, the fully nonlinear case, i.e. $ F(x, u, partial u) = 0, $ where we assume $F in C^2$. We approach by analogy. Putting $xi_i := (partial u)/(partial x_i)$, then we see $F$ as a function $RR^(2n + 1) -> RR$. We seek "characteristic" ODEs akin to those found for the integral curves in the quasilinear case. We naturally take, as in the previous, $(dif x_i)/(dif t) = (partial F)/(partial xi_i)$. Applying chain rule, we find that $ (dif y)/(dif t) = sum_i (partial u)/(partial x_i) (dif x_i)/(dif t) = sum_(i) xi_i (partial F)/(partial xi_i). $ Finally, if we differentiate $F = 0$ w.r.t. $x_j$, we find $ 0 = (partial F)/(partial x_j) + xi_j (partial F)/(partial y) + sum_(k) (partial F)/(partial xi_k) (partial xi_k)/(partial x_j) $ whence $ (dif xi_j)/(dif t) = sum_k (partial xi_j)/(partial x_k) (partial x_k)/(partial t) = - (partial F)/(partial x_j) - xi_j (partial F)/(partial y). $ In summary, this gives a system of $2 n +1$ ODEs in $(x, y, xi)$ variables $ (dif x_j)/(dif t) = (partial F)/(partial xi_j), wide (dif y)/(dif t) = sum_(i) xi_i (partial F)/(partial xi_i) \
(dif xi_j)/(dif t) = -(partial F)/(partial x_j) - xi_j (partial F)/(partial y). $ After imposing a similar (but slightly more complex) transversality requirement, one can show similarly obtain a solution from this system by an inverse function theorem argument.

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
  so in particular, $u_k$ will diverge for $x_2 eq.not 0$. The unique solution for the limiting initial data $lim_(k -> infinity) phi_k (x_1) = 0$, though, is the trivial solution. So, there is clearly no "continuity" (in some vague, heuristic sense) in this situtation.
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
  Applying the chain rule, one verifies that, in polar coordinates, $ laplace u(x) = phi''(r) + (n - 1)/r phi'(r). $ Indeed, this gives rise to the so-called _radial Laplacian operator_
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
  We'll prove for $n >= 3$. Our idea will be to regularize $N$ by shifting the pole at the origin, take derivatives of our regularization, and show that what results converges to $delta$. For $epsilon > 0$, define $ N^epsilon (x) := (abs(x)^2 + epsilon^2)^((2 - n)/n)/(omega_n (2 - n)). $
  It's clear $N^epsilon -> N$ pointwise everywhere. Indeed, associating $N^epsilon, N$ with distributions in the typical sense (which is valid since they are both locally integrable), we have $N^epsilon -> N$ in $cal(D)'$ (one can see this by the fact that $|N^epsilon phi| <= |N| |phi|$, so we can apply dominated convergence to any test function $phi in C^infinity_c$). Next, one verifies $ laplace N^epsilon (x) = n/(omega_n) epsilon^2 (abs(x)^2 + epsilon^2)^(-(n + 2)/2). $ Let $psi(x) := n/omega_n (abs(x)^2 + 1)^(- (n + 2)/2)$; then one verifies $laplace N^epsilon (x) = psi_epsilon (x) := epsilon^(-n) psi(x/epsilon)$. Thus, for $phi in C^infinity_c$, we find $ angle.l laplace N^epsilon, phi angle.r = integral psi_epsilon (-x) phi(x) dif x = psi_epsilon convolve phi (0), $ using the radial symmetry of $psi$ to write as a reflection across the origin. By the following lemma:
  #lemma[
    Let $g in L^1$ with $a := integral g dif x$. Let $f in L^p$, $p >= 1$ (resp. $f in L^infinity$, uniformly continuous on some $V subset RR^n$). Then, $f convolve g_epsilon ->_(epsilon -> 0) a f$ in $L^p$ (resp. uniformly on $V$), where $g_epsilon (x) := epsilon^(-n) g(x/epsilon).$
  ]
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

We assume that $Omega subset RR^n$ bounded and $S = partial Omega$ is $C^infinity$ (and sufficiently nice t be able to apply Green's identities). We consider the _Dirichlet problem_, $ #rect("D", inset: 0.2em) wide laplace u = f "on" Omega, u|_S = g, $ where $f, g$ are given functions, and the _Neumann problem_, $ #rect("N", inset: 0.2em) wide laplace u = f "on" Omega, u|_S = partial_nu g, $ where $nu$ the exterior outward normal to $S$.

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
This can be shown using the previous integral formula and the remarks of the previous section linking solutions of #box("D1") and #box("D2").
