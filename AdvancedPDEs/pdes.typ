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
  2. $partial_x^2 u - partial_t u = 0$ dictates that $phi_0'' (x) = phi_1 (x)$, so we can't choose arbitrary initial conditions again.
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

We can do even better:
#lemma[
  The problem (1) is equivalent to one in the same form as the previous lemma, but with $A_j$ and $B$ independent of $t$ (and $Y$ now of 1 higher dimension).
]

This last one is easy; we just introduce an additional component to $Y$ such that $partial_t Y = 1$, and subtract the initial conditions from our original $B$.

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

Assuming we can do this we'll be done. We claim that a solution to $(1')$ will majorize our constructed solution to $(1)$, which would imply our desired result (namely, that this solution converges). Indeed, we have that since each $Q_(m)^(alpha j)$ has nonnegative coefficients, $ |c_m^(alpha j)| = |Q_m^(alpha j) ("coeff." A_i, B)| <= Q_m^(alpha j) ("coeff." tilde(A)_i, tilde(B))= tilde(c)_m^(alpha j), $ and thus $sum tilde(c)_m^(alpha j) x^alpha t^j$ majorizes $sum c_m^(alpha j) x^(alpha) t^alpha$, and thus the former converges near the origin.

We proceed then to construction $tilde(A)_j, tilde(B)$ for $(1')$ and its conditions to hold. By (v) above, there exists $M > 0$ and $r > 0$ such that the series for each $A_i$ and $B$ are majorized by the (geometric) series for $ (M r)/(r - (x_1 + dots.c + x_(n - 1) - (y_1 + dots.c + y_N))). $ Thus, chosen in this way, consider our candidate $(1')$ as $ partial_t y_m = (M r)/(r - sum_(i=1)^(n - 1) x_i - sum_(j=1)^N y_j) (sum_(i=1)^(n - 1) sum_(j=1)^N partial_i y_(j) + 1), wide y_m (x, 0) = 0, $ for each $1 <= m <= N$, noting that by choice of $M, r$, $tilde("(ii)")$is satisfied, so we just need to show that this has a $C^omega$ solution.

Remark that this system is completely symmetric under permutation of the $x_j, y_m$ variables, and thus if we find a solution $u = u(s, t)$ to the system $ (1'') wide partial_t u = (M r)/(r - s - N u) (N (n - 1) partial_(s) u + 1 ), wide u(s, 0) = 0, $ where $(s, t) in RR^2$, then setting $ y_j = u(x_1 + dots.c + x_n, t), wide j = 1, dots, N, $ gives a solution to $(1')$. But $(1'')$ is just a quasilinear system, in $RR^2$, which we know how to handle. Indeed, it has characteristic equations (using $tau$ as our "characteristic" parameter) $ (dif t)/(dif tau) = n - s - N u, wide (dif s)/(dif tau) = - M r (N - 1), wide (dif u)/(dif tau) = M r\
t(0) = 0, s(0) = sigma, u(0) = 0, $ using $sigma$ as our parametrization variable along $tau = 0$. Solving this system, one readily finds $ t(tau) = 1/2 M r N (n - 2) tau^2 + alpha tau, wide s(tau) = -M r (N - 1) tau + sigma, wide u(tau) = M r tau, $ where $alpha$ an arbitrary constant. Inverting these to solve for $tau(s, t), sigma(s, t)$ and plugging into $u$ (indeed, $u$ only depends on $tau$ so it suffices to solve for this parameter), readily yields $ u(s, t) = (r - s - sqrt((r - s)^2 - 2 M r N t))/(M n). $ This is analytic in $(s, t)$ near the origin (indeed, we can avoid any blow-ups in the higher derivatives of $sqrt(dots)$), and thus $u in C^(omega)$. "Changing variables" to $u(x_1 + dots + x_n, t)$ will not change this analyticity, and so we have finished our proof. #h(1fr) $square.filled$



