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
]
