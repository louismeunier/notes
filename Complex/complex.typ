// ! external
#import "../typst/notes.typ": *
// #import "../typst/shortcuts.typ": *

#import "@preview/cetz:0.2.2"

// ! configuration
#show: doc => conf(
  course_code: "MATH249",
  course_title: "Complex Variables",
  subtitle: "",
  semester: "Winter 2026",
  professor: "Prof. Henri Darmon",
  // cute: "../analysis 3/page.png",
  doc,
)

#import "@preview/commute:0.2.0": arr, commutative-diagram, node

#set align(left)
#let boxit(arg) = box(stroke: 0.75pt, outset: 8pt, arg)

#pagebreak()

= Complex Numbers

The complex numbers are the set $ CC := {a + b i : a, b in RR}, $ where $i^2 = -1$. This set is readily equipped with operations of addition, subtraction, multiplication and division; given two complex numbers $a + b i, c + d i$, these operations are determined by the rules $ (a + b i) + (c + d i) & = (a + c) + (b + d ) i \
   (a + b i)(c + d i) & = a c - b d + (a d + b c) i \
          1/(a + b i) & = (a - b i)/(a^2 + b^2), $ assuming in the final line that $a^2 + b^2 eq.not 0$, i.e. that $a + b i eq.not 0$ in $CC$. In particular, in the division line, we obtain the result by multiplying the top and bottom by the _conjugate_ of $z := a + b i$; we denote $ overline(z) = a - b i, $ noting that in particular, $ z overline(z) = a^2 + b^2 = abs(z)^2. $

Any complex number $z = a +b i$ may be written in so-called _polar form_ $ z = r (cos theta + i sin theta), quad r := sqrt(a^2 + b^2) = abs(z), thin theta := "arg"(z) = arctan(b\/a), $ with the $theta$ read modulo $2 pi$. This is a useful representation for the sake of multiplication; given $z_i = r_i (cos(theta_i) + i sin(theta_i))$, $i = 1, 2$, we have $ z_1 z_2 = dots.c = r_1 r_2 [cos(theta_1 + theta_2) + i sin(theta_1 + theta_2)]. $
In particular, $ abs(z_1 z_2) = abs(z_1) abs(z_2), quad "arg"(z_1 z_2) = "arg"(z_1) + "arg"(z_2). $

#theorem[
  $cos(theta) + i sin(theta) = exp(i theta)$
]

#proof[Taylor expand both sides.]

In particular, this theorem gives a clear way to define the exponential of a complex number $ e^(x + i y) = e^x e^(i y) = e^x (cos(y) + i sin(y)), $ so that in particular, for any $z in CC$, $ abs(e^(z)) = e^("Re"(z)), quad "arg"(e^(z)) = "Im"(z). $

== Fundamental Theorem of Algebra

#theorem("Fundamental Theorem of Algebra")[
  If $f(z) = a_n z^n + a_(n - 1) z^(n - 1) + dots.c + a_1 z + a_0$ is a polynomial with complex coefficients $a_0, a_1, dots, a_(n-1), a_n$, then there exists a $z in CC$ such that $f(z) = 0$.
]

#proof[_(A First Proof)_
  Remark that if $abs(z) = R >> 1$ (much larger than zero), then we have $ abs(a_n z^n) & = abs(a_n) R^n, \
  abs(a_(n - 1) z^(n - 1) + dots.c + a_1 z + a_0) & <= abs(a_(n - 1)) R^(n - 1) + dots.c + abs(a_1) R + abs(a_0)\
  &<= (abs(a_(n - 1)) + abs(a_(n - 2)) + dots.c + abs(a_1) + abs(a_0)) R^(n - 1). $
  Let $z_0 in CC$ be a point for which $abs(f(z_0))$ is a minimum; this must exist for $abs(f)$ must be very large outside of the disc of radius $R$ centered at the origin. Namely, $abs(z_0) < R$. We claim $z_0$ a root of $f$. We may assume without loss of generality that $z_0 = 0$, by replacing $f(z)$ with $f(z - z_0)$. We write $ f(z) & = a_0 + dots.c + a_k z^k + dots.c + a_n z^n, \
       & = a_0 + a_k z^k (1 + a_(k + 1)/a_k z + dots.c + a_(n)/(a_k) z^(n - k)). $ where $a_k eq.not 0$ the first nonzero coefficient with $k >= 1$. If we can show $a_0 = 0$, we are done. Assume otherwise. Let $ z :=(- a_0/(a_k))^(1/k) epsilon, quad epsilon > 0. $ With this value of $z$, we have $ f(z) = a_0 - a_0 epsilon^k (1 + underbrace(dots.c, = cal(o)(epsilon)))
  approx a_0 (1 - epsilon^k). $ By choosing $epsilon$ sufficiently small, this implies $ abs(f(z)) < abs(a_0) = abs(f(0)), $ which contradicts the assumed minimality of $z_0 = 0$, unless of course $a_0 = f(z_0) = 0$, providing the claim.
]

#proof[(A Second Proof) We want to view $f(z)$ as a mapping $CC -> CC$. Assume $f(z) = z^n + a_(n - 1) z^(n - 1) + dots.c + a_1 z + a_0$. When $abs(z)$ large, we know $ abs(f(z) - z^n) < C abs(z)^(n-1), $ for some constant $C$ independent of $z$. Remark that the map $phi: z |-> z^n$ maps a circle of radius $R$ to a circle of radius $R^n$; in particular, if we take a point $z = R e^(i theta)$ on the circle of radius $R$ of angle $theta$ with the origin, and let $theta$ vary from $0$ to $2 pi$, one "rotation" in the pre-image world will lead to $n$ "rotations" in the image world. Similarly, for $z |-> f(z)$, the image of the $R$-radius circle may not be a circle, but a "fudged" circle; the curve of the image will still be some periodic curve. As we let $R -> 0$, though, the image will go to the singular point $a_0$. Thus, at some value of $R$, the image of the $R$-radius circle would have to pass through the origin, and thus this point must be a root of $f(z)$.
]

#proof[(A Third Proof) We use a result that we will prove later in the class, Liouville's Theorem, which states that any bounded differentiable function $f : CC -> CC$ must be constant.

  Suppose $p(z)$ a polynomial with no roots in $CC$. Let $f(z) = 1/(p(z))$ (this is well-defined, since by assumption $p$ has no roots); this is bounded on $CC$, and has derivative $(dif)/(dif z) f(z) = -( p'(z))/(p(z))$. By Liouville's, $f$ must be a constant and thus $p$ must be a constant.
]


== Analytic, Holomorphic Functions

#definition("Holomorphic/Analytic")[
  A function $f : CC -> CC$ is said to be _holomorphic_ is it has a well-defined derivative, i.e. if the limit $ lim_(h -> 0) (f(z + h) - f(z))/h $ exists and is well-defined (in the sense that it is independent of the "path" $h$ takes to 0).
]

We may write $f : CC -> CC$ as $ f(z) = f(x + i y) = u(x, y) + i v (x, y), $ where $u, v : RR^2 -> RR$. We can calculate $f'(z)$ in two different ways.

1. Restrict $h$ to $RR$: $ f'(z) = lim_(h -> 0, \ h in RR) (f(z + h) - f(z))/h & = lim_(h -> 0, \ h in RR) (u(x + h, y) +i v(x + h, y) - u(x, y) - i v (x, y))/h \
  &= lim_(h -> 0, \ h in RR) (u(x + h, y) - u(x, y))/h + i lim_(h -> 0, \ h in RR) (v(x + h, y) - v(x, y))/h \
  &= (partial u)/(partial x)(x, y) + i (partial v)/(partial x)(x, y). $

  2. Rescrict to $h$ purely imaginary values: $ f'(z) = lim_(h -> 0, \ h in RR) (f(z + i h) - f(z))/(i h) &= lim_(h -> 0, \ h in RR) (u(x, y + h) + i v(x, y + h) - u(x, y) - i v(x, y))/(i h) \
    &= 1/i (partial u)/(partial y)(x, y) + (partial v)/(partial y) (x, y) \
    &= (partial v)/(partial y) (x, y) - i (partial u)/(partial y)(x, y) $
    These two computations must of course agree, which imply (equating real, imaginary parts) $ (partial u)/(partial x) = (partial v)/(partial y), quad (partial v)/(partial x) = - (partial u)/(partial y). $ These are the _Cauchy-Riemann equations_. Viewing the pair $f = (u, v)$ as a mapping $RR^2 -> RR^2$, the Cauchy-Riemann equations imply that the Jacobian of $f$ is given in the form $ J_f (x, y) = mat(a, b; -b, a), quad a, b in RR. $

#proposition[
  - If $f, g$ are holomorphic and $a, b in CC$, then $a f + b g$ are also holomorphic, and moreover $(a f + b g)' = a f' + b g'$
  - With $f(z) := z^n$, $f'(z) = n z^(n - 1)$
  - As a result, any polynomial on $CC$ is holomorphic
]

#theorem[
  If $f$ satisfies the Cauchy-Riemann equations, then $f$ is holomorphic.
]

#proof[
  Write $f = u + i v$ as before.
  Let $h = h_1 + i h_2$. Then, $ u(x + h_1, y + h_2) = u(x, y) + h_1 partial_x u + h_2 partial_y u + abs(h) psi_1 (h), quad psi_1 (h) -> 0 "as" h-> 0, $ with similar for $v$ with a remainder $psi_2$. Then, by Cauchy-Riemann, $ f(z + h) & = f(z) + (partial_x v - i partial_y u) (h_1 + i h_2) + psi(h) abs(h), quad psi(h) = cal(o)(abs(h)). $ Dividng both sides by $h$ and sending $h -> 0$ gives the result.
]

== Power Series

We say a series $sum_(n=0)^infinity a_n z^n$, where $a_n, z in CC$, _converges_ if $lim_(N ->infinity) sum_(n=0)^N a_n z^n$ exists as a complex number. We say it a converges _absolutely_ if $lim_(N -> infinity) sum_(n = 0)^N abs(a_n) abs(z)^n$ exists.


#theorem[
  Given $sum_(n=0)^infinity a_n z^n$, there exists a number $0 <= R <= infinity$ for which
  1. if $abs(z) < R$, then $sum a_n z^n$ converges absolutely;
  2. if $abs(z) > R$, then $sum a_n z^n$ does not converge.
  Furthermore, $ 1/R = limsup_n abs(a_n)^(1/n). $
]

#proof[
  Let $L = 1/R$ and suppose $abs(z) < R$. There exists some $epsilon > 0$ such that $ r := (L + epsilon) abs(z) < 1. $ There exists some $N$ such that $L + epsilon > abs(a_n)^(1/n)$ for all $n > N$ by definition of limsup's; thus $ abs(z) abs(a_n)^(1/n) < ( L + epsilon ) abs(z) = r < 1 \
  => abs(z)^n abs(a_n) < r^n. $ But since $r < 1$, it follows that $sum abs(a_n) abs(z)^n$ converges by comparing to the geometric series $sum r^n$.

  If $abs(z) > R$, there is an $epsilon >0$ so that there are infinitely-many $n$'s for which $abs(a_n)^(1/n) > 1/R - epsilon$, and so $ abs(a_n)^(1/n) abs(z) > r > 1 $ hence $abs(a_n) abs(z)^n > r^n$, so that $sum abs(a_n) abs(z)^n$ diverges by comparison. Moreover, we have shown that $abs(a_n) abs(z)^n$ does not converge to zero, which implies the series does not even converge ("normally").
]

#example[
  1. $sum_(n=0)^infinity n! z^n$ has $R = 0$
  2. $sum_(n=0)^infinity (z^n)/(n!) = e^z$ with $R = infinity$.
  3. $sum_(n=0)^infinity z^n = 1/(1 - z)$ has $R = 1$.
]

#theorem[
  A power series $f(z) = sum_(n=0)^n a_n z^n$ admits a derivative on its disc of convergence, and $f'(z) = sum_(n=0)^infinity n a_n z^(n - 1)$.
]

#proof[
  Write $g(z) = sum_(n=0)^infinity n a_n z^(n - 1)$ as the "potential" derivative we aim to show, remarking that this seires converges and moreover has the same radius of convergence as $f$ since $lim n^(1/n) = 1$ and thus $limsup a_n^(1/n) = limsup (n a_n)^(1/n)$. Write $ f(z) = S_N (z) + E_N (z), quad S_N (z) := sum_(n=0)^N a_n z^n, thin E_N (z) := sum_(n=N+1)^infinity a_n z^n. $ Fix $z_0 in D_R (0)$. We show $(f(z_0 + h) - f(z_0))/h - g(z_0) -> 0$ as $h -> 0$. We can write $ (f(z_0 + h) - f(z_0))/h - g(z_0) & = (S_N (z_0 + h) - S_N (z_0))/h - g(z_0) + (E_N (z_0 + h) - E_N (z_0))/h \
  & = {(S_N (z_0 + h) - S_N (z_0))/h - S'_N(z_0)} + {S'_N (z_0) - g(z_0)} + {(E_N (z_0 + h) - E_N (z_0))/h} \
  &= (A) + (B) + (C). $

  For all $epsilon > 0$, there exists $N_1$ $abs((B)) < epsilon$ for all $N > N_1$.

  There exists $N_2$ such that $abs((C)) < epsilon$ for all $N > N_2$, since we have $ (C) = sum_(n >= N + 1) a_n ((z_0 + h)^n - z_0^n)/h, $ and $ (z_0 + h)^n - z_0^n = h ((z_0 + h)^(n - 1) + (z_0 + h)^(n - 2) z_0 + dots.c + (z_0 + h)^(n - j) z_0^j + dots.c + z_0^(n - 1)). $ Since $abs(z_0 + h), abs(z_0) < r < R$ for $h$ sufficiently small, we know $ abs((z_0 + h)^n - z_0^n) <= abs(h) n r^(n - 1), $ so that $ abs(((z_0 + h)^n - z_0^n)/h) <= n r^(n - 1). $ It follows that $ abs((C)) <= sum_(n = N + 1)^infinity abs(a_n) n r^(n - 1). $ This is the tail of an absolutely converging series, hence as $N -> infinity$, $abs((C)) -> 0$, so we have the claimed bound.

  Finally, let $N := "max"(N_1, N_2)$. We see that for any fixed $N$, $(A) -> 0$ as $h->0$ by the definition of the derivative, and thus we can take $h = h(N)$ sufficiently small so that $abs((A)) < epsilon$. Combining all these bounds gives the proof.
]

#corollary[
  $f(z) = sum a_n z_n$ is infinitely differentiable in its radius of convergence.
]

#definition[
  A function $f : Omega -> CC$ is called _analytic_ if it is equal to a power series on $D_epsilon (z_0)$ for all $z_0 in Omega$, for some $epsilon > 0$.
]

#corollary[
  $f$ analytic $=>$ $f$ holomorphic
]

#remark[We'll see later that these are actually equivalent notions.]

== Integration Along Curves

#definition[
  A parametrized curve is a function $gamma : [0, 1] -> CC$ where $gamma$ is differentiable with continuous derivative, with $gamma' (t) eq.not 0$ for all $t in [0, 1]$.
]

#definition[
  We'll say two parametrized curves $gamma, tilde(gamma)$ are equivalent if there exists a smooth function $s : [0, 1] -> [0, 1]$ smooth with $s'(t) > 0$ and such that $tilde(gamma) = gamma compose s$.
]

We will consider curves as defined up to equivalency in this way.

#definition[
  If $gamma$ is a parametrized curve, define $ integral_(gamma) f(z) dif z := integral_0^1 f(gamma(t)) gamma'(t) dif t. $
]
