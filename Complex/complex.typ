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

  If $gamma$ a piecewise smooth curve, i.e. $gamma$ can locally be written as $t |-> z(t) in CC$ for $t in [a_k, a_(k + 1))$ for $k = 0, dots, n-1$ for some sequence $a_k < a_(k + 1)$, then $ integral_(gamma) f(z) dif z := sum_(k=0)^(n + 1) integral_(a_k)^(a_(k + 1)) f(z(t)) z'(t) dif t. $
]

An obvious generalization holds for integration along more general intervals.


#proposition[
  Path integrals are independent of choice of parametrization.
]

#definition("Length of a curve")[
  Define, for $gamma$ given by $z : I -> CC$, $ "length"(gamma) := integral_(gamma) |dif z| = integral_(I) |z'(t)| dif t. $
]


#proposition[
  Let $f, g$ continuous and $alpha, beta in CC$. Then we have
  1. Linearity:  $ integral_(gamma) (alpha f + beta g) dif z = alpha integral_(gamma) f dif z + beta integral_(gamma) g dif z. $
  2. $ integral_(gamma) f(z) dif z = - integral_(gamma^(-)) f(z) dif z, $ where $gamma^-$ is the _reverse path_ of $gamma$.
  3. $abs(integral_(gamma) f(z) dif z) <= sup_(z in gamma) |f(z)| "length"(gamma)$.
]

#definition("Primitive")[
  A _primitive_ of a continuous function $f$ on a domain $Omega$ is a function $F$ such that $F' = f$ on $Omega$.
]

#proposition[
  If $f$, continuous, has a primitive $F$ on $Omega$ and $gamma$ is a curve in $Omega$ beginning at $w_1$ and ending at $w_2$, then $ integral_(gamma) f dif z = F(w_2) - F(w_1). $
]

== Cauchy's Theorem
#theorem("Cauchy")[
  If $gamma$ is a closed path contained in a region $Omega subset CC$ and its interior, and $f$ is holomorphic in $Omega$, then $integral_(gamma) f(z) dif z = 0$.
]

It will take us some building to get here. In a simple case, though, we have a positive result:

#corollary[
  If $f$ has a primitive $F$ on $Omega$, then Cauchy's theorem holds for $f$ for any $gamma$ a closed path in $"int"(Omega)$
]

#proof[
  Apply the last proposition; now, $F(w_2) = F(w_1)$, so we have the result.
]

With some more work, we can also establish the proof for $gamma$ some simple contour.

#proposition("Gorsut's Lemma")[
  Let $gamma$ be a closed triangle in $Omega$ and $f$ a holomorphic function on $Omega$. Then $integral_(gamma) f(z) dif z = 0$.
]

#proof[
  I'll add it later. Basically, follows from subsequent subdivision of the triangles and approximation of the total integral of $f$ over these triangles.
  // TODO
]

#corollary[
  If $R$ a closed rectangle and $Omega$ and $f$ holomorphic on $Omega$, then $integral_(R) f(z) dif z = 0$.
]

#proof[
  A rectangle can be written as two triangles, with the "inner region" cancelling. // TODO: add picture with orientation.
]


=== Primitives


#theorem[
  Let $f$ be holomorphic on an open disc $Omega$. Then, $f$ has a primitive on that disc.
]

#proof[
  Assume wlog that $Omega$ centered at the origin. Fix $z in Omega$ and let $gamma_z$ be the path that first travels horizontally from $0$ to $"Re"(z)$ along the real axis, then vertical to $z$. Define $ F(z) := integral_(gamma_z) f(w) dif w. $ We claim $F'(z) = f(z)$. Let $h in CC$ be small so that $z + h in Omega$, and consider the difference $ F(z + h) - F(z) = integral_(gamma_(z + h)) f (w) dif w - integral_(gamma_z) f(w) dif w. $

  These integrals have $f$ being integrated from $0$ horizontally to $"Re"(z + h)$ then vertically to $z + h$, then, in the _opposite_ orientation, from $z$ to $"Re"(z)$, then $"Re"(z)$ to 0. In particular, the two components $z -> "Re"(z)$ cancel in these two integrals, being oppositely oriented, so we are left with the contour from $z$ vertically to $"Re"(z)$, horizontally to $"Re"(z + h)$, the vertically to $z + h$. Connect $z$ to $z + "Re"(h)$ via a horizontal line, and $z$ to $z + h$ via a diagonal. This forms an (oriented) triangle and a rectangle, plus an extra diagonal, which by Gorsut's lemma must all integrate out to zero (draw it). Thus, $ F(z + h) - F(z) = integral_eta f(w) dif w, $ where $eta$ the diagonal from $z$ to $z + h$. Since $f$ continuous, $f(w) = f(z) + psi(w)$ where $psi(w) -> 0$ as $w -> z$; thus, $ F(z + h) - F(z) & = f(z) integral_eta dif w + integral_(eta) psi(w) dif w \
                  & = f(z) h + integral_(eta) psi(w) dif w \
                  & => f(z) = lim_(h -> 0) (F(z + h) - F(z))/h - lim_(h -> 0) 1/h integral_eta psi(w) dif w. $
  But since $ 1/h abs(integral_eta psi(w)) <= 1/h sup_(eta) |psi| |eta| = sup_(eta) |psi| ->_(h -> 0) 0, $ we have proven the claim.
]


// TODO the stuff here that I missed lol

#theorem("Cauchy's Integral Formula")[
  Let $f$ holomorphic on $Omega$ containing the closure of a disc $D$. Let $C$ be the boundary of this disc, then for any $z in D$,
  $
    f(z) = 1/(2 pi i) integral_(C) (f(xi))/(xi - z) dif xi.
  $
]

#remark[The same result holds for more general curves $C$ as long as $z in "int"(C)$; how/when the results extend should be clear from the proof.]



#corollary[
  $f'(z_0) = 1/(2pi i) integral_C (f(z))/(z - z_0)^2 dif z$, and more generally, $ f^((n)) (z_0) = (n!)/(2 pi i) integral_(C) (f(z))/((z - z_0)^(n + 1)) dif z. $
  So in general, $f$ holomorphic $=>$ $f$ is infinitely differentiable.
]



#corollary[
  $abs(f^((n)) (z_0)) <= (n! norm(f)_(C_R (z_0)))/R^n$, where $C_r (z_0)$ the circle of radius $R$ centered at $z_0$.
]

#theorem[$f$ is analytic centered at $z = z_0$.]

#proof[
  We can write $ f(z) = 1/(2 pi i) integral_C f(w)/(w - z) dif w, $ for some circle $C$ containing $z$. We can expand $ 1/(w - z) & = 1/((w - z_0) - (z - z_0)) \
            & = 1/(w - z_0) dot.c 1/(1 - (z - z_0)/(w - z_0)) \
            & = 1/(w - z_0) sum_(n=0)^infinity [(z - z_0)/(w - z_0)]^n \
            & = sum_(n=0)^infinity (z - z_0)^n/(w- z_0)^(n + 1) $ so that $ f(z) & = 1/(2 pi i) integral_(C) f(w) sum_(n=0)^infinity (z - z_0)^n/(w - z_0)^(n + 1) dif w \
       & = 1/(2 pi i) sum_(n=0)^infinity [integral_C f(w)/((w - z_0)^(n + 1)) dif w] (z - z_0)^n \
       & = sum_(n=0)^infinity a_n (z - z_0)^n, quad quad a_n := 1/(2pi i) integral_(C) (f(w))/((w - z_0)^(n + 1)) dif w. $ But we also realize that $ a_n = (f^((n)) (z_0))/n! $ from our previous result, hence we conclude $ f(z) = sum_(n=0)^infinity (f^((n)) (z_0))/n! (z - z_0)^n, $ as we expect from the real-valued analog.
]

#remark[
  In particular, this implies, from our previous result, that $abs(a_n) <= C/R^n$, where $C$ a constant uniform in $n$ and $R$ the radius of the circle upon which we're integrating. In particular, this means $ abs(a_n)^(1\/n) <= (C^(1\/n))/(R), $ which we see converges to $1/R$ as $n -> infinity$, hence our series above has radius of convergence at least $R$; i.e., the power series for $f$ converges on any $D_R (z_0) subset Omega$.
]

Thus, we've shown that holomorphic $=>$ analytic, and thus the two are equivalent (with appropriate assumptions on the space upon which they are defined, etc) since we showed the converse earlier.


#theorem("Lioville's Theorem")[If $f$ is holomorphic on $CC$ and bounded, then $f$ is constant.]

#proof[
  We know that for any $z_0 in CC$, $ |f'(z_0)| <= (norm(f)_(C))/(R), $ for any circle $C$ with $z_0$ center and of radius $R$. Since $f$ bounded, this means $ abs(f'(z_0)) <= 1/R sup_CC |f| -> 0, R -> infinity. $ This means $f'(z_0) = 0$ everywhere and thus $f$ is constant. We could take $R -> infinity$ since $f$ holomorphic everywhere hence on every disc $D_R (z_0)$ for $R > 0$.
]

== Rigidity of Holomorphic Functions

#theorem[Suppose that $f$ holomorphic in $Omega$ and vanishes on a sequence of distinct points $z_1, dots, z_n in Omega$ with a limit point $z_infinity in Omega$. Then, $f equiv 0$ on an open disc about $z_infinity$.]

#proof[
  Let $D$ be a disc centered at $z_infinity$ and contained in $Omega$. We write $ f (z) = sum_(n>=N)(f^((n)) (z_infinity))/n! (z - z_infinity)^n = a_N (z - z_infinity)^N sum_(n = 0)^infinity a_(N + n + 1)/(a_N) (z - z_infinity)^(n) $ where $N >= 1$ the minimal integer such that $f^((N)) (z_0) eq.not 0$ and $a_n := (f^((n)) (z_infinity))/n!$. We see that if $D$ sufficiently small, both $ (z - z_infinity)^n, quad (1 + a_(N + 1)/(a_N) (z - z_infinity) + dots.c) $ has no additional zeros in a sufficiently small disc centered at $z_infinity$; but this contradicts the fact that $z_n -> z_infinity$, i.e. there should be infinitely many zeros when $n -> infinity$. This is a contradiction, and hence there is no minimal $N$ for which $f^((n)) (z_infinity)$ doesn't vanish. Hence, it must be that $f$ identically zero on this small disc.
]


#proposition[
  If $f$ holomorphic and $f(z) = 0$ on a small disc $D subset Omega$ then $f equiv 0$ on $Omega$.
]

#proof[
  Let $ U = "int"({z in Omega : f(z) eq 0}). $
  This set is open and nonempty $(D subset U)$. It is also closed; to see this, let ${z_n} subset U$ with limit $z$. Then by the previous theorem, $f(z) = 0$, and thus $z in U$ so $U$ closed. But $Omega$ connected, so $Omega = U$.
]

This basically says that local behavior of holomorphic functions gives us information about the global behaviour.


#corollary("Principle of Analytic Continuation")[
  If $f, g$ are holomorphic on $Omega$ and $f(z) = g(z)$ for either \
  (a) $z$ in a nonempty open subset of $Omega$, or \
  (b) a sequence ${z_n}$ and its limit point
  Then $f = g$ on $Omega$.
]

#proof[
  Consider $f - g$ and apply the previous.
]

=== Special Cases

1. Let $f(z) = e^z$ and let $g(z)$ be any other holomorphic extension of $e^x$. Then, $f = g$ on $RR$, and thus agree everywhere; this is the unique extension of the exponential, i.e. $e^(x + i y) = e^x (cos y + i sin y)$.

2. Consider the Riemann zeta function, $ zeta(k) = sum_(n >= 1) 1/(n^k), $ converges for $k = 2, 3, dots$. If we allow $k = u + i v in CC$, we can write $ 1/n^k = exp(log(1/n) (u + i v)) $ thus $ |1/(n^k)| = exp(log(1/n) u) = 1/n^u, $ so that $ abs(zeta(u + i v)) < sum_(n=1)^infinity |1/(n^(u + i v))| =sum_(n=1)^infinity 1/(n^u), $ which converges when $u > 1$. Thus, $zeta(s)$ for $s in CC$ converges (absolutely) whenever $"Re"(s) > 1$. Riemann showed that $zeta(s)$ admits a holomorphic extension to $CC minus {1}$.
