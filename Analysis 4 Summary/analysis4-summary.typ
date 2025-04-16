// ! external
// #import "../notes.typ": conf
#import "../typst/shortcuts.typ": *
// ? Change me:

#let conf = (
  course_code: "MATH455",
  course_title: "Analysis 4",
  subtitle: "Functional Analysis - Summary",
  semester: "Winter 2025",
  professor: "Prof. Jessica Lin",
  author: "Louis Meunier"
)

// ! packages
#import "@preview/ctheorems:1.1.2": *
#import "@preview/commute:0.2.0": node, arr, commutative-diagram

// ! font sizes
#let fontsizes = (
  normal: 12pt,
  section: 12pt,
  subsection: 12pt,
  large: 20pt,
  small: 10pt
)
// #let fontsizes.normal = 12pt
// #let fontsizes.section = 14pt
// #let subfontsizes.section = 12pt
// #let large-size = 20pt
// #let small-size = 8pt

// ! colours
#let solarized = (
  yellow: rgb("#b58900"),
  orange: rgb("#cb4b17"),
  red: rgb("#dc322f"),
  magenta: rgb("#d33682"),
  violet: rgb("#6c71c4"),
  blue: rgb("#268bd2"),
  cyan: rgb("#2aa198"),
  cyanlight: rgb("#d4ecea"),
  green: rgb("#859900"),
  base2: rgb("#eee8d5"),
  gray: rgb("#f2f2f2")
)

// ! defaults 

#set page(
  margin: 1.5cm,
  footer-descent: 60%,
  header-ascent: -5%
)
#set text(
    font: "TeX Gyre Pagella",
    size: fontsizes.normal
  )
// #show raw: set text(font: "Palatino")

#set align(left)
#show link: set text(fill: solarized.cyan)
#show link: underline
#set list(indent: 2em)
#set enum(indent: 2em)

// ! theorems
#show: thmrules.with(qed-symbol: $square.small.filled$)

#let thmsettings = (
  inset: (top: 0.6em, left: .5em, right: .5em, bottom: 0.8em),
  base_level: 0
)

#let proof = thmproof("proof", 
  text(
    smallcaps("solution"),
    // highlight("Proof", fill: white, stroke: black, top-edge: "cap-height", extent: 3pt), 
    style: "oblique", 
    weight: "regular"
  ),
  inset: (top: 0em, left: 2.8em, right: 1.4em),
  separator: [#h(0.1em). #h(0.2em)],
)

#let theorem = thmbox("theorem", "Theorem", base_level:0,inset:(y: 0em, top: 0em, bottom: 0em))
#let corollary = thmbox("corollary", "Corollary", base_level:0,inset:(y: 0em, top: 0em, bottom: 0em))
#let definition = thmbox("definition", "Definition",base_level:0,inset:(y: 0em, top: 0em, bottom: 0em))
#let remark = thmplain("remark", "Remark",base_level:0, inset:(y: 0em, top: 0em, bottom: 0em))

// #let definition = thmbox("definition", "Definition")

#set heading(numbering: "1.1")


#set page(footer: context [
  #let elems = query(
    selector(heading).before(here())
  )
  // #let subsection = elems.last().body
  // #let num = elems.last().numbering

  // #text(num, size: fontsizes.small)
  // #text(subsection, size: fontsizes.small)
  #h(1fr)
  #text(counter(page).display(
    "1",
    // both: true,
  ),
  size: fontsizes.small
  )
])
 #show heading.where(
    level: 1
  ): it =>text(
    size: fontsizes.section,
    weight: "bold",
    if (it.numbering != none) {
      par(leading: 0em, first-line-indent: 0em, counter(heading).display(it.numbering) + h(.5em) + it.body +"\n")
    } else {
      par(leading: 0em, first-line-indent: 0em, it.body + [.]+"\n")
    }
  )
#show heading.where(
    level: 2
  ): it => text(
    size: fontsizes.normal,
    weight: "semibold",
    // style: "italic",
    par(leading: 0em, first-line-indent: 0em, counter(heading).display(it.numbering) + h(.5em) + it.body)
    // it.numbering + h(.5em) + it.body + [.],
  )
  #show heading.where(
    level: 3
  ): it => text(
    size: fontsizes.subsection,
    weight: "semibold",
    // style: "italic",
    par(leading: 0em, first-line-indent: 0em, counter(heading).display(it.numbering) + h(.5em) + it.body)
    // it.numbering + h(.5em) + it.body + [.],
  )
// #set page(header: context [
//   #let elems = query(
//     selector(heading).before(here())
//   )
//   #text(conf.class + " - " + conf.assignment, size: fontsizes.small) 
//   #h(1fr)
//   #text(conf.author + " (" + conf.student_id + ")", size: fontsizes.small)  
//   #line(
//     start: (0pt, -10pt),
//   length: 100%,
//   stroke: 0.1pt
// )
// ])

#set align(left)
#set enum(numbering: "(i)")

#let boxit(arg) = box(stroke: 0.75pt,  outset: 8pt, arg)


// Page
#v(3em)
#set align(left)
#text(18pt, conf.course_code, weight:"bold") #text(18pt, " - " + conf.course_title)
#text(12pt, "\n"+conf.subtitle)
// if cute != none {
//   // set align(center)
//  figure(
//     image(cute, width: 40%)
//   ) 
// }
// set align(left)
#text(12pt, "\n\n" +conf.semester + ", " + conf.professor + ".")
#text(12pt, "\nNotes by " + conf.author)

#set par(
  first-line-indent: 1em,
  leading: 0.5em,
  linebreaks: "simple"
)

#v(2em)
#outline(title: none, fill: none)

= Linear Operators

#definition[For $X, Y$ normed vector spaces, $cal(L)(X, Y) := {T : X -> Y | norm(T) := sup_(x in X) (norm(T x)_Y)/(norm(x)_X) < infinity}$]

#theorem[$T : X -> Y$ bounded iff continuous; if $X, Y$ Banach, so is $cal(L)(X, Y)$.]

#theorem[
  1. Any two nvs of the same finite dimension are isomorphic;
  2. Any finite dimensional space complete, any finite dimensional subspace is closed;
  3. $overline(B(0, 1))$ compact in $X$ iff $X$ finite dimensional.
]

// #remark[The last result follows from Riesz's Lemma, which states ]

#theorem("Open Mapping")[
  Let $T : X -> Y$ a bounded linear operator where $X, Y$ Banach. Then, if $T$ surjective, $T$ _open_, that is, $T(cal(U))$ open in $Y$ for any $cal(U)$ open in $X$.
]

#remark[
By scaling & translating, openness of an operator is equivalent to proving $T(B_X (0, 1))$ contains $B_Y (0, r)$ for some $r > 0$.
]

#corollary[
  If $T : X-> Y$ bounded, linear and bijective for $X, Y$ Banach, $T^(-1)$ continuous. In particular, if $(X, norm(dot)_1), (X, norm(dot)_2)$ are two Banach spaces such that $norm(x)_2 <= C norm(x)_1$, then $norm(dot)_1, norm(dot)_2$ are equivalent.
]

#theorem("Closed Graph Theorem")[
  Let $T : X -> Y$  where $X, Y$ Banach. Then $T$ continuous iff $T$ is _closed_, i.e. the graph $G(T) := {(x, T x) : x in X} subset X times Y$ is closed in the product topology.
]

#remark[
  This theorem crucially uses the fact that the norm $
  norm((x, y))_ast := norm(x)_X + norm(y)_Y
  $ (among others) induces the product topology on $X times Y$, hence in particular such a norm can be used to make $X times Y$ a nvs.
]

#theorem("Uniform Boundedness")[
  Let $X$ Banach and $Y$ an nvs, and let $cal(F) subset cal(L)(X, Y)$ such that  $forall x in X, exists M_x > 0$ s.t. $norm(T x)_Y <= M_x forall T in cal(F)$ (that is, $cal(F)$ pointwise bounded). Then, $cal(F)$ uniformly bounded, i.e. there is some $M > 0$ such that $norm(T)_Y <= M$ for every $T in cal(F)$.
]

#remark[
  This is implied by the consequence of the Baire Category theorem that states that if $cal(F) subset C(X)$ where $X$ a complete metric space and $cal(F)$ pointwise bounded, then there is a nonempty open set $cal(O) subset X$ such that $cal(F)$ uniformly bounded on $cal(O)$. In the case of a nvs, by linearity, being uniformly bounded on an open set extends to being uniformly bounded on all of $X$.
]

#theorem("Banach-Saks-Steinhaus")[
  Let $X$ Banach and $Y$ an nvs, and ${T_n} subset cal(L)(X, Y)$ such that for every $x in X$, $lim_(n) T_n (x)$ exists in $Y$. Then
  1. ${T_n}$ uniformly bounded in $cal(L)(X, Y)$;
  2. $T in cal(L)(X, Y)$ where $T (x) := lim_(n) T_n (x)$;
  3. $norm(T) <= liminf_(n) norm(T_n)$.
]

#remark[
  (i) follows from uniform boundedness, (ii) from just taking sums limits, (iii) from taking lim(inf)its.
]

= Hilbert Spaces; Weak Convergence


#theorem("Cauchy-Schwarz")[$|(u,v)| <= norm(u) norm(v)$.]

#theorem("Orthogonality")[
  If $M subset H$ a closed subspace, for every $x in H$, there is a unique decomposition $
  x = u + v, wide u in M, v in M^perp := {v in H | (v, y) = 0 forall y in M},
  $ and $
  norm(x - u) = inf_(y in M) norm(x - y), wide norm(x - v) = inf_(y in M^perp) norm(x - y).
  $
]

#theorem("Riesz")[
  For $f in H^ast := cal(L)(H, RR)$,  there is a unique $y in H$ such that $f(y) = (y, x), forall x in H$.
]

#theorem("Bessel's Inequality")[
  If ${e_n} subset H$ orthonormal, then $sum_(i=1)^infinity abs((x, e_i))^2 <= norm(x)^2$.
]

#theorem("Equivalent Notions of Orthonormal Basis")[
  If ${e_n} subset H$ orthonormal, TFAE:
  1. if $(x, e_i) = 0$ for every $i$, $x = 0$;
  2. _Parseval's identity_ holds, $norm(x)^2 = sum_(i=1)^infinity (x, e_i)^2$, for every $x in H$;
  3. ${e_i}$ a basis for $H$, that is $x = sum_(i=1)^infinity (x, e_i) e_i$ for every $x in H$.
]
#theorem[$H$ is separable (has a countable dense subset) iff $H$ has a countable basis.]

#theorem("Properties of the Adjoint")[
  For $T : H -> H$, the _adjoint_ $T^ast : H -> H$ is defined as the operator with the property $(T x, y) = (x, T^ast y)$ for every $x, y in H$. Then: 
  - if $T in cal(L)(H)$ then $T^ast in cal(L)(H)$ and $norm(T^ast) = norm(T)$;
  - $(T^ast)^ast = T$;
  - $(T + S)^ast = T^ast + S^ast$;
  - $(T compose S)^ast = S^ast compose T^ast$;
  - if $T in cal(L)(H)$, then 
    - $N(T^ast) = R(T)^perp$, and similarly,
    - $N(T) = R(T^ast)^perp$.
    Note that then $R(T)^perp$ closed, so one finds $(R(T)^perp)^perp = overline(R(T))$.
]

#definition("Weak Convergence")[
 We say ${x_n} subset X$ _converges weakly_ to $x in X$ and write $x_n harpoon.rt x$ if for every $T in X^ast$, $T x_n -> T x$. By Riesz, this is equivalent to saying $(x_n, y) -> (x, y)$ for every $y in X$.

 We define, then, $sigma(X, X^ast)$ to be the weak topology (on $X$) generated by the collection of functions $X^ast$; i.e., the coarsest topology for which every functional $T in X^ast$ is continuous.
]

#theorem("Properties of Weak Convergence")[
  1. If $x_n harpoon.rt x$, then ${x_n}$ bounded in $H$ and $norm(x) <= liminf_(n->infinity) norm(x_n)$.
  2. If $y_n -> y$ (strongly) and $x_n harpoon.rt x$ (weakly) then $(x_n, y_n) -> (x, y)$.
]

#theorem("Helley's Theorem")[
  Let $X$ a separable normed vector space and ${f_n} subset X^ast$ such that there is a $C > 0$ such that $abs(f_n (x)) <= C norm(x)$ for every $x in X$ and $n >= 1$. Then, there is a subsequence ${f_n_k}$ and $f in X^ast$ such that $f_n_k (x) -> f(x)$ for every $x in X$.
]
#remark[
  This is just the Arzelà-Ascoli Lemma; by linearity, the uniform boundedness implies uniform Lipschitz continuity and thus equicontinuity. 
]

#theorem("Weak Compactness")[
  Every bounded sequence in $H$ has a weakly converging subsequence.
]

#remark[
  This is a consequence of Helley's.
]


= $L^p$ Spaces

#theorem([Basic Properties of $L^p (Omega)$])[
  1. (Holder's Inequality) $norm(f g)_1 <= norm(f)_p norm(g)_q$ for $f in L^p (Omega), g in L^q (Omega)$ and $1/p + 1/q = 1, 1 <= p <= q <= infinity$;
  2. (Riesz-Fischer Theorem) $L^p (Omega)$ is a Banach space for every $1 <= p <= infinity$;
  3. $C_c (RR^d)$, simple functions, and step functions are all dense in $L^p (RR^d)$ for every finite $p$;
  4. $L^p (Omega)$ is separable for every finite $p$;
  5. If $Omega subset RR^d$ has finite measure, then $L^p (Omega) subset L^p' (Omega)$ for every $p >= p'$;
  6. If $f in L^p (Omega) sect L^q (Omega)$ for $1 <= p <= q <= infinity$, then $f in L^r (Omega)$ for every $r in [p, q]$.
]

#theorem([Riesz Representation for $L^p (Omega)$])[
Let $1 <= p < infinity$ and $q$ the Holder conjugate of $p$. Then, if $T in (L^p (Omega))^(ast)$, there is a unique $g in L^q (Omega)$ such that $
T f = integral_(Omega) f g, wide forall f in L^p (Omega),
$ and $norm(T) = norm(g)_q$.
]

#remark[
  When $p = 2 = q$, then $L^p (Omega)$ is a Hilbert space so this reduces to the typical Hilbert space theory.
]

#theorem([Weak Convergence in $L^p (Omega)$])[
- Let $p in (1, infinity)$ and ${f_n} subset L^p (Omega)$, then by Riesz, $f_n harpoon.rt f$ iff $integral_Omega f_n g -> integral_Omega f g$ for every $g in L^q (Omega)$. 
- Suppose $f_n$ are bounded and $f in L^p (Omega)$, then $f_n harpoon.rt f$ if and only if $f_n -> f$ pointwise a.e..
- (Radon-Riesz) For $p in (1, infinity)$, let ${f_n} subset L^p (Omega)$ such that $f_n harpoon.rt f$. Then, $f_n -> f$ strongly if and only if $norm(f_n)_p -> norm(f)$.
]

#theorem([Weak Compactness in $L^p (Omega)$])[
  Let $p in (1, infinity)$. Then, every bounded sequence in $L^p (Omega)$ has a weakly converging subsequence in $L^p (Omega)$.
]

#remark[This is essentially the same as the Hilbert space proof.]

#theorem("Properties of Convolutions")[
  1. $(f ast g) ast h = f ast (g ast h)$
  2. With $tau_z f(x) := f(x - z)$, $tau_z (f ast g) = (tau_z f) ast g = f ast (tau_z g)$
  3. $"supp"(f ast g) subset.eq overline("supp"(f) + "supp"(g)) = overline({x + y | x in "supp"(f), y in "supp"(g)})$
]

#theorem("Young's Inequality")[
  Let $f in L^1 (RR^d)$ and $g in L^p (RR^d)$ for any $p in [1, infinity]$, then $
  norm(f ast g)_p <= norm(f)_1 norm(g)_p,
  $ so in particular $f ast g in L^p (Omega)$.
]

#theorem("Derivatives of Convolutions")[
  Let $f in L^1 (RR^d)$ and $g in C^1 (RR^d)$ with $|partial_i g| in L^infinity (RR^d)$ for $i = 1, dots, d$. Then, $f ast g in C^1 (RR^d)$, and in particular $
  partial_i (f ast g) = f ast (partial_i g).
  $
]

#remark[
  This holds more generally for many different assumptions on $f, g$ but you basically need to be able to apply dominated convergence theorem to pass the limit involved in taking the derivative under the integral sign.

  This extends for $g in C^k (RR^d)$; in particular, if $g in C^infinity (RR^d)$, then $f ast g in C^infinity (RR^d)$. It also holds for the gradient, i.e. $gradient (f ast g) = f ast (gradient g)$ (where the convolution is component-wise in the gradient vector).
]

#theorem("Good Kernels")[
  A _good kernel_ is a parametrized family of functions ${rho_epsilon : epsilon in RR}$ with the properties 
  1. $integral_(RR^d) rho_epsilon (y) dif y = 1$,
  2. $integral_(RR^d) |rho_epsilon (y)| dif y <= M$,
  3. for every $delta > 0$, $integral_(|y| > delta) abs(rho_epsilon (y)) dif y -> 0$ as $epsilon -> 0^+$.

  The canonical, and in particular both smooth and compactly supported, example is $
rho (x) := cases(
C exp(-1/(1 - |x|^2)) & "if" |x| <= 1,
0 & "o.w."
  ),
  $ where $C = C(d)$ a scaling constant such that $rho$ integrates to $1$. Then $rho_epsilon (x) := (1/epsilon^d) rho(x/epsilon)$ is a good kernel, supported on $B(0, epsilon)$. Then: 

  1. if $f in L^infinity (RR^d)$, $f_epsilon := rho_epsilon convolve f$ and $f$ continuous at $x$, then $f_epsilon (x) -> f(x)$ as $epsilon -> 0$;
  2. if $f in C(RR^d)$ then $f_epsilon -> f$ uniformly on compact sets;
  3. if $f in L^p (RR^d)$ with $p$ finite, then $f_epsilon -> f$ in $L^p (RR^d)$.
]

#remark[
  Part 3. follows immediately from 2. by density of $C_c (RR^d)$ in $L^p (RR^d)$.
]

#corollary[$C^infinity_c (RR^d)$ dense in $L^p (RR^d)$ for any finite $p$.]

#theorem("Weierstrass Approximation Theorem")[
Polynomials are dense in $C([a, b])$, i.e. for any $f in C([a, b])$ and $eta > 0$, there is a polynomial $p(x)$ such that $norm(p - f)_(L^infinity ([a, b])) < eta$.
]

#theorem("Strong Compactness")[
  Let ${f_n} subset.eq L^p (RR^d)$ for $p$ finite, such that 
  - ${f_n}$ uniformly bounded in $L^p (RR^d)$, and 
  - $lim_(|h| -> 0) norm(f_n - tau_h f_n)_p = 0$ uniformly in $n$, i.e. for every $eta > 0$ there is a $delta > 0$ such that $|h| < delta$ implies $norm(f_n - tau_h f_n)_p < eta$ for every $n >= 1$.
Then, for every $Omega subset RR^d$ of finite measure, there exists a subsequence ${f_n_k}$ such that $f_n_k -> f$ in $L^p (Omega)$.
]

#remark[
  This is Arzelà-Ascoli in disguise! 
]


= Fourier Analysis

#definition("Fourier Series")[Let $L^2 (TT) = {f : TT -> RR | integral_TT f^2 < infinity}$ equipped with the inner product $(f, g) = integral_(TT) f overline(g)$. Then, $e_n (x) := e^(2 pi i n x)$, for $n in ZZ$, is an orthonormal basis for $L^2 (TT)$. The _Fourier coefficients_ of a function $f$ are defined then, for $n in ZZ$, $
hat(f)(n) = (f, e_n) = integral_(TT) f(x) e^(-2 pi i n x) dif x,
$ and so the _complex Fourier series_ is defined $
sum_(n in ZZ) hat(f)(n) e^(2 pi i n x).
$]

#theorem("Riemann-Lebesgue Lemma")[If $f in L^2 (TT)$, $lim_(n->infinity) abs(hat(f)(n)) = 0$.]

#remark[By expanding the real and complex parts of the coefficients, this also implies $
lim_(n->infinity) integral_(TT) f(x) sin(2n pi x) dif x = lim_(n->infinity) integral_(TT) f(x) cos(2 n pi  x) dif x = 0.
$]

#definition("Dirichlet Kernel")[
  The _Dirichlet Kernel_ is the sequence of functions defined $
  D_N (x) := sum_(n=-N)^N e^(2pi i n x) = sin(2pi (N+1/2) x)/sin(2pi x/2).
  $ Then, the partial sum $S_N f(x):= sum_(n=-N)^N hat(f)(n) e^(2pi i n x) = (f ast D_N)(x)$.
]

#theorem("Convergence Results")[
  1. If $f in L^2 (TT)$ and Lipschitz at $x_0$, then $S_N f(x_0) -> f(x_0)$
  2. If $f in L^2 (TT) sect C^2 (TT)$, then $S_N f -> f$ uniformly on $TT$.
]

#definition("Fourier Transform")[
  The _Fourier Transform_ of $f : RR -> CC$ is defined $
  hat(f)(zeta) := integral_(RR) f(x) e^(-2 pi i zeta x) dif x.
  $ The _Inverse Fourier Transform_ of $f in L^1 (RR)$ is defined $
  caron(f)(x) := integral_(RR) f(zeta) e^(2 pi i zeta x) dif zeta = hat(f(- dot))(x).
  $
]

#theorem("Properties of the Fourier Transform")[
  Let $f, g in L^1 (RR)$.
  1. $hat(f), caron(f) in L^infinity (RR) sect C(RR)$
  2. $hat(tau_y f) (zeta) = e^(-2 pi i zeta y) hat(f)(zeta)$, and $tau_eta hat(f)(zeta) = hat(e^(2pi i eta (dot)) f(dot))(zeta)$
  3. $hat(f ast g) = hat(f) dot hat(g)$
  4. $integral_(RR) f(x) hat(g)(x) dif x = integral_(RR) hat(f)(x) g(x) dif x$
  5. Let $h(x) := e^(pi a x^2)$ for $a > 0$, then $hat(f)(zeta) = 1/sqrt(a) e^(-pi zeta^2/a)$
]

#theorem("Fourier Inversion")[
  If $f in L^1 (RR)$ and $hat(f) in L^1 (RR)$, then $f$ agrees almost everywhere with some $f_0 in C(RR)$ and $hat(caron(f)) = caron(hat(f)) = f_0$.
]

#theorem("Plancherel's Theorem")[
  If $f in L^1 (RR) sect L^2 (RR)$, then $hat(f) in L^2 (RR)$ and $norm(f)_2 = norm(hat(f))_2$.
]

#remark[
  Using this, one extends the Fourier Transform to $f in L^2 (RR)$ by taking a sequence of smooth, compactly supporting functions approximating $f$ in $L^2$, and taking the limit of the Fourier transforms in $L^2 (RR)$.
]

#theorem[
  If $f in L^1 (RR)$, $hat(f) in C_0 (RR)$, the space of continuous functions with $|f(x)| -> 0$ as $|x| -> infinity$.
]

#theorem("Poisson Summation Formula")[
Let $f in C(RR)$ be such that $abs(f(x)) <= C(1+abs(x))^(-(1+epsilon))$ and $abs(hat(f)(zeta)) <= C (1 +|zeta|)^(-(1+epsilon))$ for some constants $C, epsilon > 0$. Then, for every $x in RR$, $
sum_(k in ZZ) f(x + k) = sum_(k in ZZ) hat(f)(k) e^(2pi i k x).
$
]

#remark[
  In words, this means the _periodization_ (the LHS) of $f$ equals the Fourier series of $f$.
]