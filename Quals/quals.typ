// ! external
// #import "../notes.typ": conf
#import "../typst/shortcuts.typ": *
// ? Change me:

#let conf = (
  course_code: "",
  course_title: "Qualifying Exams Study Guide",
  subtitle: "Personal study guide made to prepare for PhD qualifying exams at the University of British Columbia. Covers basic analysis (real, complex) and abstract algebra (linear, group theory, ring, field/Galois theory), at the 2nd, perhaps 3rd, year undergraduate level.",
  semester: ": |>",
  professor: ": |",
  author: "Louis Meunier",
)

// ! packages
#import "@preview/ctheorems:1.1.3": *
#import "@preview/commute:0.2.0": arr, commutative-diagram, node

// ! font sizes
#let fontsizes = (
  normal: 12pt,
  section: 12pt,
  subsection: 12pt,
  large: 20pt,
  small: 10pt,
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
  gray: rgb("#f2f2f2"),
)

// ! defaults

#set page(
  margin: 1.5cm,
  footer-descent: 60%,
  header-ascent: -5%,
)
#set text(
  font: "TeX Gyre Pagella",
  size: fontsizes.normal,
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
  base_level: 0,
  padding: (top: 0pt, bottom: -4pt),
)

#let proof = thmproof(
  "proof",
  text(
    size: 7pt,
    smallcaps("Proof"),
    // highlight("Proof", fill: white, stroke: black, top-edge: "cap-height", extent: 3pt),
    style: "oblique",
    weight: "regular",
  ),
  bodyfmt: body => [
    #text(size: 7pt, body) #h(1fr) $square.small.filled$ // float a QED symbol to the right
  ],
    separator: [#h(0.1em)#text(size: 7pt, ".")#h(0.2em)],
  inset: (top: 0em, left: 2.8em, right: 1.4em)
)


#let theorem = thmbox(
  "theorem",
  text("Theorem", fill: solarized.red),
  base_level: 0,
  inset: (y: 0em, top: 0em, bottom: 0em),
  padding: thmsettings.padding,
)

#let corollary = thmbox(
  "corollary",
  text("Corollary", fill: solarized.orange),
  base_level: 0,
  inset: (y: 0em, top: 0em, bottom: 0em),
  padding: thmsettings.padding,
)


#let lemma = thmbox(
  "lemma",
  text("Lemma", fill: solarized.orange),
  base_level: 0,
  inset: (y: 0em, top: 0em, bottom: 0em),
  padding: thmsettings.padding,
)
#let proposition = thmbox(
  "proposition",
  text("Proposition", fill: solarized.magenta),
  base_level: 0,
  inset: (y: 0em, top: 0em, bottom: 0em),
  padding: thmsettings.padding,
)
#let definition = thmbox(
  "definition",
  text("Definition", fill: solarized.blue),
  base_level: 0,
  inset: (y: 0em, top: 0em, bottom: 0em),
  padding: thmsettings.padding,
)
#let remark = thmbox(
  "remark",
  "Remark",
  titlefmt: title => [#text(weight: 500, size: 7pt, title)],
  bodyfmt: body => [
    #text(size: 7pt, body)
  ],
  separator: [#h(0.1em)#text(size: 7pt, ":")#h(0.2em)],
  base_level: 0,
  inset: (y: 0em, top: 0em, bottom: 0em),
  padding: thmsettings.padding,
)

// #let definition = thmbox("definition", "Definition")

#set heading(numbering: "1.1")


#set page(footer: context [
  #let elems = query(
    selector(heading).before(here()),
  )
  // #let subsection = elems.last().body
  // #let num = elems.last().numbering

  // #text(num, size: fontsizes.small)
  // #text(subsection, size: fontsizes.small)
  #h(1fr)
  #text(
    counter(page).display(
      "1",
      // both: true,
    ),
    size: fontsizes.small,
  )
])
#show heading.where(
  level: 1,
): it => text(
  size: fontsizes.section,
  weight: "bold",
  if (it.numbering != none) {
    par(leading: 0em, first-line-indent: 0em, counter(heading).display(it.numbering) + h(.5em) + it.body + "\n")
  } else {
    par(leading: 0em, first-line-indent: 0em, it.body + [.] + "\n")
  },
)
#show heading.where(
  level: 2,
): it => text(
  size: fontsizes.normal,
  weight: "semibold",
  // style: "italic",
  par(leading: 0em, first-line-indent: 0em, counter(heading).display(it.numbering) + h(.5em) + it.body),
  // it.numbering + h(.5em) + it.body + [.],
)
#show heading.where(
  level: 3,
): it => text(
  size: fontsizes.subsection,
  weight: "semibold",
  // style: "italic",
  par(leading: 0em, first-line-indent: 0em, counter(heading).display(it.numbering) + h(.5em) + it.body),
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

#let boxit(arg) = box(stroke: 0.75pt, outset: 8pt, arg)
#let sgn = "sgn"

// Page
#v(3em)
#set align(left)
// #text(18pt, conf.course_code, weight: "bold") 
#text(18pt, conf.course_title)
#text(12pt, "\n" + conf.subtitle)
// if cute != none {
//   // set align(center)
//  figure(
//     image(cute, width: 40%)
//   )
// }
// set align(left)
// #text(12pt, "\n\n" + conf.semester + ", " + conf.professor + ".")
#text(12pt, "\nNotes by " + conf.author)

#set par(
  first-line-indent: 1em,
  leading: 0.5em,
  linebreaks: "simple",
)

#v(2em)
#outline(
  title: none,
  // , fill: none
)

#pagebreak()

// ! https://www.math.ubc.ca/sites/default/files/documents/Grad/QualifyExams/Analysis_syllabus.pdf
= Analysis

== Real

=== Fundamentals

#definition("Metric Space")[
  A _metric space_ is a set $X$ equipped with a _metric_ function $d : X times X -> RR_(>= 0)$ that satisfies:
  1. $d(x, y) >= 0$ and equals 0 iff $y = x$
  2. $d(x, y) = d(y, x)$
  3. $d(x, z) <= d(x, y) + d(y, z)$
]

#definition("Convergence, Subsequences")[
  A _sequence_ $bold(x) := {x_n} subset X$ in a metric space $X$ is a function $bold(x) : NN -> X$ where we write $x_n = bold(x)(n)$. We say ${x_n}$ _converges_ to some point $x in X$ if $
forall epsilon >0, exists N in NN "s.t." n >= N => d(x, x_n) < epsilon.
  $ We write $x_n -> x$ or $lim_(n -> infinity) x_n = x$. Equivalently, $x_n -> x$ in $(X, d)$ iff $d(x_n, x) -> 0$ in $(RR, |dot|)$.

  A _subsequence_ of $bold(x)$ is a new sequence $bold(tilde(x))$ which can be written as $bold(tilde(x)) = bold(x) compose n$ where $n : NN -> NN$ a strictly increasing function, called the _reindexing_ of our sequence. Equivalently we write $bold(tilde(x)) = {x_n_k}_k$ where $n_k = n(k)$.

  We say a sequence is _bounded_ if there exists an $M in RR$ such that $d(x_n, x_m) <= M$ for all $n, m in NN$ (this is equivalent to saying there is some $M' in RR$ and $x in X$ such that $d(x_n, x) <= M'$ for all $n in NN$).
]

#definition("Cauchy")[
  A _Cauchy sequence_ in a metric space $(X, d)$ is a sequence ${x_n}$ such that $
forall epsilon > 0, exists M in N "s.t." n, m >= M => d(x_n, x_m) < epsilon.
  $
]

#proposition("Some Properties of Sequences")[
  Fix $(X, d)$ a metric space and ${x_n}$ a sequence in $X$.
  - ${x_n}$ convergent $=>$ ${x_n}$ Cauchy. If the converse holds for every sequence in $X$, we say $X$ is _complete_
  - if ${x_n}$ Cauchy and has a converging subsequence, then ${x_n}$ converges along the whole sequence
  - if ${x_n}$ Cauchy, ${x_n}$ bounded
  - if ${x_n}$ converges, then every subsequence of ${x_n}$ converges, and to the same limit
]

#definition("Continuity")[
  A function $f : (X, d) -> (Y, rho)$ is said to be continuous at $x in X$ if for every $epsilon > 0$ there exists $delta = delta(x) > 0$ such that $
d(x, x') < delta => rho(f(x), f(x')) < epsilon.
  $ It is said to be _uniformly continuous_ on $X$ if $delta$ as in the definition of continuity can be chosen independently of $x$.
]

#definition("Absolute Continuity")[
  Let $f : [a, b] -> RR$. We say $f$ is _absolutely continuous_ on $[a, b]$ if for every $epsilon > 0$, there exists a $delta > 0$ such that for any collection of disjoint intervals $(a_k, b_k) subset [a, b]$, $k = 1, dots, N$ with $sum_(k=1)^N (b_k - a_k) < delta$, then $sum_(k=1)^N |f(b_k) - f(a_k)| < epsilon$.
]

#proposition[
  $f : (X, d) -> (Y, rho)$ is continuous at $x in X$ iff for every ${x_n} subset X$ such that $x_n -> x$ in $X$, $f(x_n) -> f(x)$ in $Y$.
]

#proposition[
// ! TODO could probably make this more general
  Let $f : (a, b) -> RR$ be a uniformly continuous function on the bounded open interval $f$. Then there exists a unique continuous extension $tilde(f) : [a, b] -> RR$ that agrees with $f$ on $(a, b)$.
]

#proof[
If it were to exist, by continuity, $tilde(f) (a) = lim_(x arrow.b a) f(a)$. Take any sequence $x_n$  in $(a, b)$ converging to $a$. One uses the uniform continuity to show that ${f(x_n)}$ is Cauchy and therefore converges since $RR$ complete. So this limit exists; moreover, one gets uniqueness in a similar vein by the well-definedness of this quantity (so basically continuity and uniqueness of limits).
]

#definition("Normed and Inner Product Spaces")[
  Let $V$ be a vector space over $K in {RR, CC}$. Then $norm(dot) : V -> RR$ is called a _norm_ if:
  - $norm(v) >= 0 forall v in V,$ and equal to zero iff $v =0$
  - $norm(alpha v) = |alpha| norm(v)$ for all $alpha in K, v in V$
  - $norm(u + v) <= norm(u) + norm(v) forall u, v in V$
  A function $angle.l dot, dot angle.r : V times V -> RR$ is called an _inner product_ if, for all $u, v, w in V$ and $alpha in K$:
  - $angle.l u + v, w angle.r = angle.l u, w angle.r + angle.l v, w angle.r$
  - $angle.l alpha u, v angle.r = alpha angle.l u, v angle.r$
  - $angle.l u, v angle.r = overline((angle.l v, u angle.r))$
  - $angle.l u, u angle.r >= 0$ and equals zero iff $u = 0$,
  Accordingly, $(V, norm(dot))$ is called a _normed vector space_ and $(V, angle.l dot, dot angle.r)$ an _inner product space._
]

#remark[
  Norms induce natural metrics, $d(u, v) := norm(u - v)$. Inner products induce natural norms, $norm(u) = (angle.l u, u angle.r)^(1\/2)$. So every inner product space is (naturally) a normed vector space, and every vector space is (naturally) a metric space. We say things like "$V$ is a complete normed vector space" to mean $V$ is complete as a metric space with the natural metric induced by its norm, for convenience.
]

#proposition("Properties of Inner Product Spaces")[
  Let $V$ an inner product space.

  - $|chevron.l u, v chevron.r| <= |u||v|$
  // ! - TODO?
]

#definition("Series")[
  Let $(V, norm(dot))$ be a normed vector space. A _series_ in $V$ is a sequence of partial sums, i.e. a sequence $
S_n := sum_(k=0)^n a_k
  $ where ${a_k}$ a sequence in $V$. We say the series converges if ${S_n}$ converges in $V$.
]

#remark[]


// ! TODO

//  [x] series, sequences
//  [x] metric spaces, convergence, limits
//  [x] uniform continuity
//  [] cauchy schwarz
//  [] mean-value theorem, two forms
//  [x] contraction mapping, banach fixed point

#theorem("Banach Fixed Point")[
  Let $(X, d)$ a complete metric space. A map $T : X -> X$ is said to be a _contraction mapping_ if there exists a constant $alpha in (0, 1)$ such that for all $x, y in X$, $d(T(x), T(y)) <= alpha d(x, y)$.

  If $T : X -> X$ a contraction, there exists a unique fixed point of $T$, i.e. a unique $x_0 in X$ such that $T(x_0) = x_0$. Moreover, if $T^(n)$ represents $n$-fold composition of $T$ with itself, then $T^(n) (x) -> x_0$ as $n -> infinity$ for all $x in X$.
]

#proof[
  (Uniqueness) If $x_0, x_1$ are two fixed points, then $d(T(x_0), T(x_1)) = d(x_0, x_1)$ on one hand, and by the contraction property, $d(T(x_0), T(x_1)) <= alpha d(x_0, x_1)$. Thus $d(x_0, x_1) <= alpha d(x_0, x_1)$, but $0 < alpha < 1$ so this is only possible if $d(x_0, x_1) = 0$ i.e. if $x_0 = x_1$.

  (Existence) Fix $x in X$. Define the sequence $x_1 = x$ and $x_n = T^(n) (x) = T(x_(n-1))$ for $n >= 2$. One shows this is a Cauchy sequence by using the contraction property (inductively; one picks up a sum of the form $1 + alpha + alpha^2 + dots.c$ which can be bounded by a geometric series). By completeness, $x_n$ converges to some $x_0 in X$. We claim $x_0$ is a fixed point. Indeed, one easily sees $T$ is continuous, so $T^n (x) -> x_0$ implies $T(T^n (x)) -> T(x_0)$. On the other hand, $T(T^n (x)) = T^(n + 1) (x) -> x_0$. By uniqueness, $T(x_0) = x_0$.
]

=== Differentiation

#definition[
  Given $f : RR^n -> RR^m$, the derivative at $x_0 in RR^n$ is the linear map $Dif f (x_0) : RR^n -> RR^m$, if it exists, such that $ norm(f(x) - f(x_0) - D f(x_0) (x - x_0))/(norm(x - x_0)) -> 0 "as" x-> x_0. $
  If we fix bases for $RR^n, RR^m$, then $D f(x_0)$ can be represented by a $m times n$ matrix $J_f (x_0)$ called the _Jacobian_ of $f$ at $x_0$.
]

#remark[
  When $m = 1$, one often writes $Dif f = (gradient f)^top$ where $gradient f$ is viewed as a column vector in $RR^n$.
]

#proposition("Properties of Derivative")[
Let $f, g : RR^(n) -> RR^m$ and $h : RR^k -> RR^n$, and $alpha, beta in RR$.
  // TODO
  // uniqueness
  - $Dif f$ is unique when it exists
  - $Dif (alpha f + beta g) = alpha Dif f + beta Dif g$
  - $Dif (f g) = (Dif f) g + f (Dif g)$, when $m = 1$
  - $Dif (f compose h) = (Dif f)|_h dot (Dif h)$ (_chain rule_)
  - $f$ differentiable at $x_0$ $=>$ $f$ (Lipschitz) continuous at $x_0$
  - If $Dif f$ exists at a point $x_0$, $f$ partially differentiable in all directions, and $
J_f (x_0) = ((partial f_j)/(partial x_i) (x_0))_(1 <= i <= n \ 1 <= j <= m)
  $
  - If all of the partial derivatives of $f$ exist and are continuous at $x_0$, then $f$ differentiable at $x_0$
]

#remark[
  One need be careful with the last two properties - existence of partial derivatives needn't imply differentiability in general (we need some extra condition, such as continuity as stated here); consider $
  f : RR^2 -> RR, quad f(x, y) = cases((x^2 y)/(x^2 + y^2) quad & (x, y) eq.not 0, 0 quad & (x, y) = 0) .
  $ One can check $partial_x f$, $partial_y f$ both exist (and equal 0) at the origin, but $f$ not differentiable at $0$. Intuitively, $Dif f$ captures "average change in all directions" while partial derivatives capture "change in a specified direction".
]

#definition("Other Derivatives")[
Let $f : RR^n -> RR$ and $F = (F_1, dots, F_n) : RR^n -> RR^n$.
  - $partial/(partial x_i) f(x_1, dots, x_n) := lim_(h -> 0) (f(x_1, dots, x_i + h, dots, x_n) - f(x_1, dots, x_n))/(h)$ is called the _partial derivative_ of $f$ in the $x_i$ direction.
  - Given a vector $d in RR^n$ and $x in RR^n$, define the _directional derivative_ of $f$ in the direction $d$ at $x$ by $
    dif f(x; d) := lim_(h -> 0) (f(x + h d) - f(x))/(h).
  $
  - Define the _divergence_ of $F$ at $x$ (assuming its first-partial derivatives exist) by $
"div" F (x) := (partial F_1)/(partial x_1) (x) + dots.c + (partial F_n)/(partial x_n) (x).
   $ 
 - If $n = 3$, define the _curl_ of $F$ at $x$ (assuming its first-partial derivatives exist) by $
"curl" F(x) &:= det(mat(e_1, e_2, e_3; partial_x, partial_y, partial_z; F_1 (x), F_2 (x), F_3 (x))) \
&= (dots.c)
 $

]

#proposition[
  If $f : RR^n -> RR$ differentiable at $x in RR^n$, then $
dif f(x; d) = gradient f(x)^T.
  $ 
  If $d = e_i$ and $f$ partially differentiable in $x_i$ at $x$, then $dif f(x; d) = (partial f)/(partial x_i) (x)$.
]


#theorem("Mean-Value Theorem")[
  Let $f : RR^n -> RR$ be differentiable on an open ball $B subset RR^n$. Then for any $x, y in B$, there exists a $z in B$ such that $
f(x) - f(y) = Dif f(z_0) (x - y).
  $
]

#proof[
  Define $phi(t) := f(y + t (x-y)$ for $t in [0, 1]$, noting that $phi(0) = y$ and $phi(1) = x$. One computes, using the chain rule, that $phi'(t) = Dif f(y + t(x -y)) dot (x - y)$. By the one-variable mean-value theorem, there exists some $t_0 in [0, 1]$ such that $phi(1) - phi(0) = phi'(t_0)$. Letting $z = y + t_0 (x - y)$ gives the desired result, noting that $z$ indeed in $B$ by convexity.

  For completeness, we also prove the one-variable mean-value theorem. It suffices to prove that if $phi : RR -> RR$ is differentiable and is such that $phi(a) = phi(b) = 0$ then there exists $c in (a, b)$ such that $phi'(c) = 0$, since for a general function $f$ we can define $phi(x) := f(x) - phi(a) $
]

#theorem("Mean-Value Theorem, Integral Form")[
  Let $f : RR^d -> RR$ be differentiable. Then for any $x, y in RR^d$, $
f(y) - f(x) = integral_0^1 gradient f(x + t (x - y)) dot (x - y) dif t.
  $
]

#proof[
Let $psi(t) = f(x + t(x - y))$. Note that $psi'(t) = gradient f(x + t (x - y)) dot (x - y)$, so by fundamental theorem of calculus, $
integral gradient f(x + t (x - y)) dot (x - y) dif t &= integral_0^1 psi'(t) dif t = psi(1) - psi(0) = f(y) - f(x).
$
]

#theorem("Clairaut's Theorem")[
  Suppose $f : RR^n -> RR$ twice differentiable at $x_0$. Then, $partial_(x_j) f (x_0) = partial_(x_i) f (x_0)$ for all $i, j = 1, dots, n$.
]

#proof[_(Sketch)_
  For $n = 2$ (the proof extends to general dimensions by fixing all coordinates except the $i$th, $j$th) in variables $(x, y)$, consider the function $
phi(s, t) := f(x_0 + s, y_0 + t) - f(x_0 + s, y_0) - f(x_0, y_0 + t) + f(x_0, y_0).
  $ The idea is to recognize $phi(s, t)$ as a difference of functions in the $s$, $t$ variables resp., apply mean-value theorem to pick-up $partial/(partial x), partial/(partial y)$ terms, then use the definition of the second-order partial derivatives to estimate $phi$ in terms of $partial^2/(partial x partial y), partial^2/(partial y partial x)$. One should ultimately find that $phi(t, t)/t^2 -> (partial^2 f)/(partial x partial y) (x_0, y_0)$ and $(partial^2 f)/(partial y partial x)$, depending on which variable one chooses to expand in first.
]

#theorem("Inverse Function Theorem")[
  Let $F : Omega subset RR^n -> RR^n$ a $C^k$ map such that $Dif F(x_0)$ invertible for some $x_0 in Omega$. Then there exist neighborhoods $U subset Omega$ of $x_0$ and $V subset RR^n$ of $F(x_0)$ and a $C^k$ map $G : V -> U$ such that $
(F compose G) (y) = y quad forall y in V, quad quad (G compose F)(x) = x quad forall x in U.
  $ Moreover, $Dif F(x)$ invertible for $x in U$, and $
Dif G (y) = (Dif F)^(-1) (x), quad y = F(x), x in U.
  $
]

#theorem("Implicit Function Theorem")[
  Let $F : Omega := Omega_x times Omega_y subset RR^n times RR^m -> RR^m$ be a $C^k$ map, and assume $X_0 = (x_0, y_0) in Omega$ is such that $F(X_0) = 0$ and $Dif_y F (X_0)$ is invertible (_where $Dif_y$ the derivative in just the $y$-variables, i.e. represented by a $m times m$ matrix_). Then, there exists a neighborhood $U subset Omega_x$ of $x_0$ and a $C^k$ function $h : Omega_x -> RR^m$ such that $
F(x, h(x)) = 0, quad forall x in Omega.
  $
]

#proof[_(Sketch)_ Define $f : Omega -> RR^n times RR^m$ by $f(X) := (X, F(X))$ ("augmenting" $F$ to map to and from spaces of the same dimension). One checks $ J_f = mat(I_(n times n), 0_(n times m); Dif_x F, Dif_y F), $ which has determinant $det(Dif_y F)$ using properties of block matrices. This is non-zero at $X_0$ by assumption, so we may apply the inverse-function theorem, so locally there exists an inverse $g$. If we write $g = (tilde(g), tilde(h)) : RR^n times RR^m -> RR^(n + m),$ we see that $f(g(x, y)) = (x, y)$ (by inverse property) and $f(g(x, y)) = tilde(g)(x, y), F(tilde(g)(x, y), tilde(h)(x, y))$ by definition. In particular we see that $tilde(g)(x, y) equiv x$, and thus we get the property $
F(x, tilde(h)(x, y)) = y.
$ Thus the map $h(x) := tilde(h)(x, 0)$ gives the desired function.
]

#theorem([Lagrange Multipliers, one constraint])[
  Let $f, g : Omega subset RR^n -> RR$ be $C^1$ and $Sigma := {x in Omega : g(x) = 0}$, and assume $Dif g (x)$ nonzero (i.e. the gradient of $g$) on all of $Omega$. Then, if $f$ restricted to $Sigma$ has a max/min at $x_0 in Sigma$, then there exists $lambda in RR$ such that $
gradient f(x_0) = lambda g(x_0).
  $
]

#proof[
  Let $x_0$ be a max/min of $f$ restricted to $Sigma$. Assume wlog that $partial/(partial x_n) g (x_0) eq.not 0$. By implicit function theorem, then locally to $x_0$, $Sigma$ is represented by ${(x', h(x'))}$ (where $x' in RR^(n-1)$) for some $C^1$ function $h : RR^(n-1) -> RR$. Defining $F : RR^(n -1) -> RR, F(x') := f(x', h(x'))$, this implies $(x'_0, h(x'_0))$ a local max/min of $F$ and thus it's gradient must equal zero there. Chain rule gives $
    gradient F (x') = (partial/(partial x'_i) f(x', h(x')) + partial/(partial x_n) f(x', h(x')) (partial h(x'))/(partial x_i))_(i = 1)^(n - 1). quad (dagger)
  $ Also since $g(x', h(x')) = 0$ locally to $x_0$, we can take the derivative of this expression and find $
0 = ((partial g)/(partial x_i) (x_0) + (partial h)/(partial x'_i) (x_0) (partial g)/(partial x_n) (x_0))_(i=1)^(n - 1). quad (dagger.double).
  $ Taking $x' = x'_0$ in $(dagger)$ makes the right-hand side 0. Equating $(dagger), (dagger.double)$ and simplifying like-terms yields the proof, where $lambda$ is found to be $([(partial f)/(partial x_n)]\/[(partial g)/(partial x_n)]|_(x_0)$ .
]


#remark[
  When we say "$Sigma$ locally looks like $V$", what we really mean is there exists an open set $U$ such that $Sigma sect U = V.$
]

#remark[
  In particular, then if $f, g$ are $C^1$ on some open superset of $Omega$, and $partial Omega = {x in Omega : g(x) = 0}$, then one can compute global maxima of $f$ by
  1. computing _stationary points_ i.e. such that $gradient f = 0$, inside $Omega$, and
  2. computing points such that $gradient f = lambda gradient g,$ on $partial Omega$.
  Then, if $x_0$ a global max of $f$, then either it lies inside $Omega$ in which case $gradient f (x_0) = 0$, or it lies on the boundary in which case there exists $lambda$ such that $gradient f(x_0) = lambda gradient g(x_0)$. Thus, the global max of $f$ is the point of greatest function value among those from 1., 2.. A similar statement holds for the global min.
]

#theorem([Lagrange Multiplier, multiple constraints])[
  Let $f, g_1, dots, g_k :  Omega subset RR^n -> RR$ be $C^1$. Let $Sigma = {x in Omega : g_i (x) = 0 forall i = 1, dots, k}$, and assume ${gradient g_i (x)}_(i=1)^k$ a linearly independent set of vectors for all $x in Sigma$. Then if $f$ restricted to $Sigma$ has a local max/min at $x_0 in Sigma$, then there exists $lambda_1, dots, lambda_k$ such that $
gradient f(x_0) = lambda_1 gradient g_1 (x_0) + dots.c + lambda_k gradient g_k (x_0).
  $
]

#theorem("Taylor's Theorem")[
  Let $f : Omega subset RR^n -> RR$ be a $C^(k+1) (Omega)$ function. For any $x, x^0 in Omega$, $
f(x) = f(x^0) + sum_(j=1)^(k) sum_(1 <= i_1, dots, i_j <= n) (partial^j f)/(partial x_(i_1) dots.c partial_(x_i_j)) (x_(i_1) - x^0_(i_1)) dots.c (x_(i_j) - x^0_(i_j)) + R_k (x, x^0),
  $ where the _remainder_ $R_k$ is such that $
abs(R_k (x, x^0)) <= M_k abs(x - x^0)^(k + 1) quad "as" x -> x^0,
  $ where $M_k$ depends only on the $(k+1)$-st partial derivatives of $f$.
]

#remark[
The easiest way to prove this is to apply 1-dimensional Taylor's theorem to the function $phi(t) := f(x^0 + t (x -x^0)/(norm(x - x^0))), quad t in [0, norm(x - x^0)], $ for $t$sufficiently small, and expanding the derivatives of $phi$ by chain rule. 

On the other hand, the easiest way to derive the 1-diemnsional Taylor's theorem is by repeated application of the fundamental theorem of calculus, $
phi(t) &= phi(t_0) + integral_(t_0)^t underbrace(phi'(s)) dif s \
&= phi(t_0) + integral_(t_0)^t [phi'(t_0) + integral_(t_0)^s phi''(u) dif u] dif s \
&= phi(t_0) + phi'(t_0) (t - t_0) + integral_(t_0)^t integral_(t_0)^s phi''(u) dif u dif s,
$ etc. In particular, one sees that this implies the remainder term can be written as $
R_k (t) = integral_(t_0)^(t) integral_(t_0)^(s_1) dots.c integral_(t_0)^(s_(k-1)) phi^((k)) (u) dif u dots.c dif s_2 dif s_1, 
$ from which obtaining the bound on $R_k$ follows by approximating this integral.
]


#theorem("Taylor's Theorem, Weaker Assumptions")[
  Let $f in C^(k - 1) (Omega)$ and such that $Dif^(k - 1) f$ is differentiable at $x^0 in Omega$. Then for $x in Omega$, the same conclusion as above holds, but with remainder $
lim_(x -> x^0) (R_k (x))/(abs(x - x^0)^(k)) = 0,
  $ i.e. we can't in general say anything about how _quickly_ this quantity goes to zero.
]

#remark[
  In "asymptotic" notation, the first theorem says $R_k (x) = cal(O)(abs(x - x^0)^(k + 1))$ and the second says $R_k (x) = cal(o) (abs(x - x^0)^k)$.
]

=== Integration

#definition("Partition")[
  Given a rectangle $R subset RR^n$, a _box partition_ of $R$ is a *finite* collection $cal(P) = {B_k}_(k=1)^N$ of _boxes_ (rectangles) $B_k$ such that $R = union.big_(k=1)^N B_k$.
]

#definition("Upper/Lower Riemann Sum")[
  Let $f : R subset RR^n -> RR$ a bounded function. Given a partition $cal(P)$ of $R$, define the _upper, lower Riemann sums_ $
U(f, cal(P)) := sum_(B in cal(P)) sup_(x in B) f(x) dot "vol"(B), quad L(f, cal(P)) := sum_(B in cal(P)) inf_(x in B) f(x) dot "vol"(B),
  $ where, if $B = [a_1, b_1] times dots.c times [a_n, b_n]$, $"vol"(B) := (b_1 - a_1) dots.c (b_n - a_n)$. Define the _upper, lower Riemann integrals_ of $f$ by $
overline(integral_R) f dif x := inf_(cal(P) : "partition of" R) U(f, cal(P)), quad quad underline(integral_R) f dif x := sup_(cal(P) : "partition of" R) L(f, cal(P)).
  $
  In particular, we trivially have the inequalities $
inf_R f dot "vol"(R) <= L(f, cal(P)) <= underline(integral_R) f dif x <= overline(integral_R) f dif x <= U(f, cal(P)) <= sup_R f dot "vol"(R).
  $
  If the lower, upper Riemann sums agree, we write their shared value by $integral_R f dif x$, called the Riemann integral of $f$ over $R$.
]

#remark[
  We can extend this definition to general $f$ over bounded domains $Omega$ by taking $R$ a rectangle such that $R supset Omega$ and extending $f$ by zero outside of $R$.
]

#definition("Content Zero")[
  A set $Omega subset RR^n$ is said to be of _content zero_ if for every $epsilon > 0$, there exists a finite number of boxes $B_1, dots, B_N$ which cover $Omega$ and such that $sum_(n=1)^N "vol"(B_n) <= epsilon$.
]

#theorem[
  If $f$ bounded on $R$ and has set of discontinuities with content 0, it is Riemann integrable on $R$.
]

#proposition[
  Riemann integrals are linear.
]

#theorem("Fubini")[
  // ! TODO
]

#definition("Regular Partition")[
  Let $Omega subset RR^n$ a domain with $"content"(partial Omega) = 0$. A _regular partition_ $cal(P) = {D_k}_(k=1)^N$ is a finite collection of sets $D_k$ satisfying
  - $Omega = union.big_(k=1)^N D_k$ and $"content"(partial D_k) = 0$ for all $k = 1, dots, N$, and
  - $"content"(D_k sect D_j) = 0$ for all $k eq.not j$.
]

#proposition[
  Let $f : Omega -> RR$. Then $f$ is Riemann integrable over $Omega$ iff for all $epsilon > 0$ there exists a _regular_ partition $cal(P)$ such that $U(f, cal(P)) - L(f, cal(P)) < epsilon$
]

#theorem("Change of Variables")[
Let $Omega, Omega' subset RR^n$ be bounded domains and $T : Omega' -> Omega$ a $C^1$ bijection. Then, for any $f : Omega -> RR$ which is Riemann integrable over $Omega$, then $
integral_(Omega) f dif V = integral_(Omega') (f compose T) |det Dif T| dif V.
$
]

#proof[
  // ! TODO
]


// ! TODO

#theorem("Differentiation under the Integral")[]

#theorem("Improper Integrals")[]
=== Vector Calculus

#definition("Curve")[
  A _(parametrized) $C^k$ curve_ in $RR^n$ is a connected set $cal(C) subset RR^n$ such that there exists a $C^k$ function $gamma : I -> RR^n$ with $gamma(I) = cal(C)$, where $I subset RR$ an interval. We say $cal(C)$ _regular_ if $gamma'$ never vanishes on $I$. 

  A _piecewise $C^k$ curve_ is a set $cal(C) = cal(C)_1 union dots.c union cal(C)_m$ where each $cal(C)_i$ a $C^k$ curve and each has "shared endpoints" (in practice, think of something like a triangle).
]

#remark[More generally, a curve is generally defined as a connected subset of $RR^n$ that is "locally a parametrized curve".]

#definition("Surface")[
  A _$C^k$ surface_ in $RR^n$ is a connected set $S subset RR^n$ such that for every point $p in S$, there exists an open subset $U subset RR^2$ and $V subset RR^n$ such that $p in V$, and a $C^k$ homeomorphism $phi : U -> V sect S$ such that $phi(U) = V sect S$.

  We call $S$ regular if every such $phi$ has $dif phi_q : RR^2 -> RR^n$ is one-to-one for all $q in U$, i.e. the Jacobian $J_phi (q)$ has rank 2.
 // ! TODO
]

#definition("Tangent Plane")[
Let $S subset RR^3$ a regular $C^1$ surface. The _tangent plane_ at a point $p in S$ is $
T_p S = dif_q phi (RR^2),
$ where $phi(q) = p$. Since $dif_q phi$ one-to-one, this is a 2-dimensional subspace of $RR^3$.
]

#remark[This is well-defined, regardless of choice of parametrization, by an inverse function theorem argument.]

#definition("Normal")[
  A normal to a regular $C^1$ surface $S subset RR^3$ at a point $p$ is a vector $n in RR^3$ such that $n$ is orthogonal to $T_p S$. If we restrict $n$ to be of unit length, then since $T_p S$ two dimensional, there are precisely two such $n$'s, given by $plus.minus (v_1 times v_2)$ where ${v_1, v_2}$ a basis for $T_p S$.
]

#definition([Integration over a Surface in $RR^3$])[
  Let $S subset RR^3$ a regular parametrized surface with parametrization $phi : D -> RR^3$ and $f : RR^3 -> RR$ Riemann integrable. Define the _surface integral_ $
integral.double_S f dif sigma := integral.double_D (f compose phi) |phi_u times phi_v| dif u dif v.
  $ Suppose $F : RR^3 -> RR^3$ a vector field, and $S$ an oriented surface with unit normal $n$. Define the _flux integral_ $
    integral.double_S F dot dif sigma := integral.double_S (F dot n) dif sigma = integral.double_D (F compose phi) dot (n compose phi) |phi_u times phi_v| dif u dif v.
  $
]

#remark[
Since we are in dimension $3$, $n = plus.minus (phi_u times phi_v)/(|phi_u times phi_v|)$ so the flux integral can be evaluated as $plus.minus integral.double_D (F compose phi) dot (phi_u times phi_v) dif u dif v$ (one needs to be careful of using the right sign).
]


// ! TODO 
// outward unit normal to surfaces
// conservative vector fields
// gradient/potential fields

// ! TODO?
// [x] define general Riemann integration, all that general theory
// change of variable theorem (do this one better!)
// fubini's

// conservative vectorfields, poincare?
// define surfaces, integration on surfaces
// green's (+ consequences), stoke's, divergence, 

#theorem("Green's")[
  Let $F = (P, Q) : RR^2 -> RR^2$ a $C^1$ vector field. Let $D subset RR^2$ a bounded region with piecewise $C^1$, positively oriented boundary $partial D$. Then, $
integral.double_D (partial Q)/(partial x) - (partial P)/(partial y) dif A = integral_(partial D) F dot dif s.
  $
]

#theorem("Stoke's")[
  Let $F : RR^3 -> RR^3$ a $C^1$ vector field and $S$ a regular surface in $RR^3$ with piecewise $C^1$ boundary $partial S$. Then, $
integral.double_S "curl"(F) dot dif S = integral_(partial S) F dot dif s.
  $
]

#theorem("Divergence")[
  Let $F : RR^n -> RR$ a $C^1$ function and $W subset RR^n$ a solid bounded region with boundary $S = partial W$ which is a regular $C^1$ surface. Then, $
integral_W "div" F dif V =  integral_(S) F dot dif S.
  $
]

=== Analysis on Functions
// ! TODO
// [] sequences and series
// [] uniform convergence
//   [] some consequences + test
// [x] term-by-term differentiation, integration
// [x] Weierstrass approximation theorem
// [x] Fourier series

#remark[A lot of what is stated in this section could be generalized without too much hassle to functions on/to general metric spaces, but is cumbersome and unnecessary for my interests.]

#definition("Convergence of sequences of functions")[
  Let ${f_n}$ be a sequence of real-valued functions defined on some set $S$. We say $f_n -> f$ _pointwise on $S$_ if $f_n (x) -> f(x)$ (as sequences of real-numbers) for every $x in S$.

  We say that the convergence is _uniform_ if $sup_(x in S) |f_n (x) - f(x)| -> 0$ as $n -> infinity$, or equivalently if $f_n -> f$ under the _uniform norm_ $norm(f)_infinity := sup_S |f|$ (where we may omit the set if clear from context).
]

#remark[Equivalently, $f_n -> f$ uniformly if for every $epsilon > 0$, there exists an $N in NN$ such that for all $n >= N$, $|f_n (x) - f(x)| <= epsilon$ for all $x in S$.]

#remark[
  It's clear that uniform $=>$ pointwise convergence. A good counterexample for the other direction is the functions $f_n (x) = x^n$ defined on $[0, 1]$. We see that $f_n$ converges pointwise to the function that is $0$ everywhere except 1, at which point it is equal to 1. However, this convergence is not uniform.
]

#theorem[
  Let $C(K)$ be the set of continuous functions on a compact set $K subset RR^n$. This is a complete metric space when equipped with the uniform norm.
]

#remark[
  In particular, this means that the uniform limit of continuous functions is continuous.
]



#theorem("Interchange of Limit and Integral")[
  Let ${f_n}$ be a sequence of Riemann integrable functions on some box domain $B$ which converge uniformly to some Riemann integrable function $f$ on $B$. Then, $integral_B f_n dif x -> integral_B f dif x$.
]

#proof[
  $|integral_B f dif x - integral_B f_n dif x| <= integral_B |f - f_n| dif x <= "vol"(B) sup_B |f - f_n|$; the right-hand side above goes to zero by uniform convergence.
]

#theorem("Interchange of Limit and Derivative")[
  Suppose $f : U subset RR^n -> RR$ where $U$ open, where $f_m$ differentiable, converge pointwise at some point $x_0 in U$, and their derivatives converge uniformly, then ${f_m}$ converges uniformly to some differentiable function $f$ and $partial_x f_m (x) -> partial_x f(x)$ as $m -> infinity$ on $U$.
]

#proof[
  Assume $n = 1$ for simplicity. Let $g_n = f'_n$ and let $g$ be the uniform limit of $g_n$. Take as candidate $f(x) := f(x_0) + integral_(x_0)^x g(y) dif y$. It's clear $f$ is differentiable, and by the fundamental theorem of calculus, $
|f_n (x) - f(x)| &= |f_n (x_0) - f(x_0) + integral_(x_0)^x f'_n (y) - g(y) dif y | \
&<= |f_n (x_0) - f(x_0)| + integral_(x_0)^x |f'_n (y) - g(y)| dif y \
&<= |f_n (x_0) - f(x_0)| + |x - x_0| sup_y |f'_n (y) - g(y)|,
  $ and the right-hand side converges by the point-wise convergence at $x_0$ and the uniform convergence of the derivatives. Finally, for $x in U$, $|f'_n (x) - f' (x)| &= |g(x) - g_n (x)|$ by definition, so the convergence is immediate.
]

#theorem("Bounded Convergence for Integrals")[
  Assume $f_n -> f$ pointwise, ${f_n}, f$ Riemann integrable, and $|f_n (x)| <= B$ for all $x in I, n >= 1$. Then $integral_I f_n (x) dif x -> integral_I f (x) dif x$.
]

#proof[
  
]

#theorem("Dini's Theorem")[
  Let ${f_n}, f$ continuous functions on $I$ and $f_n -> f$ pointwise. Suppose $f_n (x) <= f_(n + 1) (x)$ for all $x$ and $n >= 1$. Then $f_n -> f$ uniformly.
]


#theorem("Interchange of Integral and Summation")[
  Suppose $f_n : K -> RR$ are Riemann integrable and $sum_n f_n -> f$ uniformly, and $f$ Riemann integrable. Then, $
sum_n integral_K f_n dif x = integral_K sum_n f_n dif x.
  $
]

#proof[
Letting $S_N (x) = sum_(n <= N) f_n (x)$, this theorem says $lim_N integral_K S_N dif x = integral_K lim_N S_N dif x$. This follows from an earlier proposition on uniform convergence of sequences of functions and integrals.
]

#theorem("Power Series")[
A _power series_ (centered at $x_0$) is a function of the form $
f(x) = sum_(n >= 0) a_n (x - x_0)^n.
$ Define $1/R := limsup_(n->infinity) |a_n|^(1\/n)$ (taking $1/R = 0, infinity <-> R = infinity, 0$ resp. as convention). Then,
- if $|x - x_0| < R$, the series converges absolutely (and in fact uniformly over compact sets)
- if $|x - x_0| > R$, the series diverges
]
#proof[
  Compare to a geometric series.
]

#theorem("Differentiating, Integrating term-by-term")[
  Let $f(x) = sum_(n>=0) a_n (x - x_0)^n$ have positive radius of convergence. Then, $f$ is infinitely differentiable and integrable on its interval of convergence, obtained by differentiating/integrating term-by-term, i.e. $
f'(x) &= sum_(n>=0) n a_n (x - x_0)^(n-1), \
integral f(x) dif x &= C + sum_(n>=0) (a_n)/(n+1) (x - x_0)^(n+1).
  $
]

#theorem("Weierstrass Approximation Theorem")[
  Let $I subset RR$ a closed and bounded interval and $f in C^0 (I)$ a continuous function. Then, for every $epsilon > 0$ there exists a polynomial $p_epsilon$ such that $
norm(f - p_epsilon)_infinity < epsilon. 
  $ That is, continuous functions are dense in the space of continuous functions on a compact interval with respect to the uniform norm.
]

#definition[
  Let $(X, d)$ a metric space. A family of functions $cal(F) subset C(X)$ is said to be:
  - _uniformly bounded_ if $sup_(f in cal(F) norm(f)_infinity < infinity$
  - _equicontinuous_ if for all $epsilon > 0 $ and $x in X$ there exists $delta > 0$ such that $d(x, y) < delta$ implies $sup_(f in cal(F)) |f(x) - f(y)| < epsilon$; it is said to be _uniformly equicontinuous_ if $delta$ is independent of $x$
]

#theorem("Arzela-Ascoli")[
  Let $(X, d)$ a compact metric space and $cal(F) subset C(X)$ be a uniformly bounded and uniformly equicontinuous family of functions. Then, $cal(F)$ is precompact with respect to the uniform metric, that is, for any sequence ${f_n} subset cal(F)$, there exists a uniformly converging subsequence ${f_n_k}$.
]

#remark[
  Usually uniform boundedness is easy to check. Uniform equicontinuity actually follows from equicontinuity when $X$ compact, so it suffices to check this. A sufficient condition for uniform equicontinuity is uniform Lipschitz continuity, i.e. there exists $L > 0$ such that for all $x, y in X$, $
sup_(f in cal(F)) |f(x) - f(y)| <= L d(x, y),
  $ which is usually easier to establish if it holds.
]





#pagebreak()
== Complex

=== Analytic Functions

// ! TODO
// [x] Cauchy-Riemann
// [x] Cauchy's Theorem
//    [x] Cauchy's Extra Stuffs
// [] Rouche's
// [] Maximum modulus principle
// [] Harmonic Functions...

Throughout this section, we'll usually assume $Omega subset CC$ a connected open set.

#definition("Analytic/Holomorphic")[
  A function $f : CC -> CC$ is said to be _analytic_ on $Omega$ if $f$ is given by a converging power series everywhere in $Omega$. It is said to be holomorphic if $f'$ exists.
]
For $z = x + i y in CC$ and $f : CC -> CC$, write $f(z) = u(x, y) + v(x, y) i$ for real-valued functions $u, v$. Then, the _Cauchy-Riemann (CR) equations_ are the equations $
(partial u)/(partial x) = (partial v)/(partial y), quad (partial u)/(partial y) = - (partial v)/(partial x).
  $

#theorem("Cauchy-Riemann Equations")[
   $f$ is holomorphic if and only if $u, v$ satisfy the CR equations.
]

#proof[
  $(=>)$ follows by taking different limit directions in the definition of the derivative. $(impliedby)$ follows by writing, for some small $h = h_1 + h_2 i$, $
u(x + h_1, y+h_2) = u(x, y) + h_1 partial_x u (x, y) + h_2 partial_y u(x, y) + |h| psi_1 (h), quad psi_1 (h) ->_(h->0) 0,
  $ similar for $v$. This implies, simplifying things with CR, $
f(z + h) = f(x, y) + (partial_x v - i partial_y u)(h) + psi(h) h|, quad psi(y) = cal(o)(|h|),
  $ which gives the proof upon dividing both sides by $h$ and sending $h -> 0$.
]

#definition("Contour Integration")[
  Given a piecewise $C^1$ contour $C = C_1 union dots.c union C_k$ with $C_i$ parametrized by $C^1$ functions $gamma_i : [t_i, t_(i + 1)] -> C_i$, define $
  integral_(C^(plus.minus)) f(z) dif z := plus.minus sum_(i=1)^k integral_(t_i)^(t_(i + 1)) (f compose gamma_i) (s) dot gamma'_i (s) dif s,
  $  where the $plus.minus$ indicates the _orientation_ of $C$.
]

A domain $Omega$ is said to be _simply connected_ if for any two curves $gamma_0, gamma_1 : [0, 1] -> CC$ with common endpoints $alpha, beta$ in $Omega$, there exists a function $gamma_t : I -> CC$ for $t in [0, 1]$ such that $(t, s) |-> gamma_t (s)$ is a continuous map, $gamma_0 = gamma_0$ and $gamma_1 = gamma_1$, and $gamma_t (0) = alpha,  gamma_t (1) = beta$ for all $t in [0, 1]$.

A curve $C$ is said to be _simple_ if it does not intersect itself, i.e. it has an injective parametrization, and _closed_ if its parametrization $gamma : I-> CC$ is equal on the endpoints of $I$.

#theorem("Cauchy")[
  Let $f$ be a holomorphic function defined on $Omega$ being simply connected with $C$ a simple closed curve contained in $Omega$. Then $
integral_C f (x) dif z = 0.
  $
]

Partial converse:

#theorem("Morera")[
  Let $f$ be continuous on $Omega$ and such that $
integral_gamma f dif z = 0
  $ for every closed, piecewise $C^1$ curve $gamma$ contained in $Omega$. Then $f$ is holomorphic in $Omega$.
]


#theorem("Cauchy's Integral Formula")[
  Let $f$ holomorphic on $Omega$, which contains a circle $C$ and its interior. Then $
f(z) = integral_(C^+) (f(w))/(w - z) dif w, quad forall z in Omega.
  $ In particular, this implies $f$ is analytic on all of $Omega$, with $
f^((n)) (z) = (n!)/(2pi i) integral_(C^+) (f(w))/((w - z)^(n + 1)) dif w, 
  $ and thus $
f(z) = sum_(n=0)^infinity (f^((n)) (z_0))/n! (z - z_0)^n, 
  $ for any $z_0 in Omega$ and $z$ such that $z - z_0 in Omega$.
]

#proof[
  Make a small indent in the contour around the singularity of the denominator and use holomorphicity to approximate.
]

#corollary("Cauchy's Inequalities")[
  Let $f : Omega -> CC$ holomorphic. Then $ |f^((n)) (z)| <= (n! norm(f)_(C_R (z), infinity))/(R^n), $ where $R > 0$ any real number such that $D_R (z) subset CC$, where $D_R (z)$ the $R$-radius disc centered at $z$, and $ norm(f)_(C_R (z), infinity) := sup_(w in C_r (z)) abs(f(w)). $
]


#corollary("Liouville's Theorem")[
  Let $f : CC-> CC$ be _entire_, i.e. holomorphic everywhere, and bounded. Then $f$ is constant.
]

#proof[
  For every $R > 0$ and $z$ fixed, Cauchy's inequalities given that $|f' (z)| <= C/R$ for some $C$ uniform in $z$. Letting $R -> infinity$ gives that $f'(z) = 0$ everywhere, and thus $f equiv$ constant. 
]

#theorem("Analytic Continuation")[
  Let $f$ holomorphic on $Omega$, and assume either
  - $f equiv 0$ on a open set $D subset Omega$ or
  - $f = 0$ on a sequence ${z_n} subset Omega$ and its limit point $z_infinity$.
  Then $f equiv 0$ on $Omega$.
]

#remark[As a result, if two holomorphic functions agree on an open subset of $Omega$ or on a converging sequence, then they agree everywhere in $Omega$. This is the _principle of analytic continuation_, demonstrating how rigid analytic functions are.]

#proof[
 The first criteria follows from the first by a connectedness argument. The second follows by contradiction and looking at a local power series centered at $z_infinity$. 
]

#theorem("Convergence of Holomorphic Functions")[
  Let ${f_n}$ a sequence of holomorphic functions converging uniformly on compact subsets of $Omega$ to some function $f$. Then $f$ is holomorphic, and moreover, $f'_n$ converges uniformly to $f'$ on compact subsets.
]

#proof[
  This follows directly from Morera's theorem; the uniform convergence implies that $0 = integral_C f_n dif z -> integral_C f dif z = 0$. 
]

#remark[
  The analgous statement is _not_ true in real variables! That is, uniform convergence of differentiable real-valued functions are not necessarily differentiable.
]

=== Meromorphic Functions

#definition("Singularities")[
  A holomorphic function $f : Omega \\ {z_0} -> CC$ is said to have a _singularity_ at $z_0$. $z_0$ is called a 
  - _removable singularity_ of $f$ if there exists a holomorphic function $tilde(f) : Omega -> CC$ that agrees with $f$ on $Omega \\ {z_0}$;
  - _pole singularity_ of $f$ if $1/f$ has a removable singularity at $z_0$ (we define $1/f$ to be zero at $z_0$); or
  - _essential singularity_ of $f$ otherwise.

  We will say a singularity is _isolated_ if there exists a neighborhood around it in which it is the only singularity of $f$.
]

#proposition("Order of zeros, poles")[
  Let $f : Omega -> CC$ holomorphic have an isolated zero at $z_0 in Omega$. Then there exists a neighborhood of $z_0$, a unique positive integer $n := "ord"_f (z_0)$, and a nonvanishing holomorphic function $g$ such that $f(z) = (z - z_0)^n g(z)$ on that neighborhood.

  The same statement holds if $z_0$ an isolated pole of $f$, with $n$ a negative integer. When $n = -1$ we call the pole _simple;_ more generally, $-n$ is called the _order/mulitiplicity_ of $z_0$.
]

#proof[
  Follows from writing $f$ in a local power series centered at $z_0$; there exists a minimally indexed nonzero coefficient. Factoring out this term gives the desired representation. Uniqueness follows easily.
]

#corollary[
  If $f$ has a pole of order $n$ at $z_0$, then $
f(z) = (a_(-n))/(z - z_0)^(n) + a_(-n + 1)/(z - z_0)^(n - 1) + dots.c + (a_(-1))/(z - z_0) + G(z) =: P(z) + G(z),
  $ for some holomorphic (locally to $z_0$) function $G$.

  The function $P$ is called the _principal part_ of $f$ at $z_0$, and $a_(-1)$ is called the _residue_, denoted $"res"_(z_0) f = a_(-1)$.
]

#proof[
  Follows from the previous proposition by expanding terms.
]

#proposition("Computation of Residues")[
  If $n = "ord"_(f) (z_0)$, $
"res"_(z_0) f = lim_(z -> z_0) 1/(n - 1)! (dif/(dif z))^(n-1) (z - z_0)^n f(z).
  $
]

#proof[
  This follows from the previous corollary by taking computing the appropriate derivatives term-by-term.
]

#theorem("Residue Theorem")[
  Let $f$ be holomorphic in an open set containing a disc with boundary $C$, except for finitely many poles $z_1, dots, z_N$ in the disc. Then, $
integral_(C) f(z) dif z = 2 pi i sum_(k=1)^N "res"_(z_k) f.
  $
]

#proof[
  The idea is to use a "keyhole contour" that indents the original circle in $N$ places to miss the poles. By holomorphicity, the integral over this contour is zero and one finds that (since the "walls" of the keyhole neighborhoods tend to zero) our integral in question is equal to the sum over the poles of the integral of $f$ over small circles centered at each pole. Appealing to the representation in the corollary from earlier and computing quickly yields the result, using crucially the fact that $
integral_C 1/(z - z_0)^n dif z = cases(0 quad & n > 1, 2pi i quad & n = 1).
  $
]


#theorem("Classification of Isolated Singularities")[
  Suppose $f : Omega\\{z_0} -> CC$ holomorphic. Then:
  - if $f$ bounded on $Omega\\{z_0}$, $z_0$ a removable singularity
  - $z_0$ a pole iff $|f(z)| -> infinity$ as $z -> z_0$.
]

#proof[
  The second follows from the first. For the first, one contends that, inspired by the Cauchy's integral formula, the representation $1/(2pi i) integral_C f(w)/(w - z) d w$ remains a holomorphic function that agrees with $f$ everywhere away from $z_0$.
]


#proposition("Residue at Infinity and Sum of Residues")[
  Let $f$ be holomorphic in a punctured neighborhood of 0. Define the _residue at infinity_ to be $
"res"_(infinity) f  := - "res"_(0) 1/(w^2) f(1/w).
  $ Let $f$ be holomorphic on $CC minus {z_1, dots, z_n}$ where ${z_k}$ are isolated singularities. Then, $
"res"_infinity f + sum_(k=1)^n "res"_(z_k) f = 0.
  $
]

Essential singularities are a lot harder to deal with. An example of a function with an essential singularity is $f(z) := e^(1/z)$ at $0$.

#theorem("Casorati-Weierstrass")[
  Let $f$ holomorphic on a punctured disc $D\\{z_0}$ with an essentially singularity at $z_0$. Then $f(D\\{z_0})$ is dense in $CC$.
]

#proof[Argue by contradiction.]

#definition("Meromorphic Function, Singularities at Infinity")[
  Let $f : Omega -> CC$. We say $f$ is _meromorphic_ if there exists a sequence ${z_n : n >= 0}$ of points in $Omega$ such that
  - ${z_n}$ has no limit points in $Omega$;
  - $f$ holomorphic on $Omega\\ union_n {z_n}$; and
  - $f$ has poles at each ${z_n}$.

  Define $F(z) := f(1/z)$. We say $f$ has a _pole/removable/essential singularity at infinity_/is _holomorphic at infinity_ if $F$ has a pole/removable/essential singularity/is holomorphic at 0. If $f$ is a meromorphic function that is either holomorphic or has a pole at infinity is said to be _meromorphic in the extended complex plane_.
]

#proposition[The only meromorphic functions in the extended comlex plane are the rational functions.]


#theorem("Argument Principle")[
  Let $f$ be a meromorphic function on the interior of a simple closed curve $C subset CC$, such that $f$ has no roots nor poles on $C$. Then, $
1/(2pi i) integral_C (f'(z))/(f(z)) dif z = hash {"zeroes of" f "inside" C} - hash {"poles of" f "inside" C},
  $ the right-hand side counted with multiplicity.
]

#proof[
  If $z_0$ a zero of multiplicity $n$ of $f$, then it will be a pole of $f'/f$ with residue $n$, and if $z_0$ a pole of order $n$ of $f$, then it will be a pole of $f'/f$ with residue $-n$. The result then follows by the residue theorem.
]

#remark[
  Sometimes the quantity $f'/f$ is called the _logarithmic derivative_ of $f$, agreeing with the idea that "$dif/(dif z) log(f) = f'/f$" .
]

#corollary[
  Let $f$ as above, $C$ as above, and let $arg (f)$ be the argument of $f$. Then, $
  hash {"zeroes of" f "inside" C} - hash {"poles of" f "inside" C} = 2pi Delta_C arg(f),
  $ where $Delta_C arg(f)$ the total change of the argument of $f$ over $C$.
]

#proof[
  One notices $(f')/f = (dif)/(dif z) log(f(z))$. Split the log into $ln$ of norm plus argument, then apply fundamental theorem of calculus.
]

#theorem("Rouché's")[
  Let $f, g$ be holomorphic functions on $Omega$ with a curve $C subset Omega$ such that 
  - $|f| > |g|$ on $C$,
  - both $f$, $g$ never vanish on $C$. 

  Then, $f$ and $f + g$ have the same number of zeros in the interior of $C$.
]

#proof[
  Define $f_t = f + t g$ for $t in [0, 1]$. The conditions on $f, g$ show that this function has no zeroes on $C$ for any $t$, so we can apply the argument principle. Defining $N(t) = 1/(2pi i) integral_(C) (f'_t (z))/(f_t (z)) dif z$, one sees that this is a continuous (in $t$) function that is integer valued, and is therefore constant. In particular, this implies $N(0) = N(1)$, where the form is the number of zeros of $f$ and the latter of $f + g$, inside $C$.
]

#theorem("Maximum Modulus Principle")[
  Let $f : Omega -> CC$ a nonconstant holomorphic function. Then $|f|$ cannot attain its maximum inside $Omega$. In particular, if $Omega$ bounded, then $
max_(overline(Omega)) |f| = max_(partial Omega) |f|,
  $ and if $|f|$ attains an "interior" maximum, then $f$ is constant.
]


#theorem("Logarithms")[
  Let $Omega$ a simply connected domain containing $1$ and not containing 0. Then there exists a function $F(z) = log_(Omega) (z)$, called a _branch_ of the logarithm, such that
  - $F$ holomorphic on $Omega$,
  - $e^(F(z)) = z$ on $Omega$, and
  - $F(r) = log(r) := integral_1^r 1/x dif x$ whenever $r$ is a real number near $1$ in $Omega$.
]

#proof[
  The idea is to define $F$ by $
F(z) = integral_(gamma_z) 1/w dif w,
  $ where $gamma_z$ any curve connecting $1$ to $z$. By simple connectedness, this integral is independent of choice of curve, and one checks the necessary properties rather easily by verifying $F'(z) = 1/z$. In particular, the last follows form the fact that if $r approx 1$, one can take $gamma_z$ to lie entirely on the real line.
]

#theorem("Function Logarithms")[
  Let $f$ a non-vanishing holomorphic function on a simply connected domain $Omega$. Then there exists a holomorphic function $g$ on $Omega$ such that $f = e^g$.
]


=== Harmonic Functions
// ! basic properties
// ! harmonic conjugates

#theorem[
  Let $f$ holomorphic on a disc $D_R (z_0)$ with series expansion $f(z) = sum_(n>=0) a_n (z - z_0)^n$. Then, for any $0 < r < R$ and $n >= 0$, $
a_n = 1/(2pi r^n) integral_(0)^(2pi) f(z_0 + r e^(i theta)) e^(-i n theta) dif theta.
  $ In particular, the case $n = 0$ yields the _mean value property_ for holomorphic functions.
]

#proof[This follows directly by parametrizing the circle in the Cauchy integral formula for the derivatives of $f$.]

#proposition("Mean Value Property for Harmonic Functions")[
  Let $u : Omega -> RR$ be a harmonic function on a simply connected domain $Omega$. Then there exists a holomorphic function $f : Omega -> RR$ such that $u = "Re"(f)$, and so in particular, $
u(z_0) = (1/(2pi r)) integral_(0)^(2pi) u(z_0 + r e^(i theta)) dif theta,
  $ for any $z_0 in Omega$ and $r > 0$ such that $D_r subset Omega$.
]

#proof[
  We need to find $v$ such that $f = u + i v$ is a holomorphic function. Such a $v$ is called a _harmonic conjugate_ of $u$. We can define $f$ to be the antiderivative of $2 (partial u)/(partial z)$, which, since $DD$ simply connected, exists. This would imply $f'(z) = u_x + i u_y$, which should hold. Moreover, $Re(f) = u$ up to a constant (check!). The mean value property for harmonic functions then holds as a consequence of the previous theorem (with $n = 0$) and taking real parts of both sides of the identity.
]

#proposition("Other Properties of Harmonic Functions")[
  Let $u$ be harmonic on $Omega$. Then:
  - $u$ cannot achieve an interior min/max, unless it is constant, and if $Omega$ bounded, $u$ obtains its absolute min/max on $partial Omega$
  - if $Omega = RR^2$ and $u$ bounded, then $u$ is constant
  - $u$ is real-analytic, and in particular $C^infinity$
]


=== Conformal Mappings

#definition("Conformal Map")[
  A function $f : U -> V$, where $U, V subset CC$ open, is said to be a _conformal mapping_ if it is bijective and holomorphic. If $U, V$ are given and there exists a conformal map $f : U -> V$, we say $U, V$ are _conformal_.
]

#proposition[
  Let $f : U -> V$ be holomorphic and injective. Then:
  - $f'(z) eq.not 0$ for every $z in U$
  - $f$ is invertible when restricted to its image, and its inverse is holomorphic
  In particular, if $f$ conformal, then it's inverse $f^(-1) : V -> U$ is automatically holomorphic, and its derivative never vanishes.
]

#proposition([Conformal map from $DD$ to $HH$])[
  Let $DD$ be the open unit disc in $CC$ and $HH := {z in CC | "Im"(z) > 0}$ be the open upper half-plane. Then $DD$ and $HH$ are conformal, under the mapping $
  F : HH -> DD, quad F(z) := (i-z)/(i+z),
  $ with inverse $
G : DD -> HH, quad G(w) := i (1 - w)/(1+w).
  $
]

#lemma("Schwarz's Lemma")[
  Let $f : DD -> DD$ be a holomorphic function with $f(0) = 0$. Then the following hold:
  - $|f(z)| <= |z|$, and if there exists a $z_0 eq.not 0$ such that $|f(z_0)| = |z_0|$, then $f(z) = c z$ where $|c| = 1$ (i.e. $f$ a rotation)
  - $|f'(0)| <= 1$, and if equality holds, then $f(z) = c z$ where $|c| = 1$.
]

#proof[
  Let $g(z) := (f(z))/z$. Since $f(0) = 0$, $g$ has a removable singularity at the origin and therefore is holomoprhic. Let $z in DD$, assuming $|z| = r < 1$. Since $f$ maps to $DD$ and thus $|f| <=1$, we have that $|g(z)| <= 1/r$. By the maximum modulus principle, this bound must hold for all $z in DD_r$ i.e. for any $|z| < r$. Letting $r -> 1$ gives that $|g| <= 1$ which gives the proof. Again by the maximum modulus principle, we see that if $|g(z_0)| = 1$ for $z_0$ in $DD$ (i.e. an "interior max"), it must be that $|g|$ constant equal to 1, which gives the result. For the second point, note that $g(z) -> f'(0)$ as $z -> 0$, but also converges to $g(0)$ by holomorphicity. We know $|g| <= 1$, so it follows that $|f'(0)| <= 1$. Finally if $|f'(0)| = |g(0)| = 1$, from the same line of reasoning as above we have that $f$ a rotation.
]

#theorem("Automorphisms of the Unit Disc")[
  For $Omega subset CC$, define $"Aut"(Omega) := {f : Omega -> Omega | f "a conformal map"}$. This is naturally a group under composition.

  If $f in "Aut"(DD)$, then there exists a $theta in RR$ and $alpha in DD$ such that $
f(z) = e^(i theta) psi_alpha (z),
  $ where $psi_alpha (z) := (alpha - z)/(1 - overline(alpha) z)$ is a _Blaschke factor_.
]

#proof[
  Let $alpha in DD$ be such that $f(alpha) = 0$, which exists and is unique. Let $g = f compose psi_alpha$. One checks that $g(0) = 0$, so by Schwarz, $|g(z)| <= |z|$. $g$ is also invertible, and $g^(-1) (0)  = 0$ so we also have $|g^(-1) (w)| <= |w|$. This implies, taking $w = g(z)$, that $|z| <= |g(z)| <= |z|$ i.e. $|g(z)| = |z|$. This implies $g(z) = e^(i theta) dot z$ for some $theta in RR$, which gives the proof upon composing both sides by $psi_alpha$ (which is its own inverse).
]

#corollary("Automorphisms of the Upper Half Plane")[
Every automorphism in $"Aut"(HH)$ is a _linear fractional transformation_ of the form $
f_M (z) = (a z + b)/(c z + d),
$ for some $M in "SL"_2 (RR) = {M in RR^(2 times 2) : det(M) = 1}$. In fact, $
"Aut"(HH) tilde.equiv "PSL"_2 (RR) := "SL"_2 (RR)\/{I, -I}
$
]

#proof[
  Recall the conformal function $F : HH -> DD$. One checks that $Gamma : "Aut"(DD) -> "Aut"(HH)$ given by $Gamma(phi) := F^(-1) compose phi compose F$ is a group isomorphism. Thus to characterize automorphisms of $HH$ it suffices to compute the conjugation by $F$ of automorphisms of $DD$, which yields the result.
]



#theorem("Riemann-Mapping Theorem")[
  Let $Omega subset CC$ be a simply connected open domain that is not all of $CC$. Given $z_0 in Omega$, then there exists a unique conformal map $F : Omega -> DD$ such that $
F(z_0) = 0, quad F'(z_0) > 0.
  $ In particular, every such domain is conformal to the open unit disc.
]

#proof[
  The proof is long. The idea is as follows:
  1. Show $Omega$ conformal to an open subset of $DD$ containing the origin. One does this by basically 'shrinking' $Omega$ via a logarithmic-type transformation.
  2. Assuming from 1. that $0 in Omega subset DD$, one considers the family of functions $
  cal(F) := {f : Omega -> DD, f "holomorphic, injective, and" f(0) = 0}.
  $ One sees that $cal(F)$ is a nonempty, uniformly bounded family of holomorphic functions. By the Cauchy inequalities, $s := sup_(f in cal(F)) |f'(0)|$ exists (and is finite). Let ${f_n} subset cal(F)$ such that $|f'_n (0)| -> s$. By combining Cauchy's integral representation theorem, one obtains equicontinuity of $cal(F)$, which allows us to use an Arzela-Ascoli-type argument to argue that ${f_n}$ actually converges uniformly (on compact sets) to some holomorphic function $f$. We see that $f$ is injective (by an "argument principle"-type argument, using properties of $f$).
  3. We claim $f$ in step 2. is conformal. We showed holomorphicity and injectivity, so we need to show surjectivitiy. Supposing otherwise, the idea is to construct another function that lives in $cal(F)$ but with strictly greater derivative norm at 0, contradiciting the maximality. Then by precomposing $f$ with a rotation, one automatically gets the $f'(0) > 0$.
]

#corollary[
  Any two simply connected proper open subsets of $CC$ are conformal.
]

#remark[
  Remark that there is no hope that there exists a conformal map $f : CC -> DD$ for such a map would necessarily be entire and bounded and thus constant by Liouville's, and in particular not injective.
]

=== Some Fourier Transform

#definition("Fourier Transform")[
  The _Fourier transform_ of a function $f : CC -> CC$ is defined by, where the integrals make sense and converge, $
hat(f)(xi) := integral_(-infinity)^infinity f(x) e^(-2pi i x xi) dif x, quad xi in RR.
  $ 

  For $a > 0$, define the class of functions $
cal(F)_a := {f : #grid(inset: .4em, [$f$ holomorphic on $S_a := {z in CC | |"Im"(z)| <= a}$], [$exists A > 0$ such that $|f(z)| <= A/(1 + Re(z)^2)$ for all $z in S_a$]) }.
  $ Define finally $cal(F) := union.big_(a > 0) cal(F)_a$.
]

#proposition[
Let $f in cal(F)_a$ for some $a > 0$. Then $|hat(f)(xi)| <= B e^(-2 pi b |xi|)$  for all $xi in RR$ and $0 <= b < a$; when such a bound on a function exists, we say it is of _exponential type_.
]

#proof[The idea is to "shift" the contour to the line from $-infinity - i b$ to $infinity - i b$.]

#theorem("Fourier Inversion")[
  For $f in cal(F)$, then the _Fourier inversion formula_ holds, that is, for all $x in RR$, $
f(x) = integral_(-infinity)^infinity hat(f)(xi) e^(2pi i x xi) dif xi.
  $
]

#theorem("Poisson Summation Formula")[
  If $f in cal(F)$, $
  sum_(n in ZZ) f(n) = sum_(n in ZZ) hat(f)(n).
  $
]



#pagebreak()


// ! https://www.math.ubc.ca/sites/default/files/documents/Grad/QualifyExams/Algebra_syllabus.pdf

= Algebra

// ! smith normal form


== Linear

=== Elementary
// ! TODO
// system of linear equations & solutions
// matrices
// guassian elimination and rref
// invertibkle matrices, determinants, vandermonde matrices, eigenvalues & vectors

=== Vector Spaces
// ! TODO
// subspaces
// quotient spaces
// bases, dimension
// linear transformation
// change of basis, similarity
// rank, nullity
// inner product
// cs
// orthogonality, ocmplements, bases, gram schmidt
// adjoints, dual spaces

=== Diagonalization and Related

// ! TODO
// symmetric matrices, normal/adjoint operators
// quadratic forms
// minimal and characteristic polynomials
// Cayley-Hamilton
// Jordan canonical form
// matrix exponential


#pagebreak()

== Groups

// ! TODO
// [x] group actions; permutation, symmetric, alternating groups
// [x] subgroups, cosets, lagrange
// [x] group homomorphisms, normal, quotient, solvable
// [x] dihedral groups
// [] finitely generated abelian groups
// [] sylow's

=== Fundamentals

#definition("Groups, Action")[
  A group $G$ is a set equipped with a binary operation $dot$ satisfying the axioms:
  - $f dot (g dot h) = (f dot g) dot h$, $forall f, g, h in G$
  - $exists 1 in G "s.t." g dot 1 = 1 dot g = g forall g in G$
  - $forall g in G, exists g^(-1) in G "s.t." g dot g^(-1) = g^(-1) dot g = 1$ 

  $G$ is said to be abelian/commutative if $g h = h g$ for every $g, h in G$.

  A group action on a set $X$ is a function $phi : G times X -> X$ satisfying:
  - $phi(h, phi(g, x)) = phi(h dot g, x), forall g, h in G, x in X$
  - $phi(1, x) = x forall x in X$
  When clear from context, we write $g dot x = phi(g, x)$.
  When $phi(G, X) := {phi(g, x) : g in G, x in X}$ is equal to $X$, we say the action of $G$ is _transitive_. A set $X$ equipped with a group action of $G$ is sometimes called a _$G$-set_.
]

#definition("Orbit, Stabilizer")[
  Let $G$ act on a set $X$. Define, for $x in X$, $
cal(O)_x = "Orb"_G (x) &:= "orbit of "x" under "G = {g dot x : g in G} subset X, \
G_x  = "Stab"_G (x) &:="stabilizer of "x" under "G = {g in G : g dot x = x} subset G.
  $
]
#remark[The orbit is "everywhere $x$ can go" (under $G$), and the stablizer is what "fixes" $x$ (under $G$).]

#definition[
  A _subgroup_ $H$ of a group $G$ is a subset of $G$ which is still a group when endowed with the operation from $G$ (so in particular it is closed under the operation). One sometimes write $H < G$, or $H <= G$ if $H$ possibly equal to $G$.

  A _(left) coset_ of $H$ in $G$ is a set of the form $
a H = {a h : h in H},
  $ where $a$ some element of $G$. One denotes $G\/H = {"set of cosets of" H}$ Equivalently, there is a natural action of $H$ acting on $G$ as a set (by right-multiplication), given by $h star g := g dot h$; thus cosets of $H$ are just orbits under this action.
]

#definition("Homomorphism")[
  A _group homorphism_ $phi : G_1 -> G_2$ is a function such that $
phi(g h) = phi(g) phi(h)
  $ for all $g, h in G_1$. When $phi$ a bijection we call it a group isomorphism.
]

#theorem("Lagrange")[
Let $H subset G$ a finite subgroup of a finite group. Then all cosets of $H$ have the same cardinality, and in particular are disjoint. In particular, we have $
|G| = |G\/H| dot.c |H|,
$ and so $|H|$ divides $|G|$.
]

#proof[
  The disjointness follows from the "orbit of an action" characterization (namely, orbits are either disjoint or equal). For the equality of cardinality, fix $a in.not H$ and define the map $f: H -> a H$, $h |-> a h$. This is an injection, since $f(h_1) = f(h_2) => a h_1 = a h_2 => h_1 = h_2$ by multiplying both sides by $a^(-1)$. This is also a surjection since given $a h in a H$, one simply maps $h$ by $f$. This shows $|a H| = |H|$ and since $a$ was arbitrary, completes the proof. The "in particular" follows from the partitioning result.
]

#proposition[
  Let $X$ a transitive $G$-set. Then there exists a subgroup $H$ of $G$ such that $X$ is isomorphic (as a $G$-set) to $X tilde.equiv G\/H$, equipped with the left-action $
  (g, a H) in G times G\/H |-> g dot a H := (g a) H in G\/H.
  $ Thus, $|X|$ divides $|G|$ and the _orbit-stabilizer formula_ holds: $
|G| = |X| dot |G_x|, quad forall x in X.
  $
]

#remark[
  When we say "$X_1, X_2$ isomorphic as $G$-sets", we mean a bijection which respects the respect group actions, i.e. $f : X_1 -> X_2$, $f(g dot_1 x) = g dot_2 f(x)$.
]

#remark[
  If $X$ not transitive, we can reword this proof by taking any orbit $cal(O)_x$ in $X$, in which case the formula reads $|G| = |cal(O)_x| dot |G_x|$.
]

#proof[
  Fix $x in X$ and let $H := G_x$, and let $f : G\/H -> X$ be given by $f(a H) := a dot x$.
]

#let normal = $triangle.l.small$

#definition("Normal subgroup, quotients")[
  Given a group $G$, a subgroup $H subset G$ is said to be _normal_ if it is closed under conjugation by $G$, that is, $
g h g^(-1) in H, quad forall g in G, h in H.
  $ Sometimes people write $H normal G$ for "$H$ is a normal subgroup of $G$" (_sometimes with a bar underneath if $H$ possible equal to $G$_).

  The _quotient group_ is the group $G\/H$ of cosets of $G$ with respect to $H$ equipped with left-multiplication (_one checks that this is indeed a well-defined group when $H$ normal in $G$)._

  $G$ is said to be _solvable_ if there exists a sequence of subgroups $
{1} = G_0 subset G_1 subset dots.c subset G_(n-1) subset G_n subset G
$ such that $G_(i-1)$ a normal subgroup of $G_i$ and $G_i\/G_(i-1)$ abelian, for $i = 1, dots, n$.
]

#proposition[Let $phi : G -> H$ a group homomorphism. Then $N := ker(phi)$ a normal subgroup of $G$.

Moreover, $phi$ induces an injective homomorphism $tilde(phi) : G\/N -> H$ defined by $tilde(phi) (a N) := phi(a)$. In particular, $im(phi)$ is isomorphic to $G\/N$.
]

#proof[
 If $h in N, g in G$, then $phi(g h g^(-1)) = phi(g) phi(h) phi(g)^(-1) = phi(g) dot phi(g)^(-1) = 1$ so $g h g^(-1) in N$.

 We need to show $tilde(phi)$ well-defined. If $a N = a' N$, then there exists $h in N$ such that $a = a' h$. So $
tilde(phi)(a N) = phi(a) = phi(a' h) = phi(a') phi(h) = tilde(phi) (a' N) dot 1 = tilde(phi)(a' N),
 $  so the function is well-defined. It is injective since $
tilde(phi)(a N) = 1 <=> phi(a) = 1 <=> a in N <=> a N = N,
 $ but $N = 1_(G\/N)$, so $phi$ injective.
]


=== Sylow

#theorem("Sylow's Theorem")[
  Suppose $hash G = m dot p^t$, where $p divides.not m$ and $p$ prime.
  1. (_Sylow 1_) $G$ has a subgroup of cardinality $p^t$ (called a _Sylow-$p$ subgroup_ of $G$).
  2. (_Sylow 2_) Suppose $H_1, H_2$ are Sylow-$p$ subgroups of $G$, then there exists a $g in G$ such that $g H_1 g^(-1) = H_2$.
  3. (_Sylow 3_) If $N_p$ the number of distinct Sylow-$p$ subgroups of $G$, then:
    1. $N_p divides m$
    2. $N_p equiv_p 1$
]

#proof[
  // TODO
]



=== Some Particular Groups

#definition("Generator of a group")[
  We say a group $G$ is _generated_ by elements $g_1, dots, g_n$ if $
G = angle.l g_1, dots, g_n angle.r := {"all possible products of powers of" g_1, dots, g_n}.
  $ 

]

#definition("Cyclic Groups, Unit Groups")[
  For $n >= 1$ an integer, the _cyclic group of order $n$_ is defined as $ZZ\/n ZZ = {0, 1, dots,n -1 }$ equipped with addition and with entries read mod $n$.

  For $n >= 1$ an integer, the _unit group of order $n$_ is defined as $(ZZ\/n ZZ)^times$ equipped with multiplication, where we restrict $ZZ\/n ZZ$ to the invertible elements (mod $n$).

]

#proposition[Let $p$ prime and $G$ a group of order $p$. Then $G = ZZ\/p ZZ$. In addition, $hash (ZZ\/p ZZ)^times = p - 1$.]

#proof[
  Let $a in G$ not equal to the identity. Then the subgroup $H$ generated by $a$ (i.e. ${a, a + a, a + a + a, dots}$) is a subgroup of $G$ isomorphic to $ZZ\/n ZZ$ where $n = hash H$. Being a subgroup, $n|hash G$, and since $n > 1$ and $hash G$ prime, $n = p$ and thus $H = G tilde.equiv ZZ\/p ZZ$.

  Let $a in (ZZ\/p ZZ) \\ {0}$. Then $a divides.not p$ so $gcd(a, p) = 1$. Thus there exists a $b, c in ZZ$ such that $a b + c p = 1$ i.e. $a b equiv_p 1.$ Rewriting $b$ mod $p$ so that $b in (ZZ\/p ZZ)\\{0}$ completes the proof of the second part, since then we've shown ($(ZZ\/p ZZ)^times$ equals (as a set) $(ZZ\/p ZZ) \\ {0}$).
]

#definition("Permutation, Symmetric, Alternatic Groups")[
  Let $X$ a finite set of $n$ elements. The _symmetric group_ of $X$ is the set of bijections of $X$, i.e. $
    S_X := {f : X -> X | f "a bijection"}.
  $
  When $X = {1, dots, n}$, we often write $S_n equiv S_X$. We call $f in S_X$ a _permutation_ of $X$.

  The _sign,_ or $sgn$, of a permutation $f in S_n$ is defined to be $
sgn(f) := (-1)^N(f), quad N(f) := hash {(x, y) in X times X | x <y "and" f(x) > f(y)},
  $ i.e. the number of "inversions" that $f$ contains. We sometimes say $f$ is even/odd if $sgn(f) = +1\/-1$.

  The _alternating group_ on $n$ elements is the subgroup $
A_n := {f in S_n | sgn(f) = 1 }.
  $
]

#proposition[
  - $hash S_n = n!$, $hash A_n = (n!)/2$
  - a _transposition_ of ${1, dots, n}$ is a permutation that only interchanges two elements and fixes the rest. Any permutation can be written as a composition of transpositions. Moreover, the sign of a permutation is equal to the parity of (any) number of transpositions needed to write the permutation
]

#proof[
  A permutation, being a bijection of ${1, dots, n}$ has $n$ choices of where to send $1$, $n-1$ choices of where to send $2$, etc, for $n dot (n-1) dots.c 1 = n!$ total choices. So, $hash S_n = n!$. The size of $hash A_n$ follows pretty clearly from the definition of $sgn$. Alternatively, one notes that $sgn : S_n -> {-1, 1}$ a surjective group homomorphism (with the right-hand side equipped with multiplication). Then $A_n = ker(sgn)$, and thus $(hash S_n)\/(hash A_n) = 2$.
]

#definition("Dihedral Groups")[
  For $n >= 1$, the _order $2n$ dihedral group_ (on $n$ vertices) is defined as the gorup generated by $
D_(2 n) := angle.l sigma, tau angle.r,quad "ord"(sigma) = 2, "ord"(tau) = n, sigma tau sigma^(-1) = tau^(-1).
  $
]

#proposition[
  $hash D_(2 n) = 2 n$.
]

#proposition("Finitely Generated Abelian Groups")[
  An abelian group $G$ is said to be _finitely generated_ if it has a finite generating set. Any finitely generated abelian group $G$ is isomorphic to $
ZZ^m plus.circle ZZ\/n_1 ZZ plus.circle dots.c plus.circle ZZ\/n_m ZZ.
  $
]


#pagebreak()
== Rings
// ! TODO
// [x] ideals; prime + maximal
// [x] homomorphosms, kernels, quotients
// [] pids, unique facotrization, euclidean domains
// [ ] unipotent & nilpotent elements
// [x] rings of polynomials; factorization of polynomials
// ! []  Gauss's lemma, eisenstein's criterion


#definition("Rings, Ideals")[A _ring_ is a set $R$ equipped with two binary operators $+$ and $times$ such that 
- $(R, +)$ an abelian group
- $(R, times)$ a monoid (has identity and is associative)
- $a times (b + c) = a times b + a times c$
- $(b + c) times a = b times a + c times a$
A commutative ring is a ring where $times$ is commutative.

An _ideal_ $I$ of a ring $R$ is a subset $I subset R$ such that $I$ is an additive subgroup of $R$ and is closed under multiplication by $R$. We sometimes write $I normal R$.
]

#remark[Some conventions do not require rings to have multiplicative identities, and call those with such elements "rings with identity".]

#definition("Types of Ideals")[
  Let $I normal R$. We say $I$ is:
  - _maximal_ if for all ideals $J normal R$, if $I subset.neq J$ then $J = R$
  - _prime_ if $a dot b in I => a$ or $b in I$
  - _principal_ if $I$ of the form $a R = (a) = {a r : r in R}$ for some $a in R$
]

#definition("Types of Rings")[
  Let $R$ be a nonzero ring. A _left (right) zero divisor_ of $R$ is an element $a in R$ such that there exists a nonzero $b in R$ such that $a b = 0$ ($b a = 0$). We say $R$ is:
  - an _integral domain_ if it is commutative and has no nonzero zero divisors
  - a _principal ideal ring_ if every ideal in $R$ is principal
  - a _Euclidean domain_ if it is an integral domain upon which there exists a function $f : R\\{0} -> ZZ_(>=0)$ such that for all $a in R,  b in R\\{0}$ there exists $q$ and $r$ in $R$ such that $a = b q + r$ and either $r =0$ or $f(r) < f(b)$
  - a _principal ideal domain (PID)_ if it is an integral domain and a principal ideal ring
]

#remark[
  The $f$ function, called a _Euclidean function_, is essentially a generalization of "size", which is not necessarily an ordering but reflects some of its properties.
]

#proposition[
  Euclidean domain $=>$ PID. The integers are a Euclidean domain. If $FF$ a field, then $FF[x] = {p(x) : p "a polynomial with coefficients in" FF}$ is a Euclidean domain.
]

#proof[
  Let $R$ a Euclidean domain and $I subset R$ an ideal. Then, $S:={f(r) | r in I}$ is a subset of the natural numbers and thus must have a least element by the Well-Ordering Principle. Let $m in I$ be such that $f(m) = min S$. We claim $I = (m)$. The direction $(m) subset I$ is clear since $m in I$. Now let $a in I$ be any other element. By the Euclidean property, $a = m q + r$ for some $q, r in R$. If $r = 0$ we're done, so assume $r eq.not 0$ so then $f(r) < f(m)$. This implies $r$ cannot be in $I$, else we'd contradict the minimality of $m$. But $a - m q in I$ (since $a, m in I$, and $q in R$ implies $m q in I$), but this equals $r$, so we have a contradiction. Thus $r = 0$, and so $a =m q in (m)$, hence $I = (a)$.

  The integers are Euclidean by taking $f(r) = r$ and by employing the Euclidean algorithm, and $FF[x]$ is by taking $f(p) = "deg"(p)$ and employing the Euclidean algorithm (for polynomials).
]

#definition("Homomorphism")[
  A ring homomorphism $phi : R -> S$ is a map that is a group homomorphism on $(R, +)$, is multiplicative (i.e. $phi(a b) = phi(a)phi(b)$), and $phi(1) = 1$.
]

#proposition[
  Given a ring homomorphism $phi : R -> S$, $ker(phi)$ an ideal of $R$. Conversely, if $I subset R$ is an ideal, then there exists a ring $S$ and a surjective homomorphism $phi : R -> S$ such that $I = ker(phi)$.

  If $phi : R-> S$ is a surjective ring homomorphism, then $R\/ker(phi)$ is isomorphic to $S$.
]

#proof[
For the first, we know from the group homomorphism property that $ker(phi)$ closed under addition, and if $r in ker(phi)$ and $a in R$, then $phi(a r) = phi(a) phi(r) = phi(a) dot 0 = 0$ so $a r in ker(phi)$. For the second, we can define the _quotient ring_ $S := R\/I = {a + I : a in R}$, with addition defined as in a quotient group and multiplication defined "component wise" (one checks this is well-defined and defines a ring). Then define $phi : R -> S$ by $phi(r) = r + I$.

The last point is the _first isomorphism theorem_ (for rings) and the proof is identical as the analog for groups.
]

#proposition[
  Let $R$ a ring.
  - $I$ is a prime ideal iff $R\/I$ has no nonzero zero divisors
  - $I$ is a maximal ideal iff $R\/I$ is a field
]

#proof[
  Assume $I$ prime and that $(a + I)(b + I) = 0 + I$. This implies $a b in I$, so either $a$ or $b$ in $I$ by primality. Thus either $a + I$ or $b + I = I$, and in either case neither can be a nonzero zero divisor. The converse direction is identical.

// ! TODO
  Assume $I$ maximal. We need to show $R\/I$ has inverses. Let $a + I in R\/I$ nonzero (i.e. $a in.not I$). Consider the ideal $J := R a + I = {r a + b : r in R, b in I}$. This is an ideal which contains $I$ as a subset. By maximality, $J = I$ or $J = R$, but the first is not possible since this would imply $a in I$. So $J = R$, and thus given $1 in R$, there exists $r in R$ and $b in I$ such that $a r + b = 1$. Thus, $
(a + I) (r + I) = a r + I = a r + b + I = 1 + I,
  $ i.e. $r + I = (a + I)^(-1)$. Conversely, assume $J supset.neq I$. Let $a in J\\I$, so $a + I eq.not 0 in R\/I$ is invertible, i.e. there is a $b in R$ such that $(a + I) (b + I) = 1 + I$. This implies there is an $r in I$ such that $a b + r = 1$. Since also $r in J$, this implies $1 in J$, and thus $J = R$ and so $I$ maximal.
]





#pagebreak()
== Fields & Galois Theory


#definition("Fields, Field Extensions")[
  A _field_ is a commutative ring $F$ with identity in which every nonzero element has a multiplicative inverse.

  A _field extension_ $E$ of a field $F$ is a field which contains $F$ as a subfield; we write $E\/F$. We can canonically view $E$ as an $F$ vector space (by forgetting the multiplicative structure of elements); we write $[E : F] := "dim"_F (E)$ for the _degree_ of $E$ over $F$. We say $E\/F$ a _finite extension_ if this number is finite.
]

#proposition("Multiplicativity of Degrees")[
  Let $K\/E$ and $E\/F$ be finite extensions. Then $K\/F$ also a finite extension, and $
[K : F] = [K : E] dot [E : F].
  $
]

#proof[
If ${e_1, dots, e_n}$ a basis for $E\/F$ and ${k_1, dots, k_m}$ a basis for $K\/E$, one checks that ${e_i dot.c k_j : 1 <= i <= n, 1 <= j <= m}$ a basis for $K\/F$.
]

#definition("Algebraic, Transcendental")[
Let $E\/F$. We say $alpha in E$ is _algebraic_ if it is the root of some polynomial $f(x) in F[x]$. We say $alpha$ is _transcendental_ otherwise.
]

#proposition[If $E\/F$ finite, every $alpha in E$ is algebraic. Moreover, there exists a polynomial of degree at most $[E : F]$ that $alpha$ satisfies.]

#proof[
Let $alpha in E$ and put $n := [E : F]$. Then ${1, alpha, alpha^2, dots, alpha^n}$ must be a linearly independent set, and thus there exist $f_0, dots, f_n in F$ such that $
f_0 + f_1 alpha + dots.c + f_n alpha^n = 0.
$ In particular, we see that this implies $f(x) := f_n x^n + dots.c + f_1 x + f_0$ is a polynomial in $F[x]$ with $alpha$ as a root.
]


#definition("Splitting Fields")[
  We say $E\/F$ a _splitting field_ of a polynomial $f(x) in F[x]$ if
  1. $f(x)$ factors into linear factors in $E[x]$, i.e. there exists $r_1, dots, r_n in E$ such that $
f(x) = (x - r_1) dots.c (x - r_n),
  $ and
  2. $E$ is _generated_ by $r_1, dots, r_n$.

  Remark that $n <= [E : F] <= n!$.
]

#remark[
  We say a field extension $E\/F$ is _generated by a set_ $S$ if it is the smallest field containing $F$ as a subfield and the elements in $S$.

  Given an element $alpha in E\/F$, a polynomial $f in F[x]$ is called a _minimal polynomial_ for $f$ if $f(alpha) = 0$ and $f$ of minimal degree.
]


#theorem("Eiseinstein's Criterion")[
  Let $f(x) = a_n x^n + dots.c + a_1 x + a_0 in ZZ[x]$. Assume there exists a prime $p$ such that:
  1. $p | a_i$ for $0 <= i < n$
  2. $p divides.not a_n$
  3. $p^2 | a_n$
  Then $f(x)$ is irreducible over $QQ$.
]

#theorem("Rational Root Theorem")[
  Let $f(x) = a_n x^n + dots.c + a_1 x + a_0 in ZZ[x]$ with $a_n eq.not 0$. Then if $x = p/q$ (reduced) a rational root of $f$, then $p|a_0$ and $q|a_n$.
]

#theorem("Gauss's Lemma")[
  
]

#let Aut = "Aut"
#let Gal = "Gal"

#definition("Automorphisms of a Field Extension")[
  Let $E\/F$, and define the group $
    Aut(E\/F) := {sigma : E -> E | sigma "is" F-"linear", "multiplicative", "and" sigma|_F equiv id }.
  $
]

#remark[
  $sigma in Aut (E\/F)$ preserves the field structure on $E$ and leaves $F$ invariant.
]

#proposition([Properties of $Aut(E\/F)$])[
Let $E\/F$ be a finite extension. Then the following hold:
  - $Aut(E\/F)$ acts on $E$ with finite orbits (that is, $hash "Orb"_(Aut(E\/F)) (alpha) < infinity$ for every $alpha in E$)
  - $hash"Aut"(E\/F) < infinity$; in fact,
  - $hash"Aut"(E\/F) <= [E : F]$.
  If $hash"Aut"(E\/F) = [E : F]$, we say that $E\/F$ a _Galois extension_, and write $Gal(E\/F) = Aut(E\/F)$.
]

#proof[
  Let $alpha in E\/F$ satisfy $f(x) = a_n x^n + dots.c + a_0$ (exists by finiteness). Let $sigma in Aut(E\/F)$. Then notice, using linearity and multiplicativity of $sigma$, $
f(sigma(alpha)) &= a_n sigma^n (alpha) + dots.c + a_1 sigma(alpha) + a_0 \
&= a_n sigma(alpha^n) + dots.c + a_1 sigma(alpha) + a_0 \
&= sigma(a_n alpha^n + dots.c + a_1 alpha + a_0) \
&= sigma (f(alpha)) = sigma(0) = 0.
  $ Thus, $sigma(alpha) in {"roots of" f}$ hence $"Orb" (alpha) subset {"roots of" f}$, proving the finiteness since $f$ has only finitely many roots. By a previous proposition, this moreover shows $hash"Orb"(alpha) <= [E : F]$.

Let $e_1, dots, e_n$ a basis for $E\/F$ and $sigma in Aut(E\/F)$. By linearity, $sigma$ uniquely determined by the $n$-tuple $S_sigma := (sigma(e_1), dots, sigma(e_n))$. We see that $S_sigma in "Orb"(e_1) times dots.c times "Orb"(e_n)$. The set on the right-hand side is finite (with size at most $n^n$ by the previous proof) so $hash"Aut"(E\/F) < infinity$.

// ! TODO the better bound... its annoying.
]

#proposition[
  Let $E\/F$ a finite Galois extension with Galois group $G$. Then, $E^G := {alpha in E : g alpha = alpha forall g in G}$ is a subfield of $E$ containing $F$ and moreover $E^G = F$.
]

#proof[
  Checking subfield is clear. Consider the group $"Aut"(E\/E^G)$. This contains $G$ as a subgroup, so $
[E:F] = hash G <= hash"Aut"(E\/E^G) <= [E : E^G].
  $ Also $[E : E^G]$ divides $[E : F]$, which is then only possible if $[E : E^G] = [E : F]$ so it must $E^G = F$.
]

#proposition[
  Let $E\/F$ Galois. If $f$ irreducible over $F$ and has a root in $E$, then $f$ splits completely into linear factors in $E$.
]

#proof[
  Let $r$ be a root. Let ${r_1, dots, r_n}$ be the orbit of $r$ under $G$. Let $ g(x) = (x - r_1) dots.c (x - r_n) = x-sigma_1 x^(n-1) + dots.c + (-1)^n sigma_n, $ where $sigma_i$'s are called _elementary symmetric functions_. Note that each $sigma_i$ invariant under permutation by $G$, and in particular, $sigma_i in E^G$. It follows that each $sigma_i in F$, by Galois and so $g(x) in F[x]$. Recalling that $f$ irreducible over $F$, it must be the minimal polynomial of $r$ and thus $f|g$. Since $g$ splits into linear factors (in $E[x]$), so must $f$.
]


=== Characterization of Finite Fields


#theorem[
  Let $F$ be a finite field (i.e. as a set, $F$ is finite). Then, $hash F = p^n$ for some prime $p$ and an integer $n >= 1$.

  Conversely, given a prime $p$ and an integer $n >= 1$, there exists a unique (up to isomorphism) field of cardinality $p^n$.
]

#proof[
  For the first, since $F$ a finite field, there must exist some minimal integer $p$ such that $1 + dots.c + 1$ ($p$-times) equals 0. $p$ must be prime, else this would imply $F$ has zero divisors. In particular, this shows $FF_p = (ZZ\/p ZZ)$ is a subfield of $F$; we can view $F$ as a vector field over $FF_p$, and letting $n = dim_(FF_p) (F)$, it's clear that $hash F = p^n$.

  For the second point, let $f(x) = x^(p^n) - x$ as a polynomial over $FF_p$ and let $F$ be its splitting field. We claim $hash F = p^n$. Indeed, $f'(x) = - 1$ in $F$ and so $gcd(f,f') = 1$ and so $f$ has no repeated roots. Thus, $hash F >= p^n$. Moreover, one remarks that the set of roots of $f$ is itself a field over $FF_p$, thus $hash F <= p^n$. Uniqueness follows from uniqueness of splitting fields.
]


=== Fundamental Theorem of Galois Theory

#lemma[
  If $E\/F$ Galois and $K subset E$, then $E\/K$ Galois. If $H$ a subgroup of the Galois group $"Gal"(E\/F)$, then $E^H$ a subfield of $G$ and $H = "Gal"(E\/E^H)$, and in particular $hash H = [E : E^H]$.
]


#remark[
 There is _no guarantee_ that $K\/F$ is Galois in general. 
]

#proposition("Galois Correspondance")[
  Let $E\/F$ a Galois extension. Then the map $
  {K "field" | F subset K subset E } -> {"subgroups of" "Gal"(E\/F)}, quad K|-> "Gal"(E\/K)
  $ is a bijection with inverse $
H |-> E^H.
  $ Moreover, these maps are "order reversving" in the sense that $
  K_1 subset K_2 => "Gal"(E\/K_1) supset "Gal"(E\/K_2), quad H_1 subset H_2 => E^(H_1) supset E^(H_2).
  $
]

#proposition[
  Let $F subset K subset E$ with $E\/F$ Galois. Then TFAE:
  1. $sigma K = K$ for all $sigma in "Gal"(E\/F)$
  2. $K$ Galois over $F$
  3. $"Gal"(E\/K)$ is a normal subgroup of $"Gal"(E\/F)$
]

#definition[
  An extension $E\/F$ is called _radical_ if there exists an integer $n >= 1$ and element $a in F$ such that $E = F(a^(1\/n))$. $E\/F$ a _tower of radical extensions_ if there is a sequence of extensions $E = E_0 subset E_1 subset dots.c subset E_n = F$ where each $E_i\/(E_(i-1))$ a radical extension.
]

#theorem[
  If $E\/F$ a tower of radical extensions, then it is contained in Galois extension with solvable Galois group.
]

#theorem("Fundamental Theorem of Galois")[
Assume $F$ a field of characteristic 0. Suppose $f(x) in F[x]$ is _solvable by radicals_, that is, a splitting field of $f$ is contained in a radical extension. Then, $"Gal"(f)$ is a solvable group.
]
// ! TODO
// [] field extensions, degrees, finite fields
// [] splitting fields, galois extensions, galois group
// [] fundamental theory of Galois theory, solvability in radicals


// ! TODO: Highlights
// - Separation of Variables
// -- application of sturm-liouville
// -- on bounded domains, disc, outside of a disc
// - Laplace, Fourier Transform
// - Dynamical systems stuff/sketching
// - Fourier series expansions
// - Sturm-Liouville Theory
// - second-order nonhomogeneous ODEs
// -- homogeneous solution -> particular solution -> general solution
// -- reduction of order
// - substitutions!


= Differential Equations

== Scalar ODEs

=== First Order

=== Second Order, Constant Coefficients

=== Reduction of Order

=== Variation of Parameters

=== Sturm-Liouville Theory

=== Power Series Solutions



== Linear Vector ODEs

=== Constant Coefficient Linear Systems

=== The Method of Undetermined Coefficients


== Nonlinear Vector ODEs

=== Critical Points and Stability



== General ODEs

=== Higher Order to Vector First Order

=== Laplace Transform



== PDEs

=== Heat Equation

=== Wave Equation

=== Laplace's Equation

=== Separation of Variables

=== Laplace, Fourier Transforms Solutions to the Heat Equation




= Miscellaneous Things to Remember

== Trigonometric Identities

$
cos^2 (theta) &= (1 + cos(2 theta))/2, quad 
sin^2 (theta) &= (1 - cos(2 theta))/2
$

$
sin(2 theta) &= 2 sin(theta) cos(theta) \
cos(2 theta) &= 1 - 2 sin^2 (theta)
$

#remark[The easiest way to prove these is to use complex exponentials:

$
sin(theta) &= (e^(i theta) - e^(- i theta))/(2 i) \
cos(theta) &= (e^(i theta) + e^(- i theta))/(2)
$]








