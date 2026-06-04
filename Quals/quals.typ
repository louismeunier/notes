// ! external
// #import "../notes.typ": conf
#import "../typst/shortcuts.typ": *
// ? Change me:

#let conf = (
  course_code: "",
  course_title: "Qualifying Exams Study Guide",
  subtitle: "Real, Complex Analysis; Linear Algebra, Group Theory, Galois Theory",
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
"div"F (x) := (partial F_1)/(partial x_1) (x) + dots.c + (partial F_n)/(partial x_n) (x).
   $ 
 - If $n = 3$, define the _curl_ of $F$ at $x$ (assuming its first-partial derivatives exist) by $
"curl"F(x) &:= det(mat(e_1, e_2, e_3; partial_x, partial_y, partial_z; F_1 (x), F_2 (x), F_3 (x))) \
&= (dots.c)
 $

]

#proposition[
  If $f : RR^n -> RR$ differentiable at $x in RR^n$, then $
dif f(x; d) = gradient f(x)^T.
  $ 
  If $d = e_i$ and $f$ partially differentiably in $x_i$ at $x$, then $dif f(x; d) = (partial f)/(partial x_i) (x)$.
]


#theorem("Mean-Value Theorem")[
  Let $f : RR^n -> RR$ be differentiable on an open ball $B subset RR^n$. Then for any $x, y in B$, there exists a $z in B$ such that $
f(x) - f(y) = Dif f(z_0) (x - y).
  $
]

#proof[
  Define $phi(t) := f(y + t (x-y)$ for $t in [0, 1]$, noting that $phi(0) = y$ and $phi(1) = x$. One computes, using the chain rule, that $phi'(t) = Dif f(y + t(x -y)) dot (x - y)$. By the one-variable mean-value theorem, there exists some $t_0 in [0, 1]$ such that $phi(1) - phi(0) = phi'(t_0)$. Letting $z = y + t_0 (x - y)$ gives the desired result, noting that $z$ indeed in $B$ by convexity.

  For completeness, we also prove the one-variable mean-value theorem.
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
// outward unit normal to surfaces
// conservative vector fields
// gradient/potential fields

// ! TODO?
// define general Riemann integration, all that general theory
// change of variable theorem (do this one better!)
// fubini's
// define curve, integration on curves
// conservative vectorfields, poincare?
// define surfaces, integration on surfaces
// green's (+ consequences), stoke's, divergence, 

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
  
]

#definition("Regular Partition")[]

#theorem("Change of Variables")[
  
]





// ! TODO


=== Analysis on Functions

#pagebreak()
== Complex

=== Analytic Functions

// ! TODO
// [x] Cauchy-Riemann
// [x] Cauchy's Theorem
//    [] Cauchy's Extra Stuffs
// [] Rouche's
// [] Maximum modulus principle
// [] Harmonic Functions...

// Conformal

#definition("Analytic/Holomorphic")[
  A function $f : CC -> CC$ is said to be _analytic_ on $Omega$ if $f$ is given by a converging power series everywhere in $Omega$. It is said to be holomorphic if $f'$ exists.
]
For $z = x + i y in CC$ and $f : CC -> CC$, write $f(z) = u(x, y) + v(x, y) i$ for real-valued functions $u, v$. Then, the _Cauchy-Riemann (CR) equations_ are the equations $
(partial u)/(partial x) = (partial v)/(partial y), quad (partial u)/(partial y) = - (partial v)/(partial x).
  $
#theorem("Cauchy-Riemann Equations")[
   $f$ is holomorphic if and only if $u, v$ satisfy the CR equations.
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

// ! some famous/important series...


#theorem("Cauchy's Integral Formula")[
  Let $f$ holomorphic on $Omega$, which contains a circle $C$ and its interior. Then $
f(z) = integral_(C^+) (f(w))/(w - z) dif w, quad forall z in Omega.
  $ In particular, this implies $f$ is analytic on all of $Omega$, with $
f^((n)) (z) = (n!)/(2pi i) integral_(C^+) (f(w))/((w - z)^(n + 1)) dif w, 
  $ and thus $
f(z) = sum_(n=0)^infinity (f^((n)) (z_0))/n! (z - z_0)^n, 
  $ for any $z_0 in Omega$ and $z$ such that $z - z_0 in Omega$.
]

#corollary("Cauchy's Inequalities")[
  Let $f : Omega -> CC$ holomorphic. Then $ |f^((n)) (z)| <= (n! norm(f)_(C_R (z), infinity))/(R^n), $ where $R > 0$ any real number such that $D_R (z) subset CC$, where $D_R (z)$ the $R$-radius disc centered at $z$, and $ norm(f)_(C_R (z), infinity) := sup_(w in C_r (z)) abs(f(w)). $
]



// ! Cauchy's integral formula and consequences
// ! 

// ! Liouville's


// ! Morera's theorem

// ! residue theorem



#theorem("Argument Principle")[
  Let $f$ be a meromorphic function on the interior of a simple closed curve $C subset CC$, such that $f$ has no roots nor poles on $C$. Then, $
1/(2pi i) integral_C (f'(z))/(f(z)) dif z = hash {"zeroes of" f "inside" C} - hash {"poles of" f "inside" C},
  $ the right-hand side counted with multiplicity.

]

#theorem("Rouché's")[
  Let $f, g$ be holomorphic functions on $Omega$ with a curve $C subset Omega$ such that 
  - $|f| > |g|$ on $C$,
  - both $f$, $g$ never vanish on $C$. 

  Then, $f$ and $f + g$ have the same number of zeros in the interior of $C$.
]

// ! Maximum modulus principle

// ! simply connectedness

// ! logarithms

// ! mean value theorem

=== Harmonic Functions
// ! basic properties
// ! harmonic conjugates
// ! schwarz's lemma

// ! Fourier transform and inversion..


// ? === Complex Integration

=== Conformal Mappings

// ???


#pagebreak()


= Algebra


== Linear

=== Elementary
// system of linear equations & solutions
// matrices
// guassian elimination and rref
// invertibkle matrices, determinants, vandermonde matrices, eigenvalues & vectors

=== Vector Spaces
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

// symmetric matrices, normal/adjoint operators
// quadratic forms
// minimal and characteristic polynomials
// Cayley-Hamilton
// Jordan canonical form
// matrix exponential


#pagebreak()

== Groups

#definition("Groups, Action")[
  A group $G$ is a set equipped with a binary operation $dot$ satisfying the axioms:
  - $f dot (g dot h) = (f dot g) dot h$, $forall f, g, h in G$
  - $exists 1 in G "s.t." g dot 1 = 1 dot g = g forall g in G$
  - $forall g in G, exists g^(-1) in G "s.t." g dot g^(-1) = g^(-1) dot g = 1$ 
  A group action on a set $X$ is a function $phi : G times X -> X$ satisfying:
  - $phi(h, phi(g, x)) = phi(h dot g, x), forall g, h in G, x in X$
  - $phi(1, x) = x forall x in X$
  When clear from context, we write $g dot x = phi(g, x)$.
  When $phi(G, X) := {phi(g, x) : g in G, x in X}$ is equal to $X$, we say the action of $G$ is _transitive_. A set $X$ equipped with a group action of $G$ is sometimes called a _$G$-set_.
]

#definition("Homomorphism")[
  A _group homorphism_ $phi : G_1 -> G_2$ is a function such that $
phi(g h) = phi(g) phi(h)
  $ for all $g, h in G_1$. When $phi$ a bijection we call it a group isomorphism.
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

#definition("Orbit, Stabilizer")[
  Let $G$ act on a set $X$. Define, for $x in X$, $
cal(O)_x &:= "orbit of "x" under "G = {g dot x : g in G} subset X, \
G_x &:="stabilizer of "x" under "G = {g in G : g dot x = x} subset G.
  $
]
#remark[The orbit is "everywhere $x$ can go" (under $G$), and the stablizer is what "fixes" $x$ (under $G$).]

#definition[
  A _subgroup_ $H$ of a group $G$ is a subset of $G$ which is still a group when endowed with the operation from $G$ (so in particular it is closed under the operation). A _(left) coset_ of $H$ in $G$ is a set of the form $
a H = {a h : h in H},
  $ where $a$ some element of $G$. One denotes $G\/H = {"set of cosets of" H}$ Equivalently, there is a natural action of $H$ acting on $G$ as a set (by right-multiplication), given by $h star g := g dot h$; thus cosets of $H$ are just orbits under this action.
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

#definition("Normal subgroup, quotients")[
  Given a group $G$, a subgroup $H subset G$ is said to be _normal_ if it is closed under conjugation by $G$, that is, $
g h g^(-1) in H, quad forall g in G, h in H.
  $
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
// [x] group actions; permutation, symmetric, alternating groups
// [x] subgroups, cosets, lagrange
// [] group homomorphisms, normal, quotient, solvable
// [] dihedral groups
// [] finitely generated abelian groups
// [] sylow's

#pagebreak()
== Rings

// ideals; prime + maximal
// homomorphosms, kernels, quotients
// pids, unique facotrization, euclidean domains
// unipotent & nilpotent elements
// rings of polynomials; factorization of polynomials
// Gauss's lemma, eisenstein's criterion


#pagebreak()
== Fields & Galois Theory

// field extensions, degrees, finite fields
// splitting fields, galois extensions, galois group
// fundamental theory of Galois theory, solvability in radicals



















