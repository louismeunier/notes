// ! external
// #import "../notes.typ": conf
#import "../typst/shortcuts.typ": *
// ? Change me:

#let conf = (
  course_code: "MATH475",
  course_title: "PDEs",
  subtitle: "Summary",
  semester: "Fall 2024",
  professor: "Prof. Rustum Choksi",
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
#let definition = thmbox("definition", "Definition",base_level:0,inset:(y: 0em, top: 0em, bottom: 0em))
#let remark = thmbox("remark", "Remark",base_level:0, inset:(y: 0em, top: 0em, bottom: 0em))

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
= First-Order Equations
#definition("Method of Characteristics")[A _characteristic_ of a PDE $
cases(F[u] = 0\, bold(x) in RR^N, u(bold(x)) = phi(bold(x))\, bold(x) in Gamma subset RR^(N-1))
$ is a curve upon which a solution to the PDE is constant. With appropriate assumptions on the PDE and its given initial data, one can find the value of a solution $u(bold(x))$ to $F$ anywhere by 
- Given $bold(x)$, find the characteristic curve $gamma$ that passes through $bold(x)$; one should take care to parametrize $gamma$ (for convenience) such that $gamma(0)$ lies on $Gamma$.
- "Trace back" along $gamma$ to where it hits the initial data. We have then that $u(bold(x)) = u(gamma(0))$.
]

#theorem("Linear Equations")[
Given a linear PDE of the form $
cases(a(x, y) u_x + b(x, y) u_y = c_1 (x, y) u + c_2 (x, y), u(x, y) =phi(x, y) "on" Gamma subset RR),
$ the characteristics $gamma(s) = (x, y, z)(s)$ of $u(x, y)$ is given by the solution to the system of ODEs $
cases(dot(x)(s) = a(x(s), y(s)), dot(y)(s) = b(x(s), y(s)), dot(z)(s) = c_1(x(s), y(s)) z(s) + c_2(x(s), y(s)), x(0) := x_0\,y(0) := y_0, z(0) := z_0 = u(x_0, y_0) = phi(x_0, y_0)),
$ where $x_0, y_0$ such that $(x_0, y_0) in Gamma$.
]
#remark[Notice that the $x,y$ and $z$ equations are decoupled. Hence, one can begin by solving for $x(s)$, $y(s)$ then plugging into the ODE for $z(s)$ to finish.]
#remark[One can pick $x_0, y_0$ (with caveats) for convenience, as long as the point $(x_0, y_0)$ lies on $Gamma$, ensuring we can find $u$ here. For simple data like $u(x, 0) = phi(x)$ for $x in RR$, it is easiest to pick $y_0 := 0$, then letting $x_0$ be free; this serves as a "parametrization" of the curves; not in the sense that $s$ is a parameter, rather a parametrization of the family of characteristics, i.e. one should end up with a family ${gamma}_(x_0 in RR)$.]
#remark[In temporal equations, i.e. where $y$ (for instance) equals $t$, we will often have $b(x, t) equiv 1$; in this case, one can often reparametrize with $t$ rather than $s$, since the ODE for $dot(t)(s)$ will just result in $t(s) = s + t_0$, effectively reducing from a system of 3 to 2 equations.]

#remark[This method extends naturally to higher-dimensions equations; a PDE on $RR^N$ will result in $N+1$ ODEs to solve. Note that characteristics are _still_ curves in this case, _not_ $N-1$ dimensional manifolds as one mihgt expect!!]
#theorem("Semiilinear Equations")[Given a semiilinear PDE of the form $
a(x, y) u_x + b(x, y)u_y = c(x, y, u),
$ where $c$ may be nonlinear, we have characteristics given by $
cases(dot(x)(s) = a(dots.c), dot(y)(s) = b(dots.c), dot(z)(s) = c(dots.c)).
$]

#theorem("Quasilinear Equations")[Given a quasilinear equation of the form $
a(x, y, u) u_x + b(x, y, u) u_y = c(x, y, u),
$ characteristics are given as in previous cases, though are ODEs are now all coupled.]

#remark["Unique"/classical solutions may not exist for all initial data in quasilinear equations; in particular, if the initial data $u(x, 0) = g(x)$ is nondecreasing, then our characteristic curves will intersect $g(x)$ precisely once and we are all good; in general, this may not hold.]

#theorem("Fully Nonlinear Equations")[
// TODO
]

= The Wave Equation

#definition[The (general) wave equation in $RR^N$ is given by $
cases(u_(t t) = c^2 Delta u\, bold(x) in RR^N
)
$ where $Delta u = sum_(i=1)^N u_(x_i x_i)$ the _Laplacian_ of $u$ and $c > 0$.]

#theorem("1D")[In $N = 1$, the general solution to the wave equation for $x in RR$ with initial data $u(x, 0) = phi(x), u_x (x, 0) = psi(x)$ is given by _D'Alembert's formula_ $
u(x, t) = 1/2 (phi(x + c t) + phi(x - c t)) + 1/(2 c) integral_(x - c t)^(x + c t) psi(s) dif s.
$]

#remark[We prove/derive this formula by
+ Factor the wave equation $(partial_t - c partial_x)(partial_t + c partial_x) u = 0$
+ Make a change of variables $xi = x + c t, eta = x - c t$ in which we see $u = f(x + c t) + g (x - c t)$ for any sufficiently smooth functions $f, g$
+ Solve for $f, g$ in terms of $phi, psi$
]
#theorem("1D, semi-infinite")[
  In $N=1$, the "semi-infinite equation", namely th wave equation restricted to $x>=0$ with boundary condition $u(0, t) = 0$ for all $t >= 0$, has solution given by $
  u(x, t) &= 1/2 (phi_"odd" (x + c t) + phi_"odd" (x - c t)) + 1/(2 c) integral_(x - c t)^(x + c t) psi_"odd" (s) dif s \
  &= cases(1/2 (phi(x + c t) + phi(x - c t)) + 1/(2 c) integral_(x - c t)^(x + c t) psi(s) dif s "if" x >= c t, 1/2 (phi(x + c t) - phi(c t - x)) + 1/(2 c) integral_(c t - x)^(x + c t) psi(s) dif s "if" 0 <= x <= c t),
  $ where $phi_"odd" (x) := cases(phi (x) "if" x >= 0, - phi(-x) "if" x < 0)$, etc.
]

#remark[Domain of dependence, influence are quite different in the semi-infinite case:
// TODO
]

#theorem("3D Wave Equation")[The solution to the 3D wave equation on all of $RR^3$ is given by $
u(bold(x), t) = 1/(4 pi c^2 t^2) integral.double_(partial B(bold(x), c t)) phi(bold(y)) + nabla phi(bold(y)) dot.c (bold(y) - bold(x)) + t psi(bold(y)) dif S_bold(y).
$]

= Distributions

#definition[
  Let $C^infinity_c (RR)$ denote the space of _test functions_, smooth (infinitely differentiable) functions with compact support. Then, a _distribution_ $F$ is an element of the dual of $C^infinity_c (RR)$, that is, a linear functional acting on smooth functions to return real numbers.

  If $f$ a (sufficiently nice) function, we have a natural way of associating $f$ to a functional $F_f$; for any test function $phi$, we define $
  angle.l F_f, phi angle.r := integral_(-infinity)^infinity f(x) phi(x) dif x.
  $
]

#definition("Derivative")[
  The _derivative_ of a functional $F$ is defined such that for any $phi in C^infinity_c (RR)$, $
  angle.l F', phi angle.r = - angle.l F, phi' angle.r.
  $
]

#definition("Delta Function")[
  $delta_0$ is defined as the distribution such that for any test function $phi$, $
  angle.l delta_0, phi angle.r = phi(0).
  $
]

#definition[
  Let $f_n$ be a sequence of functions and $F$ a distribution. We say $f_n -> F$ _in the sense of distributions_ (itsod) if for every test function $phi$, $
  angle.l f_n, phi angle.r -> angle.l F, phi angle.r
  $ as a sequence of real numbers.
]

#theorem[
  Let $f_n (x) := (n-n^2 |x|) bb(1)_([-1/n, 1/n]) (x)$ for $n >= 1$. Then, $f_n -> delta_0$ itsod.
]

= Fourier Transform

#definition[
  Let $f in L^1 (RR)$. We define for every $k in RR$ $
  hat(f) (k) := integral_(-infinity)^infinity f(x) e^(-i k x) dif x =: cal(F){f} (k),
  $ the _Fourier transform_ of $f$.
]

#theorem("Derivative of a Fourier Transform")[Assume $f in L^1 (RR)$ $n$-times differentiable, then for any positive integer $1 <= ell <= n$, $
hat((dif^((ell)) f)/(dif x^((ell)))) (k) = i^ell k^ell hat(f)(k).
$]

#theorem[Let $f, hat(f) in L^1$ be continuous. Then, for every $x in RR$, $
f(x) = 1/(2 pi) integral_(-infinity)^infinity hat(f) (k) e^(i k x) dif x.
$ More generally, given $g(k)$, we define the _Inverse Fourier Transform_ (IFT) as $
caron(g)(x) = 1/(2 pi) integral_(-infinity)^infinity g(k) e^(i k x) dif k.
$]

#definition("Convolution")[
  Let $f, g$ be integrable, then we define the _convolution_ $
  (f ast g)(x) := integral_(-infinity)^infinity f(x - y) g(y) dif y.
  $
]

#theorem("Properties of Convolution")[
  - $(f ast g)' = (f' ast g) = (f ast g')$ (supposing $f$ or $g$ differentiable).
  - $(hat(f ast g))(k) = hat(f) (k) hat(g) (k)$
]

= Diffusion Equation
#definition[
  For $alpha > 0$, the _diffusion equation_ in 1 space dimension is $
  u_t = alpha u_(x x ), wide u(x, 0) = g(x), wide x in RR, t > 0.
  $ In $RR^N$, we have similarly $
  u_t = alpha Delta u_(x x).
  $
]

#theorem[
The following solves the heat equation, under assumptions of integrability: $
u(x, t) = 1/(sqrt(4 pi alpha t)) integral_(-infinity)^infinity e^(-(x - y)^2 /(4 alpha t)) g(y) dif y.
$ In particular, $
lim_(t -> 0^+) u(x, t) = g(x)
$ for every $x in RR$.
]