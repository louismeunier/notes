// ! external
// #import "../notes.typ": conf
#import "../typst/shortcuts.typ": *
// ? Change me:

#let conf = (
  course_code: "MATH454",
  course_title: "Analysis 3",
  subtitle: "Summary",
  semester: "Fall 2024",
  professor: "Prof. Linan Chen",
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

= Sigma-Algebras and Measures

#definition([$sigma$-algebra])[A $sigma$-algebra of subsets of a space $X$ is a collection $cal(F)$ of subsets of $X$ satisfying 
- $X in cal(F)$;
- $A in cal(F) => A^c in cal(F)$;
- ${A_n}_(n=1)^infinity subset cal(F) => union.big_(n >= 1) A_n in cal(F)$.
Some $sigma$-algebras can be "generated" by a collection $cal(C)$, in which case we denote $cal(F) = sigma (cal(C))$, being the smallest $sigma$-algebra containing $cal(C)$. In general generators are not unique

A canonical example is the Borel $sigma$-algebra, $
borel = sigma({A subset RR : A "open"}).
$
]

#definition("Measure")[
  A measure $mu : cal(F) -> [0, infinity]$ is a set function defined on a $sigma$-algebra satisfying
  - $mu (nothing) = 0$;
  - for ${A_n} subset.eq cal(F)$ disjoint, $mu(union.big_(n>=1) A_n) = sum_(n>=1) mu(A_n)$.
]

#definition("Lebesgue Outer Measure")[
  For all $A subset.eq RR$, $
  m^ast (A) := inf {sum_(n=1)^infinity ell (I_n) : I_n "open intervals s.t." union.big_(n>=1) I_n supset.eq A}.
  $ A set is then called _Lebesgue measurable_ if for every $B subset.eq RR$, $
  m^ast (B) = m^ast (A sect B) + m^ast (A^c sect B).
  $
]
#theorem[
  Let $cal(M) = {A subset.eq RR : A "Lebesgue measurable"}$. Then, $cal(M)$ a $sigma$-algebra, and $m := m^ast|_(cal(M))$ is a measure on $cal(M)$.
]

#theorem[
  $m$, $cal(M)$ is translation invariant, $m((a, b)) = b - a$, $borel subset.neq cal(M)$, outer regular ($m(A) = inf{m(G): G "open", G supset.eq A}$), and inner regular ($m(A) = sup {m(K) : K "compact", K subset.eq A}$).
]

#theorem[
  $cal(M)$ is complete, and $cal(M) = overline(borel)$.
]

#theorem[
  $m$ is the unique measure on $borel$ that is finite on compact sets and translation invariant, up to rescaling.
]

#theorem[
  A collection of subsets of $X$, $cal(I)$, is called a _$pi$-system_ if $A, B in cal(I) => A sect B in cal(I)$. A collection of subsets of $X$, $cal(D)$, is called a _d-system_ if $X in cal(D), A subset.eq B in cal(D) => B\\A in cal(D)$, and $A_n arrow.t in cal(D) => union.big_n (A_n) in cal(D)$. 

  Let $cal(I)$ be a collection of subsets of $X$ and let $d(cal(I))$ be the smallest $d$-system containing $cal(I)$. Then, $d(cal(I)) = sigma(cal(I))$.
]

#theorem[
  There exists 
  - an uncountable set of measure 0 (the Cantor set);
  - a non-measurable set (the Vitali set);
  - a set that is Lebesgue but not Borel measurable.
]

= Integration Theory

#definition[
  A function $f : RR -> overline(RR)$ is called (Lebesgue) measurable if for every $a in RR$, ${f < a} := f^(-1) ([-infinity, a)) in cal(M)$.

  If $f, g$ measurable, so are $f plus.minus g, f dot g, c dot f, min {f, g}, max{f, g}, f^+, f^-$. If ${f_n}$ a sequence of measurable functions, $limsup_n f_n, liminf_n f_n$, etc are all measurable.
]

#definition("Integral")[
  A simple function is of the form $phi = sum_(k=1)^L a_k bb(1)_{A_k}$ for measurable sets $A_k$, and $L < infinity$.  We define $
  integral_RR phi := sum_(k=1)^L a_k m(A_k).
  $ 
  For any $f >= 0$, we can find a sequence of simple functions that increase to $f$.
  Let $f$ be a nonnegative measurable function. We define $
  integral_RR f := sup{integral_RR phi : phi <= f}.
  $ Finally, for general $f$ measurable, we define $
  integral_RR f := integral_RR f^+ - integral_RR f^-.
  $ We say a function $f$ _integrable_ and write $f in L^1 (RR)$ if $integral_RR |f| < infinity$.
]

#definition("Convergence a.e., in measure")[
  Let ${f_n}$ be a sequence of measurable functions. We say $f_n -> f$ _almost everywhere_ on $RR$ if $f_n (x) -> f(x)$ for almost every $x in RR$. We say $f_n -> f$ _in measure_ if for every $delta > 0$, $m{|f_n - f| > delta} -> 0$.
]

#theorem[
  $f_n -> f$ a.e. $=>$ $f_n -> f$ in measure.

  $f_n -> f$ in measure $=>$ $f_n_k -> f$ a.e. along some subsequence ${n_k}$.
]

#theorem("Egorov's")[
  Let $A in cal(M)$ be a finite measure set such that $f_n -> f$ a.e. on $A$. Then, for every $epsilon > 0$, there is a closed set $A_epsilon subset.eq A$ such that $m(A\\A_epsilon) <= epsilon$ and $f_n -> f$ uniformly on $A_epsilon$.
]

#theorem("Lusin's")[
  Let $A in cal(M)$ be a finite measure set and $f$ measurable. For every $epsilon > 0$, there exists a closed set $A_epsilon subset.eq A$ such that $m(A\\A_epsilon) <= epsilon$ and $f|_(A_epsilon)$ continuous on $A_epsilon$.
]

#theorem("Monotone Convergence")[
  $f_n arrow.t f$, nonnegative, $=>$ $integral_RR f = lim_n integral_RR f_n$.
]

#theorem("Fatou")[
  $integral_RR liminf_n f_n <= liminf_n integral_RR f_n$.
]

#theorem("Dominated Convergence")[
  $f_n -> f$ a.e. and exists $g in L^1 (RR)$ such that $|f_n| <= |g|$, then $integral_RR |f_n - f| -> 0$.
]

#definition($L^p$)[
  Put $||f||_p := (integral_RR |f|^(p))^(1/p)$ and $L^p (RR) = {f "measurable": ||f||_p < infinity}$.

  Put also $||f||_infinity = inf {a in overline(RR) : |f| <= a "a.e."}$, and $L^infinity = {f : ||f||_infinity < infinity}$.
]

#theorem("Holder, Minkowski")[
  $||f g||_1 <= ||f||_p ||g||_q$ where $1/p + 1/q = 1$ and $f, g in L^p, L^q$ resp.

  $||f + g||_p <= ||f||_p + ||g||_p$.
]

#theorem[$L^p$ a complete space with respect to the $L^p$ norm, $||dot||_p$]

#theorem[$C_c (RR)$ dense in $L^p$ for $p < infinity$]

#theorem[
A sequence of functions ${f_n}$ is said to be _uniformly integrable_ on a set $A$ if $
lim_(M -> infinity) sup_n (integral_(A sect {|f_n| > M}) |f_n|) = 0.
$ Suppose $f_n, f in L^1 (A)$ for $m(A) < infinity$. Then, $f_n -> f$ in $L^1$ if and only if ${f_n}$ uniformly integrable and $f_n -> f$ in measure on $A$.
]

= Product Space

#definition[
  Define $cal(M)^2 = sigma({ A times B : A, B in cal(M)})$. For $E in cal(M)^2$, define $E_x = {y in (x, y) in E}$, with a symmetric definition for $E^y$.
]

#theorem[
  $integral_RR m(E_x) dif x = integral_RR m(E^y) dif y$. As such, define the measure of a set $E in cal(M)^2$ by $
  m(E) := integral_RR m(E_x) dif x.
  $
]

#theorem("Tonelli's")[
  Let $f >= 0 : RR^2 -> overline(RR)$ be $cal(M)^2$-measurable. Then, $
  integral_RR^2 f = integral_RR (integral_RR f(x, y) dif x) dif y = integral_RR (integral_RR f(x, y) dif y) dif x.
  $
]

#theorem("Fubini's")[
  Let $f in L^1 (RR^2)$. Then, the above statement also holds.
]

= Differentiation

#theorem("Lebesgue Differentiation Theorem")[
Let $f in L^1 (RR)$. For $x in RR$, let ${I_n}$ be a sequence of open intervals such that $x in I_n$ for every $n >= 1$, and $m(I_n) -> 0$. Then, for almost every $x in RR$, $
lim_(n -> infinity) 1/(m(I_n)) integral_I_n |f(t) - f(x)| dif x = 0.
$
]

// #theorem[Let $f in L^1 (RR)$ and put $F(x) :$]

#theorem[Suppose $F$ nondecreasing on $[a, b]$. Then, $F'$ exists a.e., $F' in L^1 ([a, b])$, and $integral_a^b F' <= F(b) - F(a)$.]

#definition("Bounded Variation")[
  A function $f : [a, b] -> RR$ is of _bounded variation_ if $
  T_F (a, b) := sup {sum_(k=1)^N |f(x_k) - f(x_(k-1))| : a = x_0 < dots.c < x_N = b} < infinity.
  $ We write $F in "BV"([a, b])$. 
]

#theorem[
  $F in "BV"([a, b])$ $<=>$ $F = H - G$ where $H, G$ increasing.
]

#definition("Absolutely Continuous")[
A function $F$ is _absolutely continuous_ on $[a, b]$ if for every $epsilon > 0$, there is a $delta > 0$ such that if ${(a_k, b_k)}_(k=1)^N$ a disjoint sequence of open intervals with $sum_(k=1)^N (b_k - a_k) <= delta$, then $sum_(k=1)^N |F(b_k) - F(a_k)| <= epsilon$. We write $F in "AC"([a, b])$.
]
#theorem("FTC")[$F in "AC"([a, b])$, then $F'$ exists almost everywhere, $F' in L^1 ([a, b])$, and 
$
F(x) - F(a) = integral_a^x F'(t) dif t forall x in [a, b].
$
]