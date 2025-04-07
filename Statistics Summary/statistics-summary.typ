// ! external
// #import "../notes.typ": conf
#import "../typst/shortcuts.typ": *
// ? Change me:

#let conf = (
  course_code: "MATH357",
  course_title: "Statistics",
  subtitle: "Summary",
  semester: "Winter 2025",
  professor: "Prof. Abbas Khalili",
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

= Probability Prerequisites

#definition[$overline(X)_n := 1/n sum_(i=1)^n X_i$ and $S_n^2 := 1/(n-1) sum_(i=1)^n (X_i - overline(X)_n)^2$]

#theorem("Properties of Normal Distributions")[
  Let $X_1, dots, X_n tilde^"iid" cal(N)(mu, sigma^2)$, then
  1. $overline(X)_n tilde cal(N)(mu, sigma^2/n)$;
  2. $overline(X)_n$ and $S_n^2$ are independent;
  3. $((n-1) S_n^2)/sigma^2 tilde chi_((n-1))^2$;
  4. If $Z tilde cal(N)(0, 1)$ and $V tilde chi_((nu))^2$, $Z/(sqrt(V\/nu)) tilde t(nu)$. In particular, $
  (overline(X)_n - mu)/sqrt(S_n^2\/n) = (sqrt(n) (overline(X)_n - mu))/(S_n) tilde t(n - 1).
  $
  5. If $U tilde chi_((m))^2, V tilde chi_((n))^2$ are independent rv's, then $(U\/m)/(V\/n) tilde F(m, n)$.
]

#theorem("Order Statistics")[
  If $X_1, dots, X_n$ iid rv's with CDF $F$, the CDF's of the min, max order statistics are respectively $
  F_(X_((1))) (x) = 1 - [1 - F(x)]^n, wide F_(X_((n))) (x) = [F(x)]^n,
  $ and generally, for $1 <= j <= n$, $
  F_(X_((j))) (x) = sum_(k=j)^n binom(n, k) F^k (x) [1 - F(x)]^(n-k).
  $
]

#theorem("Convergence Theorems")[
1. (Slutsky's) If $X_n ->^"d" X$ and $Y_n ->^"P" a$, then $X_n + Y_n ->^"d" X + a$, $X_n Y_n ->^"d" a X$ and, if $a eq.not 0$, $X_n\/Y_n ->^"d" X\/a$.
2. (Continuous Mapping Theorem) If $X_n ->^"P, d" X$ and $g$ continuous on a set $C$ where $P(X in C) = 1$, then $g(X_n) ->^"P,d" g(X)$. 
3. (WLLN) If $X_i$ iid rv's with mean $mu$ and finite second moment, $overline(X)_n ->^"P" mu$.
4. (First-Order Delta Method) If $sqrt(n) (X_n - mu) ->^"d" V$ and $g$ a function such that $g'$ exist and is nonzero at $x= mu$, then $
sqrt(n) (g(X_n) - g(mu)) ->^"d" g'(mu) dot V.
$
5. (Second-Order Delta Method) If $sqrt(n) (X_n - mu) ->^"d" cal(N)(0, sigma^2)$, and $g$ a function with $g'(mu) = 0$ but $g''(mu) eq.not 0$, then $
sqrt(n) (g(X_n) - g(mu)) ->^"d" cal(N)(0, g'(mu)^2 sigma^2).
$
]

#theorem("Empirical CDF Properties")[
  Let $X_1, dots, X_n$ be iid with cdf $F$. The ECDF is the rv defined by, for $x in RR$, $F_n (x) := 1/n sum_(i=1)^n bb(1)(X_i <= x)$. The following hold:
  1. $n F_n (x) tilde "Bin"(n, F(x))$; in particular, 
  $
  EE[F_n (x)] = F(x), wide "Var"(F_n (x)) = 1/n F(x) (1 - F(x))
  $
  2. $(sqrt(n) (F_n (x) - F(x)))/(sqrt(F(x) (1 - F(x)))) ->^"d" cal(N)(0, 1)$
  3. $F_n (x) ->^"P" F(x)$
]


= Parametric Inference

#definition("Qualities of Estimators")[
1. The _bias_ of an estimator $hat(theta)$ of $theta$ is defined $"Bias"(hat(theta)) = EE_theta [hat(theta)] - theta$. $hat(theta)$ is _unbiased_ if it has zero bias.
2. The _mean-squared error_ (MSE) is defined $"MSE"(hat(theta)) = EE[(hat(theta) - theta)^2]$.
3. We say $hat(theta)$ _unbiased_ if $hat(theta) ->^"P" theta$
]

#theorem("Cramer-Rau Lower Bound")[
For a parametric family ${p(dot, theta) : theta in Theta}$, if $T(bold(X))$ an unbiased estimator of a function of a parameter $tau(theta)$, with finite variance, then $
"Var"(T(bold(X))) >= ([tau'(theta)]^2)/I(theta),
$ for every $theta in Theta$ in the, where $I(theta) := EE[(dif/(dif theta) log p_theta (bold(X)))^2]$ the _Fisher information_ of the parametric family and assuming the denominator is finite, and moreover:
1. ${p_theta : theta in Theta}$ has common support independent of $theta$
2. for any $bold(x)$ and $theta in Theta$, $dif/(dif theta) log p_theta (bold(x)) < infinity$
3. for any statistic $h(bold(X))$ with finite first absolute moment, differentiation under the integral holds ie $dif/(dif theta) integral h(bold(x)) p(bold(x)) dif bold(x) =integral h(bold(x)) dif/(dif theta) p_theta (bold(x)) dif bold(x)$

Moreover, equality occurs iff there exists a function $a(theta)$ such that $a(theta) {T(bold(x)) - tau(theta)} = dif/(dif theta) log p(bold(x); theta)$.
]

#remark[
If $p_theta$ twice differentiable in $theta$ and $EE [dif/(dif theta) log p_theta (bold(X))]$ differentiable "under the integral sign", then $I(theta) = - EE[dif^2/(dif theta^2) p_theta (bold(X))]$.

If working with iid rv's, then the denominator becomes $n I_1 (theta)$ where $I_1 (theta)$ the Fisher information of a single rv.
]

#theorem("Neyman-Fisher Factorization")[
A statistic $T(bold(X))$, $bold(X) tilde p_theta (dot)$ is called _sufficient_ for $theta$ if the conditional distribution of $bold(X)$ given $T(bold(X)) = t$ is independent of $theta$. $T(bold(X))$ is sufficient iff there are functions $h(dot), g(dot; theta)$ such that $p_theta (bold(x)) = h(bold(x)) g(T(bold(x)), theta)$.
]
#theorem("Minimal Sufficiency")[
  A sufficient statistic is minimal if it is a function of every other sufficient statistic. For a parametric $p_theta (dot)$, suppose $T(bold(x)) = T(bold(y)) <=> (p_theta (bold(x)))/(p_theta (bold(y)))$ does not depend on $theta$. Then, $T(bold(X))$ is minimally sufficient.
]

#definition("Completeness")[An estimator $hat(theta)$ is called _complete_ if $EE[g(hat(theta))] = 0$ for every $theta$ implies $g = 0$ (a.s.).]

#theorem("Rao-Blackwell")[
  Let $U(bold(X))$ be unbiased for $tau(theta)$ and $T(bold(X))$ sufficient, and define $delta(t) := EE_theta [U(bold(X)) | T(bold(X))] = t$. Then $delta(bold(X))$ is unbiased for $tau(theta)$, and has smaller variance then $U(bold(X))$.
]

#theorem("Lehmann-Scheffé")[
  Let $T(bold(X))$ be complete and sufficient and $U(bold(X)) = h(T(bold(X)))$ unbiased with finite second moment, then $U(bold(X))$ is the UMVUE for $tau(theta)$.
]

#remark[Combine these two theorems to systematically construct UMVUEs starting from an (arbitrary) unbiased estimator and a complete and sufficient statistic.]


= Systematic Parameter Estimation

#definition("Method of Moments")[
  The _method of moments_ estimator(s) for rv's $X_1, dots, X_n tilde^"iid" f_theta$ is given by solving the system $
  1/n sum_(i=1)^n X_i^j = mu_j (theta) := EE[X_i^j],
  $ for $j$ as high as we need for the system of equations to have solutions.
]

#definition("Minimum Likelihood Estimation (MLE)")[
  An estimator $hat(theta)_n$ is said to be an MLE of a parametric family if it maximizes the likelihood (resp. log likelihood) function (for any post-experimental data $bold(x)$) $
  #stack(
    spacing: 1em,
    $L_n: Theta -> [0, infinity)$, $L_n (theta) = p_theta (bold(x))$)
  , wide (thin #stack(
    spacing: 1em,
    $ell_n: Theta -> (-infinity, infinity)$, $ell_n (theta) = log L_n (theta)$) thin
  ).
  $ If differentiable, one can solve for the (at least a candidate) MLE by solving the likelihood equations $partial_theta L_n = 0$ or equivalently $partial_theta ell_n = 0$.
]

#remark[
  Since $log$ monotonic increasing, the likelihood/log-likelihood functions are equivalent and thus one should use which ever one is more convenient (lots of parametric families have exponentials, so using log is helpful).
]

#theorem("Properties of MLEs")[
  We assume #link("https://notes.louismeunier.net/Statistics/stats.pdf#page=44","\"the regularity conditions\"").
  1. (Invariance) If $hat(theta)$ the MLE of $theta$ and $tau(theta)$ a function of $theta$, then $tau(hat(theta))$ the MLE of $tau(theta)$.
  2. $hat(theta)$ is consistent.
  3. $sqrt(n) (hat(theta) - theta_0) ->^"d" cal(N)(0, [I_1^(-1) (theta_0)])$ where $theta_0$ the "true value".
  4. (1st Bartlett Identity) $EE_theta [(partial log f(X))/(partial theta)] = 0$.
]

#definition("Bayesian Estimation")[
  Let $bold(X) tilde p_theta$ where $theta$ also random, with pdf/pmf $pi(theta)$, called the _prior distribution_ of $theta$. The _posterior distribution_  is defined as $pi(theta|bold(x))$, which by Baye's is proportional to $p_theta (bold(x)) pi(theta)$. A _loss function_ $L(delta(bold(X)), theta)$ is a function assigning a "penalty" to an estimator $delta(bold(X))$, for instance the $L^2$-loss given by $(delta(bold(X)) - theta)^2$. _Baye's risk_ given a loss function $L$ is defined $
  R(delta) := EE_pi [EE_(bold(X)|theta) [L(delta(bold(X)), theta)]].
  $ Then, _Baye's estimator_ is simply $hat(delta)(bold(X)) := "argmin"_(delta) R(delta)$.
]

#theorem[
  For $L$ the $L^2$-loss function, the Baye's estimator is $
  hat(delta)(bold(X)) = EE_(theta|bold(X) = x) [theta|bold(X)].
  $
]

#remark[So, given $p_theta$ and $pi(theta)$, the typical steps to finding $hat(delta)(bold(X))$ are: 
1. compute $p_theta (bold(x)) pi(theta)$, and deduce the distribution of $(theta|bold(X))$;
2. hopefully the distribution found in (i) has a well-known mean, which is then equal to the Baye's estimator $hat(delta)(bold(X))$ by the previous theorem.
]







= Confidence Intervals and Hypothesis Testing

= Some MLEs and Such To Remember