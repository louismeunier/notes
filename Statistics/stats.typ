// ! external
#import "../typst/notes.typ": *
#import "../typst/shortcuts.typ": *

// ! configuration
#show: doc => conf(
  course_code: "MATH357",
  course_title: "Statistics",
  subtitle: "",
  semester: "Winter 2025",
  professor: "Prof. Abbas Khalili",
  doc
)
#set align(left)

#pagebreak()

= Review of Probability
#definition("Measurable Space, Probability Space")[
We work with a set $Omega = $ sample space $ = {"outcomes"}$, and a $sigma$-algebra $cal(F)$, which is a collection of subsets of $Omega$ containing $Omega$ and closed under taking complements and countable unions. The tuple $(Omega, cal(F))$ is called _measurable space_.

We call a nonnegative function $P : cal(F) -> RR$ defined on a measurable space a _probability function_ if $P(Omega) = 1$ and if ${E_n} subset.eq cal(F)$ a disjoint collection of subsets of $Omega$, then $P(union.big_(n>=1) E_n) = sum_(n>=1) P(E_n)$. We call the tuple $(Omega, cal(F), P)$ a _probability space_.
]

#definition("Random Variables")[
Fix a probability space $(Omega, cal(F), P)$. A Borel-measurable function $X : Omega -> RR$ (namely, $X^(-1) (B) in cal(F)$ for every $B in frak(B)(RR)$) is called a _random variable_ on $cal(F)$.
- _Probability distribution_: $X$ induces a probability distribution on $frak(B)(RR)$ given by $P(X in B)$
- _Cumulative distribution function (CDF)_: $
F_X (x) := P(X <= x).
$ Note that $F(-infinity) = 0, F(+infinity) = 1$ and $F$ right-continuous.

We say $X$ _discrete_ if there exists a countable set $S := {x_1, x_2, dots} subset RR$, called the _support_ of $X$, such that $P(X in S) = 1$. Putting $p_i := P(X = x_i)$, then ${p_i : i >= 1}$ is called the _probability mass function_ (PMF) of $X$, and the CDF of $X$ is given by $
P(X <= x) = sum_(i : x_i <= x) p_i.
$

We say $X$ _continuous_ if there is a nonnegative function $f$, called the _probability distribution function_ (PDF) of $X$ such that $F(x) = integral_(-infinity)^x f(t) dif t$ for every $x in RR$. Then, 
- $forall B in frak(B)(RR), P(X in B) = integral_B f(t) dif t$
- $F'(x) = f(x)$
- $integral_(-infinity)^infinity f(x) dif x = 1$

If $X : Omega -> RR$ a random variable and $g : RR -> RR$ a Borel-measurable function, then $Y := g(X) : Omega -> RR$ also a random variable.
]