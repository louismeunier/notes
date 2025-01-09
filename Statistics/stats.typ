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

#definition("Moments")[
  Let $X$ be a discrete/random random variable with pmf/pdf $f$ and support $S$. Then, if $sum_(x in S) |x| f(x)$/$integral_S |x| f(x) dif x < infinity$, then we say the first moment/mean of $X$ exists, and define $
  mu_X = EE[X] = cases(sum_(x in S) x f(x) \ integral_S x f(x) dif x).
  $

   Let $g : RR -> RR$ be a Borel-measurable function. Then, we have $
   EE[g(X)] = cases(sum_(x in S) g(x) f(x) \ integral_S g(x) f(x)).
   $
   Taking $g(x) = |x|^k$ gives the so-called "$k$th absolute moments", and $g(x) = x^k$ gives the ordinary "$k$th moments". Notice that $EE[dot]$ linear in its argument. 
   
   For $k >= 1$, if $mu$ exists, define the central moments $
   mu_k := EE[(X - mu)^k],
   $ where they exist.
]

#definition("Moment Generating Function (mgf)")[
  If $X$ a r.v., the mgf of $X$ is given by $
  M(t) := EE[e^(t X)],
  $ if it exists for $t in (-h, h)$, $h > 0$. Then, $M^((n)) (0) = EE[X^n]$.
]

#definition("Multiple Random Variable")[
  $X = (X_1, dots, X_n) : Omega -> RR^n$ a random vector if $X^(-1) (I) in cal(F)$ for every $I in frak(B)_(RR^n)$. (It suffices to check for "rectangles" $I = (-infinity, a_1] times dots.c times (-infinity, a_n]$, as before.)

  Let $F$ be the CDF of $X$, and let $A subset.eq {1, dots, n}$, enumerating $A$ by ${i_1, dots, i_k}$. Then, the CDF of the subvector $X_A = (X_i_1, dots, X_i_k)$ is given by $
  F_(X_A) (x_i_1, dots, x_i_k) = lim_(x_(i_j) -> infinity, \ i_j in cal(I) \\ A) F(x_1, dots, x_n).
  $ In particular, the marginal distribution of $X_i$ is given by $
  F_(X_i) (x) = lim_(x_1, dots, x_(i-1), x_(i+1), dots, x_n -> + infinity) F(x_1, dots, x, dots, x_n).
  $ Let $g : RR^n -> RR$ measurable. Then, $
  EE[g(X_1, dots, X_n)] = cases(
    sum_((x_1, dots, x_n)) g(x_1, dots, x_n) f(x_1, dots, x_n) \ 
    integral dots.c integral g(x_1, dots, x_n) f(x_1, dots, x_n) dif x_1 dots.c dif x_n
  ).
  $ We have the notion of a joint mgf, $
  M(t_1, dots, t_n) = EE[e^(sum_(i=1)^n t_i X_i)],
  $ if it exists for $0 < (sum_(i=1)^n t_i^2)^(1/2) < h$ for some $h > 0$. Notice that $M(0, dots, 0, t_i, 0, dots, 0)$ is equal to the mgf of $X_i$.
]