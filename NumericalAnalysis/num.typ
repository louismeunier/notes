// ! external
#import "../typst/notes.typ": *
// #import "../typst/shortcuts.typ": *

#import "@preview/cetz:0.2.2"

// ! configuration
#show: doc => conf(
  course_code: "MATH578",
  course_title: "Numerical Analysis 1",
  // subtitle: "Abstract Metric, Topological Spaces; Functional Analysis.",
  semester: "Fall 2025",
  professor: "Prof. J.C. Nave",
  // cute: "../analysis 3/page.png",
  doc,
)

#import "@preview/commute:0.2.0": arr, commutative-diagram, node

#set align(left)

#pagebreak()

= Polynomial Interpolation

In general, the goal of interpolation is, given a function $f(x)$ on $[a, b]$ and a series of distinct ordered points (often called _nodes_ or _collocation points_) ${x_j}_(j=1)^(n) subset.eq [a, b]$, to find a polynomial $P(x)$ such that $f(x_j) = P(x_j)$ for each $j$.

#theorem("Existence and Uniqueness of Lagrange Polynomial")[
  Let $f in C[a, b]$ and ${x_j}$ a set of $n$ distinct points. Then, there exists a unique $P(x) in PP_(n-1)$, the space of $n-1$-degree polynomials, such that $P(x_j) = f(x_j)$ for each $j$.

  We call such a $P$ the _Lagrange polynomial_ associated to the points ${x_j}$ for $f$.
]

#proof[
  We define the following $n-1$ degree "fundamental polynomials" associated to ${x_j}$, $ ell_j (x) equiv product_(1 <= i <= n \ i eq.not j) (x - x_i)/(x_j - x_i), wide j = 1, dots, n. $ Then, one readily verifes $ell_j (x_i) = delta_(i j)$, and that the distinctness of the nodes guarantees the denominator in each term of the product is nonzero. Define $ P(x) = sum_(j = 1)^n f(x_j) ell(x), $ which, being a linear combination of $n-1$ degree polynomials is also in $PP_(n-1)$. Moreover, $ P(x_i) = sum f(x_j) delta_(i, j) = f(x_i), $ as desired.

  For uniqueness, suppose $overline(P)$ another $n-1$ degree polynomial satisfying the conditions of the theorem. Then, $q(x) equiv P(x) - overline(P)(x)$ is also a degree $n-1$ polynomial with $q(x_i) = 0$ for each $i = 1, dots n$. Hence, $q$ a polynomial with more distinct roots than its degree, and thus it must be identically zero, hence $P = overline(P)$, proving uniqueness.
]

#theorem("Interpolation Error")[
  Suppose $f in C^n [a, b]$, and let $P(x)$ be the Lagrange polynomial for a set of $n$ points ${x_j}$, with $x_1 = a, x_n = b$. Then, for each $x in [a, b]$, there is a $xi in [a, b]$ such that $ f(x) - P(x) = (f^((n)) (xi))/n! (x - x_1) dots.c (x - x_n). $ Moreover, if we put $h := max_i (x_(i+1) - x_i)$, then $ norm(f - P)_infinity <= (h^n)/(4n) norm(f^((n)))_infinity. $
]

#proof[
  We prove the first identity, and leave the second "Moreover" as a homework problem. Notice that it holds trivially for $x = x_j$ for any $j$, so assume $x eq.not x_j$ for any $j$, and define the function $ g(t) := f(t) - P(t) - omega(t) (f(x) - P(x))/(omega(x)), wide omega(t) := (t - x_1) dots (t - x_n) in PP_n [t]. $ Then, we observe the following:
  - $g in C^n [a, b]$
  - $g(x) = 0$
  - $g(t = x_j) = 0$ for each $j$
  Recall that by Rolle's Theorem, if a $C^1$ function has $>= m$ roots, then its derivative has $>= m - 1$ roots. Thus, applying this principle inductively to $g(t)$, we conclude that $g^((n)) (t)$ has at least one root. Take $xi$ to be such a root. Then, one readily verifies that $P^((n)) equiv 0$ and $omega^((n)) equiv n!$ (using polynomial properties), from which we may use the fact that $g^((n)) (xi) = 0$ to simplify to the required identity.
]

#remark[
  In general, larger $n$ leads to smaller maximum step size $h$. However, it is _not_ true that $n->infinity$ implies $P -> f$ in $L^infinity$. From the previous theorem, one would need to guarantee $norm(f^((n)))-> 0$ (or at least, doesn't grow faster than $(h^n)/(4n)$), which certainly won't hold in general; we have no control on the $n$th-derivative of an arbitrarily given function. However, we can try to optimize our choice of points ${x_j}$ for a given $j$.
]


We switch notation for convention's sake to $n + 1$ points $x_j$. Our goal is the optimization problem $ min_(x_j) max_(x in [a, b]) abs(product_(j) (x - x_j)), $ the only term in the error bound above that we have control over. Remark that we can expand the product term: $ product_(j) (x - x_j) = x^n - r(x), $ where $r(x) in PP_(n)$. So, really, we equivalently want to solve the problem $ min_(r in PP_(n)) norm(x^(n + 1) - r(x))_infinity, $ namely, what $n$-degree polynomial minimizes the max difference between $x^(n + 1)$?


#theorem("De la Vallé-Poussin Oscillation Theorem")[
  Let $f in C([a, b])$, and suppose $r in PP_n$ for which there exists $n + 2$ distinct points ${x_j}$ such that $a <= x_0 < dots.c < x_(n + 1) <= b$ at which the error $f(x) - r(x)$ "oscillate" sign, i.e. $ "sign"(f(x_j) - r(x_j)) = - "sign"(f(x_(j + 1)) - r(x_(j + 1))). $ Then, $ min_(P in PP_n) norm(f - P)_(infinity) >= min_(0 <= j <= n + 1) |f(x_j) - r(x_j)|. $

]




