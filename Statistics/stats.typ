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
// % ! 01-09
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

#definition("Conditional Probability")[
  Let $(X_1, dots, X_n)$ a random vector. Let $cal(I) = {1, dots, n}$ and $A, B$ disjoint subsets of $cal(I)$ with $k := |A|, h := |B|$. Write $X_A = (X_i_1, dots, X_i_k)^t$, similar for $B$. Then, the conditional probability of $A$ given $B$ is given by $
  f_(X_A|X_B)(x_a|x_b) := f_(X_A | X_B = x_B) (x_A) =( f_(X_A, X_B) (x_a, x_b))/(f_X_b (x_b)),
  $ provided the denominator is nonzero. Sometimes we have information about conditional probabilities but not the main probability function; we have that $
  f(x_1, dots, x_n) = f(x_1) f(x_2 | x_1) f(x_3|x_1 ,x_2) dots.c f(x_n |x_1, dots, x_(n-1)),
  $ which follows from expanding the previous definition and observing the cancellation.

  Let $X = (X_1, dots, X_n) tilde F$. We say $X_1, dots, X_n$ (mutually) independent and write $product.co_(i=1)^n X_i $ if 
  $
  F(x_1, dots, x_n) = product_(i=1)^n F_(X_i) (x_i),
  $ where $F_X_i$ the marginal cdf of $X_i$. Equivalently, $
  product.co_(i=1)^n X_i  &<=> f(x_1, dots, x_n) = product_(i=1)^n f_(X_i) (x_i) \ 
  & <=> P(X_1 in B_1, dots, X_n in B_n) = product_(i=1)^n P(X_i in B_i) forall B_i in borel \
  & <=> M_(X) (t_1, dots, t_n) = product_(i=1)^n M_(X_i) (t_i).
  $ If $X, Y$ are two random variables with cdfs $F_X, F_Y$ such that $F_X (z) = F_Y (z)$ for every $z$, we say $X, Y$ identically distributed and write $X =^d Y$ (note that $X$ need not equal $Y$ pointwise). If $X_1, dots, X_n$ a collection of random variables that are independent and identically distributed with common cdf $F$, we write $X_1, dots, X_n tilde^("iid") F$.

  Further, define the covariance, correlation of two random variables $X, Y$ respectively: $
  "Cov"(X, Y) := sigma_(X, Y) := EE[(X - EE[X])(Y - EE[Y])] = EE[X Y] - mu_X mu_Y, wide rho_(X, Y) := (sigma_(X Y))/(sigma_X sigma_Y),
  $ _if_ $EE[ |X - EE[X]| |Y - EE[Y]| ] < infinity$.
]

#theorem[If $X_1, dots, X_n$ independent and $g_1, dots, g_n : RR-> RR$ borel-measurable functions, then $g_1 (X_1), dots, g_n (X_n)$ also independent.]


#definition("Conditional Expectation")[
  Let $X, Y$ be random variables and $g : RR -> RR$ a borel-measurable function. We define the following notions: $
  EE[g(X)|Y = y] = cases(sum_(x in S_X) g(x) f(x|y) "discrete", integral_S_x g(x) f(x|y) dif x "cnts").\
  "Var"(X|Y = y)  = EE[X^2|Y=y] - EE^2 [X|Y = y].
  $
]
#theorem[If $EE[g(X)]$ exists, then $EE[g(X)] = EE[EE[g(X)|Y]]$, where the first nested $EE$ is with respect to $x$, the second $y$.]

#theorem[If $EE[X^2] < infinity$, then $"Var"(X) = "Var"(EE[X|Y]) + EE["Var"(X|Y)]$. In particular, $"Var"(X) >= "Var"(EE[X|Y])$.]

= Statistics
#definition("Inference")[
  We consider some population with some characteristic we wish to study. We can model this characteristic as a random variable $X tilde F$. In general, we don't have access to $F$, but wish to take samples from our population to make inferences about its properties. 

  (1) _Parametric inference:_ in this setting, we assume we know the functional form of $X$ up to some parameter, $theta in Theta subset RR^d$, where $Theta$ our "parameter space". Namely, we know $X tilde F_theta in cal(F) := {F_theta | theta in Theta}$.

  (2) _Non-parametric inference:_ in this setting we know noting about $F$ itself, except perhaps that $F$ continuous, discrete, etc.

Other types exist. We'll focus on these two.
]

#definition("Random Sample")[Let $X_1, dots, X_n tilde^("iid") F$. Then $X_1, dots, X_n$ called a _random sample_ of the population.

We also call $X_i$ the "pre-experimental data" (to be observed) and $x_i$ the "post-experimental data" (been observed).
]

#definition("Statistics")[
  Let $X_1, dots, X_n tilde^"iid" F$ where $X_i$ a $d$-dimensional random vector. Let $
  T : underbrace(RR^d times RR^d times dots.c times RR^d, n-"fold") -> RR^k
  $ be a borel-measurable function. Then, $T(X_1, dots, X_n)$  is called a _statistic_, provided it does not depend on any unknown.
]

#example[
  $overline(X_n) := 1/n sum_(i=1)^n X_i$ (the "sample mean") and $S_n^2 = 1/(n - 1) sum_(i=1)^n (X_i - overline(X_n))^2$, (the "sample variance") are both typical statistics.
]

#theorem[
  Let $x_1, dots, x_n in RR$, then 

  (a) $"argmin"_(alpha in RR) {sum_(i=1)^n (x_i - alpha)^2} = overline(x_n)$;

  (b) $sum_(i=1)^n (x_i - overline(x_n))^2 = sum_(i=1)^n (x_i^2) - n overline(x_n)^2$;

  (c) $sum_(i=1)^n (x_i - overline(x_n)) = 0$.
]

#theorem[
  Let $X_1, dots, X_n tilde^"iid" F$, and $g : RR-> RR$ borel-measurable such that $"Var" (g(X)) < infinity$. Then, 

  (a) $EE[sum_(i=1)^n g(X_i)] = n EE[g(X_1)]$;

  (b) $"Var" (sum_(i=1)^n g(X_i)) = n "Var"(X_1)$.
]

#theorem[
  Let $X_1, dots, X_n tilde^"iid" F$ with $sigma^2 < infinity$, then 

  1. $EE[overline(X_n)] = mu$, $"Var"(overline(X_n)) = (sigma^2)/n$, $EE[S_n^2] = sigma^2$.
  2. If $M_X_1 (t)$ exists in some neighborhood of $0$, then $M_(overline(X_n)) (t) = M_(X_1) (t/n)^n$, where it exists. 
]