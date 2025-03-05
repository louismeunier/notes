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


// TODO
#let Var = "Var"
#let Cov = "Cov"

#let Bias = "Bias"
#let mse = "MSE"
#let MSE = "MSE"

#let dby(x, n) = $dif^(#n)/(dif #x^#n)$
// TODO

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

= Common Statistical Tools

== Definition of Statistics
// == Sample Distributions
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

== Properties of Normal and other Common Distributions

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

#theorem[
  Let $X_1, dots, X_n tilde^("iid") cal(N)(mu, sigma^2)$. Then

  1. $overline(X_n) tilde cal(N)(mu, sigma^2 /n)$;
  2. $overline(X_n), S_n^2$ are independent;
  3. $((n-1) S_n^2)/(sigma^2) = (sum_(i=1)^n (X_i - overline(X_n))^2)/(sigma^2) tilde chi_((n-1))^2$.
]

#remark[
  2. actually holds iff the underlying distribution is normal.
]

#proof[
  We prove 2. We first write $S_n^2$ as a function of $(X_2 - overline(X)_n, dots, X_n - overline(X)_n)$: $
  S_n^2 = 1/(n - 1) sum_(i=1)^n (X_i - overline(X)_n)^2 &= 1/(n - 1) {sum_(i=2)^n (X_i - overline(X)_n)^2 + (X_1 - overline(X)_n)^2} \ 
  &= 1/(n - 1) {sum_(i=2)^n (X_i - overline(X)_n)^2 + (sum_(i=2)^n (X_i - overline(X)_n))^2}.
  $ Then, it suffices to show that $overline(X)_n$ and $(X_2 - overline(X)_n, dots, X_n - overline(X)_n)$ are independent.

  Consider now the transformation $
  cases(
    y_1 &= overline(x)_n, 
    y_2 &= x_2 - overline(x)_n, 
    &dots.down,
    y_n &= x_n - overline(x)_n
  ) => cases(
    x_1 &= y_1 - sum_(i=2)^n y_i ,
    x_2 &= y_2 + y_1 ,
    & dots.down ,
    x_n &= y_n + y_1
  ),
  $ which gives Jacobian $
  |J| = abs(mat(
    1, -1, dots.c, -1;
    1, 1, 0, dots.c;
    dots.v, dots.down, dots.down, dots.v;
    1,0, dots.c, 1
  )) = n,
  $ and so $
  f_(Y_1, dots, Y_n) (y_1, dots, y_n) &= |J| dot f_(X_1, dots, X_n) (x_1 (y_1, dots, y_n), dots, x_n (y_1, dots, y_n)) \ 
    &= n dot product_(i=1)^n 1/(sqrt(2 pi sigma^2)) e^(-1/(2 sigma^2) (x_i (y_1, dots, y_n) - mu)^2) \ 
    &approx underbrace(e^(- n ((y_1 - mu)^2)/(2 sigma^2)), "only" y_1) dot underbrace(e^( - 1/(2 sigma^2) {(sum_(i=2)^n y_i)^2 + sum_(i=2)^n y_i^2}), "no" y_1 "dependence"),
  $ and hence as the PDFs split, we conclude $Y_1$ independent of $Y_2, dots, Y_n$ and so $overline(X)_n$ independent of $(X_2 - overline(X)_n, dots, X_n - overline(X)_n)$ and so in particular of any Borel-measurable function of this vector such as $S_n^2$, completing the proof.

  For 3, note that $
  V := sum_(i=1)^n ((X_i - mu)/sigma)^2 &= 1/(sigma^2) sum_(i=1)^n ((X_i - overline(X)_n) - (mu - overline(X)_n))^2 \ 
  &=  (sum_(i=1)^n (X_i - overline(X)_n)^2)/(sigma^2) + (n (overline(X)_n - mu)^2)/sigma^2 =: W_1 + W_2.
  $ The first part, $W_1$, of this summation is just $(n - 1)(S_n^2)/(sigma^2)$, a function of $S_n^2$, and the second, $W_2$, is a function of $overline(X)_n$. By what we've just shown in the previous part, these two are independent. In addition, $V tilde chi_((n))^2$ and $
  W_2 = (n (overline(X)_n - mu)^2)/sigma^2 = ((overline(X)_n - mu)/(sigma/(sqrt(n))))^2 tilde chi_((1))^2,
  $ since the inner random variable is a standard normal. Then, since $W_1, W_2$ independent, $M_V (t) = M_W_1 (t) M_W_2 (t)$, so for $t < 1/2$, $
  M_(W_1)(t) = (M_V (t))/(M_W_2 (t)) = ((1-2 t)^(- n/2))/((1 - 2 t)^(-1/2))= (1 - 2 t)^(- ((n - 1))/2),
  $ hence $W_1 tilde chi_((n - 1))^2$.
]

#proposition[
  Let $X tilde t(nu)$, the Student $t$-distribution i.e $
  f(x) = Gamma((nu+1)/2)/(sqrt(pi nu) dot Gamma(nu/2)) (1 + x^2 /nu)^(- (nu+1)/2),
  $ then 
  - $"Var"(X) = nu/(nu - 2)$ for $nu > 2$
  - If $Z tilde cal(N)(0, 1)$ and $V tilde chi^2_((nu))$ are independent random variables, then $T = Z/(sqrt(V \/nu)) tilde t(nu)$.
]

#theorem[
  Let $X_1, dots, X_n tilde^("iid") cal(N)(mu, sigma^2)$. Then, $
  T = (overline(X)_n - mu)/(sqrt(S_n^2 \/n)) = (sqrt(n) (overline(X)_n - mu))/(S_n) tilde t(n - 1).
  $
]

#remark[
  By combing CLT and Slutsky's Theorem, $T$ asymptotes to $cal(N)(0, 1)$, but this gives a general distribution. Note that for large $n$, $t(n - 1)$ approximately normal too.
]

#proof[
  Notice that $
  W_1 := sqrt(n) (overline(X)_n - mu)/(sigma) tilde cal(N)(0, 1), wide W_2 := ((n - 1) S_n^2)/(sigma^2) tilde chi_((n-1))^2
  $ are independent, and $
  T = W_1/(sqrt(W_2 \/ (n- 1)))
  $ so by the previous proposition $T tilde t(n - 1)$.
]

#proposition[
  Given $U tilde chi_((m))^2, V tilde chi_((n))^2$ independent, then $F = (U\/m)/(V\/n) tilde F(m, n)$. If $T tilde t(nu)$, $T^2 tilde F(1, nu)$.
]

#theorem[
  Let $X_1, dots, X_m tilde^"iid" cal(N)(mu_1, sigma_1^2)$ and $Y_1, dots, Y_n tilde^"iid" cal(N)(mu_2, sigma_2^2)$ be mutually independent random samples. Then, $
  F = (S_m^2 \/ sigma_1^2)/(S_n^2 \/ sigma_2^2) tilde F(m - 1, n - 1).
  $
]

#proof[
  We have that $U = ((m - 1) S_m^2)/(sigma_1^2) tilde chi_((m - 1))^2$ and $V = ((n - 1) S_n^2)/(sigma_2^2)$ are independent so by the previous proposition $
  F = (U \/ (m - 1))/(V \/ (n - 1)) tilde F(m - 1, n - 1).
  $
]

== Order Statistics

#definition[
Let $X_1, dots, X_n tilde^"iid" F$. Then, the _order statistics_ are $
X_((1)) <= X_((2)) <= dots.c <= X_((n)),
$ where $X_((i))$ the $i$th largest of $X_1, dots, X_n$.
]

#definition("Related Functions of Order Statistcs")[
 The _sample range_ is defined $
R_n := X_((n)) - X_((1)).
$ The _sample median_ is defined $
M(X_1, dots, X_n) := cases(
X_(((n+1)/2)) & "if" n "odd",
(X_(((n)/2)) + X_(((n+1)/2)))/2 & "if" n "even".
)
$
]

#theorem("Distribution of Max, Min")[
Let $X_1, dots, X_n tilde^"iid" F, f$.

_(Discrete)_ 

(a) $
P(X_((1)) = x) =  [1 - F(x^-)]^n - [1 - F(x)]^n$

(b) $P(X_((n)) = y) = [F(y)]^n - [F(y^-)]^n$

_(Continuous)_

(c) $F_(X_((1))) (x)  = P(X_((1)) <= x) = 1 - [1 - F(x)]^n$, $wide$ $f_(X_((1))) (x) = n dot f (x) [1 - F(x)]^(n-1)$

(d) $F_(X_((n))) (y) = [F(y)]^n, wide f_(X_((n))) (y) = n dot f (y) [F(y)]^(n-1)$
]

#proof[
  (a) Notice $
P(X_((1)) = x) &= P(X_((1)) <= x) - P(X_((1)) < x).
$ We have $
P(X_((1)) <= x) &= 1 - P(X_((1)) > x) \ 
&= 1 - P(X_1 > x, X_2 > x, dots, X_n > x) \ 
&= 1 - P(X_1 > x) P(x_2 > x) dots.c P(X_n > x) \ 
&= 1 - [1 - F(x)]^n,
$ and similarly $
P(X_((1)) < x) = 1 - P(X_((1)) >= x) = 1 - [1 - F(x^-)]^n,
$ where $F(x^-) = lim_(z -> x^-) F(z)$. So in all, $
P(X_((1)) = x) =  [1 - F(x^-)]^n - [1 - F(x)]^n.
$ (b) is very similar. For (c), we have $
P(X_((1)) <= x) &= 1 - P(X_((1)) > x) \ 
&= 1 - P(X_1 > x, dots, X_n > x) \ 
&= 1 - [1 - F(x)]^n.
$ (d) is similar.
]

#theorem([Distribution of $j$th Order Statistics])[
Let $X_1, dots, X_n tilde^"iid" F, f$.

  _(Discrete)_ Suppose the $X_i$'s take values in $S_x = {x_1, x_2, dots}$ and put $p_i = P(X_i)$. Then, $
  F_(X_((j))) (x_i) = P(X_((j)) (x_i) <= x_i) = sum_(k=j)^n binom(n, k) P_i^k (1 - P_i)^(n -k),
  $ where $P_i = P(X_i <= x_i) = sum_(ell=1)^i p_ell$.

  _(Continuous)_ $
  F_(X_((j))) (x) = sum_(k=j)^n binom(n, k) F^k (x) [1 - F(x)]^(n-k),
  $ so $
  f_(X_((j))) (x) = (n!)/((j-1)! (n-j)!) thin f(x) [F(x)]^(j-1) [1 - F(x)]^(n-j).
  $
]

#proof[
  For discrete, we have $
  P(X_((j)) (x_i) <= x_i) &= P("at least" j "out of" X_1, dots, X_n <= x_i).
  $ Then, $
   P("at least" j "out of" X_1, dots, X_n <= x_i) &= sum_(k=j)^n binom(n, k) P_i^k (1 - P_i)^(n -k).
  $ Continuous is similar.
]

== Large Sample/Asymptotic Theory

#definition("Convergence in Probability")[
  We say $T_n = T(X_1, dots, X_n)$ converges _in probability_ to $theta$ $T_n ->^P theta$ as $n -> infinity$ if for any $epsilon > 0$, $
  lim_(n -> infinity) P(|T_n - theta| > epsilon) = 0.
  $
]

#definition("Convergence in Distribution")[
  Find a positive sequence ${r_n}$ with $r_n -> infinity$ such that $
  r_n (T_n - theta) ->^"d" T,
  $ where $T$ a random variable. 
]

#theorem("Slutsky's")[
  Suppose $X_n ->^"d" X$ and $Y_n ->^"P" a$ for some $a in RR$. Then, $
  X_n + Y_n &->^"d" X + a \ 
X_n Y_n &->^"d" a X,
$ and if $a eq.not 0$,
$
  X_n/Y_n &->^"d" X/a.
  $
]

#theorem("Continuous Mapping Theorem (CMT)")[
  Suppose $X_n ->^"P" X$ and $g$ is continuous on the set $C$ such that $P(X in C) = 1$. Then, $
  g(X_n) ->^"P" g(X).
  $
]

#example[
  Let $X_1, dots, X_n tilde^"iid" F$ with $mu = EE[X_i], sigma^2 = "Var"(X_i) < infinity$. Then, $
  (sqrt(n) (overline(X)_n - mu))/(S_n) ->^"d" cal(N) (0, 1),
  $ since we may rewrite $
  (sqrt(n) (overline(X)_n - mu)\/sigma)/(S_n\/sigma).
  $ The numerator $->^"d" cal(N)(0, 1)$ by CLT. $S_n^2 ->^P sigma^2$, so the denominator goes to $1$ in probability.
]

#definition([Big $cal(O)$, Little $cal(o)$ Notation])[
  Let ${a_n}, {b_n} subset.eq RR$ real sequences. 
  
  - We say $a_n = cal(O)(b_n)$ if $exists 0 < c in RR$ and $N in NN$ such that $|a_n/b_n| <= c$ for every $n >= N$.

  - We say $a_n = cal(o)(b_n)$ if $lim_(n->infinity) a_n/b_n = 0$.
]

#definition([Big $cal(O)_p$, Little $cal(o)_p$ Notation])[
  Let ${X_n}, {Y_n}$ sequences of random variables. 
  - We say $X_n = cal(O)_p (1)$ if $forall epsilon > 0$ there is a $N_epsilon in  NN$ and $C_epsilon in RR$ such that $
  P(|X_n| > C_epsilon) < epsilon
  $ for every $n > N_epsilon$.
    - We say $X_n = cal(O)_p (Y_n)$ if $X_n\/Y_n = cal(O)_p (1)$.
  - We say $X_n = cal(o)_p (1)$ if $X_n ->^"P" 0$.
    - We say $X_n = cal(o)_p (Y_n)$ if $X_n\/Y_n = cal(o)_p (1)$.
]

#proposition[
  If $X_n ->^d X$, then $X_n = cal(O)_p (1)$.
]

#proposition("The Delta Method (First Order)")[
Let $sqrt(n) (X_n - mu) ->^"d" V$ and $g$ a real-valued function such that $g'$ exists at $x = mu$ and $g'(mu) eq.not 0$. Then, $
sqrt(n) (g(X_n) - g(mu)) ->^"d" g'(mu) V.
$ In particular, if $V tilde cal(N)(0, sigma^2)$ then $
sqrt(n) (g(X_n) - g(mu)) ->^"d" cal(N)(0, g'(mu)^2 sigma^2).
$
]
#proof[
  Taylor expanding the LHS, $
  sqrt(n) {g(X_n) - g(mu)} = g'(mu) sqrt(n) (X_n -mu) + cal(o)_p (1) -> g'(mu) V.
  $ 
]

#proposition("The Delta Method (Second Order)")[
  Suppose $sqrt(n) (X_n - mu) ->^"d" cal(N)(0, sigma^2)$ and $g'(mu) = 0$ but $g'' (mu) eq.not 0$. Then, $
  n {g(X_n) - g(mu)} ->^"d" sigma^2 dot( g''(mu))/2  dot chi_((1))^2.
  $
]
#proof[
  $
  g(X_n) - g(mu) = (g''(mu))/2 (X_n - mu)^2 + cal(o)_p (1),
  $ so $
   n (g(X_n) - g(mu)) = sigma^2 (g''(mu))/2 [(sqrt(n)(X_n - mu))/sigma]^2 + cal(o)_p (1).
  $ The bracketed term converges in distribution to $cal(N)(0, 1)$ and the $cal(o)_p (1)$ term converges in probability to zero, so the proposition follows by applying Slutsky's Theorem.
]

#example[
  $sqrt(n) (overline(X)_n - mu) ->^"d" cal(N) (0, sigma^2)$ by CLT. Letting $g(x) = x^2$, and assuming $mu eq.not 0$, then $
  sqrt(n) (overline(X)_n^2 - mu^2) -> cal(N)(0, 4 mu^2 sigma^2),
  $ by the first-order delta method.
]

#proposition[
  Let $X_1, dots, X_n tilde^"iid" F$, and denote the ECDF $F_n (x) = 1/n sum_(i=1)^n bb(1)(X_i <= x)$. Then, 
  1. $EE[F_n (x)] = F(x)$;
  2. $"Var" (F_n (x)) = 1/n F(x) (1 - F(x))$;
  3. $n F_n (x) = sum_(i=1)^n bb(1) (X_i <= x) tilde "Bin"(n, F(x))$;
  4. $(sqrt(n) (F_n (x) - F(x)))/(sqrt(F(x)(1 - F(x)))) ->^"d" cal(N)(0, 1)$.
  5. $F_n (x) ->^"P" F(x)$.
  6. $P(|F_n (x) - F(x)| >= epsilon) <= 2 e^(- 2 n epsilon^2)$, by Hoeffing's Inequality.
  7. $sup_(x in RR) |F_n (x) - F(x)| = ||F_n - F||_infinity ->^"a.s." 0$, by the Glivenko-Cantelli Theorem.
  8. $P(||F_n - F||_infinity > epsilon) <= C epsilon e^(-2 n epsilon^2)$ for some constant $C$ (Dvoretzky-Kiefer-Wolfowitz Theorem).
]
#remark[
  The constant in 8. was shown to be $2$ by Massart.
]

= Parametric Inference

#definition("Point Estimator")[
  Let $X_1, dots, X_n$ a random sample. A _point estimator_ $hat(theta):=hat(theta) (X_1, dots, X_n)$ is an estimator of a parameter $theta$ if it is a statistic. 
]

#example[
  Let $X$ be a random variable denoting whether a randomly selected electronic chip is operational or not, i.e. $X = cases(
1 "operational", 0 "else"
  )$, supposing $X tilde "Ber"(theta)$, then $0 < theta < 1$ is the probability a randomly selected chip is operational. Let $X_1, dots, X_n tilde^"iid" "Ber"(theta)$. Then, $
  cal(F) = {"Ber"(theta) : 0 < theta < 1}, wide Theta = (0, 1).
  $ Then, possible estimators are $overline(X)_n, (X_1 + X_2)/2$, just $X_2$, etc. 
]

#definition("Bias")[
  An estimator $hat(theta)_n$ is an _unbiased_ estimator of $theta$ if $
  EE_theta [hat(theta)_n] = theta, wide forall theta in Theta,
  $ where the expected value is taken with respect to the distribution of $hat(theta)_n$ (and thus depends on the distribution $F_theta$).

  Generally, the _bias_ of an estimator $hat(theta)_n$ is defined $
  "Bias"(hat(theta)_n) := EE_theta [hat(theta)_n] - theta, wide theta in Theta.
  $ If $hat(theta)_n$ unbiased, then $"Bias"(hat(theta)_n) = 0$.
]

#example[
For instance, recalling the previous example, $
EE_theta [overline(X)_n] = 1/n sum_(i=1)^n EE_theta [X_i] = 1/n n theta = theta,
$ so $overline(X)_n$ unbiased. Also, $
EE_theta [X_1] = theta,
$ so just $X_1$ also unbiased, as is $(X_1 + X_2)/2$.
]

#example[
  Let $X_1, dots, X_n tilde^"iid" F_theta$, $theta = vec(mu, sigma^2)$, $mu = EE[X_i], sigma^2 "Var"(X_i)$. Then, $hat(mu)_n = overline(X)_n = 1/n sum_(i=1)^n X_i$ an unbiased estimator of $mu$. Let $hat(sigma)_n^2 = S_n^2 = 1/(n - 1) sum_(i=1)^n (X_i - overline(X)_n)^2$, then recalling $EE[hat(sigma)^2_n] = sigma^2$, this is an unbiased estimator of $sigma^2$. However, changing the constant term, to get $
  hat(sigma)^(ast 2)_n = 1/n sum_(i=1)^n (X_i - overline(X)_n)^2,
  $ is biased, with $
  EE_theta [hat(sigma)^(ast 2)_n] = (n-1)/n sigma^2,
  $ so $
  "Bias"(hat(sigma)^(ast 2)_n) = - sigma^2/n < 0,
  $ i.e. $ hat(sigma)^(ast 2)_n$ underestimates the true parameter on average. Of course, in the limit it becomes 0.
]

#example[
  Let $X_1, dots, X_n tilde^"iid" cal(U)(0, theta)$, $theta > 0$, $Theta = (0, infinity)$. Recall $EE_theta [X_i] = theta/2$. Consider $
  hat(theta)_(n,1) := 2 X_3, wide hat(theta)_(n, 2) := 2 overline(X)_n, wide hat(theta)_(n, 3) := X_((n)) .
  $ Then, $EE[hat(theta)_(n, i)] = theta$ for $i = 1, 2$ and $n/(n+1) theta$ for $i = 3$. Hence, we can scale the last one, $hat(theta)_(n, 4) := (n+1)/n hat(theta)_(n, 3)$,  to get an unbiased estimator.
]

#definition("Mean-Squared Error")[
The _Mean-Squared Error_ (MSE) of an estimator is defined $
mse_(theta) (hat(theta)_n) &:= EE_(theta) [(hat(theta)_n - theta)^2] \ 
&= EE_theta [((hat(theta)_n - EE_theta [hat(theta)_n]) + (EE_theta [hat(theta)_n] - theta))^2] \
&= Var_(theta) (hat(theta)_n) + [Bias (hat(theta)_n)]^2.
$ Remark that if $EE_theta [hat(theta)_n] = theta$, i.e. $hat(theta)_n$ unbiased, then $MSE_theta (hat(theta)_n) = Var_theta (hat(theta)_n)$.
]

#definition("Consistency")[
  We say an estimator $hat(theta)_n$ of $theta$ is _consistent_ if $hat(theta)_n ->^"P" theta$ as $n -> infinity$.
]

#remark[
  There are many ways of establishing consistency; by direct definition of convergence in probability, the WLLN (maybe continuous mapping theorem), or checking if $EE_theta [hat(theta)_n]-> theta$ (if this happens we say $hat(theta)_n$ "asymptotically unbiased") and $Var_theta (hat(theta)_n) -> 0$ as $n-> infinity$, for in this case by Chebyshev's Inequality we have consistency.
]

#example[
  Let $X_1, dots, X_n tilde^"iid" F_theta$.

  1. $hat(mu)_n := overline(X)_n ->^"P" mu$ by WLLN, and $S_n^2 ->^"P" sigma^2$ similarly.

  2. If $X_1, dots, X_n tilde^"iid" cal(U)(0, theta)$, then $EE[X_i] = theta/2$. Note that $hat(theta)_(n, 1) = 2 overline(X)_n$ and $hat(theta)_(n, 2) = (n + 1)/n X_((n))$ are both unbiased estimators of $theta$, and both are consistent. To see the second one, we have that for any $epsilon > 0$, $
  P(|X_((n)) - theta| > epsilon) &= P(theta - X_((n)) > epsilon) \ 
  &= P(X_((n)) <  theta - epsilon)\
  &= ((theta - epsilon)/(theta))^n -> 0 "as" n -> infinity.
  $ We have too that $
  MSE_theta (hat(theta)_(n, 1)) = Var_theta (hat(theta)_(n, 1)) = 4 Var_theta (overline(X)_n) = 4/n Var(X_i) = 4/n theta^2/12 = theta^2/(3n).
  $ Also $
  MSE_theta (hat(theta)_(n, 2)) &= Var_theta (hat(theta)_(n, 2)) = ((n + 1)/n)^2 Var(X_((n))) \
  &= dots.c = theta^2/n(n + 2) = theta^2/(3 n) dot 3/(n +2) 
  <= MSE_theta (hat(theta)_(n, 1)) forall n >= 1.
  $
]

We will focus on the class of unbiased estimators of a real-valued parameter, $tau(theta)$, $tau : Theta -> RR$. 


== Uniformly Minimum Variance Unbiased Estimators (UMVUE), Cramér-Rau Lower Bound (CRLB)

#definition("UMVUE")[
  Let $bold(X) = (X_1, dots, X_n)^t$ be a random variable with a joint pdf/pmf given by $
  p_theta (bold(x)) = p_theta (x_1, dots, x_n),
  $ where $theta$ some parameter in $Theta subset.eq RR^d$. An estimator $Tau(bold(X))$ of a real valued parameter $tau(theta) : Theta -> RR$ is said to be a UMVUE of $tau(theta)$ if 
  1. $EE_theta [Tau (bold(X))] = tau(theta)$ for every $theta in Theta$;
  2. for any other unbiased estimator $Tau^ast (bold(X))$ of $tau(theta)$, we have $
  Var_theta (Tau(bold(X))) <= Var_theta (Tau^ast (bold(X))), forall  theta in Theta.
  $
]

#proposition("Cramér-Rau Lower Bound")[
We define in the case $d = 1$ ($Theta subset.eq RR$) for convenience. Assume that 

(1) the family ${p_theta : theta in Theta}$ has a common support $S = {bold(x) in RR^n : p_theta (bold(x))  > 0}$ that does not depend on $theta$;

(2) for $bold(x) in S$, $theta in Theta$, $dif/(dif theta) log p_theta (bold(x)) < infinity$;

(3) for any statistic $h(bold(x))$ with $EE_theta [ |h(bold(x))| ] < infinity$ for every $theta in Theta$, we have $
dif/(dif theta) integral_S h(bold(x)) p_theta (bold(x)) dif bold(x) = integral_S h(bold(x)) dif/(dif theta) p_theta (bold(x)) dif bold(x),
$ whenever the right-hand side is finite.

Let $Tau(bold(X))$ be such that $Var_theta (Tau(bold(X))) < infinity$ and $EE_theta [Tau(bold(X))] = tau(theta)$ for every every $theta in Theta$. Then if $0 < EE_theta [(dif/(dif theta) log(p_theta (bold(x))))^2] < infinity$ for every $theta in Theta$, then the Cramér-Rao Lower Bound (CRLB) holds: $
Var_theta (Tau(bold(X))) >= [tau'(theta)]^2/(EE_theta [(dif/(dif theta) log p_theta (bold(x)))^2]), wide forall theta in Theta.
$
]

#remark[
  The quantity $
  I(theta) := EE_theta [(dif/(dif theta) log(p_theta (bold(x))))^2]
  $ is called the _Fisher information_ contained in $bold(X)$ about $theta$.
]

#proof[
  Note that $tau(theta) = EE_theta [Tau(bold(X))]$ implies $
  tau'(theta)&= dif/(dif theta) EE[Tau(bold(X))] \
  &= dif/(dif theta) [integral_S Tau(bold(x)) p_theta (bold(x)) dif bold(x)] \ 
  "by ass. 2, 3" wide &= integral_S  Tau(bold(x)) dif/(dif theta) p_theta (bold(x)) dif bold(x) \ 
  &= integral_S Tau(bold(x)) dif/(dif theta) [log p_theta (bold(x))] p_theta (bold(x)) dif x \ 
  &= EE_theta [Tau(bold(X)) dif/(dif theta) log p_theta (bold(X))], wide forall theta in Theta. wide "(I)"
  $ On the other hand, by (3) with $h equiv 1$, then $
  0 = integral_S dif/(dif theta) p_theta (bold(x)) dif bold(x) = integral_S [dif/(dif theta) log p_theta (bold(x))] p_theta (bold(x)) dif bold(x) wide forall theta in Theta \ 
  => EE_theta [dif/(dif theta) log p_theta (bold(X))] = 0. wide "(II)"
  $ Combining (I) and (II), $
  tau' (theta) = "Cov"_theta (Tau(bold(X)), dif/(dif theta) log p_theta (bold(x))),
  $ since $"Cov"(X, Y) = EE[X Y] - EE[X]EE[Y]$, but the second of these terms vanishes by (II). Thus, $
  [tau'(theta)^2] = Cov_theta^2 (Tau(bold(X)), dif/(dif theta) log p_theta (bold(X))).
  $ By Cauchy-Schwarz, we find $
  [tau'(theta)]^2  &<= "Var"_theta (Tau(bold(X))) Var_theta (dif/(dif theta) log p_theta (bold(X))) \ 
  & <= "Var"_theta (Tau(bold(X))) EE_theta {[dif/(dif theta) log p_theta (bold(X))]^2},
  $ the last line following by the Bartlett Identity.
]

#remark[
  If $X_1, dots, X_n tilde^"iid" f_theta$, then $p_theta (bold(x)) = product_(i=1)^n f(x_i; theta)$, and $
  I(theta) = EE_theta {[dif/(dif theta) log p_theta (bold(X))]^2} &= EE_theta {[sum_(i=1)^n dif/(dif theta) log f(X_i; theta)]^2} \ 
  &= n underbrace(EE_theta {(dif/(dif theta) log f(X_1; theta))^2}, = I_1 (theta)),
  $ so the CRLB in this case reads $
  "Var"_theta (Tau(bold(X))) >= ([tau'(theta)]^2)/(n I_1 (theta)),
  $ and moreover if $tau(theta) = theta$ itself,$
  Var_theta (Tau(bold(X))) >= 1/(n I_1 (theta)).
  $
]

#example[
  Let $X_1, dots, X_n tilde^"iid" "Ber"(theta)$, so $f(x; theta) = theta^x (1-theta)^(1 - x)$ for $x = 0, 1$. Then, $
  log (f(x; theta))= x log (theta) + (1 - x) log(1 - theta)
  $ so $
  dif/(dif theta) log(f(x; theta)) = x/theta - (1-x)/(1-theta),
  $ so the Fisher information in one $X_1$ is given $
  I_1 (theta) = EE_theta {(X/theta - (1 - X)/(1 - theta))^2} = 1/(theta (1 - theta)).
  $ For any unbiased estimator of $tau(theta) = theta$, the CRLB gives $
  Var_theta (Tau(bold(X))) >= 1/(n I_1 (theta)) = theta(1-theta)/n.
  $
  Recall our estimator $hat(theta)_n = overline(X)_n$. We have that $Var_theta (overline(X)_n) = 1/n Var_theta (X_1) = (theta(1-theta))/n$.
]

#remark[
  If $p_theta$ additionally twice differentiable in $theta$ and $EE_theta {dif/(dif theta) log p_theta (bold(X))}$ is also differentiable under the $EE_theta$, $
  dif/(dif theta) log p_theta (bold(X)) = integral dif/(dif theta) {[dif/(dif theta) log p_theta (bold(x))] p_theta (bold(x))} dif x.
  $ In particular, this implies $integral p''_theta (bold(x)) dif bold(x) = 0$. Then, $
  I(theta) = EE_theta {[dif/(dif theta) log p_theta (bold(X))]^2} = - EE_theta {dif^2/(dif theta^2) p_theta (bold(X))},
  $ making it easier to compute $I(theta)$. This follows from the fact that $
  dif^2/(dif theta^2) log p_theta (bold(x)) = (p_theta ''(bold(x)))/(p_theta (bold(x))) - [dif/(dif theta )log p_theta (bold(x))]^2,
  $ and so taking the expected value of both sides cancels the inner-most term by the differentiability condition of $p_theta$;
  $
   EE[dif^2/(dif theta^2) log p_theta (bold(x))] &= EE[(p_theta ''(bold(x)))/(p_theta (bold(x)))] - EE[[dif/(dif theta )log p_theta (bold(x))]^2] \ 
   &=cancel( integral p''_theta (bold(x)) dif bold(x)) - I(theta).
  $
]

#example[
  Returning to the previous example, remark that $
  dby(theta, 2) log (f(x; theta)) = - x/(theta^2) - (x - 1)/((1 - theta)^2),
  $ and so $
  EE[dby(theta, 2) log f(x; theta)] = 1/theta + 1/(1 - theta)
  $ so $I_1 (theta) = 1/(theta (1 - theta))$ as we found before. 
]

#remark[
  The CRLB is _not_ a sharp bound, in the sense that the UMVUE for a particular parameter may be strictly larger than the CRLB.
]

#example[
  Let $X_1, dots, X_n tilde^"iid" cal(N)(mu, theta^2)$. Then, $hat(mu)_n$ the UMVUE for $mu$. If $mu$ known, then $hat(sigma)^2_n = 1/n sum_(i=1)^n (X_i - mu)^2$ is the UMVUE for $sigma^2$. If $mu$ is unknown, then $1/(n- 1)sum_(i=1)^n (X_i - overline(X)_n)^2$ would be the UMVUE for $sigma^2$.

  However, if $X_i tilde^("iid") exp(beta)$, with $f(x; beta) = 1/beta e^(-x/beta)$ for $x > 0$, $S_n^2$ is not the UMVUE for $"Var"_beta (X_i) = beta^2$.
]

#theorem("Attaining the CRLB")[
Suppose $bold(X) = (X_1, dots, X_n) tilde p_theta$. Let $Tau(bold(X))$ be unbiased for $tau(theta)$. Then, $Tau(bold(X))$ attains the CRLB if and only if $
a(theta) { Tau(bold(x)) - tau(theta)} = dif/(dif theta) log p(bold(x); theta),
$ for some function $a(theta)$, for every $theta in Theta$ and $bold(x)$ in the support of $p$.
]

#proof[
  In the proof of the CRLB, the only inequality arose from using Cauchy-Schwarz with bounding the covariance of $Tau(bold(X))$ and $dif/(dif theta) log p_theta (bold(X))$. Equality in this inequality holds if and only if the terms are linearly dependent, namely if there is some function $a(theta)$ and $b(theta)$ such that $a(theta) T(bold(x)) + b(theta) = dif/(dif theta) log p_theta (bold(x))$.

  On the other hand, $
  EE_theta {a(theta) T(bold(X)) + b(theta)} = EE_theta {dif/(dif theta) log p _theta (x)} = 0 => b(theta) = - EE_theta {a(theta) T(bold(X))} = - a(theta) tau(theta),
  $ so combining these two gives the desired linear relation.
]

#example("Exponential family")[
  $X_i tilde^"iid" f(x; theta) = h(x) c(theta) exp{omega(theta) T_1 (x)}$, where $h$ a nonnegative function of only $x$ and $c$ a nonnegative function of only $theta$, with the support of $f$ being independent of $theta$. Then $
  p_theta (bold(x)) = product_(i=1)^n f(x_i; theta) = [product_(i=1)^n h(x_i)] (c(theta))^n exp(omega(theta) sum_(i=1)^n T_1 (x_i)).
  $ Taking the log: $
  dif/(dif theta) log p_theta (bold(x))& = n (c'(theta))/c(theta) + omega'(theta) sum_(i=1)^n T_1(x_i) \ 
  &= omega'(theta) {sum_(i=1)^n T_1 (x_i) - (-n c'(theta))/(c(theta) omega'(theta))}.
  $ Let $
  tau(theta) = - (c'(theta))/(c(theta) omega'(theta)).
  $ Then, since $
  EE_theta [dif/(dif theta) log p_theta (bold(x))] = 0,
  $ then $
  EE_theta [sum_(i=1)^n T_1 (X_i)] = n tau(theta),
  $ so $
  T(bold(X)) = 1/n sum_(i=1)^n T_1 (X_i)
  $ is a UMVUE for $tau(theta)$ by the previous theorem.
]

#example[
  Let $X_i tilde^"iid" "Poisson"(theta)$ so $
  f(x; theta) = e^(-theta)/(x!) theta^x = e^(-theta)/(x!) e^(x log (theta)),
  $  with support $x in {0, 1, dots}$. Then, we notice that with $
  h(x) = 1/x!, c(theta) = e^(-theta), omega(theta) = log(theta), T_1 (x)  =x,
  $ that $X_i$ in the exponential family. Then, according to the previous example, $
  tau(theta) = - (- e^(-theta))/(e^(-theta) 1/theta) = theta,
  $ has UMVUE $
  T(bold(X)) = 1/(n) sum_(i=1)^n X_i = overline(X)_n.
  $
]

#example[
  Recall we found, for $X_i tilde^"iid" cal(U)(0, theta)$, that $hat(theta)_n := (n+1)/n X_((n))$ was an unbiased estimator but cannot obtain the CRLB since the regularity conditions are not satisfied (namely, the support of the pdfs depends on the parameter). Moreover, we found $
  EE_(theta) {(n+1)/n X_((n))} = theta,
  Var_theta {(n+1)/n X_((n))} = theta^2/(n(n+2)).
  $ If we temporarily ignore that we cannot apply CRLB, we would find $
  "CRLB" = 1/(n I_1 (theta)) = (theta^2)/n,
  $ so our estimator actually has a "better" variance. We'll see later that this estimator actually the UMVUE.
]

== Sufficiency


We can't always find unbiased estimators; here we look for other ways for comparing different estimators.

#example[
  Let $X_i tilde^"iid" cal(N)(mu, sigma^2)$, and consider the following estimators of $sigma^2$: $
  S_1^2 = 1/(n-1) sum_(i=1)^n (X_i - overline(X)_n)^2,\
  S_2^2 = 1/n sum_(i=1)^n (X_i - overline(X)_n)^2, \
  S_3^2 = 1/(n+1) sum_(i=1)^n (X_i - overline(X)_n)^2.
  $ One verifies these have respective means, variances #align(center, table(
    columns: 4,
    stroke: none,
    "", $S_1^2$, $S_2^2$, $S_3^2$,
    table.hline(start:0, end:4),
    table.vline(x:1, start:0, end:4),
    $EE$, $(n-1)/n sigma^2$, $sigma^2$, $(n-1)/(n+1) sigma^2$,
    $Var$, $(2(n-1)sigma^4)/n^2$, $(2sigma^4)/(n-1)$, $(2(n-1))/(n+1)^2 sigma^4$
  )). We notice then that $
  MSE(S_3^2) < MSE(S_2^2) < MSE(S_1^2),
  $ so despite the fact that $S_2^2$ is unbiased, it does not minimize the MSE.
]

#definition("Sufficiency")[
 Suppose $bold(X) = (X_1, dots, X_n)$ has joint pdf (pmf) $p(bold(x); theta)$ for $theta in Theta$. A statistic $T(bold(X)) : RR^n supset.eq X -> S_T subset.eq RR^k$, $k <= n$, is _sufficient_ for $theta$ or the parametric family ${p_theta : theta in Theta}$ if the conditional distribution of $(X_1, dots, X_n)$ given $T(bold(X)) = t$ for any $theta in Theta$ and $t in S_T$ in the support such that $P_theta (t in S_T) = 1$, does not depend on $theta$. Namely, $
 f_(bold(X)|T(bold(X))=t) (x_1, dots, x_n),
 $ does _not_ depend on $theta$.
]

#example[
  Let $X_1, dots, X_n tilde^"iid" "Ber"(theta)$. Let $T(bold(X)) = sum_(i=1)^n X_i$. We know that then $T (bold(X)) tilde "Bin"(n, theta)$. We claim $T$ sufficient; we have $
  f_theta (x_1, dots, x_n | T(bold(X)) = t) = cases(
  1/(binom(n, t)) "if" sum_(i=1)^n x_i = t,
  0 "else"
  ),
  $ which is independent of $theta$ so indeed sufficient.
]

#remark[
  A sufficient statistic induces a partitioning of the sample space $Chi subset.eq RR^n$; namely, $
    Chi = union.big_(t in S_T) Pi_t,
  $ such that $
    Pi_t = {bold(x) = (x_1, dots, x_n) in Chi | T(bold(x)) = t},
  $ and $S_T$ the support of $T$.
]

#example[
  Return to the Bernoulli example from before, and consider specifically the case when $n = 2$, so $T(bold(X)) = X_1 + X_2$ is a sufficient statistic as we showed. Then, the sample space is given by $
    Chi = {(0,0), (0, 1), (1,0), (1, 1)},
  $  and $T$ has support $
    T(bold(x)) = x_1 + x_2 in {0, 1, 2} =: S_T.
  $ This induces the partitioning $
Chi = Pi_0 union.sq Pi_1 union.sq Pi_2 = {(0,0)} union.sq {(0, 1), (1, 0)} union.sq {(1,1)}.
  $
]

#theorem("Neyman-Fisher Factorization Theorem")[
  Let $bold(X) = (X_1, dots, X_n)^t$ be a random vector with a joint pdf/pmf $p_theta (bold(x)) = p(bold(x); theta)$. A statistic $T(bold(X))$ is sufficient for $theta$ if and only if there exist functions $g(dot; theta)$ and $h(dot)$ such that $
  p_theta (bold(x)) = h(bold(x)) dot g(theta, T(bold(x))),
  $ for every $theta in Theta$ and $bold(x) in Chi$. 

  Note that $g$ depends on $bold(x)$ _only_ through $T(bold(x))$, and $h$ does _not_ depend on $theta$.
 ]

#proof[We prove in the discrete case.

Note that $
f_(bold(X)|T(bold(X)) = t_(bold(x))) (bold(x)) = (P_theta (X_1 = x_1, dots, X_n = x_n, T(bold(X)) = t_(bold(x))))/(P_theta (T(bold(X)) = t_(bold(x)))),
$ for every $bold(x)$ such that $T(bold(x)) = t_bold(x)$, and $0$ otherwise;
$
 = (P_theta (X_1 = x_1, dots, X_n = x_n))/(sum_(bold(y) = (y_1, dots, y_n) : T(bold(y)) = t_bold(x)) P(X_1 = y_1, dots, X_n = y_n)).
$

If $T(bold(X))$ a sufficient statistic for $theta$, then the above ratio, by definition, does not depend on $theta$; hence, putting $h(bold(x))$ to be the ratio above, it is independent of $theta$ (is only a function of the data), and if we take $g$ to be the denominator of the ratio above, then $g$ depends on the data only through $T$. Hence, we can write $p_theta (bold(x)) = h(bold(x)) dot g(t_bold(x); theta)$.

Conversely, suppose $p_theta (bold(x))= g(T(bold(x)); theta) h(bold(x))$. Then, $
f_(bold(X)|T(bold(X))=t_bold(x)) (bold(x); theta) &= (g(t_bold(x); theta) h(bold(x)))/(sum_(bold(y) : T(bold(y)) = t_bold(x)) g(T(bold(y)); theta) h(bold(y))) = (h(bold(x)))/(sum_(bold(y) : T(bold(y)) = t_bold(x)) h(bold(y))),
$ which depends only on $bold(x)$ and hence $T(bold(X))$ a sufficient statistic.
]

#example[
Let again $X_1, dots, X_n tilde^"iid" "Ber"(theta)$ so $
p_theta (x_1, dots, x_n) = product_(i=1)^n theta^(x_i) (1 - theta)^(1- x_i) = theta^(sum_(i=1)^n x_i) (1 - theta)^(n - sum_(i=1)^n x_i) product_(i=1)^n bb(1){x_i in {0,1}}.
$ for $x_i = 0, 1$.

One notices that the LHS (not the product) can be written as a function of $theta$ and $sum_(i=1)^n x_i$ only, and the remaining term is independent of $theta$. Hence by the previous theorem $T(bold(X)) = sum_(i=1)^n X_i$ a sufficient statistic for $theta$.
]

#example[
  Let $X_1, dots, X_n tilde^"iid" cal(U)(0, theta)$, so $f(x; theta) = cases(1/theta & "if" 0 < x < theta, 0 & "else")$. Then $
p_theta (bold(x)) &= product_(i=1)^n 1/theta bb(1)(0 < x_i < theta)\
&= underbrace(1/(theta^n) bb(1)(0 <x_((n)) < theta}, =: g(T(bold(x); theta))) underbrace(bb(1)(0 < x_((1)) < theta), =: h(bold(x))),
  $ so $X_((n))$ is a sufficient statistic for $theta$.
]

#remark[
  If $T$ is a sufficient statistic for $theta$ and $T(bold(X)) = Phi(T^ast (bold(X)))$ where $Phi$ is a measurable function and $T^ast$ another statistic, then $T^ast$ is also a sufficient statistic.
]

#example[
  In the exponential family, we claim $T(X_1, dots, X_n) = sum_(i=1)^n T_1 (X_i)$.
]

#example[
Let $X_1, dots, X_n tilde^"iid" cal(N)(mu, sigma^2)$ and $theta = (mu, sigma^2)$ both unknown. Using the factorization theorem, we can see that $
T(bold(X)) = (sum_(i=1)^n X_i, sum_(i=1)^n X_i^2)
$ is a sufficient statistic for $theta$, as is $(overline(X)_n, S_n^2)$.
]

#remark[
This does _not_ imply that say $sum_(i=1)^n X_i$ sufficient for $mu$! Namely $T$ is a sufficient statistic for the 2-dimensional parameter $theta$. We cannot simply separate the dependence.
]

#example[
Recall the Bernoulli example once again. We claim that $
T^ast_m (bold(X)) = (sum_(i=1)^m X_i,  sum_(i=m+1)^n X_i), wide 1 <= m <= n - 1
)
$ is also sufficient for $0 < theta < 1$. Clearly this is no different then just using the one-dimensional statistic $sum_(i=1)^n X_i$; we'd like to formalize how to differentiate such statistics. Namely, $sum_(i=1)^n X_i$ is called a _minimal_ sufficient statistic for $theta$.
]

// TODO midterm up to this point!

#definition("Minimal Sufficient Statistic")[
A statistic $T(bold(X))$ is a _minimal sufficient statistic_ for $theta$ iff 

- $T(bold(X))$ is sufficient;
- For any other sufficient statistic $T^ast (bold(X))$ of $theta$, $T(bold(X))$ is a function of $T^ast (bold(X))$, i.e. $
T(bold(X)) = phi(T^ast (bold(X))),
$ where $phi(dot)$ some measurable function, or equivalently, $forall bold(x), bold(y) in Chi subset.eq RR^n$, if $T^ast (bold(x)) = T^ast (bold(y))$ then $T(bold(x)) = T(bold(y))$.
]

#remark[
  If $T(bold(X))$ minimally sufficient and induces a partitioning $
  Chi = union.big_(t in S_T) Pi_t, wide Pi_t := {bold(x) in Chi : T(bold(x)) = t}
  $ and $T^ast (bold(X))$ any sufficient statistic that induces a partitioning $
  Chi = union.big_(t^ast in S^ast_(T^ast)) Pi^ast_(t^ast),wide Pi^ast_t^ast := {bold(x) in Chi : T^ast (bold(x)) = t^ast},
  $ then we find that $forall t^ast in S_(T^ast)^ast$, there is some $t in S_T$ such that $Pi_(t^ast)^ast subset.eq Pi_t$; namely, the partition induced by $T(bold(X))$ is the _coarsest_ possible partition of $Chi$.
]

#theorem("Lehmann-Scheffé")[
For a parametric family $p_theta (dot)$ (the joint pdf/pmf of $bold(X)$), suppose a statistic $T(bold(X)) = T(X_1, dots, X_n)$ is such that for every $bold(x), bold(y) in Chi subset.eq RR^n$ $T(bold(x)) = T(bold(y)) <=>  (p_theta (bold(x)))/(p_theta (bold(y)))$ does not depend on $theta$. Then, $T(bold(X))$ is a minimal sufficient statistic for $theta$.
]

#example[
  Suppose $X_i tilde^"iid" cal(U)(0, theta)$, then $p_theta (bold(x)) = 1/(theta^n) bb(1){x_((n)) < theta} bb(1){x_((1)) > 0}$; then $T(bold(X)) = X_((n))$ is a sufficient statistic for $theta$. For any $bold(x), bold(y) in Chi$, we find $
  (p_theta (bold(x)))/(p_theta (bold(y))) &= (bb(1){x_((n)) < theta} bb(1){x_((1)) > 0})/(bb(1){y_((n)) < theta} bb(1){y_((1)) > 0}),
  $ which does not depend on $theta$ iff $x_((n)) = y_((n))$ iff $T(bold(x)) = T(bold(y))$ and therefore by the previous theorem $T(bold(X))$ is a minimally sufficient statistic.
]

#example[
  If $X_i tilde^"iid" cal(N)(mu, sigma^2)$ and $theta = (mu, sigma^2)$, it can be shown that $
  T(bold(X)) = (sum_(i=1)^n X_i, sum_(i=1)^n X_i^2)
  $ is a minimal sufficient statistic for $theta$. Any one-to-one function of a minimally sufficient statistic also minimally sufficient, hence this implies $(overline(X)_n, S_n^2)$ is also minimally sufficient for $theta$.
]

== Completeness

#definition("Completeness")[
  Let $X$ be a random variable with a pmf/pdf belonging to a parametric family $cal(F) = {f_theta : theta in Theta}$. This family is said to be _complete_ if for any measurable function $g$ with $EE_theta [g(bold(X))] < infinity$, then $EE_theta [g(bold(X))] = 0$ for all $theta in Theta$ implies $P_theta (g(X) = 0) = 1$.

  A statistic $T(bold(X)) = T(X_1, dots, X_n)$ is said to be _complete_ if the family of its distributions is complete.
]

#remark[
  Complete and sufficient $=>$ minimal, but minimally sufficient may not be complete, as we'll see.
]

#example[
  Let $X_i tilde^"iid" "Ber"(theta)$, then note $T(bold(X)) = sum_(i=1)^n X_i tilde "Bin"(n, theta)$. Let $g$ a measurable function. Then, $
  0 = EE_theta [g(bold(X))]  =>  0 &= sum_(t=0)^n g(t) binom(n, t) theta^t (1 - theta)^(n - t)  \ 
  &=cancel( (1 - theta)^n )sum_(t=0)^n g(t) binom(n, t) (overbrace((theta)/(1-theta), =: eta))^t \ 
  &= sum_(t=0)^n g(t) binom(n, t) eta^t.
  $ Then, this is just a polynomial in $eta$, which, being equal to zero implies all the coefficients $g(t) binom(n, t) = 0$ for every $t$ and hence $g(t) = 0$. Hence, $T(bold(X))$ is a complete statistic.
]

#example[
  If $X tilde cal(N)(0, theta)$, the family is not complete. For instance with $g(x) := x$, $EE_theta (X) = 0$ but $g(x)$ is not identically zero. On the other hand, $T(X) = X^2$ is a complete statistic. To see this, we know $(X^2)/theta tilde chi^2_((1))$, so $
  EE_theta (g(T)) = 0 =>0 &=  integral_(0)^infinity g(t) f_T (t; theta) dif t \ 
  &= integral_(0)^infinity 1/(sqrt(2 pi theta)) g(t) t^(-1/2) e^(-t/(2 theta)) dif t \ 
  &= cal(L){g(t) t^(-1/2) 1/(sqrt(2 pi theta))}.
  $ By uniqueness of the Laplace transform, it must be that $g(t) t^(-1/2) equiv 0$ hence $g(t) = 0$ and thus $T(X) = X^2$ is a complete statistic.
]

#example[
  In the exponential family, $sum_(i=1)^n T_1 (X_i)$ is a complete statistic.
]

Note that an unbiased estimator of a parameter of interest may not even exist. For instance, #example[
  If $X tilde "Bin"(n, theta)$, let $tau(theta) = 1/theta$. If $delta(X)$ is an unbiased estimator of $tau(theta)$, we must have $EE_theta [delta(X)] = 1/theta$ i.e. $
  sum_(x=0)^n delta(x) binom(n, x) theta^x (1 - theta)^(n - x) = 1/theta.
  $ As $theta -> 0$, the left-hand side will just be $delta(0)$, while the right-hand side will diverge to $infinity$, so no such estimator exists.
]

#theorem("Rao-Blackwell")[
  Let $U(bold(X))$ be an unbiased estimator of $tau(theta)$ and let $T(bold(X))$ be a sufficient statistic for the parametric family. Set $
  delta(t) = EE_theta [U(bold(X)) | T(bold(X)) = t], wide t in S_T.
  $ Then, 

  - $delta(T(bold(X)))$ is a statistic, i.e. only depends on $bold(X)$;
  - $EE_theta [delta(T(bold(X)))] = tau(theta)$;
  - $Var_theta (delta(T(bold(X)))) <= Var_theta [U(bold(X))]$.
]

#proof[
  - $delta(T(bold(X))) = EE_theta [U(bold(X))|T(bold(X))]$ is a random variable in its own right, and is a statistic because $T(bold(X))$ is sufficient, hence conditioning on $T(bold(X))$ will result in no reliance on $theta$.

  - $EE_theta [delta(T(bold(X)))] = EE_theta [EE_theta [U(bold(X))|T(bold(X))]]=EE_theta [U(bold(X))] = tau(theta)$ (using the law of total expectation), since $U(bold(X))$ is an unbiased estimator of $tau(theta)$.
  
  - Using the law of total variance, we find $
    Var_theta (U(bold(X))) &= Var_theta \(underbrace(EE_theta [U(bold(X))|T(bold(X))], = delta(T(bold(X))))) + EE_theta [Var_theta (U(bold(X))|T(bold(X)))] \ 
    &= Var_theta [delta(T(bold(X)))] + EE_theta [underbrace(Var_theta (U(bold(X))|T(bold(X))), >= 0)\] \ 
    &>= Var_theta [delta(T(bold(X)))].  
  $
]

#remark[
  This theorem gives a systematic manner of improving unbiased estimators, by taking an unbiased estimator and a sufficient statistic, and "Rao-Blackwell-izing", leading to a uniform improvement in variance.
]

#theorem("Lehmann-Scheffé: Uniqueness")[
  Let $T(bold(X))$ be a complete sufficient statistic. Let $U(bold(X)) = h(T(bold(X))),$ for a measurable function $h$, an unbiased estimator of $tau(theta)$ such that $EE_theta [U(bold(X))^2] < infinity$. Then, $U(bold(X))$ is the unique unbiased estimator of $tau(theta)$ with the smallest variance in the class of unbiased estimators of $tau(theta)$.
]

#proof[
  By the Rao-Blackwell Theorem, it suffices to restrict attention to unbiased estimators that are only functions of $T(bold(X))$; for any other such unbiased statistic, applying Rao-Blackwell to it results in a new statistic with smaller variance.

  Now, let $V(bold(X)) = h^ast (T(bold(X)))$ be any other unbiased estimator of $tau(theta)$. Then, $
  EE_theta [V(bold(X))] = EE_theta [U(bold(X))] = tau(theta)
  $ hence $
  EE_theta [V(bold(X)) - U(bold(X))] = EE_theta [h^ast (T(bold(X))) - h(T(bold(X)))] = 0.
  $ Let $g(T(bold(X))) = h^ast (T(bold(X))) - h(T(bold(X)))$; then, since $T(bold(X))$ complete, it must be that $P(g = 0) = 1$ i.e. $
  P(h(T(bold(X))) = h^ast (T(bold(X)))) = 1,
 $ so $U(bold(X)), V(bold(X))$ are almost surely identical, hence we indeed have uniqueness.
]

#remark[
  This, combined with the Rao-Blackwell theorem, provides a method for obtaining the UMVUE for $tau(theta)$ starting with a complete sufficient statistic and an unbiased statistic.
]

#example[
  Let $X_i tilde^"iid" "Ber"(theta)$, $i = 1, dots, n$ and $hat(theta)_n = overline(X)_n$. This is unbiased, and $sum_(i=1)^n X_i$ is a complete and sufficient statistic. Hence, $hat(theta)_n$ is a unbiased estimator that is a function of a complete and sufficient statistic and thus is the UMVUE for $theta$ by the Lehmann-Scheffé Theorem.
]

#example[
 Let $X_i tilde^"iid" "Pos"(theta), i = 1, dots, n$ and $hat(theta)_n = overline(X)_n$. This is unbiased, and again $sum_(i=1)^n X_i$ is a complete sufficient statistic hence $hat(theta)_n$ is the UMVUE of $theta$.

 Suppose now $tau(theta) = P_theta (X = 0) = e^(-theta)$; can we obtain a UMVUE for this (function of) a parameter? Define $
 U(X_1) = bb(1){X_1 = 0},
 $ which will be unbiased for $tau(theta)$. We already have a complete and sufficient statistic. Applying now the Rao-Blackwell theorem, we obtain $
 delta(t) = EE_theta [U(X_1) | sum_(j=1)^n X_j = t].
 $ One verifies that $
 (X_i | sum_(j=1)^n X_j = t) tilde "Bin"(t, 1/n),
 $ therefore $
 delta(t) =  P_theta (X_1 = 0 | T(bold(X)) = t) = (1 - 1/n)^t.
 $ So, $delta(T(bold(X))) = (1 - 1/n)^(sum_(i=1)^n X_i)$ is the UMVUE of $e^(-theta)$. Remark that $
 delta(T(bold(X))) = (1 - 1/n)^(n overline(X)_n) approx e^(- overline(X)_n) "for large" n.
 $
]


#example[
  Let $X_i tilde^"iid" "Ber"(theta), i = 1, dots, n$, and suppose $tau(theta) = "Var"(X_i) = theta(1 - theta)$. Recall the UMVUE for $theta$ is $hat(theta)_n$. Note that $
  T(bold(X)) = sum_(i=1)^n X_i tilde "Bin"(n, theta),
  $ is complete and sufficient. We know $S_n^2 = 1/(n-1) sum_(i=1)^n (X_i - overline(X)_n)^2 = U(bold(X))$ is unbiased for $tau(theta)$. We may write $
  U(bold(X)) &= 1/(n - 1) [sum_(i=1)^n X_i^2 - n overline(X)_n^2] \ 
  "since" X_i in {0, 1} wide &= 1/(n-1) [sum_(i=1)^n X_i - n overline(X)_n^2] \ 
  &= 1/(n - 1) (T(bold(X)) - (T^2 (bold(X)))/n) \ 
  &= n/(n-1) overline(X)_n (1 - overline(X)_n)
  $ Hence, $U(bold(X))$ a function of $T(bold(X))$, a complete sufficient statistic, and $U(bold(X))$ is unbiased, so we conclude $U(bold(X))$ the UMVUE for $tau(theta)$.
] 

== Existence of a UMVUE

#definition("Unbiased Estimators of Zero")[
  An estimator $delta(bold(X))$ satisfying $EE_theta [delta(bold(X))] = 0$ is called an _unbiased estimator of zero_.
]

// #theorem[
//   An estimator $U(bold(X))$ of $tau(theta) = EE_theta [U(bold(X))]$
// ]
