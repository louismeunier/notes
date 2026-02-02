// ! external
#import "../typst/notes.typ": *
// #import "../typst/shortcuts.typ": *

#import "@preview/cetz:0.2.2"

// ! configuration
#show: doc => conf(
  course_code: "MATH562",
  course_title: "Theory of Machine Learning",
  subtitle: "",
  semester: "Winter 2026",
  professor: "Prof. Courtney Paquette",
  // cute: "../analysis 3/page.png",
  doc,
)

#import "@preview/commute:0.2.0": arr, commutative-diagram, node

#set align(left)
#let boxit(arg) = box(stroke: 0.75pt, outset: 8pt, arg)

#let Yc = $cal(Y)$
#let Xc = $cal(X)$

#pagebreak()

= Introduction

== Some Linear Algebra

=== Inverting Block Matrices
Let $ M := mat(A, B; C, D) in RR^((p + q) times (p + q)), $ i.e. $A in RR^(p times p), B in RR^(p times q), C in RR^(q times p)$ and $D in RR^(q times q)$ (where we use the convention that if $A in RR^(m times n)$, then $A$ has $m$ rows and $n$ columns, so in particular maps $RR^n -> RR^m$). If $A$ is invertible, let $ M \\ A := D - C A^(-1) B =: "Schur Complement (of "A" with respect to "M")". $ Then, $ M^(-1) = mat(A^(-1) + A^(-1) B (M \\ A)^(-1) C A^(-1), quad - A^(-1) B (M \\ A)^(-1); - (M \\ A)^(-1) C A^(-1), (M \\ A)^(-1)). $ Similarly, if $D$ invertible and $M \\ D := A - B D^(-1) C$, then $ M^(-1) = mat((M \\ D)^(-1), -(M\\D)^(-1) B D^(-1); - D^(-1) C (M \\ D)^(-1), quad D^(-1) + D^(-1) C (M \\ D)^(-1) B D^(-1)). $

=== Eigenvalues and Singular Values

Given $A in RR^(n times n)$ symmetric, there exists $U in RR^(n times n)$ orthogonal (i.e., $U^T = U^(-1)$) such that $ A = U "diag"(lambda) U^T, $ where $lambda = (lambda_1, dots, lambda_n)$ for $lambda_i$'s the eigenvectors of $A$. In particular, if $U^((i))$ enumerate the columns of $U$, we have $ A U^((i)) = lambda_i U^((i)), $ i.e. the $U^((i))$'s are the eigenvectors of $A$.

Given $X in RR^(n times d), n >= d$, then there exists an orthogonal matrix $V in RR^(d times d)$ and $U in RR^(n times d)$ with orthogonal columns, and a matrix of _singular values_ $s in RR^d_+ = {(v_1, dots, v_d) in RR^d | v_i >= 0 forall i = 1, dots, d}$ such that $ X = U "Diag"(s) V^T. $

#remark[
  1. if $u_i in RR^n, v_j in RR^d$ are the columns of $U, V$ resp., then $X = sum_(i= 1)^d s_i u_i v_i^T$
  2. if $s_i$ a singular value of $X$, then $s_i^2$ an eigenvalue of $X X^T$ and $X^T X$.
]

== Concentration Inequalities

Here we study the question of how the magnitude of the average of $n$ independent, mean $0$ random variables behaves compared to their average magnitude, specifically with respect to $n$.

We know that the central-limit theorem states that for $z_i$ iid with variance $sigma^2$, $sqrt(n) (1/n sum z_i - EE[z])$ converges in distribution to a $cal(N)(0, sigma^2)$; this is an asymptotic result, which gives no information about the rate of this converge with respect to $n$, which is what we care about in our study.

#proposition("Markov's")[
  Let $Y$ be a nonnegative r.v. with finite mean. Then, $ PP(Y >= epsilon) <= 1/epsilon EE[Y], quad forall epsilon > 0. $
]

#proposition("Chebyshev's")[
  Let $X$ be a r.v. with finite mean and variance, then $ PP(abs(X - EE[X]) >= epsilon) <= "Var"[X]/epsilon^2, quad forall epsilon > 0. $
]

#corollary[
  If $z_i, i = 1, dots, n$ are iid with variance $sigma^2$, then $ PP(abs(1/n sum_(i=1)^n z_i - EE[z]) >= epsilon) <= (sigma^2)/(n epsilon^2). $
]

#proposition("Union Bound, Max/Tail Bound")[
  1. $PP(union.big_(f in cal(F)) A_f) <= sum_(f in cal(F)) PP(A_f)$
  2. $PP(sup_(f in cal(F)) Z_f >= t) <= sum_(f in cal(F)) PP(Z_f >= t)$
]

#proposition("Jensen's Inequality")[
  If $F : RR -> RR$ convex and $X$ an r.v. with finite mean, $ F(EE[X]) <= EE[F(X)]. $
]

=== Hoeffding Inequality

#proposition("Hoeffding Inequality")[
  Let $z_1, dots, z_n$ be independent r.v.s with $z_i in [0, 1]$ a.s.. Then, for any $t >= 0$, $ PP(1/n sum_(i= 1)^n z_i - 1/n sum_(i=1)^n EE[z_i] >= t) <= exp(-2 n t^2). $
]

#remark[Read this result as a _fast_ (exponential) convergence of the empirical mean to the true mean as the sample size $n$ grows.]

#proof[
  First we claim that $ z in [0, 1] "a.s." => EE[exp(s (z - EE[z]))] <= exp(s^2/8). quad (dagger) $
  We'll assume $z$ is centered for the sake of notation. Let $phi(s) := log(EE[exp(s z)])$. Remark that $ phi(0) = 0 \
  phi'(s) = EE[z exp(s z)]/(EE[exp(s z)]) \
  phi''(s) = EE[z^2 exp(s z)]/(EE[exp(s z)]) - (EE[z exp(s z)]/(EE[exp(s z)]))^2. $
  In particular, if we define a new probability density $ tilde(z) |-> e^(s tilde(z))/(EE[e^(s z)]) $ with respect to that of $z$, and let $tilde(z)$ be distributed with respect to this distibution, then $ "Var"(tilde(z)) = phi''(s). $ Note that $tilde(z) in [0, 1]$ a.s.. In addition, we have that $ "Var"(tilde(z)) & = "inf"_(v in [0, 1]) EE[(tilde(z) - v)^2] \
                  & <= EE[(tilde(z) - 1/2)^2] = 1/4 EE[(underbrace(2 tilde(z) - 1, <= 1 "a.s."))^2] <= 1/4, $ so that $phi''(s) <= 1/4$ for all $s$. Thus, by Taylor expanding $phi$, we find $ phi(s) <= phi(0) + phi'(0) s + s^2/2 1/4 = s^2/8, $ using the bound above and the fact $phi'(0) = 0$ (checking the above formula). Thus, $ phi(s) = log(EE[exp(s z)]) <= s^2/8, $ from which the claim $(dagger)$ follows by taking $exp$ of both sides.

  Next, let $t >= 0$ and put $overline(z) = 1/n sum z_i$. Then, $ PP(overline(z) - EE[overline(z)] >= t) & = PP(exp(s (overline(z) - EE[overline(z)])) >= exp(s t)) \
                       ("Markov's") quad & <= e^(- s t) EE[exp(s (overline(z) - EE[overline(z)]))] \
                         ("Indep.") quad & = e^(- s t) product_(i = 1)^n EE[exp(s/n (z_i - EE[z_i]))] \
                           (dagger) quad & <= e^(-s t) product_(i=1)^n exp(s^2/(8n^2)) = exp(- s t + s^2/(8n)). $ This bound held for all $s$, so in particular holds at $overline(s) = "argmin"{-s t + s^2/(8 n)} = 4 n t$. Plugging in this value for $s$ gives the result.
]

#corollary("2-sided Hoeffding")[
  With the same hypotheses as the previous proposition, we have $ PP(abs(1/n sum z_i - 1/n sum EE[z_i]) >= t) <= 2 exp(- 2 n t^2), forall t >= 0. $ If instead $z_i in [a, b]$ a.s., we can replace the rhs with $ <= 2 exp((-2 n t^2)/(a - b)^2). $
]

#remark[
  1. How is Hoeffding used? Start with a probability, then derive the necessary $t$ (usually, as a function of $n$) to achieve that bound. e.g., if $z_i in [a, b] a.s.$ and for any $delta in (0, 1)$, then with probability $1 - delta$, $ abs(1/n sum z_i - 1/n sum EE[z_i]) < abs(a - b)/sqrt(2 n) sqrt(log(2/delta)) $
  2. An extension exists for martingales. If $Z_i, i = 1, dots, n$ martingales with respect to a filtration ${cal(F)_i}$  and $abs(Z_i) <= c_i$ a.s., then $ PP(1/n sum_(i=1)^n Z_i >= t) <= exp(- (n^2 t^2)/(2 norm(c)^2)), quad c := (c_1, dots, c_n). $
]

#definition("Sub-Gaussian")[
  We say an r.v. $X$ is _sub-Gaussian_ if there exists $tau in RR_+$ such that $ EE[exp(s(X - EE[X]))] <= exp(tau^2/2 s^2), quad forall s in RR. $ We define the _sub-Gaussian norm_ by $ norm(X)_(psi_2) := inf{k >= 0 : EE[exp(X^2/k^2)] <= 2}, $ i.e. the "best" sub-Gaussian parameter for $X$.
]
#remark[
  Interpretation: $X$ has tails decaying as fast (or faster) than a Gaussian.
]

#remark[
  _Different texts may define this differently, i.e. with/without a 2 factor under the $tau^2$. The notational advantage of this definition is that a Gaussian random variable with variance $sigma^2$ has sub-Gaussian parameter $sigma$._
]

#proposition[
  $X$ is sub-Gaussian iff there exists a $k in RR_+$ such that $ PP(abs(X - EE[X]) >= t) <= 2 exp(- t^2/k^2), quad forall t in RR. $
]


#definition("Sub-Exponential")[
  We say $X$ _sub-exponential_ if $ PP(abs(X - EE[X]) >= t) <= 2 exp(- t/k), $ for some $k$ and for all $t >= 0$. We define the _sub-Gaussian norm_ by $ norm(X)_(psi_1) := inf{k >= 0 : EE[exp(abs(X)/k^2)] <= 2}, $ i.e. the "best" sub-Gaussian parameter for $X$.
]
#remark[This is a similar, but slower, tail bound than sub-Gaussian.]

=== McDiamarid's Inequality

For a measure space $Z$ and nonnegative integer $n$, we say $f :Z^n -> RR$ is a function of bounded variation with constant $c$ if for all $i in [n] := {1, dots, n}$ and points $z_1, dots, z_n, z'_i in Z$, then $ abs(f(z_1, dots, z_i, dots, z_n) - f(z_1, dots, z'_i, dots, z_n)) <= c. $
#proposition("McDiamarid's Inequality")[
  Let $z_1, dots, z_n$ be independent r.v.s on some measure space $Z$ and $f : Z^n -> RR$ be a function of bounded variation with constant $c$. Then, $ PP(|f(z_1, dots, z_n) - EE[f(z_1, dots, z_n)]| >= t) <= 2 exp(- (2 t^2)/(n c^2)), quad forall t >= 0. $
]

#remark[
  We can extend this to $z_i in RR^d$; if $norm(z_i)_2 <= c$ a.s., then $norm(1/n sum z_i)_2 <= c/sqrt(n) (1 + sqrt(2 log(1/delta)))$ with probability $>= 1 - delta$.
]

=== Bernstein's Inequality
#proposition("Bernstein's")[
  Let $z_i, i = 1, dots, n$ be independent with $abs(z_i) <= c$ a.s. and mean zero. Then for all $t >= 0$, $ PP(1/n abs(sum_i z_i) >= t) <= 2 exp(- (n t^2)/(2 sigma^2 + 2 c t\/3)), quad sigma^2 := 1/n sum_i "Var"(z_i). $ In particular, for $delta in (0, 1)$, then with probability $>=1 - delta$, $ abs(1/n sum z_i) <= sqrt((2 sigma^2 log(2/delta))/n) + (2 c log(2/delta))/(3 n). $
]

#proposition("Extension of Bernstein's, sub-exponential")[
  Let $x_1, dots, x_n$ be mean zero, independent, sub-exponential r.v.s with constants $k_i$, and let $a in RR^n$. Then, for all $t >= 0$, $ PP(abs(sum a_i x_i) >= t) <= 2 exp(- c min{t^2/(k^2 norm(a)_2^2), 1/(k norm(a)_infinity)}). $
]

#proposition("Extension of Bernstein's, non-zero means")[
  With the same hypothesis as Bernstein's but without the zero means, we have $ PP(abs(1/n sum z_i - 1/n sum EE[z_i]) >= t) <= 2 exp(- (n t^2)/(2 sigma^2 + 2 c t/3)). $
]

=== Expectation of the Maximum

#proposition[
  Let $z_i$ be (possible dependent) mean-zero, $RR$-values r.v.s which are all sub-Gaussian with constant $tau^2$. Then, $ EE[max{z_1, dots, z_n}] <= sqrt(2 tau^2 log(n)). $
]

#proof[
  For all $t > 0$,
  $ EE[max{z_1, dots, z_n}] & <= 1/t log)EE[exp(t max(Z_i))] quad ("Jensen's") \
                          & = 1/t log(EE[max{exp(t Z_i)}]) quad (exp "increasing") \
                          & <= 1/t log(EE[sum exp(t Z_i)]) quad ("max leq sum") \
                          & <= 1/t log(n exp(tau^2 t^2/2)) quad ("sub-Gaussian") \
                          & = log(n)/t + (tau^2 t)/2. $ The proof follows by taking $t := tau^(-1) sqrt(2 log(n))$.
]

= Introduction to Supervised Learning


== Training Data Predictions

The goal of supervised learning is to take a series of observations $(x_i, y_i) in cal(X) times cal(Y)$ for $i in [n]$ (called _training data_) and to predict a new $y in cal(Y)$ given a (previously unseen) $x in cal(X)$ (_testing data_).

We write
- $cal(X)$ for our space of _inputs_, typically embedded in $RR^d$ (where $d$ tends to be very large; think images encoded as large matrices of pixels, text, videos, etc)
- $cal(Y)$ for our space of _outputs_ or _labels_ for the data

The challenges in supervised learning are twofold:
1. $y in cal(Y)$ may not be a deterministic function of $x in cal(X)$
2. inputs may live a high-dimensional space, hence it is computationally expensive to work with them

We make two primary blanket assumptions of our problem:
1. we aim to maximize the expectation of some measure of performance with respect to some testing distribution we put on our data
2. we assume $(x_i, y_i)$ are iid, with the training data having the same distribution as the testing data

#definition("Machine Learning (ML) Algorithm")[
  An _ML algorithm_ is a function from the data set, $(cal(X) times cal(Y))^n$ to a function $cal(X) -> cal(Y)$.
]

== Decision Theory
The question we aim to answer here is, what is the _optimal_ performance of an algorithm, regardless of the finiteness of the data? I.e., if we havd perfect knowledge of the underlying probability distribution of our data, how should we design our algorithm?

We assume for now a fixed (testing) distribution $P_(x, y)$ on $cal(X) times cal(Y)$ with $P_(x)$ marginal distribution on $cal(X)$.

=== Supervised Learning and Loss Functions
#definition("Loss Function")[
  A _loss function_ is a mapping $ell : cal(Y) times cal(Y) -> RR$ where $ell(y, z)$ some measure of how close a true label $y$ is to a predicted label $z$.
]

#example[
  1. (Binary classification) Let $cal(Y) = {0, 1}$, or even $cal(Y) = {0, dots, 9}$. A typical loss on such labels is the "0-1 loss", $ell(y, z) := bb(1)_({y eq.not z})$.
  2. (Regression) Let $cal(Y) = RR$, then two typical loss functions are the _mean-square loss_ $ cal(l)(y, z) := (y - z)^2 $ or _absolute loss_ $ ell(y, z) := |y - z|. $
]

=== Risks

#definition("Expected Risk")[
  Given a prediction function $f : cal(X) -> cal(Y)$, a loss function $ell : cal(Y) times cal(Y) -> RR$ and a probability distribution $P$ on $cal(X) times cal(Y)$, the _expected risk_ of $f$ is defined by $ cal(R)(f) := EE_(x, y) [ell(y, f(x))] = integral_(cal(X) times cal(Y)) ell(y, f(x)) dif P(x, y). $
]

#definition("Empirical Risk")[
  Given a prediction function $f : cal(X) -> cal(Y)$, a loss function $ell : cal(Y) times cal(Y) -> RR$ and $(x_i, y_i)_(i=1)^n in cal(X) times cal(Y)$, the _empirical risk_ is given by $ hat(cal(R))(f) &:= 1/n sum_(i=1)^n ell(y_i, f(x_i)) \
  &= integral_(cal(X) times cal(Y)) ell(y, f(x)) dif mu(x, y), quad mu(x, y) := 1/n sum_(i=1)^n delta_{(x_i, y_i)}. $
]

#remark[Heuristically, $hat(cal(R))(f)$ should approach $cal(R)(f)$ as $n->infinity$.]

#example[
  1. If $cal(Y) = {0, 1}, ell(y, z) = bb(1)_{y eq.not z}$, then $ cal(R)(f) = EE[bb(1)_{y eq.not f(z)}] = PP(y eq.not f(x)) = "probability of missclassifying" $
  2. $cal(Y) = RR, ell(y, z) = (y - z)^2$, $ cal(R)(f) = EE[(y - f(x))^2], quad "mean-square error (MSE)" $
]

=== Baye's Risk, Predictor

Here, we answer the question: what's the best predictor $f$ we could find, assuming we knew everything about the underlying distibution on $cal(X) times cal(Y)$?

We can write, by law of total expectation, $ cal(R)(f) & = EE[ell(y, f(x))] \
          & = EE[EE[ell(y, f(x))|x]] \
          & = EE_(x' tilde p) [EE[ell(y, f(x')) | x = x']] \
          & = integral_(cal(X)) EE[ell(y, f(x')) | x = x'] dif p(x'). $
Define the _conditional risk_ given $x' in cal(X)$ by $ r(z|x') := EE_y [ell(y, z) | x = x'], $ so that we can write $ cal(R)(f) = integral_(Xc) r(f(x')|x) dif p(x') =^(Xc "finite") sum_(x' in cal(X)) r(f(x')|x') PP(x = x'). $ In particular, in the finite case, we can see that to minimize the risk $cal(R)(f)$, we can minimize the individual conditional risks $r(f(x')|x')$ for each $x' in cal(X)$. The so-called _Baye's predictor_ is a function $f_ast$ which for each $x'$ minimizes $r(f(x')|x')$. Formally,
#proposition("Baye's Predictor/Risk")[
  The expected risk is minimized at a _Baye's predictor_ $f_ast : Xc -> Yc$ such that, for all $x' in Xc$, $ f_ast (x') in "argmin"_(z in cal(Y)) EE[ell(y, z) | x = x']. $
  The _Baye's risk_ is the risk of a (any) Baye's predictor, written $ cal(R)^ast := EE_(x' tilde p) [inf_(z in cal(Y)) EE[ell(y, z) | x = x']] = EE[ell(y, f_ast (x'))]. $
]

#remark[
  1. Finding an $f_ast$ is an impossible task in practice. Instead, we'll usually assume $f$ takes some parametrized form, and optimize these parameters.
  2. Baye's predictor may not be unique, but all Baye's predcitors have the same risk
  3. Baye's risk is usually nonzero, unless the dependency between $x$ and $y$ is deterministic.
]

#definition("Excess Risk")[
  The _excess risk_ of a predictor $f$ is the value $cal(R)(f) - cal(R)(f_ast) >= 0$.
]

#remark[
  Thus, if we knew the conditional distribution $(y|x)$ for each $x$, the optimal predictor is known. ML can be succinctly be described as dealing with the general case in which we do not know $(y|x)$ for all $x$, and can only work with given samples of data.
]

#example[
  1. (Binary classification) With $cal(Y) := {-1, 1}$ and $ell(y, z) = bb(1)_{y eq.not z}$ the 0-1 loss, we can see that $ f_ast (x') & in "argmin"_(z' in {-1, 1}) P(y eq.not z | x = x') \
               & = "argmax"_(z in {-1, 1}) PP(y = z | x = x') \
               & = cases(
                   1 quad & PP(y = 1 | x = x') > 1/2,
                   -1 & PP(y = 1 | x = x') < 1/2,
                   "anything" & PP(y = 1 | x = x') = 1/2
                 ). $
    Putting $cal(L)(x') := PP(y = 1 | x = x')$, this implies $ cal(R)^ast = EE[min{cal(L)(x), 1 - cal(L)(x)}]. $
    2. (Regression) With $cal(Y) = RR$, $ell(y, z) = (y - z)^2$, we see that $ "argmin"_(z in RR) EE[(y - z)^2 | x = x'] & = "argmin"_(z in RR) {underbrace(EE[(y - EE[y | x= x'])^2 | x = x'], "independent of " z) \
        & quad quad quad quad quad quad quad quad quad + underbrace((z - EE[y | x = x'])^2, "minimize this") } \
      & = EE[y | x = x']. $ Hence, $f_ast (x') = EE[y|x = x']$, and so $ cal(R)^ast = EE_(x' tilde p)[inf_(z in RR) EE[(y - z)^2 | x = x']] = EE_(x') [(y - EE[y|x=x'])^2] quad ("conditional variance") $
]

== Empirical Risk Minimization

We don't know the underlying distributions we work with (of course, otherwise we'd be done), and we need to work with samples, and need to simplify what kind of prediction functions we consider (since we don't know the underlying distribution, thus can't find the Baye's predictor in general).

We'll assume a parametrized family of predictor functions (called our _model_), $ f_(theta) : cal(X) -> cal(Y), quad theta in Theta, $ where $Theta subset RR^d$ typically. Heuristically, as $d$ increases, if we could find the best $f_theta$ predictor for $theta in Theta$, that predictor will approach the Baye's predicotr.

#definition("Empirical risk with respect to a parameter")[
  The _empirical risk w.r.t $theta in Theta$_ is $ hat(R)(f_theta) := 1/n sum_(i=1)^n ell(y_i, f_theta (x_i)). $
  We consider the optimal parameter minimizing this empirical risk as $ hat(theta) in "argmin"_(theta in Theta) hat(R)(f_theta), $ and so our "optimal" prediction function with respect to $Theta$ is $f_(hat(theta))$.
]

#example[
  A typical linear least-squares problem takes this form, $ min_(theta in Theta = RR^d) 1/n sum_(i=1)^n (y_i - theta^T phi(x_i))^2, $ so that here, $f_theta (x) = theta^T phi(x_i)$ and our loss function is the square loss.
]

=== Risk Decomposition

Given a $hat(theta) in Theta$ (not necessarily optimal w.r.t $Theta$), we would like to break down the excess risk of the predictor $f_(hat(theta))$ w.r.t the Baye's predictor to see the difference in error coming from our choice of model (we call this _approximation error,_ i.e. how far our model is from approoximating our true predictor function) versus from the choice of $f_(hat(theta))$ over the "true" best predictor with respect to $Theta$ (as defined in the previous section. This is called the _estimation error_, and should be thought of as how well any underlying optimization algorithm used to find $hat(theta)$ performed compared to the theoretical best).

Mathematically, we can write $ underbrace(cal(R)(f_(hat(theta))) - cal(R)^ast, #underline("Excess Risk") \ "how good our estimator is" \ "from the best possible") &= underbrace({cal(R)(f_(hat(theta))) - inf_(theta in Theta) cal(R)(f_theta)}, #underline("Estimation Error") \ "how good our estimator is compared" \ "to the best the model can do") + underbrace({inf_(theta in Theta) cal(R)(f_theta) - cal(R)^ast}, #underline("Approximation Error") \ "how good our model (theoretically) is" \ "compared to the best possible"). $

Note that the approximation error is due to the modelling choice, and is independent of the specific $f_(hat(theta))$. Vaguely, "as $Theta$ grows, the approximation error should shrink".

The estimation error can further be broken down into three parts; let $theta' in Theta$ be the minimizer of $theta |-> cal(R)(f_(theta'))$ (e.g., $cal(R)(f_(theta')) = inf_(theta in Theta) cal(R)(f_theta)$), then $ underbrace(cal(R)(f_(hat(theta))) - cal(R)(f_(theta')), "Estimation Error") & = {cal(R)(f_(hat(theta))) - hat(cal(R))(f_(hat(theta)))} arrow.l #text(size: 10pt, stack(spacing: .3em, "How good the model risk is", "on data vs true risk of model")) \
#text(size: 9pt, stack(spacing: .3em, underline("Empirical Optimization Error"), "How bad our choice of predictor is", "compared true best in terms", "of performance on the data", [(for $hat(theta)$ )])) arrow.r & quad + {hat(R)(f_(hat(theta))) - hat(R)(f_(theta'))} \
&quad + {hat(R)(f_(theta')) - cal(R)(f_(theta'))} arrow.l #text(size: 10pt, stack(spacing: .3em, "How good the model risk is", "on data vs true risk of model", [(for $theta'$ )])) \
& <= 2 underbrace(sup_(theta in Theta) |cal(R)(f_(theta)) - hat(cal(R))(f_theta)|, "should" arrow.b "as" n arrow.t) + underbrace({hat(R)(f_(hat(theta))) - hat(R)(f_(theta'))}, arrow.t "as" Theta arrow.t \ "("Theta "gets too large to optimize over)"). $

In brief, we expect that as the parameter space $Theta$ _grows_, the esimation error _increases_, but the approximation error _decreases_. But as $n$ (number of samples) increases, we expect the estimation error to decrease (and there is no effect on the approximation error). Thus, there is a subtle interplay between $d := dim(Theta)$ and $n$.

== Statistical Learning Theory

"Statistical learning theory" asks how to provide guarantees of performance of an algorithm on previously unseen data.

We assume we have data $ D_n (p) := {(x_1, y_1), dots, (x_n, y_n)} $ which are assumed to be iid from some unknown distribution $p$ which is part of some family $P$ of distributions.

An algorithm then is a mapping $A$ from $D_n (p)$ to a prediction function $A (D_n (p)) = f : cal(X) -> cal(Y)$. Our goal is to find an algorithm such that the excess risk of the prediction function given by $A$ is "small", in a sense we'll define in the next section.

=== Measures of Performance

#definition("Expected Risk")[
  The _expected risk_ of an algorithm $A$ on sample size $n$ and probability distribution $p$ is the quantity $ EE[cal(R)_p (A(D_n(p)))], $ where the expected value is taken over all possible $n$-size subsets of the training data. We say that an algorithm is _consistent in expectation_ if the above quantity converges, with $p$ fixed, to $cal(R)^ast$ as $n -> infinity$.
]

#definition([Probability Approximately Correct $ast$])[
  We say an algorithm $A$ is Probability Approximately Correct (PAC) if for any given $delta in (0, 1)$ and $epsilon > 0$, there exists $N in NN$ such that for all $n >= N$, $ PP(cal(R)_p (A(D_n (p))) - cal(R)^ast <= epsilon) >= 1 - delta. $
]

=== Notions of Consistency over Classes of Probability distributions

Remark that our definition of consistency in expectation gave no guarantee over rate of convergence, especially not with respect to the specific distribution.

#definition[
  An algorithm is _uniformly consistent_ if for all probability distributions on $(x, y)$, the algorithm is consistent.
]

#definition("Minimax risk")[
  The minimax risk is defined to be, given $cal(X) times cal(Y)$, $ inf_(A : "algorithm") sup_(p in P : \ "class of dists.") {EE[cal(R)_p (A(D_n (p)))] - cal(R)^ast}. $
]

#remark[
  This is hard to evaluate in general, but is easy to upper bound (just fix any $A$ and evaluate the inner supremum, i.e., look at the worst-case performance of the algorithm). Lower bounds are much harder to compute, since they need to hold for any possible algorithm.
]

== "No Free Lunch"

_No, this section is not about SSMU shutting down Midnight Kitchen..._

Here, we make clearer the remarks of the previous section in terms of performance of algorithms for arbitrarily distributed data. Namely, we show that, for a specific loss function and input/output space, for any size of data $n$, we can construct a distribution on our data such that any algorithm we can come up with will perform "poorly" (i.e. it's excess risk is bounded away from 0). Hence, there is no "free lunch", i.e no "easy algorithm" that will work without further assumptions on what our possible probability distributions could be

#proposition(
  "No Free Lunch",
)[Consider a binary classification with $0-1$ loss and with $cal(X)$ infinite. Let $cal(P)$ be the class of all probability distributions on $cal(X) times {0, 1}$. Then, for all $n$ and for all algorithms $A$, $ sup_(p in cal(P)) {EE[cal(R)_p (A(D_n (p)))] - cal(R)^ast} >= 1/2. $]<prop:nofreelunch>

#remark[
  As we'll see in the proof, the bounds we obtain will not give any rate in $n$, asymptotic or not. Indeed, the probability distribution for each $n$ will crucially depend on a certain parameter $n$ being much larger than $n$. Indeed, we can state (but will not prove) the much stronger statement as follows.
]

#theorem("Devroye, '96")[
  Consider the same setup as @prop:nofreelunch. Then, for any decreasing sequence $a_n -> 0$ with $a_1 <= 1/16$, then for any algorithm $A$, there exists a $p in cal(P)$ such that for all $n >= 1$, $ EE[cal(R)_p (A(D_n (p)))] - cal(R)^ast >= a_n. $
  I.e., the supremum over $cal(P)$ has excess risk going to zero _arbitrarily slowly._
]
#proof[(of @prop:nofreelunch)
  Fix $n in NN$ and assume wlog $NN subset cal(X)$ (by relabelling otherwise). Let $k in ZZ_+$, and, given a $k$-length vector $r =(r_1, dots, r_k) in {0, 1}^k$, define a joint probability distribution $p$ on $(x, y)$ such that $ PP(x = j, y = r_j) = 1/k, quad j = 1, dots, k. $
  In particular, in this case, $y$ is a deterministic function of $x$; given $x = j$, $y = r_j$. In particular, this means $cal(R)^ast = 0$.

  Denote $hat(f)_(D_n) := A(D_n (p))$ as the classifier under $p$ given by algorithm $A$, and write $S(r) := EE[cal(R)_p (hat(f)_(D_n))]$ as the expectation of the expected risk under this given probability distribution of the classifier given by the algorithm $A$ for the given vector $r in {0, 1}^k$. We aim to pick $r$ such that we maximize this quantity; if we can pick $r$ such that this quantity is larger than $1/2$, we'll be done (why?).

  This is hard to do directly, so we'll instead lower bound the max probabilistically; given any distribution $q$ on ${0, 1}^k$, we certainly have $ max_(r in {0, 1}^k) S(r) >= EE_(r tilde q) [S(r)]. $ Thus, we'll design some $q$ so that this quantity on the right is large. Specifically, let $q$ be uniform on ${0, 1}^k$, i.e. each $r = (r_1, dots, r_k)$ a vector of $r_j$'s each independent, unbiased, Bernoulli r.v.'s. Then, $ EE_(r tilde q) [S(r)] = PP(hat(f)_(D_n) (x) eq.not y) = PP(hat(f)_(D_n) (x) eq.not r_x), $ which follows from the fact that we can write $ EE[S(r)] & = EE_r [EE[cal(R)_p (hat(f)_(D_n))]] \
           & = EE_r [ EE_p [EE_(x, y) [ell(x, hat(f)_(D_n) (y))]]] \
           & =EE_(r, p, (x, y)) [bb(1)_(y eq.not hat(f)_(D_n) (x))] = PP(y eq.not hat(f)_(D_n) (x)), $ just by unpacking all of the definitions. Continuing from above, we can write then $ EE_(r tilde q) [S(r)] & = EE_p [PP(hat(f)_(D_n) (x) eq.not r_x) | x_(1), dots, x_n ; r_(x_1), dots, r_x_n] quad ("total expectation") \
  &>= EE[PP(hat(f)_(D_n) (x) eq.not r_x, x eq.not x_1, dots, x_n) | x_1, dots]. $ By Baye's rule, $ PP(hat(f)_(D_n) (x) eq.not r_x, x eq.not x_1, dots, x_n | x_1, dots, x_n) = underbrace(PP(hat(f)_(D_n) (x) eq.not r_x | x eq.not x_1, dots, x_n\; x_1, dots, x_n), = 1/2) dot PP(x eq.not x_1, dots, x_n | x_1, dots, x_n), $ since, supposing we didn't observe $x$, $x$ has equal probability of being labeled $0,1$. Thus, all together, $ EE[S(r) & >= 1/2 EE[PP(x in.not {x_1, dots, x_n} | x_1, dots, x_n)] \
          & = 1/2 PP(x in.not {x_1, dots, x_n}) \
          & = 1/2 EE[PP(x in.not {x_1, dots, x_n} | x)] \
          & = 1/2 EE[product_(i=1)^n PP(x eq.not x_i | x)] quad ("independence") \
          & = 1/2 (1 - 1/k)^n. $ We have $n$ fixed; as $k -> infinity$, this quantity $-> 1/2$, proving the result.
]

= Linear Least Squares

== Framework
_Goal:_ Consider $f_theta : cal(X) -> cal(Y) subset RR$, for some parameter $theta in Theta subset RR^d$, and minimize the empirical risk $ min_(theta in Theta) 1/n sum_(i=1)^n (y_i - f_theta (x_i))^2. $ Specifically, we'll study when $f_theta$ is linear in $theta$, but not necessarily $x$, i.e. $ f_theta (x) := sum_(i=1)^d a_i (x) theta_i = phi(x)^T theta, $ where $phi(x) = (a_1, dots, a_d)^T (x) in RR^d$. Our goal then will be to compute $ min_(theta in RR^d) {hat(cal(R)) (theta) := 1/n sum_(i=1)^n (y_i - phi(x_i)^T theta)^2}. $ or equivalently, writing $y = (y_1, dots, y_n)^T$ and $ Phi(x) = vec(dots.v, – phi(x_i)^T –, dots.v) in RR^(n times d), $ then $ hat(R)(theta) = 1/n norm(y - Phi(x) theta)^2. $
== Ordinary Least Squares

Assume $Phi$ from above has full column rank, i.e. $d <= n$ (we say the problem then is "overdetermined/underparametrized"). This implies $Phi^T Phi in RR^(d times d)$ is invertible.

#proposition("OLS")[
  When $Phi$ has rank $d$, the minimizer of what we now call the _ordinary least squares problem_ (OLS) is unique, and given by $ hat(theta) = (Phi^T Phi)^(-1) Phi^T y. $

  In particular, we call the relation $ Phi^T Phi hat(theta) = Phi^T y $ the _normal equations_.
]

#proof[
  By homework (this is just a quadratic).
]


== Statistical Analysis of OLS

There are two main assumptions on OLS we will study:
1. _Random design setting:_ assume both the inputs and outputs are random
2. _Fixed design setting:_ assume the inputs are fixed, but the outputs are random. In this case, $phi$ is deterministic, and thus our goal is to minimize $ cal(R)(theta) = EE_y [1/n sum_(i=1)^n (y_i - phi(x_i)^T theta)^2]. $

== Fixed Design
We assume the following:
1. $Phi$ is deterministic, and $hat(Sigma) := 1/n Phi^T Phi$ is invertible
2. $exists theta_ast in RR^d$ such that $y_i = phi(x_i)^T phi_ast + epsilon_i$
3. $epsilon_i$'s are independent with mean zero and variance $sigma^2$. We define $epsilon := (epsilon_1, dots, epsilon_n)^T in RR^n$.

#proposition("Risk Decomposition of OLS - Fixed Design")[
  Under the linear model and the assumptions above, for $theta in RR^d$, $cal(R)^ast = sigma^2$ and the excess risk is given by  $ cal(R)(theta) - cal(R)^ast = norm(theta - theta_(ast))^2_(hat(theta)) = (theta - theta_ast)^T hat(Sigma) (theta - theta_ast). $ If $hat(theta)$ a random variable, then $ EE_(hat(theta)) [cal(R)(hat(theta)) - cal(R)^ast] =underbrace(norm(EE[hat(theta)] - theta_ast)^2_(hat(Sigma)), "bias") + underbrace(EE[norm(hat(theta) - EE[hat(theta)])^2_(hat(Sigma))], "variance"). $
]<thm:riskdecompols>

#remark[Since $y$ has some noise, it makes sense to assume $hat(theta)$ could be random in its own right.]

#proof[
  Using $y = Phi theta_ast + epsilon$, we readily see $ cal(R)(theta) & = EE_y [1/n norm(y - Phi theta)_2^2] \
  & = EE_epsilon [1/n norm(Phi (theta_ast - theta) + epsilon)^2] \
  &= 1/n EE_epsilon [underbrace(norm(Phi (theta_ast - theta))^2_2, perp epsilon) + underbrace(norm(epsilon)_2^2, arrow.squiggly n sigma^2) + underbrace(2 (Phi (theta_ast - theta))^T epsilon, "mean zero")] \
  &= 1/n norm(Phi (theta_ast - theta))_2^2 + sigma^2 \
  &= sigma^2 + (theta_ast - theta)^T underbrace((Phi^T Phi)/n, = hat(Sigma)) (theta_ast - theta) \
  &= sigma^2 + norm(theta_ast - theta)^2_(hat(Sigma)). $ It's clear that this is minimized at $theta = theta_ast$ (uniquely, since $hat(Sigma)$ invertible), which thus has risk $cal(R)_ast = sigma^2$.

  Suppose now $hat(theta)$ random. Then, $ EE[cal(R)(hat(theta)) - cal(R)^ast] & = EE[norm(hat(theta) - theta_ast)_(hat(Sigma))^2 plus.minus EE[hat(theta)]] \
  & = EE[norm(hat(theta) - EE[hat(theta)])_(hat(Sigma))^2] + underbrace(2 EE[(hat(theta) -EE[hat(theta)])^T hat(Sigma) (EE[hat(theta)] - theta_ast)], = 0) + EE[norm(EE[hat(theta)] - theta_ast)_(hat(Sigma))^2]. $
]

// TODO
=== Statistical Properties of the OLS Estimator

Recall the OLS estimator, $ hat(theta) = (Phi^T Phi)^(-1) Phi^T y = hat(Sigma)^(-1) (1/n Phi^T y), quad y = Phi theta_ast + epsilon, $ where the only randomness comes from $epsilon$.

#proposition("Estimation Properties of OLS")[
  The OLS estimator $hat(theta)$ has the following properties:
  1. $EE[hat(theta)] = theta_ast$, i.e. $hat(theta)$ is unbiased
  2. $"Var"(hat(theta)) = EE[(hat(theta) - theta_ast) (hat(theta) - theta_ast)^T] = (sigma^2\/n) hat(Sigma)^(-1)$, where $hat(Sigma)^(-1)$ is often called the _precision matrix_.
]

#proof[
  Since $EE_epsilon [y] = EE[Phi theta_ast + epsilon] = Phi theta_ast$, we find $ EE[(Phi^T Phi)^(-1) Phi^T y] = (Phi^T Phi)^(-1) Phi^T Phi theta_ast = theta_ast, $ since $Phi$ is deterministic.

  Next, for the variance, compute $ hat(theta) - theta_ast = (Phi^T Phi)^(-1) Phi^T epsilon, $ so that $ "Var"(hat(theta)) & = EE[(Phi^T Phi)^(-1) Phi^T epsilon ((Phi^T Phi)^(-1) Phi^T epsilon)^T] \
                    & = EE[(Phi^T Phi)^(-1) Phi^T epsilon epsilon^T Phi (Phi^T Phi)^(-1)] \
                    & = sigma^2 (Phi^T Phi)^(-1) Phi^T Phi (Phi^T Phi)^(-1) \
                    & = sigma^2 (Phi^T Phi)^(-1) = sigma^2/n hat(Sigma)^(-1), $ as claimed.
]

#proposition("Risk of OLS")[
  The excess risk of the OLS estimator is $ EE[cal(R)(hat(theta)) ] - cal(R)^ast = sigma^2 d/n. $
]

#proof[
  We plug in the previous result to @thm:riskdecompols. We find $ EE[cal(R)(hat(theta))] - cal(R)^ast & = EE[norm(hat(theta) - theta_ast)_(hat(Sigma))^2] \
                                      & = EE[(hat(theta) - theta_ast)^T hat(Sigma) (hat(theta) - theta^ast)] \
                                      & = EE[tr((hat(theta) - theta_ast)^T hat(Sigma) (hat(theta) - theta^ast))] \
                                      & = tr(EE[hat(Sigma) (hat(theta) - theta_ast) (hat(theta) - theta_ast)^T]) \
                                      & = tr(EE[hat(Sigma) sigma^2/n hat(Sigma)^(-1)]) \
                                      & = sigma^2/n tr(I_d) = sigma^2 d/n, $ where we use the linearity of the trace, and the fact that $tr(A B) = tr(B A)$.
]

_Observations:_

- In fixed design setting, OLS thus leads to unbiased estimation with excess risk of $sigma^2 d/n$.
- For excess risk being small compared to $sigma^2$, need $d/n$ to be small. This seems to exclude _high-dimensional problems_ where $d$ is close to $n$ (let alone $d > n$ or $d >> n$). Regularization (ridge) can help.

== Ridge Least-Squares Regression

When $d > n$, $Phi^T Phi$ is no longer invertible, and so the normal equations admit a whole subspace of solutions. We have two main solutions to this:

1. _Dimension reduction:_ aims to replace the feature vector $phi(x)$ with another feature vector of lower dimension
2. _Regularization:_ adds a term to the least-squares objective function, (i.e. $ell^1$-penalty, which leads to _lasso_, or $ell^2$-penalty, which leads to _ridge_)

#definition("Ridge Least Squares Regression Estimator")[
  For a regularization parameter $lambda > 0$, we define the _ridge least squares estimators_ $hat(theta)_lambda$ as the minimizer of $ min_(theta in RR^d) {1/n norm(y - Phi theta)_2^2 + lambda norm(theta)_2^2} quad "(ridge regularization)". $
]

We can express the ridge regression estimator in closed form; we don't even need $Phi^T Phi$ to be invertible as in the OLS case.

#proposition[
  With, as usual, $hat(Sigma) = 1/n Phi^T Phi in RR^(d times d)$, then $ hat(theta)_lambda = 1/n (hat(Sigma) + lambda I)^(-1) Phi^T y. $
]

#remark[In particular, when $lambda = 0$, we recover the OLS estimator assuming $hat(Sigma)$ invertible.]

#proof[
  This is essentially the same as the proof for the OLS; one recognizes that we have a quadratic in $theta$. The invertibility of $hat(Sigma) + lambda I$ follows from the fact that $hat(Sigma)$ positive semidefinite, and thus has nonnegative eigenvalues, and thus $hat(Sigma) + lambda I$ has strictly positive eigenvalues and is thus invertible.
]

=== Statistical Properties of Ridge Least Squares Estimator

#proposition[The ridge least squares estimator, under the fixed-design assumptions, is equal to $hat(theta)_lambda = 1/n (hat(Sigma) + lambda I)^(-1) Phi^T y$ has excess risk $ EE[cal(R)(hat(theta)_lambda)] - cal(R)^ast = underbrace(lambda^2 theta_ast^T (hat(Sigma) + lambda I)^(-2) hat(Sigma) theta_ast, "bias") + underbrace(sigma^2/n tr(hat(Sigma)^2 (hat(Sigma) + lambda I)^(-2))., "variance") $]

_Observations:_
- The result above gives a bias/variance decomposition of the excess risk; this is related to the approximation/estimation error decomposition of the risk.

The bias term is part of the approximation error - it has the main influences of $lambda$, which only effects $theta$ and is thus really a modelling assumption. The variance term captures the "noise" ($sigma^2$ only appears here), and is really about estimation error.

- _Bias:_ as $lambda$ $arrow.t$, bias $arrow.t$ and is equal to zero if $lambda = 0$ (and $hat(Sigma)$ is invertible, of course). In particular, the bias grows like $lambda^2$, and as $lambda -> infinity$, the bias approximates $lambda^2 dot theta_ast^T hat(Sigma)^(-1) theta_ast$ (which is independent of $n$).

- _Variance_ as $lambda$ $arrow.t$, the variance $arrow.b$ and when $lambda = 0$, the variance is $sigma^2/n$; this depends on $n$.

In particular, since the excess risk is the sum of these two, we expect a kind of parabolic relationship between excess risk and $lambda$, implying the existence of some optimal $lambda$.

- The quantity $tr(hat(Sigma)^2 (hat(Sigma) + lambda I)^(-2))$ is called the _degrees of freedom_, and is considered as an "implicit number of parameters".


- As $lambda -> 0$, $hat(theta)_lambda$ converges to the OLS estimator

- $lambda = 0$ is not usually the optimal choice (i.e. yielding the best excess risk); we want to bias our estimator in general

=== Choice of $lambda$

Can we tune $lambda$ to achieve a better bound than our OLS?

#proposition("Choice of regularization parameter")[
  Let $ lambda_ast = (sigma dot tr(hat(Sigma))^(1\/2))/(norm(theta_ast)_2 sqrt(n)). $ Then, $ EE[cal(R)(hat(theta)_(lambda_ast))] - cal(R)^ast = (sigma dot "tr"(hat(Sigma))^(1\/2) norm(theta_ast)_2)/sqrt(n). $
]

#proof[
  Recall that the eigenvalues of $lambda I + hat(Sigma)$ are of the form $lambda + mu$ for $mu$ an eigenvalue of $hat(Sigma)$. In addition, we will need to use the fact that $tr(A B) <= lambda_max (A) tr(B)$ (special case of Holder's inequality).

  We need first a bound on the eigenvalues of the matrix $(hat(Sigma) + lambda I)^(-2) lambda hat(Sigma)$. Let $mu$ be an eigenvalue of $hat(Sigma)$, so $mu + lambda$ an eigenvalue of $hat(Sigma) + lambda I$. We know $(mu + lambda)^2 >= 2 lambda mu$ (AM-GM), and hence $lambda mu (mu + lambda)^(-2) <= 1/2$ and so the eigenvalues of $(hat(Sigma) + lambda I)^(-2) lambda hat(Sigma)$ are always $<= 1/2$, i.e. $ lambda_max {(hat(Sigma) + lambda I)^(-2) hat(Sigma)} <= 1/2. $

  Therefore, we can bound the bias $ "bias" = lambda theta_ast^T (hat(Sigma) + lambda I)^(-2) lambda hat(Sigma) theta_ast & <= lambda lambda_max {(hat(Sigma) + lambda I)^(-2) lambda hat(Sigma)} norm(theta_ast)_2^2 <= lambda/2 norm(theta_ast)_2^2. $

  Similarly, we can bound the variance, $ "variance" = sigma^2/n tr(hat(Sigma)^2 (hat(Sigma) + lambda I)^(-2)) &= sigma^2/(n lambda) tr(hat(Sigma) [lambda hat(Sigma) (hat(Sigma) + lambda I)^(-2)]) \
  & <= (sigma^2)/(n lambda) tr(hat(Sigma)) lambda_(max) {lambda hat(Sigma) (hat(Sigma) + lambda I)^(-2)} \
  & <= (sigma^2)/(2 n lambda) tr(hat(Sigma)). $ Together, these imply that, for any $lambda > 0$, $ EE[cal(R)(hat(theta)_lambda)] - cal(R)_ast &= "bias" + "variance" <= lambda/2 norm(theta_ast)_2^2 + sigma^2/(2 n lambda) tr(hat(Sigma)). $ We optimize the right-hand side, which is of the form $f(lambda) = a lambda + b/lambda$. One verifies that the minimum is $lambda = sqrt(b/a)$, which has value $f(sqrt(b/a)) = 2 sqrt(a b)$. Since $a = norm(theta_ast)_2^2/2$ and $b = sigma^2/(2 n) tr(hat(Sigma))$, this implies $ lambda_ast = (sigma tr(hat(Sigma))^(1\/2))/(sqrt(n) norm(theta_ast)_2), $ as claimed, and similarly, we get the actual excess risk of $hat(theta)_(lambda_ast)$ upon plugging in the appropriate values.
]

#remark[
  1. Let $R = max_(i in [n]) norm(phi(x_i))_2$. Then $ tr(hat(Sigma)) = sum_(j=1)^d hat(Sigma)_(j j) = 1/n sum_(i=1)^n sum_(j=1)^d (phi(x_i)_j)^2 = 1/n sum_(i=1)^n norm(phi(x_i))_2^2 <= R^2. $ Namely, the dimension $d$ of the parameter space plays no role in the excess risk, and thus $d$ could be infinite, provided $R$ and $norm(theta_ast)^2_2$ are finite (normally, $R$ grows with $d$, so need these extra assumptions).

  2. We can compare this to the excess risk of the OLS estimator, which we found to be $sigma^2 d/n$. We see that
  - With $lambda_ast$, our excess risk of ridge goes to zero as $n -> infinity$ like $1/sqrt(n)$, which is slower than that of OLS (which goes like $1/n$)
  - However, the ridge estimator has risk proportional to $sigma$ while the OLS is proportional to $sigma^2$, i.e. OLS has a higher dependency on the noise variance

  3. $lambda_ast$ involves constants we don't know, i.e. $sigma$, $norm(theta_ast)_2$ - in practice, we have to find $lambda_ast$ by trial and error.

  4. $lambda_ast$ is not necessarily the best choice in the sense of minimizing the excess risk, since we found it by optimizing an upper bound of the excess risk.

  5. $lambda$ is an example of a "hyperparameter" - something a user must choose. It should not be taken as an _absolute_ - rather, it should be consider as a "guide" as to how to pick $lambda$.
]




== Random Design Analysis

Here, we assume the following:
1. Both $x$ and $y$ are random and each pair $(x_i, y_i)$ from a probability distribution $p$ on $cal(X) times RR$
2. $exists theta_ast in RR^d$ s.t. $y_i = phi(x_i)^T theta_ast + epsilon_i$
3. $epsilon_i$'s are independent from $x_j$'s and each other, and are mean zero, variance $sigma^2$.


In particular, remark that under these assumptions, $EE[y_i | x_i] = phi(x_i)^T theta_ast$.


#proposition[
  Under the above assumptions, for any $theta in RR^d$, we have $ cal(R)(theta) - cal(R)^ast = norm(theta - theta_ast)^2_Sigma, quad Sigma := EE[phi(x) phi(x)^T], $ and $cal(R)^ast = sigma^2$.
]

#proof[
  $
    cal(R)(theta) & = EE_(x, y, epsilon) [(y - theta^T phi(x))^2] \
    & = EE[(phi(x)^T theta_ast + epsilon - theta^T phi(x))^2] \
    &= EE[(phi(x)^T (theta_ast - theta) - epsilon)^2] \
    &= EE[(theta - theta_ast)^T phi(x) phi(x)^T (theta - theta_ast) + epsilon^2 - 2 epsilon phi(x_0)^T (theta - theta_ast)] \
    &= EE_x EE_epsilon [[dots.c | x]] \
    ("independence")quad&= EE[epsilon^2] + EE[(phi(x)^T (theta - theta_ast))^2] \
    &= sigma^2 + (theta - theta_ast)^T Sigma (theta - theta_ast).
  $
]


#proposition[
  Under the above assumptions, assume $hat(Sigma) = 1/n sum_(i=1)^n phi(x_i) phi(x_i)^T = 1/n Phi^T Phi$ is invertible. Then, the expected excess risk of the OLS estimator is given by $ sigma^2/n EE[tr(Sigma hat(Sigma)^(-1))]. $
]

#remark[
  We see $Sigma$ as the "expected covariance matrix" and $hat(Sigma)$ as the "empirical covariance matrix"; in particular, these two were equal in the fixed-design case (as our inputs were deterministic) and thus the above quantity becomes $ sigma^2/n EE[tr(I_d)] = d/n sigma^2. $
]

#proof[
  Recall that $hat(sigma) = 1/n hat(Sigma)^(-1) Phi^T y$, which, by assumption on the $y$'s, becomes $ hat(theta) & = 1/n hat(Sigma)^(-1) Phi^T (Phi theta_ast + epsilon) = theta_ast + 1/n hat(Sigma)^(-1) Phi^T epsilon. $ By the previous proposition, then, it follows that $ EE[cal(R)(hat(theta)) - cal(R)^ast] &= EE[(1/n hat(Sigma)^(-1) Phi^T epsilon)^T Sigma (1/n hat(Sigma)^(-1) Phi^T epsilon)] \
  &= 1/n^2 EE[tr(Sigma (hat(Sigma)^(-1) Phi^T epsilon epsilon^T Phi hat(Sigma)^(-1)))] quad "(i)" \
  &= sigma^2/n^2 EE[tr(Sigma hat(Sigma)^(-1) underbrace(Phi^T Phi hat(Sigma)^(-1), = n I))] quad "(ii)" \
  &= sigma^2/n EE[tr(Sigma hat(Sigma)^(-1))]. $ In (i) we use the fact that for any real matrices $A, B$, $tr(A B) = tr(B A)$; in particular, here this case, $A B in RR$ so that $A B = tr(A B)$ (where $A, B$ are the appropriate matrices above). In (ii) we use the linearity of the trace, as well as the fact that, by conditioning on $x$ first and using independence of $epsilon, x$, we can factor out $EE[epsilon epsilon^T] = n sigma^2$.
]

=== Gaussian Design

Here, we briefly study what more we can say in the case that $phi(x) tilde cal(N)(0, Sigma)$ for some $Sigma in RR^(d times d)$. We can write $ phi(x) = Sigma^(1\/2) hat(Z), quad hat(Z) tilde cal(N)(0, I_d). $

Generating $n$ (independent) $hat(Z) in RR^(n times d)$, we then form the random matrix $ Z := vec(– hat(Z)_1^T –, dots.v, – hat(Z)_n^T –) in RR^(n times d). $ This gives $ Z Sigma^(1\/2) = Phi in RR^(n times d) => hat(Sigma) = 1/n Phi^T Phi = 1/n Sigma^(1\/2) Z^T Z Sigma^(1\/2). $ Thus, apply the "trace trick" from the previous proposition again, we find that $ EE[tr(Sigma hat(Sigma)^(-1))] = n EE[tr(Sigma (Sigma^(-1/2) (Z^T Z)^(-1) Sigma^(-1\/2)))] = n EE[tr((Z^T Z)^(-1))] = (n d)/(n - d - 1), $ which implies the excess risk $approx d/n sigma^2$ (this equality above uses the fact that much is known about the spectral properties of the $(Z^T Z)^(-1)$, which we won't discuss here).
