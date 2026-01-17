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
  We say an r.v. $X$ is _sub-Gaussian_ if there exists $tau in RR_+$ such that $ EE[exp(s(X - EE[X]))] <= exp(tau^2 s^2), quad forall s in RR. $ We define the _sub-Gaussian norm_ by $ norm(X)_(psi_2) := inf{k >= 0 : EE[exp(X^2/k^2)] <= 2}, $ i.e. the "best" sub-Gaussian parameter for $X$.
]
#remark[
  Interpretation: $X$ has tails decaying as fast (or faster) than a Gaussian.
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
                   -1 & PP(y = 1 | x = x') < 1/2
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
