// ! external
#import "../typst/notes.typ": *
// #import "/documents/notes/typst/notes.typ"
#import "../typst/shortcuts.typ": *

// ! configuration
#show: doc => conf(
  course_code: "MATH574",
  course_title: "Dynamical Systems",
  subtitle: "",
  semester: "Winter 2025",
  professor: "Prof. Antony Humphries",
  doc
)
#set align(left)

#pagebreak()

= Examples of Dynamical Systems
Roughly speaking, a dynamical system is a system that evolves in time, with common examples being a differential equation, in the continuous case, or a map, in the discrete case.

// TODO
// - In one dimension, dynamics are very limited for ODEs

#example("The Logistic Map")[]

= Existence-Uniqueness Theory

#definition("Lipschitz")[
  We say a function $f : RR^p -> RR^p$ is Lipschitz on $B subset.eq RR^p$ if there is a constant $L > 0$ such that $||f(x) - f(y)|| <= L ||x - y||$ for every $x, y in B$. We call $L$ a "Lipschitz" constant. It is certainly not unique in general.

  We say $f$ _globally Lipschitz_ if it is Lipschitz on $B = RR^p$, and $f$ _locally Lipschitz_ if $f$ Lipschitz on every bounded domain $B subset.eq RR^p$ (note: the $L$ will in general depend on the domain).
]

#theorem[Let $f : RR^p -> RR^p$ be a locally Lipschitz function. Then, there exists a unique solution to the initial value problem $dot(u) = f(u), u(0) = u_0$ on some interval $t in (-T_1 (u_0), T_2 (0))$, where $-T_1 (u_0) < 0 < T_2 (u_0)$ and
- either  $T_2 (u_0) = +infinity$ or $||u(t)|| -> infinity$ as $t -> T_2 (u_0)$, and
- either $T_1 (u_0) = infinity$ or $||u(t)|| -> -infinity$ as $t -> - T_1 (u_0)$.

Heuristically, this first condition states that either our solution exists for all (forward) time after $-T_1 (u_0)$, or it blows up in finite time, with a similar interpretation for the second, going backwards.
]

#proposition[Let $dot(u) = f(u)$ where $f$ locally Lipschitz. Let $B subset.eq RR^p$ be a bounded subset such that initial conditions $u_0, v_0 in B$ define solutions $u(t), v(t)$ with $u(t), v(t) in B$ for all $t in [0, T]$. Let $L$ be a Lipschitz constant for $f$ on $B$. Then, $
e^(-L t) ||u_0 - v_0|| <= ||u(t) - v(t)|| <= e^(L t) ||u_0 - v_0|| wide forall t in [0, T].
$ This provides a bound on how quickly solutions grow, decay in $B$.
]

#corollary[Let $f$ locally Lipschitz and $u_0 eq.not v_0$. Then, $u(t) eq.not v(t)$ for all time such that the solutions both exist.]

= Limit Sets and the Evolution Operator

We state definitions in this section first for ODEs, but they generalize.

#definition("Evolution Operator")[
  Given $dot(u) = f(u)$, the _evolution operator_ is the map $
  S(t) : RR^p -> RR^p, wide t >= 0
  $ such that $u(t) = S(t) u_0$.

  Such a map also defines a _semi-group_ ${S(t) : t >= 0}$ under composition, namely it is closed under repeated composition and this operator is associative.

  For $B subset.eq RR^p$ define $
  S(t) B := union.big_(u in B) S(t) u = {u(t) = S(t) u_0 : u_0 in B}.
  $
]

#definition("Forward/Positive Orbit")[
  We define the _forward orbit_ of a point $u_0$ as $
  Gamma^(+) (u_0) := union.big_(t >= 0) S(t) u_0,
  $ i.e. the set of all points $u_0$ may "visit" as time increases.
]

#definition("Backwards/Negative Orbit")[
  Similarly, define a _backwards orbit_ (if one exists) $
  Gamma^- (u_0) := {u(t) : t <= 0},
  $ s.t. $forall t <= s <= 0 , S(-t) u(t) = u_0$ and $S(s - t) u(t) = u(s)$. 
]
Note that a negative orbit won't be unique in general, eg in maps, periodic points may multiple preimages.
#definition("Complete Orbit")[
  If a negative orbit for $u_0$ exists, define the _complete orbit_ through $u_0$ as $
  Gamma(u_0) := Gamma^(+) (u_0)
 union  Gamma^(-) (u_0).
  $
]

Notice that if $v in Gamma (u_0)$, then $Gamma (v) = Gamma (u_0)$; namely a complete orbit through $v$ exists.


#definition("Invariance")[The set $B$ is said to be _positively invariant_ if $S(t) B subset.eq B$ for all $t >= 0$. Similarly, $B$ is said to be _negatively invariant_ if $B subset.eq S(t) B$ for all $t >= 0$.
]

#definition([$omega$-limit sets])[
  A point $x in RR^p$ is called an _$omega$-limit point_ of $u_0$ if there exists a sequence ${t_n}$ with $t_n -> infinity$ such that $S(t_n) u_0 -> x$ as $n->infinity$. The set of all such points for an initial condition $u_0$ is denoted $omega(u_0)$, and called the $omega$-limit set of $u_0$.

  Given a bounded set $B$, the $omega$-limit set of $B$ is defined as $
  omega(B) := {x in RR^p : exists t_n -> infinity, y_n in B "s.t." S(t_n)y_n -> x}.
  $
]

#remark[
  In general, $omega(B)$ is _not_ the union of $omega$-limit sets of points in $B$.
]

#theorem[
  For any $u_0 in RR^p$, $
  omega(u_0) = sect.big_(s >= 0) overline(union.big_(t >= s) {S(t) u_0}),
  $ and similarly for any bounded $B subset.eq RR^p$, $
  omega(B) = sect.big_(s >= 0) overline(union.big_(t >= s) S(t) B).
  $
]


#definition([$alpha$-limit set])[
  A point $x in RR^p$ is called an _$alpha$-limit point_ for $u_0 in RR^p$ if there exists a negative orbit through $u_0$ and a sequence ${t_n}$ with $t_n -> - infinity$ such that $u(t_n) -> x$. The set of all such points for $u_0$ is denoted $alpha(u_0)$.
]

#theorem[
  If $Gamma^+ (u_0)$ bounded, then $omega(u_0)$ is a non-empty, compact, invariant, connected set.
]

#definition("Attraction")[
  We say a set $A$ _attracts_ $B$ if for every $epsilon > 0$, there is a $t^ast = t^ast (epsilon, A, B)$ such that $S(t) B subset.eq N(A, epsilon)$ for every $t >= t^ast$, where $N(A, epsilon)$ denotes the $epsilon$-neighborhood of $A$.

  A compact, invariant set $A$ is called an _attractor_ if it attracts an open neighborhood of itself, i.e. $exists epsilon > 0$ such that $A$ attracts $N(A, epsilon)$.

  A _global attractor_ is an attractor that attracts every bounded subset of $RR^p$.
]

#theorem("Continuous Gronwall Lemma")[
  Let $z(t)$ be such that $dot(z) <= a z + b$ for some $a eq.not 0, g in RR$ and $z(t) in RR$. Then, $forall t >= 0$, $
  z(t) <= e^(a t) z(0) + b/a (e^(a t) - 1).
  $
]

#theorem([$omega$-limit sets as attractors])[
  Assume $B subset.eq RR^p$ is a bounded, open set such that $S(t) B subset.eq overline(B) forall t>0$. Then, $omega(B) subset.eq B$, and $omega(B)$ is an attractor, which attracts $B$. Furthermore, $
  omega(B) = sect.big_(t >= 0) S(t) B.
  $
]

#definition("Dissipative")[
  A dynamical system is called _dissipative_ if there exists a bounded set $B$ such $forall A$ bounded, there exists a $t^ast = t^ast (A) > 0$ such that $S(t) A subset.eq B$ $forall t >= t^ast$. We then call such a $B$ an _absorbing set_. 
]

#remark[
  $B$ absorbing $=>$ $omega(A) subset.eq omega(B)$. Moreover, $omega(B)$ attracts $A$ for every bounded set $A$. I.e., $omega(B)$ is a global attractor.
]

= Stability Theory

#definition("Stable/Unstable Manifolds")[
If $u^ast$ a steady state of a dynamical system, the _stable manifold_ of $u^ast$ is defined as the set $
{u in RR^p : omega(u) = u^ast},
$ and similarly, the _unstable manifold_ is defined $
{u in RR^p : Gamma^(-) (u) exists "and" alpha(u) = u^ast}.
$
]

#definition("Lyapunov Stability")[
  A steady state $u^ast$ is called _Lyapunov stable_ if $forall epsilon > 0$, there exists a $delta > 0$ such that if $||u^ast - v|| < delta$, then $||S(t) v - u^ast|| < epsilon$ for all time $t >= 0$.
]

#definition("Quasi-Asymptotically Stable")[
  A steady state $u^ast$ is called _Quasi-asymptotically stable_ (qas) if there exists a $delta > 0$ such that if $||u - u^ast|| < delta$, $lim_(t -> infinity) ||S(t)u - u^ast|| = 0$. 
]

#definition("Asymptotically Stable")[
  A steady state $u^ast$ is called asymptotically stable if it is both Lyapunov stable and qas.
]

#definition("Linearization")[
 Consider a dynamical system $dot(u) = f(u)$, where $f(u^ast) = 0$. Let $v(t) = u(t) - u^ast$, then, $dot(v) = f(u^ast + v)$, and $v^ast = 0$ corresponds to a fixed point. Taylor expanding $dot(v)$, we find $
 dot(v) &= f(u^ast + v) \
 &= f(u^ast) + J_f (u^ast) v + cal(O)(||v||^2) \ 
 &= J_f (u^ast) dot v + cal(O)(||v||^2),
 $ where $J_f (u^ast)$ the Jacobian matrix of $f$ evaluated at $u^ast$. The linear system $
 dot(v) = J_f (u^ast) v
 $ is called the _linearization_ of $dot(u) = f(u)$ at $u^ast$.
]

#proposition[
  The general solution to the linearized system $
  dot(v) = J v, wide v(0) = v_0,
  $ is $
  v(t) = e^(t J) dot v_0 ,
  $ where $e^(dot )$ the matrix exponential defined by the (always convergent) series $
  e^(M) = sum_(j=0)^infinity M^j/j!.
  $
]

Suppose $dot(v) = J v$ and $J$ complex diagonlizable with eigenvalues $lambda_1, dots, lambda_n$. Then, $J$ conjugate to the diagonal matrix $Lambda$ with diagonal entries equal to the eigenvalues, namely $
J = P Lambda P^(-1).
$ It follows that $
v(t) = P e^(t Lambda) P^(-1) v_0.
$ Equivalently (changing coordinates), letting $w (t) = P^(-1) v(t)$, we find $
w(t) = e^(t Lambda) w(0),
$ noting that now, since $Lambda$ diagonal, $
e^(t  Lambda) = mat(e^(t lambda_1), "", ""; "", dots.down, ""; "", "", e^(t lambda_n)).
$

#definition("Linear Stable, Unstable, Centre Manifolds")[
  Supposing $0$ a steady state and $J_f (0)$ complex diagonalizable, define respectively the _linear_ stable, unstable, and centre manifolds:  $
  E^s (0) &:= {u | u "spanned by eigenvectors with" Re(lambda) < 0} \ 
  E^u (0) &:= {u | u "spanned by eigenvectors with" Re(lambda) > 0} \ 
  E^c (0) &:= {u | u "spanned by eigenvectors with" Re(lambda) = 0}.
  $
  Notice that if $u_0 in E^s (0)$, then the corresponding solution with initial condition $u_0$, $u(t)$, converges to $0$ as $t-> infinity$, with similar conditions for $u_0 in E^u (0)$.
]

#definition("Hyperbolic")[
  A steady state $u^ast$ is called _hyperbolic_ if $J_f (u^ast)$ has no eigenvalues with $Re(lambda) = 0$, i.e. $dim(E^c (u^ast)) = 0$.
]

#theorem[
  If $u^ast$ a hyperbolic steady state of $dot(u) = f(u)$, and all of the eigenvalues of $J_f (u^ast)$ have strictly negative real part, then $u^ast$ is asymptotically stable.
]

#theorem[
  If $u^ast$ a steady state and $J_f (u^ast)$ has a steady state with eigenvalue having real part strictly positive real part, then $u^ast$ unstable (namely not Lyapunov stable).
]

#remark[
  These theorems describe cases in which the linearization is correct in predicting the nonlinear behaviour.
]

#remark[
  The second theorem can only guarantee non-Lyapunov stability because linearization is a local process - quasi-asymptotic stability is "more global", and not picked up by the linearization necessarily.
] 

#theorem("Hartman-Grobman Theorem")[
  If $f$ continuously differentiable and $dot(u) = f(u)$ has a hyperbolic steady state $u^ast$, then there exists an open ball $B(u^ast, delta) subset.eq RR^p$, an open set $0 in N$ and a homeomorphism $
  H : B(u^ast, delta) -> N
  $ such that while $u(t) in B(u^ast, delta)$ a solution to $dot(u) = f(u),$ then $v(t) = H(u(t))$ a solution of $dot(v) = J_f (u^ast) v$.
]

#definition("Stable, Unstable Manifold")[
  The _stable, unstable_ manifolds of a steady state $u^ast$ are defined $
  W^s (u^ast) := {u in RR^p | S(t) u -> u^ast "as" t -> infinity} \ 
  W^u (u^ast) := {u in RR^p | Gamma^- (u) exists "and" S(t) u -> u^ast "as" t->-infinity}.
  $
]

= Delay Differential Equations

A delay differential equation (DDE) is, broadly speaking, an ODE that depends on the state of the system in the past. We'll focus on DDEs of the form $
dot(u)(t) = f(u(t), u(t - tau)),
$ where $u in RR^p, f : RR^p times RR^p -> RR^p$, and $tau > 0$ a fixed time delay.

The "canonical" first example of a DDE is $dot(u)(t) = u(t - tau)$ for $t >= 0$. Notice that for any time $t in [0, tau]$, then, $dot(u)(t)$ depends on $u$ for times that are not given by the DDE directly. In short, then, we need to supply not just an initial value to the DDE, but a whole initial data, namely $u(t) = phi(t)$ for $t in [-tau, 0]$. 

Suppose for now we take $phi equiv 1$, so we wish to solve the DDE with initial data $
cases(dot(u)(t) = u(t - tau) & wide t > 0, u(t) = 1 & wide  - tau <= t <= 0
).
$
One method of solution is called the "method of steps". Note that the initial data implies $
dot(u)(t) = 1 "for" t in [0, tau],
$ hence $u(t) =  t + 1$ on $[0, tau]$. Then, for $t in [tau, 2 tau]$, $
dot(u)(t) = u(underbrace(t - tau, in [0, tau])) = (t - tau) + 1,
$ so $u(t) = 1 + tau + (t - tau)(1 - tau) + 1/2 (t^2 - tau^2)$ for $t in [tau, 2 tau]$. Repeating this procedure arbitrarily results in a a piecewise solution defined on each interval of the form $[n tau, (n +1 ) tau]$ for $n in NN$. This method can be applied for more general DDEs, and will, in general, result in continuous solutions, differentiable everywhere except, in general, at the endpoints $n tau$.

Another method, specifically for linear DDEs, which more related to the ODE theory, is to derive a characteristic equation. Suppose a solution of the form $u(t) =k e^(lambda t)$ to the DDE $dot(u)(t) = beta u(t - tau)$. Plugging this into the equation gives $
k lambda e^(lambda t) = beta k e^(lambda (t - tau)) => Delta(lambda) := lambda - beta e^(- lambda tau) = 0.
$ Solving for $lambda$ such that $Delta(lambda) = 0$ is, in general, difficult. However, one notices that if $beta > 0$, $
lim_(lambda -> -infinity) Delta(lambda) = +infinity, wide delta(0) = - beta < 0,
$ so by the intermediate value theorem, there exists at least one solution to the characteristic equation, and moreover, $lambda in (0, infinity)$. Similar applies for $beta < 0$.
== DDE Linearization

Suppose we have a DDE $
dot(u)(t) = f(u(t), u(t - tau)),
$ where $u in RR^d$ (so $f : RR^d times RR^d -> RR^d$),  with a steady-state solution $u^ast$. Then, the linearization of the DDE about $u^ast$ is given by $
dot(v)(t) =  A v(t) + B v(t - tau), wide v(t) := u(t) - u^ast,
$ where $A, B$ are $d times d$ matrices given by $
A := (partial f)/(partial u)|_(u = u^ast), wide  B := (partial f)/(partial v)|_(u = u^ast).
$ The characteristic equation of the linearization is given $
Delta(lambda) = lambda I_d - A - B e^(-lambda tau) = 0.
$

For an example, consider the Mackey-Glass Equation, $
dot(u)(t) = - gamma u(t) + (beta u(t - tau))/(1 + u(t - tau)^n).
$ There are two steady states given by $
u_1 = 0, wide u_2 = (beta/gamma - 1)^(1/n),
$ the second only existing when $gamma/beta < 1$. In our earlier notations, we find $
f(u, v) = -gamma u + (beta v)/(1 + v^n).
$ Then, $f_u = - gamma$ and $f_v = beta [1 + (1 - n)v^n]/((1 + v^n)^2)$.


= Bifurcation Theory

#theorem("Implicit Function Theorem")[
  Let $f : RR^p times RR -> RR^p$ be a $C^1$ function of $(u, mu)$ with $f(0, 0) = 0$. If $J_f = f_u (0,0)$ is invertible, then there exists $epsilon > 0$ and a smooth curve $u = G(mu)$ which is the unique solution of $f(G(mu), mu) = 0$ for $abs(mu) < epsilon$ and $norm(u) < epsilon$.
]

#corollary[
  If $(u^ast, mu^ast)$ a hyperbolic steady state of $dot(u) = f(u, mu)$, then for some $epsilon > 0$ there is a smooth curve $u = G(mu)$ with $u^ast = G(mu^ast)$ whenever $norm(u - u^ast) < epsilon$ and $abs(mu - mu^ast) < epsilon$, such that $G(mu)$ a steady state of $dot(u) = f(u, mu)$, i.e. $f(G(mu), mu) = 0$.
]

#remark[
  Heuristically, this means that if $J_f$ invertible, there can be no change in the number of steady states near $u^ast$ while $mu$ near $mu^ast$. Similarly, small perturbations of $J_f$ won't change the sign of the real part of the eigenvalues of $J_f$, hence stability won't change in this case. Thus, to study scenarios in which changes in $mu$ qualitatively change dynamics, we need to study non-hyperbolic steady states. We call such a scenario a "bifurcation".
]

== Canonical 1-Dimensional Bifurcations

Suppose $
dot(u) = f(u, mu), wide f : RR times RR -> RR
$ has a fixed point at $(u, mu) = (0, 0)$ (if the fixed point is at a different point, we may simple change coordinates to move it to the origin). The following table outlines the most common bifurcation types, and conditions for the to occur, in the one-dimensional case.

In the "Conditions" column, all partial derivatives are evaluated at $(0,0)$. These conditions arise naturally from a Taylor expansion of $f$ about the steady state, and considering different combinations of quantities being zero or nonzero.

#table(
stroke: none,
columns: 4,
row-gutter: (0em, 1em),
"Name", "Normal Form", [Conditions$""^ast$], "Description",
table.vline(start: 0, end: 6, x : 1),
table.hline(start: 0, end: 4),
"Saddle Node", $dot(u) = mu - u^2$, $f = f_u = 0, f_mu eq.not 0$, "Single s.s. branches into 2",
"Transcritical", $dot(u) = mu u - u^2$, $f = f_u = f_mu = 0, f_(u u) eq.not 0, f_(u mu)^2 > f_(mu mu) dot f_(u u) $, "2 steady states pass through each other and change stability",
"Supercritical Pitchfork", $dot(u) = mu u - u^3$, $ f = f_u = f_mu = f_(u u) = 0, f_(u u u ) eq.not 0, f_(mu u) eq.not 0$, "Single stable fixed point becomes unstable and two new stable fixed points are born surrounding it",
"Subcritical Pitchfork", $dot(u) = -mu u + u^3$, "As above", "Same as above, interchanging stable and unstable"
)

#remark[
$""^ast$ The first two conditions, $f = f_u = 0$, which appear in all the cases, are required for a bifurcation ($f = 0$ gives a steady state, $f_u = 0$ means the implicit function theorem doesn't apply). Then, $f_mu eq.not 0$ implies a saddle-node, so the requirement $f_mu = 0$ in the other cases just rule out not being a saddle-node. The other conditions from there are just technical, and arise from the Taylor expansion naturally. 
]

#table(
  columns: 2,
  stroke: none,
  [#image("saddlepre.png"),
  #image("saddlepost.png")],
  image("sadddlebifurcation.png")
  // TODO
)

== Bifurcations In $RR^p$

In higher dimensions than 1, we have slightly more complex behaviour. From the Implicit Function Theorem, we know that if the Jacobian $J_f$ remains invertible as a parameter is varied, a steady state $u^ast (mu)$ will vary continuously with $mu$. So, the stability of the steady state may change with $mu$, but the number (locally) of steady states stays the same. For instance, this can happen in $RR^2$ if a complex conjugate pair of eigenvalues has real part changing sign. In this case, the steady state not hyperbolic, yet $J_f$ remains invertible (as long as the imaginary part of the eigenvalues remain nonzero.) This is called a "Hopf bifurcation", which we'll see more of later. Otherwise, bifurcations in $RR^2$ occur when a single real eigenvalue changes sign. We'll deal, first off, with bifurcations that involve a single eigenvalue crossing $0$ (changing sign) at a given time, which generally occurs with one-parameter systems. More generally if there are $>1$ parameters in a dynamical system, it is possible to make $k$ eigenvalues simultaneously zero, in which case we have a so-called "co-dimension $k$" bifurcation. We touch on these later.

// Consider for now $mu in RR$ and $dot(u) = f(u, mu)$ for $u in RR^2$, which has a steady state $u^ast (mu^ast)$, for which the Jacobian $J_f (u(mu))$ has two eigenvalues, $
// lambda_1 (mu^ast) = 0, wide lambda_2 (mu^ast) eq.not 0,
// $ and suppose finally $u^ast$ independent of $mu$. If $lambda_1 (mu^ast)$ crosses $0$ at $mu = mu^ast$,

#theorem("Center Manifold Theorem")[
Consider $dot(u) = f(u)$ where $f in C^r (RR^p, RR^p)$ and $f(0) = 0$. We classify the eigenvalues $lambda$ of the Jacobian of $f$ at $0$ in the following: $
sigma_u &:= {lambda | "Re"(lambda) > 0} \ 
sigma_s &:= {lambda | "Re"(lambda) < 0} \ 
sigma_c &:= {lambda | "Re"(lambda) = 0}.
$ Denote $E^u, E^s, E^c$ the corresponding subspaces of $RR^p$ (namely the spaces spanned by the eigenvectors corresponding to eigenvalues in $sigma_u, sigma_s, sigma_c$ respectively). Then, there exist $C^r$-smooth stable, unstable manifolds $W^s, W^u$ tangential to $E^s, E^u$ at $0$, and a $C^(r-1)$-smooth manifold $W^c$ tangential to $E^c$ at $0$, with the propertie that all of these manifolds are invariant for the dynamical system.
]

#remark[
  In this theorem, $W^s, W^u$ and $W^c$ are not the same as those discussed before, defined using $omega$-limit sets; now we require both $"Re"(lambda) eq.not 0$ _and_ stability/instability criteria.
]

We can often approximate the manifolds in the theorem by assuming that they can be written as curves that are functions of one variable, then applying an appropriate series expansion to determine coefficients. Globally, this may not work, but locally can give a good picture of the nonlinear manifold.

#example[In $RR^2$, let $
dot(x) = x y, dot(y) = -y - x^2.
$]

This system has a steady state at $(0,0)$, with  $
J_f (0,0) = mat(0,0;0,-1),
$ so there are two eigenvalues, $0, -1$. Moreover, this gives $E^s = "span"vec(0,1)$ and $E^c = "span"vec(1,0)$. 

If $x(0) = 0$, $dot(x) = 0$ so $x = 0$ for all time, hence $W^s (0,0) = E^s$ in this case.

For the nonlinear center manifold, $W^c$, suppose that locally, $W^c$ is the graph of a smooth function of $x$, $y = h(x)$, i.e. $
W^c = {(x, h(x)) | x in RR}.
$ To compute $h$, suppose $
y = h(x) = sum_(j=0)^infinity c_j x^j,
$ with the coefficients $c_j$ to be determined. By assumption, the dynamics are invariant on $h(x)$, so on the one hand $
dot(y) = h'(x) dot(x) = h'(x) (x y) = x h'(x)h(x) 
$ while also $
dot(y) = - y - x^2 = - h(x) - x^2,
$ so setting these equal, we find the relation $
x h'(x)h(x)  = - h(x) - x^2.
$ Equating like terms, we find $
c_0 = c_1 = 0, wide c_2 = -1, c_3 = 0, c_4 = -2, c_5 = 0,
$ etc. (note that we could have found the first two sooner; we know the curve must pass through the origin hence $c_0 = 0$, and we know it must be tangential to $E^c$, the $x$-axis, so its first derivative $c_1$ must also be zero). Plotting the first few terms of these curve against the actual vector field, we find:


#align(center,
image("firstexamplemanifold.png", width:50%)
)

Locally, its clear this curve is invariant under the dynamics of the system, and as we move further the approximation fails. This is because, away from the origin, the assumption that the unstable manifold could be represented as a curve parametrized in one variable fails.

#example[
  More generally, let $
  dot(x) = x(mu + y), wide dot(y) = -y - x^2,
  $ for $mu$ near $0$. Repeat the analysis of the system in the previous example (which is just this equation with $mu = 0$). (The algebra is a little more difficult, but doable.)
]

== Hopf Bifurcations

The Hopf Bifurcation is most readily described by example. #example[
  Consider the system $
  dot(x) = mu x - omega y - a x (x^2 + y^2), wide dot(y) = omega x + mu y - a y (x^2 + y^2),
  $ where $omega, mu, a$ are real parameters.
]

In polar coordinates, this system becomes $
dot(r) = mu r - a r^3, wide dot(theta) = omega,
$ from which we see that there is a unique fixed point at the origin. Here, the Jacobian (in Cartesian coordinates) is $
J (0,0) = mat(mu, - omega; omega, mu),
$ so eigenvalues are given by $
lambda_(plus.minus) = mu plus.minus i omega.
$ For $omega > 0$ (we'll only consider this case; the case $omega < 0$ is symmetrical, as we are dealing with a conjugate pair of eigenvalues), as $mu$ is varied and crosses zero, we see that the stability of the origin changes but the number of fixed points remains constant. Namely, when $mu > 0$ the origin is unstable, and vice versa.

Returning to polar, we see that $dot(r) = 0$ only if either $r = 0$ or $r = sqrt(mu/a)$. $dot(theta)$ is constant, so this implies that there is a circular orbit of radius $r = sqrt(mu\/a)$ and period $2pi\/omega$, whenever $mu$ and $a$ have the same sign.

For $a < 0$, this periodic orbit is unstable and the origin must be stable, so this is called a _subcritical Hopf_; for $a > 0$, the orbit is stable, the origin is unstable and we have a _supercritical Hopf_; finally, for $a = 0$, the origin is stable for $mu < 0$ and vice versa, and when $mu = 0$, everything is periodic (the phase space consists only of concentric circles).

#table(
stroke: none, align: center, columns: 3,
image("hopf1.png"),image("hopf2.png"),image("hopf3.png"),
"",[A subcritical Hopf bifurcation],""
)
// TODO bifurcation diagram.

#theorem("Conditions for a Hopf Bifurcation")[
  let $dot(x) = f(x, y, mu)$ and $dot(y) = g(x, y, mu)$ with $f(0,0,mu) = 0 = g(0,0,mu)$ for all $mu$, and Jacobian at $(0,0)$ given by $mat(0,-omega; omega,0)$, for some $omega eq.not 0$. Then, if $f_(mu x) + g_(mu y) eq.not 0$ and $a eq.not 0$, where $
  a := 1/16 (f_(x x x) + g_(x x y) + f_(x y y) + g_(y y y)) + 1/(16 omega) (f_(x y) (f_(x x) + g_(y y)) - g_(x y) (g_(x x) + g_(y y)) - f_(x x) g_(x x) - f_(y y) g_(y y)),
  $ then a curve of periodic orbits bifurcates from the origin into $mu < 0$ if $a (f_(x mu) + g_(y mu)) > 0$ or into $mu < 0$ if $a (f_(x mu) + g_(y mu)) < 0$.

- The steady state at the origin is stable for $mu > 0$ and unstable for $mu < 0$ if $f_(mu x) + g_(mu y) < 0$, and the opposite for $f_(mu x) + g_(mu y) > 0$. 
- The periodic orbit is stable/unstable if the origin is unstable/stable.
- The amplitude of the periodic orbit grows according to $abs(mu)^(1\/2)$, and need not in general be circular. The period converges to $2pi/abs(omega)$ as $abs(mu) -> 0$.

The bifurcation is called supercritical if the periodic orbit is stable, and subcritical if the periodic orbit is unstable.
]