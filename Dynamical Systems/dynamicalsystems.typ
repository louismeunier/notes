// ! external
#import "../typst/notes.typ": *
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