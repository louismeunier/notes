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
