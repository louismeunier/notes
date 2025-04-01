// ! external
#import "../typst/notes.typ": *
#import "../typst/shortcuts.typ": *

// ! configuration
#show: doc => conf(
  course_code: "MATH358",
  course_title: "Advanced Calculus",
  subtitle: "",
  semester: "Winter 2025",
  professor: "Prof. John Toth",
  doc
)
#set align(left)

#pagebreak()

% ! 01-07
= Differentiation

For a function $f : (a, b) -> RR$, $f$ differentiable at $x_0 in (a, b)$  if $L := lim_(h -> 0) (f(x_0 + h) - f(x_0))/h$ exists, and write $f'(x_0) = L$. Equivalently, $f'(x_0)$ exists and is equal to $L$ if $
(|f(x) - f(x_0) - L (x - x_0)|)/(|x - x_0|) -> 0
$ as $x -> x_0$. This characterization motivates the generalization we'll follow in the general dimensional case.

Let $Omega subset RR^n$ a connected, open set. We call such a set a _domain_ to follow. Let $f : Omega -> RR^m$.

#definition[
  $f$ differentiable at $x_0 in Omega$ if there exists a linear map $L : RR^n -> RR^m$ (which can be viewed as a matrix) such that $
  lim_(x-> x_0 \ x eq.not x_0) (||f(x) - f(x_0) - L (x - x_0)||_(RR^m))/(||x - x_0||_(RR^n)) = 0.
  $ Equivalently, $forall epsilon > 0$, there is a $delta > 0$ such that if $0 < ||x - x_0|| < delta$, then $
  ||f(x) - f(x_0) - L (x - x_0)|| <= epsilon ||x - x_0||. wide dagger
  $
]

#theorem[
  If $L$ as in the previous definition exists, then it is unique.

  We write then $D f(x_0) := L$.
]

// TODO I prefer to proof of theorem 2.1 in Spivak
#proof[
Suppose $L_1, L_2 : RR^n -> RR^m$ are two linear maps such that $dagger$ holds. Fix $epsilon > 0$ and let $delta > 0$ such that $dagger$ holds for both $L_1, L_2$ with $epsilon/2$. Then, for $x$ such that $0 < ||x - x_0|| < delta$, then $
||(L_1 - L_2) (x - x_0)|| &<= ||f(x) - f(x_0) - L_1 (x - x_0)|| + ||f(x) - f(x_0) - L_2 (x - x_0)|| \
&<= epsilon ||x - x_0||.
$ Put $h = (x - x_0)/(||x - x_0||)$ which is a unit vector in $RR^n$. Then, this gives $
||(L_1 - L_2) h|| <= epsilon.
$ For any vector $y in RR^n$, there is a constant $rho = ||y||$ and appropriate $h$ such that $y = rho h$, and so $
||(L_1 - L_2) (rho h)|| = |rho| ||(L_1 - L_2) h|| <= |rho| epsilon,
$ by linearity, and since $epsilon$ arbitrary, it must be that $L_1 = L_2$.
]

#proposition[If $f : Omega -> RR^m$ is differentiable at $x_0 in Omega$, then $f$ is continuous at $x_0$.]

#proof[
  Let $epsilon = 1$ and $delta > 0$ such that $dagger$ holds. Then, for $x$ such that $0 < || x - x_0|| < delta$,$
  ||f(x) - f(x_0)|| &<= ||L(x - x_0)|| + ||f(x) - f(x_0) - L(x - x_0)|| \
  & < (||L|| + 1) ||x - x_0|| =: K ||x - x_0||.
  $ where $||L||$ is the "maximal value" of $L (x - x_0)$, which is finite. Let, then, $delta' < min{delta, epsilon/K}$. Then, if $x$ is such that $||x - x_0|| < delta'$, then $
  ||f(x) - f(x_0)|| < K ||x - x_0|| < epsilon,
  $ proving continuity.
]

#definition[
  Let $f = (f_1, dots, f_m) : Omega -> R^m$. Define, for $i = 1, dots, n, j = 1, dots, m$, $
  (partial f_j)/(partial x_i) (x_1, dots, x_n) := lim_(h -> 0\ h eq.not 0) [(f_j (x_1, dots, x_i + h, dots, x_n) - f_j(x_1, dots, x_n))/(h)],
  $ the partial derivative of the $j$th component of $f$ with respect to $x_i$.
]

#proposition[
  If $f$ differentiable at $x_0 in Omega$, then $(partial f_j)/(partial x_i) (x_0)$ exists for each $i = 1, dots, n, j = 1, dots, m$, and moreover, $L = D f(x_0) = ((partial f_j)/(partial x_i))$.
]

#proof[
  Denote the entries of $L = (a_(j i))$. Put for arbitrary $h$, $x = x_0 + h e_i$. Then, $
  (||f(x) - f(x_0) - L (x - x_0)||)/(||x - x_0||) &= (sum_(j=1)^m [(f_j (x) - f_j (x_0))/(h) - a_(j i)]^2)^(1/2).
  $ This term converges to zero by assumption as $h -> 0$, and by continuity of $(dot)^(1/2)$, and the fact that the summation is over nonnegative summands, it must be that $
  lim_(h->0) (f_j (x_0 + h e_i) - f_j (x_0))/(h) = a_(j i)
  $ for each $i, j$. The LHS limit is simply $(partial f_j)/(partial x_i) (x_0)$, completing the proof.
]

% ! 01-09