// ! external
#import "../typst/notes.typ": *
#import "../typst/shortcuts.typ": *

// ! configuration
#show: doc => conf(
  course_code: "MATH358",
  course_title: "Advanced Calculus",
  subtitle: "",
  semester: "Winter 2026",
  professor: "Prof. John Toth",
  doc,
)
#set align(left)

#pagebreak()

= Differentiation

We say $Omega subset RR^n$ a _domain_ if it is open and connected.

#definition("Differentiation")[
  Let $f = (f_1, dots, f_m)^T : Omega -> RR^m$, $Omega$ a domain in $RR^n$ and $f_j : Omega -> RR$. We say $f$ _differentiable_ at $x_0 in Omega$ if there exists a linear map $L : RR^n -> RR^m$ such that $ lim_(x -> x_0) (norm(f(x) - f(x_0) - L (x - x_0)))/(norm(x - x_0)) = 0. $
]
#remark[Note that the first norm on $RR^m$, the second on $RR^n$.]
#remark[In terms of $epsilon, delta$, the definition says that $forall epsilon > 0$, $exists delta > 0$ such that if $x in Omega inter B(x_0, delta)$, then $norm(f(x) - f(x_0) - L (x - x_0)) < epsilon norm(x - x_0)$.]

#theorem[
  $L$ as above is unique if it exists.
]

#proof[
  Suppose $L_1 eq.not L_2$ both satisfy the definition. Then, for all $epsilon > 0$, there exists $delta > 0$ such that if $0< norm(x - x_0) < delta$, then $ norm((L_1 - L_2) (x - x_0)) & <= norm(f(x) - f(x_0) - L_1 (x- x_0)) + norm(f(x) - f(x_0) - L_2 (x - x_0)) \
                              & <= epsilon norm(x - x_0), $ by differentiability (and the previous remark). In particular, $norm((L_1 - L_2) u) < epsilon$ for all unit vectors $u$, which implies $norm((L_1 - L_2) u) = 0$ and thus $L_1 = L_2$.
]

#definition[If $f$ differentiable at $x_0$, we'll write $D f(x_0) = L$ for the _differential_ of $f$ at $x_0$.]

#proposition[$f$ differentiable at $x_0$ implies $f$ continuous at $x_0$. In fact, $f$ is Lipschitz at $x_0$.]

#proof[
  Let $delta > 0$ such that $norm(x - x_0) < delta$ implies $norm(f(x) - f(x_0) - D f(x_0) (x - x_0)) < norm(x - x_0)$, which implies $ norm(f(x) - f(x_0)) <= norm(D f(x_0) (x - x_0)) + norm(x - x_0) <= (norm(L) + 1) norm(x - x_0), $ which readily proves the statement.
]

#proposition[
  $f$ differentiable at a point $x_0$ iff each of its component functions are differentiable at $x_0$.
]

#definition[
  For $f : Omega subset RR^n -> RR^m$, define the _partial derivative_
  $ (partial f_j)/(partial x_i) (x_1, dots, x_m) := lim_(h -> 0) [f_j (x_1, dots, x_i + h, dots, x_m) - f_j (x_1, dots, x_i, dots, x_m)]/h, $ if the limit exists.
]

#proposition[
  Let $f : Omega subset RR^n -> RR^m$ be differentiable at $x_0$. Then, $(partial f_j)/(partial x_i) (x_0)$ exists for each $i = 1, dots, n$ and $j = 1, dots, m$, and $ L= D f(x_0) = ((partial f_j)/(partial x_i)(x_0))_(#stack(spacing: .5em, $1 <= i <= n$, $1 <= j <= m$)). $ We call this matrix the Jacobian or derivative of $f$ at $x_0$.
]

#proof[
  Write $L = (a_(j i))$ in the standard basis $e_1, dots, e_n$ for $RR^n$. Let $epsilon > 0$, fix some $i$ with $1 <= i <= n$, and set $x := x_0 + h e_i$, with $abs(h) < delta$ sufficiently small. By differentiability, $ (norm(f(x) - f(x_0) - L(x - x_0)))/(norm(x - x_0)) = (sum_(j = 1)^m [(f_j (x) - f_j (x_0))/h - a_(j i)]^2)^(1\/2). $ Since the limit as $h -> 0$ of the above ratio must be zero, the limit of each term in the summation as $h -> 0$ must be zero as well (being a sum of nonnegative terms), i.e. $ lim_(h -> 0) (f_j (x) - f_j (x_0))/h = a_(j i) quad forall j = 1, dots, m. $ But the limit on the left is just $(partial f_j)/(partial x_i) (x_0)$, which proves all of the claims in turn.
]

#remark[
  This proposition says that $f$ differentiable at $x_0$ implies $(partial f_j)/(partial x_i) (x_0)$ exists for all $i, j$. The converse need not be true. Consider $ f(x, y) := cases(
    (x y)/(sqrt(x^2 + y^2)) quad & (x, y) eq.not 0,
    0 & "else"
  ). $
]

#example[
  Another counterexample as in the previous remark is the function $ f(x, y) := cases(
    (x^2 y)/(x^2 + y^2) quad & (x, y) eq.not (0,0),
    0 & (x, y) = (0, 0)
  ). $
  _Claim 1:_ $f$ continuous at $(0,0)$. We have, for $(x, y) eq.not (0,0)$, $ abs(f(x, y) - f(0,0)) & = abs((x^2 y)/(x^2 + y^2)) \
                        & = (x^2 abs(y))/(x^2 + y^2) \
                        & <= abs(y) -> 0 "as" (x, y) -> (0,0), $ so we have continuity indeed.

  _Claim 2:_ $partial_x f, partial_y f$ exist at the origin, and are equal to zero. Note that $f(x, 0) = 0$ for $x eq.not 0$, and $f(0,0) = 0$, so it follows that $partial_x f (0,0) =0$. Similarly for $partial_y f(0,0)$.

  _Claim 3:_ $f$ is not differentiable at $(0,0)$. Suppose otherwise. Then, $L = D f(0,0) = (0,0)$, so $ 0 & = lim_((x, y) -> (0,0)) abs(f(x, y) - f(0,0) - D f (0,0)(x,y))/(norm((x, y))) \
    & = lim_((x, y) -> (0,0)) abs(f(x, y))/(norm((x, y))) \
    & = lim_((x, y) -> (0,0)) (x^2 abs(y))/((x^2 + y^2) dot sqrt(x^2 + y^2)) \
    & = lim_((x, y) -> (0,0)) (x^2 abs(y))/((x^2 + y^2)^(3\/2)). $ Suppose $y = x$ in the final term (i.e., we approach the limit on a diagonal), and $x > 0$, then this ratio simplifies $ x^3/((2 x^2)^(3\/2)) = 1/(2^(3\/2)) eq.not 0, $ so we have a contradiction.
]
We can get a partial converse, however, if we assume continuity.
#theorem[
  Let $f = (f_1, dots, f_m) : Omega subset RR^n -> RR^m$. Suppose each $(partial f_j)/(partial x_i)$ is continuous at some $x^0 in Omega$. Then, $f$ is differentiable at $x^0$.
]

#proof[
  We use MVT, and suppose $n = 2, m = 1$ for simplicity of notation, so that $f : Omega subset RR^2 -> RR$. We write $x = (x_1, x_2) in Omega, x^0 = (x^0_1, x^0_2)$. Let $epsilon > 0$. By assumption, there exists a $delta > 0$ such that $ norm(y - x^0) < delta => abs((partial f)/(partial x_i) (y) - (partial f)/(partial x_i) (x^0)) <= epsilon/2, quad i = 1, 2. $ We write $ f(x) - f(x^0) & = f(x_1, x_2) - f(x_1^0, x_2) + f(x_1^0, x_2) - f(x_1^0, x_2^0) \
  ("MVT, coordinate-wise")quad & = (partial f)/(partial x_1) (z_1, x_2) (x_1 - x_1^0) + (partial f)/(partial x_2) (x_1^0, z_2) (x_2 - x_2^0), $ for some $z_1$ between $x_1$ and $x_1^0$ and some $z_2$ between $x_2$ and $x_2^0$. Thus, $ f(x) - f(x^0) - D f(x^0)(x - x^0) & = f(x) - f(x^0) - (partial_(x_1) f (x^0), partial_(x_2) f(x^0)) dot (x - x^0) \
  &= (partial f)/(partial x_1) (z_1, x_2) (x_1 - x_1^0) + (partial f)/(partial x_2) (x_1^0, z_2) (x_2 - x_2^0) \
  & quad - (partial f)/(partial x_1) (x^0) (x_1 - x_1^0) - (partial f)/(partial x_2) (x^0) (x_2 - x_2^0) \
  &=[partial_(x_1) f (z_1, x_2) - partial_(x_1) f (x^0_1, x^0_2)] (x_1 - x_1^0) \
  & quad quad + [partial_(x_2) (x_1^0, z_2) - partial_(x_2) f (x^0_1, x^0_2)] (x_2 - x_2^0). $

  By choice of $z_1, z_2$ and for $(x_1, x_2)$ in $B(x^0, delta)$, we know $(z_1, x_2) in B(x^0, delta)$ and $(x_1^0, z_2) in B(x^0, delta)$ as well, so we can appeal to continuity. In addition, its clear that $abs(x_i - x_i^0) <= norm(x - x^0)$. Thus, using continuity, we find $ abs(f(x) - f(x^0) - D f(x^0)(x - x^0)) & <= (epsilon/2 + epsilon/2) norm(x - x^0) = epsilon norm(x - x^0), $ so dividing both sides by $norm(x - x^0)$ immediately gives the result.
]

#definition[
  Suppose $f : Omega subset RR^n -> RR$ has continuous $(partial f)/(partial x_i)$ at all points in $Omega$. Then, we say $f$ is _continuously differentiable_ (in $Omega$), and we write $f in C^1 (Omega)$.
]

#remark[
  Continuity of partial derivatives is sufficient, but not necessary, for differentiability. For instance, $ f(x, y) = cases(
    (x^2 y^2)/(x^2 + y^4) quad & (x, y) eq.not (0,0),
    0 & (x, y) = (0,0)
  ). $ On readily computes $partial_x f (0,0) = partial_(y) f(0,0) = 0$, but along the parabola $x = t^2, y = t$ ($t eq.not 0$), $ partial_x f (t^2, t) = 1/2, $ so $partial_x f$ can't be continuous. However, $f$ is still differentiable at $(0,0)$: we claim $L = 0$, then $ abs(f(x, y) - f(0,0) - L (x, y))/(norm((x, y))) & = abs(f(x, y))/((x^2 + y^2)^(1/2)) = (x^2 y^2)/((x^2 + y^4) (x^2 + y^2)^(1/2)) <= (y^2)/(abs(x^2 + y^2)^(1/2)) <= abs(y) ->_((x, y) -> 0) 0. $
]

#proposition("Basic Properties of Differentiation")[
  1. If $f, g : Omega -> RR^m$ both differentiable at $x^0 in Omega$, then so is $F = f + g$, and $ D(f + g)(x^0) = D f(x^0) + D g(x^0). $
  2. If $f, g : Omega -> RR^m$ both differentiable at $x^0 in Omega$, then so is $F = f g : Omega -> RR$, and $ D F (x^0) = f(x^0) D g(x^0) + g(x^0) D f(x^0). $
  3. $f, g : Omega -> RR$ both differentiable at $x^0$ with $g(x^0) eq.not 0$, then so is $F = f/g$, and $ D F(x^0) = (D F(x^0))/(g(x^0)) - (f(x^0) D g(x^0))/(g^2 (x^0)). $
  4. (Chain Rule) Given $f : Omega subset RR^n -> tilde(Omega) subset RR^m$ and $g : tilde(Omega) -> RR^k$, with $f$ differentiable at $x^0$ and $g$ differentiable at $y^0 = f(x^0)$, then $H = g compose f : Omega subset RR^n -> RR^k$ is differentiable at $x^0$, and $ D H(x^0) = D g (y^0) dot D f(x^0), $ in which one should read the "$dot$" as matrix multiplication.
]

#proof[
  1., 2., 3. left as an exercise. We prove 4., the Chain Rule, for it is realistically the most interesting. Set $L := D g (y_0) dot D f(x_0)$, and we'll write $y = f(x)$ (so in particular $y_0 = f(x_0)$, as in the statement). We need to show $ lim_(x -> x_0) norm(H(x) - H(x_0) - L (x - x_0))/(norm(x - x_0)) = 0. $ Let us work the numerator: $ H(x) - H(x_0) - L (x - x_0) & = g(y) - g(y_0) - D g (y_0) D f(x_0)(x - x_0) \
                              & = g(y) - g(y_0) - D g (y_0) (y - y_0) \
                              & quad quad + D g(y_0) (y - y_0) - D g(y_0) D f(x_0)(x - x_0) \
                              & = g(y) - g(y_0) - D g (y_0) (y - y_0) \
                              & quad quad + D g(y_0) (f(x) - f(x_0) - D f(x_0)(x - x_0)). $ This means $ norm(H(x) - H(x_0) - L (x - x_0)) & <= overbrace(norm(g(y) - g(y_0) - D g(y_0) (y - y_0)), =: (A)) \
  & quad quad + norm(D g(y_0)) overbrace(norm(f(x) - f(x_0) - D f(x_0) (x - x_0)), =:(B)). $  By differentiability of $f$ at $x_0$, $(B) -> 0$ as $norm(x - x_0) -> 0$. We also have that, since $f$ differentiable it is Lipschitz continuous, there is some $C > 0$ such that for $norm(x - x_0)$ sufficiently small, $ (A) = norm(y - y_0) dot ((A))/(norm(y - y_0)) <= C norm(x - x_0) (A)/(norm(y - y_0)). $ By differentiability of $g$, the ratio $norm(A)/(norm(y - y_0)) -> 0$ as $norm(y - y_0) -> 0$. By continuity of $f$, $norm(y - y_0) = norm(f(x) - f(x_0))$ will become small as $norm(x - x_0) -> 0$, so that we have in all $(A)/(norm(x - x_0)) -> 0$ as $norm(x - x_0) -> 0$.
]

#exercise[
  Let $f$ differentiable in $RR^2$ and $g(r, theta) := (r cos theta, r sin theta)$ with $(r, theta) in (0, infinity) times [0, 2 pi)$. Let $F(r, theta) = f(g(r, theta))$. Compute $(partial F)/(partial theta)$ and $(partial F)/(partial r)$.
]

== Aside on Tangent Planes
Let $f : Omega subset RR^n -> RR$ differentiable on $Omega$. Then $D f(x) = ((partial f)/(partial x_1) (x), dots, (partial f)/(partial x_2) (x)) =: gradient f(x)$, called the _gradient_ of $f$. Let $S := {(x, z) in Omega times RR : z = f(x)}$ be the _graph_ of $f$. Then, for $x^0 in RR$, $ T_(x_0) S = {(x, z) in RR^n times RR : z = f(x^0) + sum_(j=1)^n (partial f)/(partial x_j)(x^0) (x_j - x_j^0)} $ is the _tangent plane_ to $S$ at $x^0$.

To see this, let $v in RR^n$ be a unit vector and $x in Omega$. Define $g(t) := f(x + t v)$ for $f : Omega -> RR$ differentiable (for $t$ sufficiently small, $x + t v$ remains in $Omega$ by openness). We find $ g'(t) = angle.l gradient f(x + t v), v angle.r $ for $t$ sufficiently small.

#proposition[Suppose $gradient f(x) eq.not 0$. Then, $gradient f(x)$ points in the direction of steepest increase of $f$.]
#proof[
  For $v$ a unit vector, the _directional derivative_ in the direction of $v$ is $D_v f(x) = angle.l gradient f(x), v angle.r = norm(gradient f(x)) cos(theta)$ where $theta$ the angle between $gradient f(x)$ and $v$. This is maximized when $theta= 0$, i.e. when $v = (gradient f(x_0))/(norm(gradient f(x_0)))$.
]

We can rewrite the graph $S$ as the level set ${(x, z) in Omega times RR | g(x, z) = 0}$ where $g(x, z) := z - f(x)$. Heuristically, $gradient g(x_0, z_0)$ should be _normal_ to the surface $S$ at $(x_0, z_0)$ (for steepest increase). As such, we define $ T_((x_0, z_0)) S := {gradient g(x_0, z_0) dot (x - x_0, z - z_0) = 0}. $ Note that $ gradient g(x_0, z_0) & = (- partial_(x_1) f(x_0), dots, - partial_(x_n) f(x_0), 1), $  so that $ T_((x_0, z_0)) = {z - z_0 = gradient f(x_0) dot (x - x_0)}, $ which gives the definition from above.

== Clairault's Theorem

Here, the question is, given $f : Omega subset RR^n -> RR$ twice differentiable, when can we exchange order of second-order partial derivatives, i.e. when is $ (partial^2 f)/(partial x_j partial x_i) = (partial^2 f)/(partial x_i partial x_j), quad forall i,j = 1, dots, n? $

We need to establish first a generalization of the mean-value theorem. First, note that if $ gamma : (a, b) -> RR^n, quad g : Omega subset RR^n -> RR $ are two differentiable functions with $gamma((a, b)) subset Omega$, then by the chain rule, if we put $H(t) := g(gamma(t))$, $ (partial H)/(partial t) = D g(gamma(t)) dot D gamma(t), quad D gamma(t) = (gamma'_1 (t), dots, gamma'_n (t)). $

#theorem("Mean-Value Theorem")[
  Let $B subset RR^n$ be a ball and $f : B -> RR$ be differentiable for all $x in B$. Then, for any $x, y in B$, there exists $z in B$ such that $ f(x) - f(y) = D f(z) dot (x - y). $

  In particular, $abs(f(x) - f(y)) <= norm(D f(z)) norm(x - y)$.
]

#proof[
  Let $x, y in B$ fixed and let $gamma(t) := t x + (1 - t) y$ for $t in [0, 1]$. We see that $gamma(t) in B$ for all $t in [0, 1]$, and that $D gamma(t) = x - y$. Set $F(t) := f(gamma(t))$ (i.e., we restrict $f$ to its values along the straight line along $x$ and $y$), noting $F : RR -> RR$. So, by 1-dimensional mean-value theorem, there is some $t^ast in [0, 1]$ such that $ f(x) - f(y) = F(1) - F(0) = F'(t^ast) & = D f (underbrace(t^ast x + (1 - t^ast) y, =: z in B)) dot D gamma (t) \
                                        & = D f (z) dot (x - y). $
]

Let $f : Omega subset RR^n -> RR^m$ differentiable. Remember that $D f : Omega -> RR^(m times n)$.

#definition[
  We say $f$ twice differentiable at $x$ if $D f$ exists locally to $x$ and $D f$ is differentiable at $x$. We write $ D^2 f = D (D f), $ and similarly $ D^k f := D (D^(k - 1) f) $ with an analogous definition.
]

#definition[
  Given $f : Omega subset RR^n -> RR$, we see that $f in C^k (Omega)$ for $k in ZZ_+$ if all the partial derivatives to order $k$ exist and are continuous in $Omega$.
]

#definition[
  If $f : Omega subset RR^n -> RR$ twice differentiable, the _Hessian matrix_ is given by $ H_f (x) = mat(
    (partial^2 f)/(partial x_1 partial x_1), (partial^2 f)/(partial x_1 partial x_2), dots.c, (partial^2 f)/(partial x_1 partial x_n);
    dots.v, dots.v, dots.down, dots.v;
    (partial^2 f)/(partial x_n partial x_1), (partial^2 f)/(partial x_n partial x_2), dots.c, (partial^2 f)/(partial x_n partial x_n)
  ). $
]

#exercise[
  Let $f(x, y) := cases(((x y)(x^2 - y^2))/(x^2 + y^2) quad & (x, y) eq.not (0, 0), 0 & (x, y) = (0, 0))$ and compute $H_f (x, y)$.
]

#theorem("Clairault")[
  Let $f : Omega subset RR^n -> RR$ be twice differentiable at $x in Omega$. Then, $ (partial^2 f)/(partial x_i partial x_j) (x) = (partial^2 f)/(partial x_j partial x_i) (x), quad forall i, j = 1, dots, n. $
]

#corollary[
  If $(partial^2 f)/(partial x_i partial x_j)$ are all continuous at $x in Omega$ for $i, j = 1, dots, n$, then $(partial^2 f)/(partial x_i partial x_j) (x) = (partial^2 f)/(partial x_j partial x_i) (x).$
]

#proof[(Of Clairault's)
  It's enough to consider $n = 2$. Fix $(x, y) in Omega$, and note that for $s, t in RR$ sufficiently small, $(x + s, y + t) in Omega$ by openness. Set $ Delta(s, t) & := f(x + s, y + t) - f(x, y + t) - f(x + s, y) + f(x, y) \
              & = g_t (x + s) - g_t (x), quad g_t (u) := f(u, y + t) - f(u, y). $ By the mean-value theorem, there is some $xi_(s, t)$ between $x$ and $x + s$ suh that $ Delta (s, t) = (partial g_t)/(partial x) (xi_(s, t)) dot s = [(partial f)/(partial x)(xi_(s, t), y + t) - (partial f)/(partial x)(xi_(s, t), y)]s. quad (dagger.double) $ By assumption, $(partial f)/(partial x)$ is differentiable at $(x, y)$, so $ (partial f)/(partial x) (z_1, z_2) = (partial f)/(partial x) (x, y ) (z_1 - x) + (partial^2)/(partial x^2) (x, y)(z_2 - y) + E_1 (z_1, z_2), quad (dagger) $ where $ abs(E_1 (z_1, z_2))/(sqrt((z_1 - x)^2 + (z_2 - y)^2)) -> 0, quad "as" (z_1, z_2) -> (x, y). $
  Evaluating $(dagger)$ at $(z_1, z_2) = (xi_(s, t), y + t)$ and $(xi_(s, t), y)$, and plugging into $(dagger.double)$ yields $ Delta (s, t) & = ((partial^2 f)/(partial y partial x)(x, y) t + E_1 (xi_(s, t), y + t) - E_1 (xi_(s, t), y)) s. $ Let $s = t$ and let $t -> 0$. We claim that $ (partial^2 f)/(partial y partial x)(x, y) = lim_(s = t-> 0) (Delta (s, t))/(s t) = (partial^2 f)/(partial x partial y)(x, y) $
]
