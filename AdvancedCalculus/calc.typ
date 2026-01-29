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
  Evaluating $(dagger)$ at $(z_1, z_2) = (xi_(s, t), y + t)$ and $(xi_(s, t), y)$, and plugging into $(dagger.double)$ yields $ Delta (s, t) & = ((partial^2 f)/(partial y partial x)(x, y) t + E_1 (xi_(s, t), y + t) - E_1 (xi_(s, t), y)) s. $ Let $s = t$ and let $t -> 0$. We claim that $ (partial^2 f)/(partial y partial x)(x, y) = lim_(s = t-> 0) (Delta (s, t))/(s t) = (partial^2 f)/(partial x partial y)(x, y). $
  The first equality is obvious from the assumptions on the error terms. On the other hand, we can switch the order of the middle terms in $Delta (s, t)$ and write $ Delta (s, t) & = f(x + s, y + t) - f(x, y + t) - f(x + s, y) + f(x, y) \
               & = h_s (y + t) - h_s (y), quad h_s (u) := f(x + s, u) - f(x, u). $ Repeating the same argument as above with $g_t$, we get that $ Delta (s, t) = ((partial^2)/(partial x partial y) (x, y) s + E_2 (x + s, eta_(s, t)) - E_2 (x, eta_(s, t))) t, $ where $eta_(s, t)$ lies between $y$ and $y + t$, and $ abs(E_2 (x + s, eta_(s, t))) <= abs(s^2 + t^2), quad abs(E_2 (x, eta_(s, t))) <= sqrt(s^2 + t^2). $ Setting $s = t$ here, we get $ lim_(s, t -> 0 \ s = t) Delta(s, t)/(s t) = (partial^2)/(partial x partial y) (x, y). $ This proves the claim.
]

== Inverse Function Theorem

#theorem("In 1D")[
  If $f : (a, b) -> (c, d)$ is differentiable with $f'(x) > 0$, then there exists $g : (c, d) -> (a, b)$ differentiable such that $y = f(x) <=> x = g(y)$ (i.e. $x = g(y)$).
]

In higher dimensions, we recall some preliminaries before proving.

#theorem[
  Let $(X, d)$ a complete metric space and $f : X -> X$ a contraction mapping, with $d(f(x_2), f(x_1)) <= alpha d(x, y)$ for all $x, y in X$ for some $0 < alpha < 1$. Then, there exists a unique $x_0 in X$ such that $f(x_0) = x_0$.
]

We will write $M_n := {n times n "matrices"} tilde.equiv RR^(n^2)$, and $norm(A) := sqrt(sum_(i, j = 1)^n a_(i j)^2)$ where $A := (a_(i j)) in M_n$. We use $ "GL"(n) := {A in M_n : det(A) eq.not 0} = "det"^(-1) (RR \\ {0}), quad det : M_n -> RR. $
Remark that since $RR\\{0}$ is open, and the map $det$ is continuous (it can be written as a polynomial in the entries $a_(i j)$'s of the matrix $A$), we know that $"GL"(n)$ an open subset of $M_n$.

Consider the map $ f : "GL"(n) -> "GL"(n), quad f(A) := A^(-1). $

#lemma[
  $"GL"(n) subset M_n$ open and $f in C^k$ for all $k = 1, 2, dots$.
]

#proof[
  We already proved the first statement in our remarks above.

  Let $A(j|i)$ be $(n - 1) times (n - 1)$ matrix with its $j$th row and $i$th columns deleted, then recall $ "adj"(A) = ((-1)^(i + j) det A(j|i)). $
  By Cramer's formula from linear algebra, $ f(A) = A^(-1) 1/("det"(A)) "adj"(A), $ which is in $C^k$ since $"det"(A)$ $C^k$ (being a polynomial in the coefficients of $A$) and $"det"(A) eq.not 0$.
]

#theorem("Inverse Function Theorem")[
  Let $f : Omega subset RR^n -> RR^n$ be $C^1$. Let $x_0 in Omega$ and assume $D f(x_0) in "GL"(n)$. Then, there exist domains $U$ and $V$ of $x_0$ and $f(x_0)$ resp. such that $f(U) = V$ and $f|_(U)$ has a $C^1$ inverse map $f^(-1) : V -> U$. Moreover, for any $y in V$ and $x = f^(-1)(y)$, $D f^(-1) (y) = [D f(x)]^(-1)$.
]

#remark[
  By the first lemma above, if $f in C^k$, $k >= 1$, we get the same regularity for $f^(-1)$.
]

#proof[
  By translation, its enough to assume $x_0 = f(x_0) = y_0 = 0$ and $D f(x_0) = "Id"$ by replacing $f$ with $[D f (0)]^(-1) f$, so we have a mapping $ f : Omega -> RR^n, quad f(0) = 0, D f(0) = "Id". $

  Fix $y in V$ and set $ g_y (x) := y + x - f(x), $ remark that $ g_y (x) = x <=> y = f(x), $ so it suffices to show $g_y$ as a mapping $RR^n -> RR^n$ is a contraction mapping, and $ D g_y (0) = "Id" - "Id" = 0. $ If $f in C^1 (U)$, then $g_y in C^1 (U)$ so that $D g_y in C^0 (U)$ (similar if $f in C^k => g_y in C^k$). Since $D g_0 in C^0 (U)$, there exists some $delta > 0$ sufficiently small such that $norm(D g_0 (x)) <= 1/2$, for all $x in B_delta (0)$. By mean-value theorem, there exists some $z in B_delta (0)$ such that $ norm(g_0 (x)) & = norm(g_0 (x) - underbrace(g_0 (0), = 0)) \
                & <= norm(D g_0 (z)) norm(x) \
                & <= norm(x)/2 < delta/2, $ which implies we can view $ g_0 : B_delta (0) -> B_(delta\/2) (0). $ It follows that $ g_y : B_delta (0)-> B_delta (0), quad forall y in B_(delta\/2) (0), $ using the fact $g_y = y + g_0$ and the triangle inequality. By MVT once again for any $x, x' in B_delta (0)$, there exists $y in B_(delta\/2) (0)$
  // TODO I think this is wrong
  such that $ norm(g_y (x) - g_y (x')) & = norm(g_0 (x) - g_0 (x')) \
                           & <= norm(D g_0 (y)) norm(x - x') \
                           & <= norm(x - x')/2 $ hence $g_y : B_delta -> B_delta$ is a contraction mapping. By the fixed-point theorem, there exists a unique point $x in B_delta (0)$ such that $g_y (x) = x <=> y = f(x).$ That is, there exists an inverse map $f^(-1) : B_(delta\/2) (0) -> B_delta (0)$. Moreover, for any $x, x' in B_delta (0)$, $ norm(x - x') & <= norm(f(x) - f(x')) + norm(g_0 (x) - g_0 (x)) \
               & <= norm(f(x) - f(x')) + 1/2 norm(x - x'), $ i.e. $ norm(x - x') <= 2 norm(f(x) - f(x')). $ From here, we know that for $y, y' in B_(delta\/2) (0)$, $ norm(f^(-1) (y) - f^(-1) (y')) <= 2 norm(y - y') => f^(-1) in C^0 (B_(delta\/2) (0)). $

  Next, we need to show that $D f^(-1)(y)$ exists for $y in B_(delta\/2) (0)$ for small $delta > 0$. Since $D f(0) in "GL"(n)$, we know $D f(x) in "GL"(n)$ if $x in B_delta (0)$ (possible after shrinking $delta > 0$). Set $ W := f^(-1) (B_(delta\/2) (0)), $ and choose $R > 0$ suff. small so that $ overline(B_(R) (0)) subset W. $
  Since $[D f]^(-1) in C^0 (overline(B_R))$ and $overline(B_R)(0)$ is compact, $ norm([D f (x)]^(-1)) <= K, x in overline(B_r (0)). $
  Then, given $y, y' in B_(delta\/2) (0)$ and with $x = f^(-1) (y), x' = f^(-1) (y')$, we find $ norm(f^(-1) (y) - f^(-1) (y') - [D f (x')]^(-1) (y - y'))/(norm(y - y')) &= norm(x - x' - [D f(x')]^(-1) (f(x) - f(x')))/(norm(f(x) - f(x'))) \
  &= norm(x - x')/(norm(f(x) - f(x'))) (norm(D f(x')^(-1) (f(x) - f(x') - D f(x') (x - x'))))/(norm(x - x')) \
  &<= 2 K norm(f(x) - f(x') - D f(x') (x - x'))/(norm(x - x')), $ which converges to zero by differentiability of $f$. This proves the claim $D f^(-1) (y) = [D f (x)]^(-1)$ where $y = f(x)$.
]

#remark[
  The inverse function theorem is _local._ In general we can't expect to find a single global inverse. For instance, let $ f(x, y) := (e^y cos(x), e^y sin(x)). $ One easily verifies $ "det"(D f(x, y)) = e^(-y) eq.not 0. $ However, $ f(x + 2 k pi, y) = f(x, y), forall k in ZZ, $ so there is certainly no hope of a global inverse, for $f$ is not even injective.
]


#theorem("Implicit Function Theorem")[
  Let $F : Omega subset RR^n_x times RR^m_y -> RR^m_y$ be a $C^k$ map. Denote $X = (x, y) in RR^n times RR^m$, and let $X_0 = (x_0, y_0) in Omega$ with $F(X_0) = 0$. Writing $F = (F_1, dots, F_m)$, assume that $ D_y F(X_0) = mat((partial F_1)/(partial y_1), dots, (partial F_1)/(partial y_m); dots.v, dots.down, dots.v; (partial F_m)/(partial y_1), dots, (partial F_m)/(partial y_m)) (X_0) $ is invertible. Then, there exist neighborhoods $U$ and $V$ of $x_0 in RR^n$ and $y_0 in RR^m$ resp. and a unique $C^k$ map $f : U -> V$ such that $ F(x, f(x)) = 0, quad forall x in U. $
  In other words, the level set of $F$ is locally to $x_0$ the graph of some function $f$ of the same regularity as $F$.
]

#proof[
  Define $G : Omega -> RR^n times RR^m$ by $ G(x, y) := (x, F(x, y)). $ Obviously $G$ is $C^k$. We can apply the inverse function theorem to $G$ near $X_0$; indeed, $ D G (X_0) = mat(I_(n times n), 0; D_x F (X_0), D_y F(X_0)), $ which means $ "det" D G(X_0) = "det" D_y F(X_0) eq.not 0, $ by assumption. Thus there exist neighborhoods $W_1, W_2$ of $X_0$, $(x_0, 0)$ respectively (since $(x_0, 0) = G(X_0)$) for which $G^(-1)$ exists (and is $C^k$) from $W_2 -> W_1$. Then, there are neighborhoods $U subset RR^n$ of $x_0$ and $V subset RR^m$ of $y_0$ such that $U times V subset W_1$; set $Z = G(U times V)$ (which is also open, with $Z subset W_2$). Thus we can view $ G : U times V -> Z, quad G^(-1) : Z -> U times V, $ which are both $C^k$ maps. Since $G(x, y) = (x, F(x, y))$, we know that $G^(-1) (x, w) = (x, H(x, w))$ for all $(x, w) in Z$. Here, $H : Z -> V$ is $C^k$ since $G$ is. Thus, $ (x, F(x, H(x, w))) = G(x, H(x, w)) = (x, w), $ using the definition of $G$ in the first equality and the inverse fact in the second line. Thus, it follows that $ F(x, H(x, w)) = w, quad forall (x, w) in Z, $ thus taking $f(x) := H(x, 0)$ gives the proof.
]

#corollary[
  Let $F : Omega subset RR^n -> RR$ be a $C^k (Omega)$ function. Let $X = (x', y) in RR^(n- 1) times RR$ and suppose $(x'_0, y_0) in Omega$ with $(partial f)/(partial y) (x'_0, y_0) eq.not 0$. Then, there exist neighborhoods $U$ and $V$ of $x'_0 in RR^(n - 1)$ and $y_0 in RR$ and a unique $C^k (U)$ function $f : U -> V$ such that $ {F(x', y) = 0} = {y = f(x')}, quad (x', y) in U times V. $
]

#theorem("Morse Lemma")[
  Let $f : Omega subset RR^n -> RR$ be a $C^k$ function with $k >= 3$. Let $0 in Omega$ be a critical point, i.e. $gradient f(0) = 0$. Assume further $f(0) = 0$ and $gradient^2 f(0)$ is invertible. There exist open sets $U, V$ of $0 in U sect V$ and $g in C^(k - 2) (U)$, $g : U -> V$ with $g^(-1) : V -> U$, $g^(-1) in C^2 (V)$, such that $ f(g(y)) = y_(ell + 1)^2 + dots.c + y_n^2 - (y_1^2 + dots.c + y_ell^2), $ for some $ell in ZZ sect [0, n]$.
]

== Taylor's Theorem in $RR^n$

Let $f : Omega subset RR^n -> RR$, $f in C^(k + 1) (Omega)$. Let $x_0 in Omega$ and $|t|$ small. Consider $ g(t) := f(x_0 + t (x - x_0)/(norm(x - x_0))), quad x eq.not x_0, quad g(0) = f(x_0). $
Since $x_0 in Omega$ and $Omega$ open, $x_0 + t (x - x_0)/(norm(x - x_0)) in Omega$ for $t$ sufficiently small. By Taylor in 1-dimension, $ g(t) & = g(0) + g'(0) t + (g''(0) t^2)/(2!) + dots.c + (g^((k))(0) t^k)/(k!) + R_k (g) (t), quad abs(R_k (g) (t))/(abs(t)^k) <= M |t| "as" t-> 0. $

To get Taylor expansion for $f(x)$ around $x_0$, we set $t = abs(x - x_0)$ and apply chain rule to $g(t)$. First, we compute $g^((j)) (0)$; we get $ g(0) = f(x_0), \
g(t) = g(norm(x - x_0)) = g(x). $ By chain rule, $ g'(0) = sum_(i=1)^n (partial f)/(partial x_i) (x_0) (x_j - x_j^0)/(norm(x - x_0)). $ Similarly, ....
