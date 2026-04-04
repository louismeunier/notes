// ! external
#import "../typst/notes.typ": *
#import "../typst/shortcuts.typ": *

// ! configuration
#show: doc => conf(
  course_code: "MATH358",
  course_title: "Advanced Calculus",
  subtitle: [Differentiation, integration in $RR^n$],
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
  Let $B subset RR^n$ be a ball and $f : B -> RR$ be differentiable for all $x in B$. Then, for any $x, y in B$, there exists $z in B$ (in particular, we can find $z$ which lies along the line segment between $x$ and $y$) such that $ f(x) - f(y) = D f(z) dot (x - y). $

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

== Taylor's Theorem in $RR^n$ and Lagrange Multipliers

Let $f : Omega subset RR^n -> RR$, $f in C^(k + 1) (Omega)$. Let $x_0 in Omega$ and $|t|$ small. Consider $ g(t) := f(x_0 + t (x - x_0)/(norm(x - x_0))), quad x eq.not x_0, quad g(0) = f(x_0). $
Since $x_0 in Omega$ and $Omega$ open, $x_0 + t (x - x_0)/(norm(x - x_0)) in Omega$ for $t$ sufficiently small. By Taylor in 1-dimension, $ g(t) & = g(0) + g'(0) t + (g''(0) t^2)/(2!) + dots.c + (g^((k))(0) t^k)/(k!) + R_k (g) (t), quad abs(R_k (g) (t))/(abs(t)^k) <= M |t| "as" t-> 0. $

#remark[
  This expansion suggests that one should be able to weaken the $C^(k +1)$ assumption on $g$ if we only require $ lim_(t -> 0) (|R_k (g) (t)|)/(|t|^k) = 0. $ Indeed, we only really need $g in C^(k - 1)$ and $D (D^(k - 1)) g (0)$ existing.
]


To get the Taylor expansion for $f(x)$ around $x_0$, we set $t = abs(x - x_0)$ and apply chain rule to $g(t)$. First, we compute $g^((j)) (0)$; we get $ g(0) = f(x_0), \
g(norm(x - x_0)) = f(x). $ By chain rule, $ g'(0) = sum_(j=1)^n (partial f)/(partial x_i) (x_0) (x_j - x_j^0)/(norm(x - x_0)) = gradient f (x_0)^T ((x - x_0)/(norm(x -x_0))). $ Similarly, $ g''(t) & = (dif)/(dif t) g'(t) \
& = (dif)/(dif t) (gradient f(x_0 + t (x - x_0)/(norm(x - x_0)))^T (x - x_0)/(norm(x - x_0))) \
& = (D^2 f(x_0 + t (x - x_0)/(norm(x - x_0))) (x - x_0)/(norm(x - x_0))) dot (x - x_0)/(norm(x - x_0)) \
& = ((x - x_0)/(norm(x-x_0)))^T D^2 f(x_0 + t (x - x_0)/(norm(x - x_0))) (x - x_0)/(norm(x - x_0)) \
& = sum_(i, j = 1)^n (partial^2 f)/(partial x_i partial x_j) (x_0 + t (x - x_0)/(norm(x - x_0))) ((x_i - x^0_i) (x_j - x_j^0))/(norm(x - x_0)^2), $ so that $ g''(0) = [(x - x_0)/(norm(x - x_0))]^T D^2 f (x_0) dot [(x - x_0)/(norm(x - x_0))]. $ Similar computation can be used to compute $g^((ell))$ for $ell$ up to $k$. In general, we find that $ g^((ell)) (0) = sum_(i_1, dots, i_ell = 1)^n (partial^(ell) f)/(partial x_(i_1) dots.c partial x_(i_ell)) (x_0) (x_i_1 - x^0_i_1)/(norm(x - x_0)) dots.c (x_i_ell - x^0_i_ell)/(norm(x - x_0)). $
Moreover, since $t^ell = norm(x - x_0)^ell$, the term in the Taylor expansion of $g$ corresponding to $g^((ell)) (0) t^ell/(ell!)$ becomes $1/(ell!)$ times the above, with the denominator $norm(dots)$ terms cancelling.
This leads to the following theorem.

#theorem([Taylor in $RR^n$])[
  Let $f : Omega subset RR^n -> RR$, $f in C^(k + 1) (Omega)$. Then, for any $x^0 in Omega$, $ f(x) = f(x^0) + sum_(j=1)^k 1/(j!) [sum_(i_1, dots, i_j = 1)^n (partial^j f)/(partial x_i_1 dots.c partial x_(i_j)) (x_i_1 - x^0_i_1) dots.c (x_i_ell - x^0_i_j)] + R_k (f)(x), $ where $ abs(R_k (f)(x))/(norm(x - x^0)^k) <= M_k norm(x - x^0) quad "as" x -> x^0. $
]

#remark[
  The $k$-th order Taylor polynomial of $f$ is the quantity $ P_k (f)(x) = f(x_0) + sum_(j=1)^k 1/(j!) [sum_(i_1, dots, i_j = 1)^n (partial^j f)/(partial x_i_1 dots.c partial x_(i_j)) (x_i_1 - x^0_i_1) dots.c (x_i_ell - x^0_i_j)] $ before the remainder, and is a "good approximation" to $f(x)$ for $x$ near $x^0$, provided $ lim_(x-> x^0) abs(R_k (f)(x))/(norm(x - x^0)^k) = 0. $ If we just make this assumption on the remainder term, we get the following more general result with weaker assumptions:
]

#theorem[
  Let $f : Omega subset RR^n -> RR$ be $C^(k - 1) (Omega)$ and assume $D^(k - 1) f$ is differentiable at $x^0 in Omega$. Then the $k$th order Taylor expansion for $f$ about $x^0$ from the previous theorem still holds, but with now $ lim_(x -> x^0) abs(R_k (f) (x))/(norm(x - x^0)^k) = 0. $
]
#remark[
  Of course, we lose the rate of decay of the remainder, but we gain fewer assumptions needed on $f$.
]

#example[
  Let $f(x, y) = e^x + sin(x y)$. Then $ f(0,0) = 1, $ $ f_x (0,0) = 1, quad f_y (0,0) = 0, $ $ f_(x x) (0,0 ) = 1, quad f_(x y) (0,0) = 1 \
  f_(y x) (0,0) = 1, quad f_(y y) (0,0) = 0. $ Thus, $ f(x, y) = 1 + x + x^2/2 + x y + R_2 (f)(x, y), $ with $ abs((R_s (f)(x, y))/(x^2 + y^2)) <= M sqrt(x^2 + y^2). $
]

== Lagrange Multipliers

The basic problem is, given $f, g : Omega subset RR^n -> RR$  both $C^1 (Omega),$ putting $Sigma := {x in Omega : g(x) = 0}$, to find $ max f|_Sigma, quad min f|_Sigma. $ We call $g : Omega -> RR$ the "constraint function" (i.e., we are doing constrained optimization of $f$ subject to $g$).


#theorem[
  Let $f, g$ as above, and assume $D g (x^0) eq.not 0$ for all $x^0 in Sigma$. Then, if $f|_Sigma$ has a max or min at $x_0 in Sigma$, then there exists $lambda in RR$ such that $ gradient f(x_0) = lambda gradient g(x_0). $
]

#proof[
  Let $x^0 in Sigma$. Since by assumption $gradient g(x_0) eq.not 0$, then we can assume (by possibly relabelling the coordinates in $RR^n$) that $(partial g)/(partial x_n) (x^0) eq.not 0$. We can write $ Sigma = {g(x', x_n) = 0}, $ with $x' = (x_1, dots, x_(n - 1))$. By IFT, $Sigma$ then is of the form $ x_n = h(x'), $ for $x' in RR^(n - 1)$ for $(x', x_n) in Omega$ near $x^0 in Sigma$, where $h in C^1$ locally to $x'_0 := (x^0_1, dots, x^0_(n - 1))$. Now, we set $ F = f|_Sigma, $ so that $ F(x') = f(x', h(x')) $ locally to $x'_0$. Since $x'$ a local max/min of $F$, we know that $gradient F(x') = 0$. Applying chain rule (valid since $h in C^1$) above, we also know that $ 0 =gradient_(x') F(x'_0) & = gradient_(x') f(x'_0, h(x'_0)) = ((partial f)/(partial x_i) (x_0) + (partial h)/(partial x_i) (x'_0) (partial f)/(partial x_n) (x_0))_(i=1)^(n - 1). quad (dagger) $ We also know that $ 0 = G(x') := g(x', h(x')) $ for all $x'$ local to $x'_0$, and hence $gradient G(x') = 0$ local to $x'_0$ as well, i.e. $ 0 = gradient_(x') G(x'_0) = ((partial g)/(partial x_i) (x_0) + (partial h)/(partial x'_i) (x'_0) (partial g)/(partial x_n) (x_0) )_(i=1)^(n-1). quad (dagger.double) $ Since $(partial g)/(partial x_n) (x_0) eq.not 0$ by assumption, we use $(dagger.double)$ to isolate $ (partial h)/(partial x'_i) (x'_0) = -[(partial g)/(partial x_n) (x_0)]^(-1) (partial g)/(partial x_i) (x_0), quad i = 1, dots, n - 1. $ Plugging these expressions into $(dagger)$, we obtain $ (partial f)/(partial x_i) (x_0) = [(partial g)/(partial x_n) (x_0)]^(-1) (partial f)/(partial x_n) (x_0) (partial g)/(partial x_i) (x_0) , quad i = 1, dots, n - 1. $ This implies $ gradient f(x_0) = ((partial f)/(partial x_1) (x_0), dots, (partial f)/(partial x_(n-1)) (x_0), (partial f)/(partial x_(n)) (x_0)) = underbrace([((partial f)/(partial x_n) (x_0))/((partial g)/(partial x_n) (x_0))], = lambda) ((partial g)/(partial x_1) (x_0), dots,(partial g)/(partial x_(n-1)) (x_0), (partial g)/(partial x_n) (x_0)) = lambda gradient g (x_0), $ as claimed (remarking that equality for the first $n - 1$ entries follows from our work above, and the last $n$ is trivial since then the denominator of $lambda$ cancels with the $n$th entry of $gradient g$.)
]


#theorem("Max/min")[
  Let $Omega subset RR^n$ be a domain with bounded closure, with $Omega subset tilde(Omega)$ and assume $f, g : tilde(Omega) -> RR$ are $C^1 (tilde(Omega))$, where $ partial Omega = {x in tilde(Omega) | g(x) = 0} $ (we say $g$ the _defining function_ of $partial Omega$). Then,
  1. if $x^0 in partial Omega$ a local max/min of $f|_(partial Omega)$ then $gradient f(x^0) = lambda gradient g(x^0)$ for some $lambda in RR$,
  2. if $x^0 in "int"(Omega)$ a local max/min of $f$ in $"int"(Omega)$, then $gradient f(x^0) = 0$, and
  3. the global max (resp. min) of $f|_(overline(Omega))$ is largest (resp. smallest) value of $f$ at all points in 1., 2.
]

#proof[
  Apply the previous result with $Sigma = partial Omega$.
]

#theorem("Multiple Constraints")[
  Let $f, g_i : Omega subset RR^n -> RR$ $i = 1, dots, k$ are all $C^1 (Omega)$. Let $ Gamma_0 := {x in Omega | g_i (x) = 0, quad i = 1, dots, k } $ and assume $ {gradient g_1 (x), dots, gradient g_k (x)} $ are linearly independent for $x in Gamma_0$. Then if $f|_(Gamma_0)$ has max/min at $x^0 in Gamma_0$, there exist $lambda_1, dots, lambda_(k)$ such that $ gradient f(x^0) = sum_(i=1)^k lambda_i gradient g_i (x^0). $
]

#example[
  Find the absolute max/min of $f(x_1, dots, x_n) = x_1 + x_2$ in $D_1 (0) = {abs(x)^2 <= 1}$. We take $g(x) = abs(x)^2 - 1$. Since $gradient f(x) = (1, 1, 0, dots, 0)$ there cannot be any interior critical points. By Lagrange, at $x_0 in partial D_1$, a max/min occuring implies $ gradient f(x^0) = lambda gradient g(x^0) <=> (1, 1, 0, dots, 0) = 2 lambda (x_1^0, dots, x_n^0). $ Note that $lambda$ can't be zero, thus $x_3^0, dots, x_n^0 = 0$ and $x_1^0 = 1/(2 lambda) = x_2^0$. Since $x_1^0, x_2^0 in partial D_1 (0)$ as well, we know $(x_1^0)^2 + (x_2^0)^2 = 1$. This implies $lambda = plus.minus sqrt(1/2)$ and so $x_1^0 = x_2^0 = plus.minus 1/sqrt(2)$. We see that $ f(1/sqrt(2), 1/sqrt(2), 0, dots, 0) = sqrt(2), quad f(-1/sqrt(2), - 1/sqrt(2), 0, dots, 0) = - sqrt(2), $ thus the global max of $f$ is $sqrt(2)$ and the global min of $f$ is $-sqrt(2)$.
]

#pagebreak()
= Riemann Integration

== Integration over Box Domains in $RR^n$


A _box_ $B subset RR^n$ is a closed and bounded subset of the form $ B = [a_1, b_1] times dots.c times [a_n, b_n]. $

Given a function $f : B -> RR$, we want to define the Riemann integral (we will drop the "Riemann" specification from here on) of $f$ over $B$, i.e. $integral_B f dif V$.

We know that in $n = 1$, for a function $h : [a, b] -> RR$ (assume nonnegative for simplicity), then $ integral_(a)^b h(x) dif x =^"if it exists" lim_(n -> infinity) sum_(i=1)^n h(x_i) Delta x_i, $ where $a = x_0 < x_1 < dots.c < x_(n - 1) < x_n = b$ a partition of $[a, b]$ and $Delta x_i = x_(i) - x_(i-1)$. With this as "motivation", say, we will define the integral of $f$ over $B$.

#definition("Partition of a box")[
  Let $B$ a box as above. A _partition_ of $B$ is an ordered set $ cal(P) = {P_i}_(i=1)^n, quad P_i = {x_i^(0), dots, x_i^(m_i)}, $ where each $P_i$ a partition of $[a_i, b_i]$ with $a_i = x_i^0 < x_i^(1) < dots.c < x_i^(m_i - 1) < x_i^(m_i) = b_i$.
]

#definition("Refinement")[
  Given two partitions $cal(P) = {P_i}, tilde(cal(P)) = {tilde(P)_i}$, we say that $tilde(cal(P))$ is a _refinement_ of $cal(P)$ (and write $tilde(cal(P)) supset cal(P)$) if for each $j = 1, dots, n$, $P_j subset tilde(P)_j$.
]

#definition(
  "Subbox",
)[Given a partition $cal(P)$ of $B$, let $ B_(i_1, i_2, dots, i_n) subset.eq B = [x_1^(i_1 - 1), x_1^(i_1)] times dots.c times [x_n^(i_n - 1), x_n^(i_n)] $ be a _subbox_ of $B$, for some ${i_1, dots, i_n}$ partition indices for $cal(P)$ (i.e., $1 <= i_j <= m_j$ for $j = 1, dots, n$). We define then $ Delta x_j^(i_j) := x_j^(i_j) - x_j^(i_(j) - 1), quad j = 1, dots, n, 1 <= i_j <= m_j, $ for the length of the $j$th interval in the subbox, and $ Delta V_(i_1, dots, i_n) := Delta x_1^(i_1) dots.c Delta x_n^(i_n) $ as thus the volume of the subbox $B_(i_1, dots, i_n)$. ]

Heuristically, then, we'd like to define $integral_B f dif V$ as $ lim_(m_1 -> infinity) dots.c lim_(m_n -> infinity) sum_(i_1 = 1)^(m_1) dots.c sum_(i_n = 1)^(m_n) f(x_1^(i_1), dots, x_n^(i_n)) Delta V_(i_1, dots, i_n). $
The key question, then, is when does the sum on the right-hand side exist?

#definition("Lower/Upper Riemann Sum")[
  Let $f : B -> RR$ be bounded and $cal(P)$ a partition of $cal(B)$. Define the _lower Riemann sum_ of $f$ over $B$ corresponding to partition $cal(P)$ by $ L(f, cal(P)) & := sum_(i_1 = 1)^(m_1) dots.c sum_(i_n = 1)^(m_n) (inf_(x in B_(i_1, dots, i_n)) f(x)) Delta V_(i_1, dots, i_n). $ Similarly define the _upper Riemann sum_ (of $f$ over $B$ corresponding to partition $cal(P)$) by $ U(f, cal(P)) & := sum_(i_1 = 1)^(m_1) dots.c sum_(i_n = 1)^(m_n) (sup_(x in B_(i_1, dots, i_n)) f(x)) Delta V_(i_1, dots, i_n). $
]

#remark[
  This infs/sups are well-defined since $f$ bounded.
]

#lemma[
  Let $f : B -> RR$ be bounded and $tilde(cal(P)) supset cal(P)$ a refinement. Then, $ L(f, cal(P)) <= L(f, tilde(cal(P))) <= U(f, tilde(cal(P))) <= U(f, cal(P)). $
]

#proof[
  The intermediate inequality is obvious.

  Since $tilde(cal(P)) supset cal(P)$, then there exists $N_i_j in ZZ^+$ and $i_(1, ell_1), dots, i_(n, ell_n)$ (indices of the refined partition) such that $ B_(i_1, dots, i_n) = union.big_(ell_1 = 1)^(N_i_1) dots.c union.big_(ell_n = 1)^(N_i_n) tilde(B)_(i_(1, ell_1), dots, i_(n, ell_n)), $ with $tilde(dot)$ used to denote objects belonging to the refinement. Thus, $ inf_(x in B_(i_1, dots i_n)) f(x) <= inf_(x in tilde(B)_(i_(1, ell_1), dots i_(n, ell_n))) f(x), quad sup_(x in B_(i_1, dots i_n)) f(x) >= sup_(x in tilde(B)_(i_(1, ell_1), dots i_(n, ell_n))) f(x). $ Summing over the $i_1, dots, i_n$'s and multiplying by the appropriate volumes gives the result.
]

#definition[
  Let $f : B -> RR$ bounded. Define $ cal(U)(f) := inf_(cal(P)) {U(f, cal(P))}, quad cal(L)(f) := sup_(cal(P)) {L(f, cal(P))}. $
]

#remark[
  If $f$ bounded with $m <= f <= M$ over $B$, then $ m "vol"(B) <= U(f, cal(P)) <= M "vol"(B) $ for any partition $cal(P)$, similar for the lower Riemann sum. This implies these two quantities above are well-defined (infs/sups taken over bounded sets). Moreover, we take inf/sup respectively for the upper/lower sums because of the respective monotonicity properties we proved in the previous lemma.
]

#definition("Riemann integrable")[
  Let $f : B -> RR$ be bounded. Then, we say that $f$ is _Riemann integrable_ (RI) over $B$ if $cal(L)(f) = cal(U)(f)$, in which case we define $ integral_B f dif V := cal(L)(f) = cal(U)(f). $
]

#lemma[
  Let $f : B -> RR$ be bounded then $f$ is RI over $B$ iff $forall epsilon > 0$, there exists a partition $cal(P)$ of $B$ such that $ U(f, cal(P)) - L(f, cal(P)) <= epsilon. $
]

#proof[
  ($impliedby$) We know $U(f, cal(P)) >= cal(U)(f)$ and $L(f, cal(P)) <= cal(L)(f)$, so this is immediate since then we conclude that for all $epsilon > 0$, $ cal(U)(f) <= U(f, cal(P)) <= L(f, cal(P)) + epsilon <= cal(L)(f) + epsilon. $ Since this holds for all $epsilon > 0$, this implies $cal(U)(f) - cal(L)(f) <= epsilon$ for all $epsilon > 0$ and thus must be equal, since $cal(U)(f) >= cal(L)(f)$ always.

  ($=>$) For any $epsilon > 0$, there exists a $cal(P)_1$ with $L(f, cal(P)_1) - cal(L)(f) <= epsilon/2$ and $cal(P)_2$ with $cal(U)(f) - U(f, cal(P)_2) <= epsilon/2$. Let $cal(P) = cal(P)_1 union cal(P)_2$, then the result follows by monotonicity and triangle inequality.
]

#theorem[
  Let $f : B -> RR$ be in $C^0 (B)$. Then $f$ is Riemann integrable.
]

#proof[
  Since $f$ continuous on a compact set it is uniformly continuous. Thus for any $epsilon > 0$, we can find a partition $cal(P)$ such that for every subbox $B_(i_1, dots, i_n)$, we have $ sup_(x in B_(i_1, dots, i_n)) f(x) - inf_(x in B_(i_1, dots, i_n)) f(x) < epsilon/("vol"(B)). $  This readily implies $U(f, cal(P)) - L(f, cal(P)) <= epsilon$, so the result follows by the previous lemma.
]

#lemma("Mean Value Theorem for Integrals")[
  Let $f : B -> RR$ be continuous. Then, there exists $x_0 in B$ such that $integral_B f dif V = f(x_0) "vol"(B)$.
]

#proof[
  Let $m := inf_B |f|$, $M := sup_B |f|$. Then $ m dot "vol"(B) <= integral_B f dif V <= M dot "vol"(B). $ Then we can just apply the intermediate value theorem to $f$.
]

== General Riemann Integration

We've defined the Riemann integral for $f$ continuous over box domains, but we wish to define the integral for more general domains. Let $Omega$ a bounded domain in $RR^n$ and let $B$ a box with $Omega subset B$. Extend $f : Omega -> RR$ to $F : B -> RR$ by $ F(x) := cases(f(x) quad & x in Omega, 0 & x in B \\ Omega). $
Heuristically, then, we wish the integral to satisfy the following: $ integral_B f dif V = integral_Omega f dif V + integral_(B \\ Omega) F dif V = integral_Omega f dif V. $

#definition[
  Given $f : Omega -> RR$ bounded, set $ integral_Omega f dif V := integral_B F dif V, $ whenever the right-hand side exists.
]

This leaves the obvious next question - what happens when $f$ not continuous? When is the integral defined?

#definition[
  Let $Gamma subset RR^n$ is of _content zero_ if for all $epsilon > 0$, there exist closed box domains $B_1^0, dots, B_N^0 subset RR^n$ such that $Gamma subset union.big_(n=1)^N B_i^0$ and $sum_(i=1)^N "vol"(B_i^0) < epsilon$.
]


#remark[
  1. The closed boxes can be replaced with open boxes
  2. If $D_1, dots, D_N$ are content zero so are their union
]

#theorem[
  Suppose $f : B subset RR^n -> RR$ bounded. Let $ Gamma(f) := {x in B : f "discontinuous at" x}. $ Then, if $Gamma(f)$ has content zero, then $integral_B f dif V$ exists.
]

#proof[
  We prove using the lemma following the definition of Riemann integrability. Let $epsilon > 0$ and put $M := sup_(B) |f|$. Since $Gamma(f)$ has content zero, there exists $B_1^0, dots, B_N^0 subset RR^n$ such that $ Gamma(f) subset union.big_(i=1)^N B_i^0, quad "and" quad sum_(i=1)^N "vol"(B_i^0) < epsilon/(4 (M + 1)). $ Let $P_0$ be a partition of $B$ such that each subrectangle $B_(i_1, dots, i_n)$ is either in some $B_j^0$, or doesn't intersect any such $B_j^0$ i.e. $B_(i_1, dots, i_n) sect (union.big_(i=1)^N B_i^0) = nothing$. Let $A$ be the union of these boxes that don't intersect $union.big_(i=1)^N B_i^0$. $A$ is compact, being bounded ($A subset B$) and closed (finite union of closed sets). Thus $f|_A$ is uniformly continuous, and so there exists a refined partition $tilde(cal(P))$ of $cal(P)$ such that for each subrectangle $Q in tilde(cal(P))$ that is a subset of $A$, $ sup_Q f - inf_Q f < epsilon/(2 ("vol"(B)+1)). $ Then $ U(f, tilde(cal(P))) - L(f, tilde(cal(P))) &= sum_(Q subset A) (sup_Q f - inf_Q f) "vol"(Q) + sum_(Q in tilde(cal(P)), Q subset.not A) (sup_Q f - inf_Q f) "vol"(Q) \
  & <= (epsilon "vol"(B))/(2 ("vol"(B) + 1)) + (2 M) dot epsilon/(4 M + 1) <= epsilon. $
]

#example[
  Let $Omega subset RR^(n - 1)$ compact and $g : Omega -> RR$ continuous. Then $Gamma := {(x', g(x')) : x' in Omega}$ is has content zero.
]

#corollary[
  Suppose $f : B -> RR$ bounded and $Gamma(f)$ the union of finitely many graphs of continuous functions over closed, bounded domains in $RR^(n - 1)$. Then $f$ is integrable over $B$.
]

#corollary[
  Let $Omega subset RR^n$ closed and bounded and suppose $partial Omega$ the union of finitely many graphs of $C^0$ functions over closed domains in $RR^(n - 1)$. Suppose $f : Omega -> RR$ bounded and $Gamma(f) sect Omega$ has content zero. Then $integral_Omega f dif V$ exists.
]

There is a special case of the previous result that is of practical importance. Let $Omega subset RR^n$ closed and bounded and suppose $Omega subset tilde(Omega)$ a bounded a domain.
Let $G in C^1 (tilde(Omega))$ be a defining function for $partial Omega$, i.e. $ partial Omega = {G(x) = 0 : x in tilde(Omega)}, quad gradient G(x) eq.not 0 forall x in partial Omega. $ By inverse-function theorem, $partial Omega$ is the finitely many (since compact) graphs of $C^1$-functions over closed and bounded domains in $RR^(n - 1)$. Thus, we have the following:

#corollary[
  Let $Omega := {G(x) <= 0, x in RR^n}$ be bounded and assume $gradient G (x) eq.not 0$ whenever $G = 0$. Suppose $f : Omega -> RR$ bounded and $Gamma(f) sect Omega$ has content zero. Then $integral_Omega f dif V$ exists.
]


== Basic Properties of Integrals

#proposition[
  Assume $Omega subset RR^n$ bounded and $f, g : Omega -> RR$ are both Riemann integrable over $Omega$. Then,
  1. $integral_(Omega) (f + g) dif V = integral_(Omega) f dif V + integral_(Omega) g dif V$
  2. $integral_(Omega) alpha f dif V = alpha integral_(Omega) f dif V, quad alpha in RR$
  3. $f <= g => integral_(Omega) f dif V <= integral_(Omega) g dif V$
  4. If $Omega = Omega_1 union Omega_2$ with each $Omega_i$ bounded with $Omega_1 sect Omega_2$ having content zero, then $ integral_Omega f dif V = integral_(Omega_1) f dif V + integral_(Omega_2) f dif V. $
]


== Fubini's Theorem


Given $Omega subset RR^n$ bounded etc, how do we actually compute $integral_(Omega) f dif V$? Consider $B = [a, b] times [c, d] subset RR^2$ (2 dimensions is sufficient to demonstrate the main results).

Given $f : B -> RR$ bounded, we define the iterated integrals $ integral_a^b integral_c^d f(x, y) dif y dif x := integral_a^b [integral_c^d f(x, y) dif y] dif x, $ similarly for the other order. We assume formally for now that both 1-dimensional integrals involved exists, i.e. that $integral_a^b f(x, y) dif x$ exists for $y in [c, d]$ and $integral_c^d f(x, y) dif y$ exists for $x in [a, b]$. Fubini essentially says that both of these iterated integrals are equal to $integral_B f dif V$.

#remark[
  For $Omega subset RR^2$ we often denote $integral_Omega f dif V =: integral.double_Omega f dif A$.
]


#theorem("Fubini for Box Domains")[
  Suppose $f : B -> RR$ is Riemann integrable with $B = [a, b] times [c, d]$.
  1. Assume $integral_c^d f(x, y) dif y$ exists for all $x in [a, b]$. Then the iterated integral $integral_a^b integral_c^d f(x, y) dif y dif x$ exists and equals $integral_Omega f dif V$.
  2. The same statement, but with the other iterated integral.
]

#proof[
  For any $epsilon > 0$ choose $cal(P)$ of $B$ such that $U(f, cal(P)) - L(f, cal(P)) < epsilon$. This partition induces partitions $ cal(P)_x = {x_0 = a < x_1 < dots.c < x_(n - 1) < x_n = b}, quad cal(P)_y = {y_0 = c < y_1 < dots.c < y_(m - 1) < y_m = d}. $ Set $F(x) = integral_c^d f(x, y) dif y = sum_(j=1)^m integral_(y_(j-1))^(y_j) f(x, y) dif y$. We compute $ U(F, cal(P)_x) = sum_(i=1)^n (sup_(x in [x_(i - 1), x_i]) F(x)) Delta x_i, quad L(F, cal(P)_x) = sum_(i=1)^n (inf_(x in [x_(i - 1), x_i]) F(x)) Delta x_i. $ Thus, we find $ U(F, cal(P)_x) &= sum_(i=1)^n (sup_(x in [x_(i - 1), x_i]) sum_(j=1)^m integral_(y_(j-1))^(y_j) f(x, y) dif y) Delta x_i \
  & <= sum_(i=1)^n sum_(j=1)^m [sup_(x in [x_(i - 1), x_i]) integral_(y_(j - 1))^(y_j) f(x, y) dif y] Delta x_i \
  & <= sum_(i=1)^n sum_(j=1)^m [sup_(x in [x_(i-1), x_i]) sup_(y in [y_(j-1), y_j]) f(x, y)] Delta y_(j) Delta x_i \
  & = sum_(i=1)^n sum_(j=1)^m [sup_((x, y) in B_(i j)) f(x, y)] Delta B_(i j), quad B_(i j) := [x_(i-1), x_i] times [y_(j-1), y_j] \
  &= U(f, cal(P)). $ Similar work shows $L(F, cal(P)) >= L(f, cal(P))$ and thus $ U(F, cal(P)) - L(F, cal(P)) <= U(f, cal(P)) - L(f, cal(P)) < epsilon $ which gives the proof.
]

=== Fubini for More General Domains

#definition[
  A domain $Omega subset RR^2$ is called _$y$-simple_ if it is of the form $ Omega = {a <= x <= b, phi_1 (x) <= y <= phi_2 (x)}, $ for some $phi_1, phi_2 in C^0 ([a, b])$. Similarly it is called _$x$-simple_ if $ Omega = {c <= y <= d, psi_1 (y) <= x <= psi_2 (y)} $ for some $psi_1, psi_2 in C^0 ([c, d])$. Finally, it is called _simple_ if it is both $x$- and $y$-simple, and _elementary_ if it is $x$- or $y$-simple.
]


#theorem("Fubini")[
  Suppose $Omega subset RR^2$ is bounded and $f$ integrable over $Omega$.
  1. If $Omega$ is $y$-simple and for all $x in [a, b]$, $integral_(phi_1 (x))^(phi_2 (x)) f(x, y) dif y$ exists, then $ integral_Omega f dif V = integral_(a)^b integral_(phi_1 (x))^(phi_2 (x)) f(x, y) dif y dif x. $
  2. The analogous statement for $x$-simple.
  3. If both $x$- and $y$-simple, we can compute the Riemann integral with either iterated integral in 1., 2..
]

#proof[
  Suppose $Omega$ $y$-simple. Choose a box domain $B = [a, b] times [c, d]$ for which $Omega subset B$. Then $ integral.double_(Omega) f dif A = integral.double_B F dif A, quad F := cases(
    f quad "in" Omega,
    0 quad "else"
  ). $ Note $F$ RI since $f$ is. By Fubini on box domains, $ integral.double_B F dif A = integral_(a)^b integral_(c)^d F(x, y) dif y dif x = integral_(a)^b integral_(phi_1 (x))^(phi_2 (x)) F(x, y) dif y dif x = integral_(a)^b integral_(phi_1 (x))^(phi_2 (x)) f(x, y) dif y dif x, $ since $F(x, dot)$ is zero outside $y in [phi_1 (x), phi_2 (x)]$. The proof for $x$-simple domains follows similarly.
]

#example[Compute $integral.double_Omega x dif A$ where $Omega = {(x, y) : 0 <= x <= sqrt(pi), 0 <= y <= sin(x^2)}$. It's clear $(x, y) |-> x$ continuous on $Omega$ and since $Omega$ is bounded and $y$-simple, the double integral exists and moreover can be computed using Fubini's. We have $ integral.double_Omega x dif A & = integral_(0)^(sqrt(pi)) integral_(0)^(sin(x^2)) x dif y dif x \
                                & = integral_(0)^(sqrt(pi)) x sin(x^2) dif x quad [u = x^2] \
                                & = 1/2 integral_(0)^pi sin(u) dif u = 1. $
]

#example[
  Compute $I = integral_(0)^1 integral_(y)^1 e^(x^2) dif x dif y$. We can't compute the inner integral in closed-form. But, if we let $Omega := {(x, y) : 0 <= y <= 1, y <= x <= 1}$, we find that $I = integral.double_Omega e^(x^2) dif A$. We can rewrite this domain as $Omega = {(x, y) : 0 <= x <= 1, 0 <= y <= x}$, and thus by Fubini's (everything that needs to be continuous is continuous), $ I & = integral_(0)^1 integral_(0)^x e^(x^2) dif y dif x \
    & = integral_(0)^1 x e^(x^2) dif x \
    & = 1/2 (e - 1). $
]


=== Fubini in $RR^n$

Given a box domain $B subset RR^n$, write $ underline(integral_(B)) f dif V := cal(L)(f), quad overline(integral_B) f dif V := cal(U)(f) $ (here, $f$ needn't be RI).


#theorem[
  Let $B = B_1 times B_2$ be a box domain in $RR^n$ where $B_1 subset RR^k$, $B_2 subset RR^(n - k)$ are also boxes. Suppose $f : B -> RR$ is Riemann integrable. Set $ ell(x) := underline(integral_(B_2)) f(x, y) dif V(y), quad u(x) := overline(integral_(B_2)) f(x, y) dif V(y), quad x in B_1 $ and $ tilde(ell)(y) := underline(integral_(B_1)) f(x, y) dif V(x), quad tilde(u)(y) := overline(integral_(B_1)) f(x, y) dif V(x), quad y in B_2. $
  Then, $ell(x)$ and $u(x)$ are Riemann integrable over $B_1$ and $tilde(ell)(y)$ and $tilde(u)(y)$ are Riemann integrable over $B_2$. Moreover, $ integral_B f dif V & = integral_(B_1) ell(x) dif V (x) = integral_(B_1) u(x) dif V(x), \
  integral_B f dif V & = integral_(B_2) tilde(ell)(y) dif V(y) = integral_(B_2) tilde(u)(y) dif V(y). $
]

#proof[
  The proof follows in the same way as in $RR^2$ by noting the following: $ L(f, cal(P)) <= L(ell(x), cal(P)_x), quad U(u(x), cal(P)_x) <= U(f, cal(P)). $ This implies, suping/infing over all $cal(P)$, $ cal(L)(f) <= cal(L)(ell(x)), quad cal(U)(u(x)) <= cal(U)(f) $ and thus since $f$ Riemann integrable, $ 0 = cal(U)(f) - cal(L)(f) & >= cal(U)(u(x)) - cal(L)(ell(x)) >= 0 => cal(U)(u(x)) = cal(L)(ell(x)) $ thus $ell(x)$ Riemann integrable and in particular $cal(L)(f) = cal(L)(ell(x)) = cal(U)(ell(x)) = cal(U)(f)$. Similar holds in the $y$-variables.
]

#remark[
  If for all $x in B_1$, $f(x, y)$ is integrable in $B_2$ (i.e. $integral_(B_2) f(x, y) dif V(y)$ exists), then $ integral_(B) f dif V & = integral_(B_1) [integral_(B_2) f(x, y) dif V(y)] dif V(x). $ Similarly, if $integral_(B_1) f(x, y) dif V(x)$ exists for all $y in B_2$, then $ integral_(B) f dif V = integral_(B_2) [integral_(B_1) f(x, y) dif V(x)] dif V(y). $
]

=== Fubini's in $RR^3$

#definition[
  A bounded domain $W subset RR^3$ is called _$z$-simple_ if there exists an elementary region $Omega subset RR^2$ and $eta_1, eta_2 in C^0 (Omega)$ such that $ W = {(x, y, z) : (x, y) in Omega, eta_1 (x, y) <= z <= eta_2 (x, y)}. $ Analogous definitions hold for $x$-, $y$-simple as in the $RR^2$ case. We additionally say $W$ elementary if it is simple in some axis.
]

#theorem([Fubini in $RR^3$])[
  Suppose $W subset RR^3$ is bounded and $z$-simple and $f : W -> RR$ is RI. Assume that for all $(x, y) in Omega$, $integral_(eta_1 (x, y))^(eta_2 (x, y)) f(x, y, z) dif z$ exists. Then, it is Riemann integrable over $Omega$ and $ integral.triple_(W) f dif V
  = integral_(Omega) [integral_(eta_1 (x, y))^(eta_(2 (x, y))) f(x, y, z) dif z ] dif V(x, y). $ Similar holds for $x$-, $y$- simple domains.
]

#proof[
  Follows as in $RR^2$.
]

== Change of Variables Formula

Let $Omega subset RR^n$ be a bounded domain. We defined $integral_Omega f dif V$ by looking at $L(f, cal(P))$ and $U(f, cal(P))$ where $cal(P)$ was a _rectangular partition_. Can we use other partitions of $Omega$ that are _not_ rectangular?

#definition[
  Let $Omega subset RR^n$ be a domain with content zero boundary. A _regular partition_ $cal(P)_"reg" = {D_k}_(k=1)^N$ is a collection of subdomains of $D_k subset Omega$ such that
  1. $Omega = union.big_(k=1)^N D_k$ and $"Content"(partial D_k) = 0$ for all $k = 1, dots, N$, and
  2. $"Content"(D_k sect D_ell) = 0$ for $k eq.not ell$.
]

#definition[
  $f : Omega -> RR$ is bounded where $Omega$ a bounded domain and $cal(P)_"reg" = {D_k}_(k=1)^N$ a regular partition of $Omega$. Define $ U(f, cal(P)_"reg") := sum_(k=1)^N (sup_(D_k) f) "vol"(D_k), quad L(f, cal(P)_"reg") := sum_(k=1)^N (inf_(D_k) f) "vol"(D_k). $
]

#lemma[
  Let $f : B -> RR$. Then $f$ is Riemann integrable over $B$ iff for any $epsilon > 0$ there exists a regular partition $cal(P)_"reg"$ of $B$ such that $ U(f, cal(P)_"reg") - L(f, cal(P)_"reg") < epsilon. $
]

#proof[
  ($=>$) is immediate, since a rectangular partition is regular and we already know the analogous statement for such partitions.

  ($impliedby$) Fix $epsilon > 0$ and let $cal(P)_"reg" = {D_k}$ is such that $ U(f, cal(P)_"reg") - L(f, cal(P)_"reg") < epsilon. $ Then, $Gamma := union.big_(k) partial D_k$ has content zero by assumption, and so there exist boxes $B_1, dots, B_m$ such that $Gamma subset union.big_(j) B_j$ and $sum_(j) "vol"(B_j) < epsilon/(2 (M + 1))$ where $M := sup_B abs(f)$. Pick a box partition $cal(P)$ such that $ sum_(B_i in cal(P) \ cal(B_i) sect Gamma eq.not nothing) "vol"(B_i) < epsilon/(2 (M + 1)), $ and for each $B_j subset cal(P)$ with $B_j sect Gamma = nothing$ we have that $B_j subset D_ell$ for some $ell$ (obtained by refining). Note that if $B_j$ is such that $B_j sect Gamma$, $ 0 <= sup_(B_j) f - inf_(B_j) f <= sup_(D_ell) f - inf_D_ell f. $ Then $ U(f, cal(P)) - L(f, cal(P)) & = sum_(B_i in cal(P) \ B_i sect Gamma eq.not nothing) (sup_(B_i) f - inf_(B_i) f) "vol"(B_i) + sum_(B_i in cal(P) \ B_i sect Gamma = nothing) (sup_(B_i) f - inf_(B_i) f) "vol"(B_i) \
  & <= 2 M sum_(B_i in cal(P) \ B_i sect Gamma eq.not nothing) "vol"(B_i) + sum_(D_ell) (sup_D_ell f - inf_(D_ell)) "vol"(D_ell) \
  & < (2 M) epsilon/(2 ( M + 1)) + U(f, cal(P)_"reg") - L(f, cal(P)_"reg") \
  & < 2 epsilon. $
]

#theorem("Change of Variables")[
  Let $Omega, Omega' subset RR^n$ bounded domains and let $T : Omega' -> Omega$ be a $C^1$ map that is bijective from $Omega'$ onto $Omega$. Then, for any $f : Omega -> RR$ which is Riemann-integrable over $Omega$, then $ integral_Omega f dif V = integral_(Omega') (f compose T) abs(det D T) dif V. $
]

To prove, we need to first observe how the volume of a box $B$ changes under application of $T$. Let $B' subset Omega'$ be a small rectangular box. Since $T$ $C^1$, by Taylor expansion, we have for any $y_0 in B' subset RR^n$, $ T(y) = T(y_0) + D T(y_0) (y - y_0) + E_1 (y, y_0) $ where $lim_(y -> y_0) norm(E_1 (y, y_0))/(norm(y - y_0)) = 0$. Since $D T (y_0)$ is linear, $ "vol"(T(B')) = abs(det(D T(y_0))) "vol"(B') + E_2 (B') $ where for any $epsilon > 0$, there exists $delta > 0$ such that $norm(E_1 (y, y_0)) <= epsilon norm(y - y_0)$ whenever $0 < norm(y - y_0) < delta$. Suppose $B' = {y in RR : max_(j=1)^n abs(y_j - y_j^0) <= delta}$ (a box of side length $delta$). Using the fact that $norm(y - y_0) <= sqrt(n) max_(j=1)^n abs(y_j - y_j^0)$. Then, $ E_2 (B') <= (epsilon norm(y - y_0))^n <= (epsilon sqrt(n) max_(j) abs(y_j - y_j^0))^n <= (sqrt(n))^n epsilon^n (max_(j) abs(y_j - y_j^0))^n = (sqrt(n)^n epsilon^n) "vol"(B') <= C_n epsilon "vol"(B'), $ where $C_n$ some dimensional constant. Thus, $ abs(E_2 (B'))/("vol"(B')) -> 0 "as" norm(y - y_0) -> 0. $

Remark that since $T in C^1 (B')$, $abs(det(D T)) in C^0 (B')$ and so uniformly continuous in $B'$, so given $epsilon > 0$, we can find $delta > 0$ such that $abs(E_2 (B')) <= epsilon "vol"(B')$ and $abs(abs(det (D T (y_0))) - abs(det D T (y))) <= epsilon$ for any $y in B'$ with $norm(y - y_0) < delta$ (?) and thus, for all $epsilon> 0$, there exists a $B'$ of sidelength $<=delta$, $ "vol"(T B') = abs(det D T (y)) "vol"(B') + tilde(E)(B'), quad abs(tilde(E)(B')) <= epsilon "vol"(B') $


#proof[
  We use the observations above and the previous lemma on regular partitions. For any $epsilon > 0$, we can find $delta > 0$ and a box $B'$ with sidelength $<delta$ such that $ "vol"(T B') = abs(det D T (y)) "vol"(B') + E_2 (B'), $ for any $y in B'$, where $abs(E_2 (B')) <= epsilon "vol"(B')$.

  Choose a box partition $cal(P)' = {B'_j}$ on $Omega'$. Since $T : Omega' -> Omega$ a $C^1$ bijection onto $Omega$, $cal(P)_"reg" = {D_i = T(B'_i)}$ is a regular partition on $Omega$ (why?).
  We assume that $U(f, cal(P)_"reg") - L(f, cal(P)_"reg") < epsilon$ and $abs(E_2 (B'_i)) <= epsilon "vol"(B'_i)$ for all $B'_i in cal(P)'$, by refinement and since $f$ integrable. Then, $ U(f, cal(P)_"reg") >= U((f compose T) abs(det (D T)), cal(P)') - 2 M epsilon "vol"(Omega'), $ and similarly $ L(f, cal(P)_"reg") <= L((f compose T) abs(det(D T)), cal(P)') + 2 M epsilon "vol"(Omega') $ where $M = sup_Omega abs(f).$ This implies $ epsilon > U(f, cal(P)_"reg") - L(f, cal(P)_"reg") >= U((f compose T) abs(det(D T)), cal(P')) - L((f compose T) abs(det(D T)), cal(P)') - 4 M epsilon "vol"(Omega') \
  => U((f compose T) abs(det(D T)), cal(P')) - L((f compose T) abs(det(D T)), cal(P)') < epsilon (1 + 4 M "vol"(Omega')). $ Since $epsilon$ arbitrary, this proves the result.
]

#example(
  "Polar Coordinates",
)[Take $x = r cos theta, y = r sin theta$, so $r = sqrt(x^2 + y^2)$. Let $T (r, theta) = (x, y)$ from $Omega' -> Omega$ with $Omega' = {(r, theta) in (0, a] times [0, 2 pi)}$ and $Omega = {(x, y) : x^2 + y^2 <= a^2}$. Then $ integral.double_({x^2 + y^2 <= a^2}) f(x, y) dif A = integral.double_(Omega') f(r cos(theta), r sin(theta)) abs(det (D T)) dif r dif theta, $ where $ det(D T) = det(mat(cos theta, - r sin theta; sin theta, r cos theta)) = r. $ By Fubini, then, we get $ integral.double_({x^2 + y^2 <= a^2}) f(x, y) dif A = integral_0^(2pi) integral_0^(a) f(r cos (theta), r sin (theta)) r dif r dif theta. $
]

#example(
  "Spherical Coordinates",
)[Let $x = rho sin phi cos theta, y = rho sin phi sin theta, z = rho cos phi$ and $T(rho, phi, theta) = (x, y, z)$ with $theta in [0, 2 pi), phi in [0, pi)$ and $(0, a]$. In this case $ |det (D T)| = |det mat(
    sin phi cos theta, rho cos phi cos theta, - rho sin phi sin theta;
    sin phi sin theta, rho cos phi sin theta, rho sin phi cos theta;
    cos phi, - sin phi, 0
  )| = rho^2 sin phi $ so that $ integral.triple_({x^2 + y^2 + z^2 <= a^2}) f(x, y, z) dif V = integral_0^(2 pi)
  integral_0^pi integral_0^a f(rho sin phi cos theta, rho sin phi sin theta, rho cos phi). $
]

#example[
  Compute $integral.double_(Omega) (y-x) cos (x y) dif A$, with $Omega$ the region bounded by $x + y = 1, x + y = 4$, $x y = -1$ and $x y = - 4$ and $y - x >= 0$. Let $u = x + y$, $v = x y$ and $T (u, v) = (x, y)$ with $T : Omega' -> Omega$, where we now have $Omega' = {(u, v) in [1, 4] times [-4, -1]}$. Moreover, we have $ (x + y)^2 - (x - y)^2 = 4 x y =>u^2 - (x - y)^2 = 4 v => abs(x - y) = sqrt(u^2 - 4 v). $ Finally, $ abs(det(D T^(-1))) & = |det(mat(1, 1; y, x))| = abs(x - y) => abs(det D T) = 1/(abs(x - y)). $ This implies $ integral.double_Omega (x - y) cos (x y) dif A = integral_(1)^4 integral_(-4)^(-1) cos(v) dif v dif u =3 [sin(-1) - sin(-4)]. $
]

= Vector Fields, Curves and Surfaces

== Integration along Curves

#definition[
  A curve in $RR^n$ is a continuous function $gamma : I -> RR^n$ where $I subset RR$ some interval.
]

#definition[
  Let $gamma$ be a $C^1$ curve defined on $I = [0, L]$. Define the integral over $gamma$ of a real-valued function as $ integral_(gamma) f dif s := integral_0^L f(gamma(t)) abs(gamma'(t)) dif t. $
]

== Integration of Vector Fields

#definition[
  A _vector field_ on $RR^n$ is a function $F : Omega subset RR^n -> RR^n$. We usually assume $F$ $C^0$ on $Omega$.
]

How can we integrate a vector field along a path $gamma$? (think: the work done by $F$ along $gamma$)

Let $gamma : [a, b] -> RR^n$ be a $C^1$ path, and consider $ Delta s_i := gamma(t_i + Delta t_i) - gamma(t_i) $ for $Delta t_i$ _small_. This is a vector.

Thus, since $gamma$ is $C^1$, $ Delta s_i = gamma' (t_i) Delta t_i + R(t, Delta t_i), $ where $norm(R(t, Delta t_i))/(Delta t_i) -> 0$ as $Delta t_i$. We get: $ F(gamma(t)) dot Delta s_i = F(gamma(t_i)) [gamma' (t_i) Delta t_i + R(t_i, Delta t_i)]. $
Takeing $cal(P) = {t_i}_(i=1)^N$ of $[a, b]$, we can repeat this over every partition. This motivates:

#definition[
  Define the _total work done_ by $F$ along $gamma$ by $ integral_(gamma) vec(F) dot vec(dif s) := lim_(N -> infinity) sum_(i=1)^N vec(F)(gamma(t_i)) vec(Delta s_i), $ as defined above. This is equal to $ integral_a^b vec(F)(gamma(t)) dot gamma' (t) dif t, $ assuming the Riemann integral exists, where $gamma$ lives on $[a, b]$.
]

#definition[
  Let $gamma$ a piecewise smooth path and $F$ a vector field defined in a neighborhood of $gamma$. The _line integral_ (also called _path integral_) of $F$ along $gamma$ is $ integral_(gamma) F dot dif s = integral_c^b F (gamma(t)) dot.c gamma'(t) dif t. $
]

If $gamma$ is regular, i.e. $gamma' (t) eq.not 0$, let $T (t) = (gamma'(t))/norm(gamma' (t))$ be the _unit tangent field_. Then, we see that $ integral_gamma F dot dif s = integral_gamma F (gamma(t)) dot T(t), $ where $dif s equiv norm(gamma' (t)) dif t$ the "arclength element".

Formally, we write $vec dif s = vec T dif s$.

#lemma[
  If $gamma$ a piecewise-smooth path and $tilde(gamma)$ a reparametrization of $gamma$, then if $F$ a $C^0$ vector field, then $ integral_gamma F dot dif s = epsilon integral_(tilde(gamma)) F dot dif s, $ where $epsilon = +1$ if an orientation-preserving reparametrization, and $epsilon = - 1$ if an orientation-reversing reparametrization.
]

=== Conservative Vector Fields

#definition[
  A vector field $F : Omega -> RR^n$ is _conservative_ in $Omega$ if there exists a $C^1$ function $f : Omega -> RR$ such that  $F(x) = gradient f(x)$ for all $x in Omega$.
]

#theorem[
  Suppose $F$ a conservative vector field in a neighborhood of a piecewise-smooth path $gamma$. Then $ integral_gamma F dot dif s = f(gamma(b)) - f(gamma(a)). $
]

#corollary[If $gamma$ closed, then $integral_gamma F dot dif s = 0$.]

#proof[(Of Theorem) $ integral_gamma F dot dif s & = integral_a^b gradient f (gamma(t)) dot gamma' (t) dif t \
                             & = integral_a^b dif/(dif t) f(gamma (t)) dif t \
                             & = f(gamma(b)) - f(gamma(a)). $

]

If $C = union_i C_i$ a finite union of curves $C_i$, we extend our definition to $ integral_C F dot dif s = sum_(i) integral_C_i F dot dif s. $


=== Poincaré Lemma

The question we aim to address here is, when is $F : Omega -> RR^n$ conservative?

A necessary condition is as follows.

#theorem[Let $F = (F_1, dots, F_n)$ a $C^1$ conservative vector field. Then,  $ (partial F_i)/(partial x_j) (x) = (partial F_j)/(partial x_i) (x) $ for all $i, j$ and $x in Omega$.]

#proof[
  We have $F = gradient f$ for $f in C^1 (Omega)$; then $(partial F_i )/(partial x_j) = (partial^2 f)/(partial x_j partial x_i)$, so the claim follows by Clairault's.
]

When is this condition sufficient?

== Poincaré Lemma


#lemma[
  Suppose $g (x, y)$ is $C^1$ in $Omega times A$ where $Omega subset RR^n$ open and $A subset RR^m$ is compact. Then, $ partial/(partial x_i) (integral_A g(x, y) dif y) = integral_A partial/(partial x_i) g(x, y) dif y $ for any $i in [n]$ and $x in Omega$.
]

#proof[
  Fix $r > 0$ so that $B_r (x) subset Omega$. Let $h in RR$ with $abs(h) < r$. By the mean-value theorem, $ g(x + h e_i, y) - g(x, y) = (partial g)/(partial x_i) (x^h, y) dot h, quad x^h in B_r (x). $ Since $overline(B_r (x)) times A$ is compact, $(partial g)/(partial x_i)$ is uniformly continuous on this set. Thus for any $epsilon > 0$, there exists $delta > 0$ such that $ abs(partial_(x_i) g (x^h, y) - partial_(x_i) g(x, y)) < epsilon, quad forall abs(h) < delta, y in A. $ Then, $ abs(overbrace((integral_A g(x + h e_i, y) dif y - integral_A g(x, y) dif y)/(h), "difference quotient for integral") - integral_A partial_x_i g(x, y) dif y) & <= integral_A abs((partial g)/(partial x_i) (x^h, y) - (partial g)/(partial x_i) (x, y)) dif y \
  & <= epsilon "vol"(A), $ for all $epsilon > 0$ with $abs(h) < delta$. Since $epsilon$ arbitrary, this proves the claim.
]

This tells us when we can differentiate under an integral sign.

#definition("Star-Shaped Region")[
  $Omega subset RR^n$ _star-shaped_ if there exists $p_0 in Omega$, which we call a _center_, such that the line segment $ell(p_0, x)$ connecting $p_0$ to $x$ is contained entirely within $Omega$ for all $x in Omega$.
]

#theorem("Poincaré Lemma")[
  Suppose $Omega subset RR^n$ is star-shaped and $F$ is a $C^1 (Omega, RR^n)$ vector field. Then, $F$ is conservative iff $ (partial F_i)/(partial x_j) = (partial F_j)/(partial x_i) $ for all $i, j = 1, dots, n$.
]

#remark[
  The statement holds for more general, so-called "contractible domains", but we limit our exposition here.
]

#proof[
  We know the "$=>$" direction already. Conversely, suppose wlog that $p_0 = 0$ is a "center" of our star-shaped domain. The idea to construct our $f$ such that $F = gradient f$ is to integrate $F$ along the straight-line curve connecting $x$ to $0$ for each $x$. Formally, define $gamma_x (t) = t x, 0 <= t <= 1$, and define $ f(x) = integral_gamma_x F dot dif s = integral_0^1 F(t x) dot x dif t = sum_(i=1)^n integral_0^1 F_i (t x) x_i dif t. $ We need to compute the gradient of this function. Since $(t, x) |-> F_i (t x) x_i$ clearly $C^1$ and $[0, 1]$ compact, we can apply the lemma and differentiate in $x$ under the integral sign, and we find $ (partial f)/(partial x_j) (x) &= integral_0^1 sum_(i=1)^n [(partial F_i)/(partial x_j) (t x) t x_i + F_i (t x) delta_(i, j)] dif t \
  &= integral_0^1 F_j (t x) + sum_(i=1)^n t x_i (partial F_i)/(partial x_j) (t x) dif t \
  ("integrate by parts on first summand") quad &= integral_0^1 sum_(i=1)^n t x_i (partial F_i)/(partial x_j) (t x) dif t + [t F_j (t x)]_0^1 - integral_0^1 t sum_(i=1)^n (partial F_j)/(partial x_i) x_i (t x) dif t \
  &= integral_0^1 sum_(i=1)^n t x_i underbrace([(partial F_i)/(partial x_j) (t x) - (partial F_j)/(partial x_i) (t x)], = 0 "by assumption") dif t + F_j (x) = F_j (x), $ as claimed.
]

== Integration on Surfaces

#definition[
  A parametrized surface $S subset RR^(3)$ is the image of a map $Phi : D -> S$, $ S = {(x(u, v), y(u, v), z(u, v)) = Phi(u, v) : (u, v) in D}, $ where $D subset RR^2$ some bounded domain. If $Phi$ is $C^k$ we call $S$ a $C^k$ surface. Note that $ Phi_u = (partial_u x, partial_u y, partial_u z), quad Phi_v = (partial_v x, partial_v y, partial_v z) $ are tangent to $S$.
]

#definition[
  For a regular $C^1$ parametrization $Phi : D -> S$, define $ "area"(S) := integral.double_D norm(Phi_u times Phi_v) dif A, $ when it exists.
]

#definition[
  Let $S = Phi(D)$ a $C^1$ parametrized surface and suppose $f in C^0 (S)$. Then we define $ integral.double_S f dif S := integral.double_D f(Phi) norm(Phi_u times Phi_v) dif A. $
]

#proposition[
  In the special case that $S$ is the graph of a $C^1$ function $g : D -> RR$ (i.e. $S = {(x, y, g(x, y)) : (x, y) in D}$), then this integral becomes $ integral.double_D f(x, y, g(x, y)) sqrt(1 + g_x^2 + g_y^2) dif A. $
]

#proof[
  This follows from computing $ Phi_x = (1, 0, g_x), quad Phi_y = (0, 1, g_y) => Phi_x times Phi_y = (- g_x, -g_y, 1). $
]

#definition[
  Given $S = Phi(D)$ a $C^1$ parametrized surface, we say $S$ is regular if the normal $Phi_u times Phi_v$ never vanishes over $D$, i.e. if $Phi_u, Phi_v$ are never linearly dependent. If $S$ regular, we can choose $ N = plus.minus (Phi_u times Phi_v)/(norm(Phi_u times Phi_v)) $ to be the _unit normal_; there are two choices of sign, leading to different _orientations_ of $S$.
]

#definition[
  Let $F$ a $C^0$ vector field on a regular parametrized surface $S = Phi(D)$. Then, we define $ integral.double_S F dot dif s := integral.double_D F dot N norm(Phi_u times Phi_v) dif u dif v = integral.double_D (F compose Phi) dot (Phi_u times Phi_v) dif A. $
]

Note that this is defined up to orientation of $S$; however, it isn't clear from the definition that this is independent of parametrization.

#definition[
  Given $Phi : D -> S, tilde(Phi) : tilde(D) -> S$ regular $C^1$ parametrizations of the same surface, we say $tilde(Phi)$ is a reparametrization of $Phi$ if there exists a bijective $C^1$ map $h : tilde(D) -> D$ with $C^1$ inverse, such that $tilde(Phi) (s, t) = (Phi compose h) (s, t)$.

  We say $tilde(Phi)$ _orientation-preserving_  if $ ((Phi_u times Phi_v) (h(s, t)))/(norm((Phi_u times Phi_v) (h(s, t)))) = ((tilde(Phi)_s times tilde(Phi)_t)(s, t))/(norm((tilde(Phi)_s times tilde(Phi)_t)(s, t))), $ and _reversing_ if the same equality holds with a negative in front of the second term.
]

#lemma[
  Let $tilde(Phi), Phi$ as above with $h : tilde(D) -> D$ written as $h(s, t) = (u(s, t), v(s, t)) in C^1 (tilde(D), D)$ a change of parameters. Then $h$ is orientation-preserving iff $det((partial (u, v))/(partial (s, t))) >0$, and reversing iff $det((partial (u, v))/(partial (s, t))) < 0$, where $(partial (u, v))/(partial (s, t))$ the Jacobian matrix of $h$.
]

#proof[
  Follows from the chain rule upon computing $tilde(Phi)_s$ and $tilde(Phi)_t$, namely we find $ tilde(Phi)_s times tilde(Phi)_t = det((partial (u, v))/(partial (s, t))) (Phi_u times Phi_v), $ from which the claim readily follows.
]

From this lemma, it readily follows that the previous definition of the integral of a vector field over a surface is well-defined (modulo orientation) regardless of choice of parametrization, by applying the chain of variables formula and the previous lemma. We'll often denote a positively/negatively oriented surface by $S^+, S^-$ depending on the choice of sign of the normal vector. As an immediate corollary, we find $ integral.double_(S^(plus.minus)) F dot dif s = - integral.double_(S^minus.plus) F dot dif s. $

== Green's Theorem and its Consequences

#definition[
  A surface $S subset RR^3$ is said to be a _regular surface with $C^1$ boundary $partial S$_ if $S$ is compact and if for all $p in S$, there exists $r, delta > 0$ with $B_r (rho) subset RR^3$ and $D = {- delta < u < delta, - delta < v < delta} subset RR^2$ and a regular parametrization map $Phi : D -> RR^3$ such that either
  1. $S inter B_r (rho) = Phi(D)$, or
  2. $S subset B_r (rho) = Phi(D^+)$ where $D_+ := {- delta < u < delta, 0 <= v < delta}$. Points in 1. are called _interior charts_ of $S$ and points in 2. are called _boundary charts of $S$_; the boundary of $S$ is defined as $partial S = {"all boundary points of" S}$. The local parametrized surfaces are called coordinate charts.
]

#definition[
  A regular surface $S subset RR^3$ is orientable if the unit normal $n in C^0 (S, RR^3)$.
]

In general there are two choices of unit normal at any point of a surface of $RR^3$ ("in/out"). Given a regular orientable surface $S subset RR^3$, we say it is positively oriented if:
1. If $partial S = nothing$, the unit normal is pointing "outwards" towards the "unbounded" region of the ambient $RR^3$
2. If $partial S eq.not nothing$, then we choose a "positive/counterclockwise" orientation for the curve $partial S$ which induces an orientation on $S$ by the right-hand rule.

We are now in the position to state and prove Green's, which relates line integrals of vector fields over $partial D$ to double integrals over a planar domain $D$. We say that a bounded planar domain $D subset RR^2$ is positive if the unit normal (with respect to orientation on boundary) is $lambda = (0, 0, 1)$ (equivalently, we can embed $D$ into $RR^3$ as a (planar) surface, then positive orientation is the same as that defined above for surfaces).

#theorem("Green")[
  Let $D subset RR^2$ be a positively oriented bounded piecewise $C^1$ domain and $F = (P, Q) : D -> RR^2$ a vector field on $D$. Then $ integral_(partial D) F dot dif s = integral.double_D ((partial Q)/(partial x) - (partial P)/(partial y)) dif A. $
]

#proof[
  On $partial D$, we have the short-hand $dif s = i dif x + j dif y = (dif x, dif y)$ where $i = (1, 0), j = (0, 1)$. We can write $ integral_(partial D) F dot dif s & = integral_(partial D) (P, Q) dot (dif x, dif y) \
                                   & = integral_(partial D) P dif x + Q dif y. $

  Assume first $D$ is a simple domain $ D = {a <= x <= b , phi_1 (x) <= y <= phi_2 (x)} = {c <= y <= d, psi_1 (y) <= x <= psi_2 (y)} $ with boundary $C$. We claim $- integral.double_D (partial P)/(partial y) dif A = integral_C P dif x$. Write $ C_1 & = {a <= x <= b, y = phi_1 (x)} \
  C_2 & ={a <= x <= b, y = phi_2 (x)} \
  B_1 & = {x = a, phi_1 (a) <= y <= phi_2 (a)} \
  B_2 & = {x = b, phi_1 (b) <= y <= phi_2 (b)}. $
  $C_1^+, C_2^+$ are oriented $a |-> b$ and $B_1^plus, B_2^plus$ are oriented from $phi_1 (a)$ to $phi_2 (a), phi_1 (b)$ to $phi_2 (b)$ respectively. By Fubini, $ integral.double_D (partial P)/(partial y) dif A &= integral_a^b integral_(phi_1 (x))^(phi_2 (x)) (partial P)/(partial y) dif y dif x \
  ("FTC") quad &= integral_a^b (P(x, phi_2 (x)) - P(x, phi_1 (x))) dif x \
  &= integral_(C_2^+) P dif x - integral_(C_1^+) P dif x = integral_(C_2^+ union C_1^-) P dif x \
  &= - integral_(C_2^(-) union C_1^+ ) P dif x +integral_(B_1^+) P dif x - integral_(B_2^+) P dif x \
  &= - integral_(C_2^(-) union C_1^+ union(B_2^+) union B_1^-) P dif x \
  &= - integral_(C) P dif x, $ where we use the fact that $ integral_(B^+_1) P dif x - integral_(B_2^+) P dif x = 0 $ since $x$ is constant on $B_1$ and $B_2$ to add them in to our computations.

  Similarly, one shows that $ integral.double_D (partial Q)/(partial x) dif A = integral_(partial D) Q dif y. $ Combining these identities gives the proof.

  For a more general domain, one case use the implicit function theorem and the piecewise-$C^1$ assumption to reduce the domain to a union of simple regions, which sum up to give the general result.
]


#corollary[
  $ integral_(partial D) x dif y = - integral_(partial D) y dif x = 1/2 integral_(partial D) x dif y - y dif x = "area"(D), $ where we use as in the previous theorem the notation, where if $gamma = (gamma_1, gamma_2) : I -> RR^2$ is a parametrization of $partial D$, then $ dif x = gamma'_1 (t) dif t, $ etc (and the input is evaluated on $(x, y) = gamma(t)$).
]

#proof[
  Set $F = (0, x)$. By Green's, $ integral_(partial D) F dot dif s = integral_(D) dif A = "area"(D). $ On the other hand, the left-hand side is readily seen to be equal to $integral_(partial D) x dif y$. Similar proofs with $F = (y, 0)$, $F = (-y, x)$ yield the other results.
]

#exercise[
  Compute $"area"(D)$ via Green's, where $D = {x^2/a^2 + y^2/b^2 <= 1}$.
]



#solution[
  The boundary is given parametrically in two parts, $x in [-a, a]$ and $y = plus.minus b sqrt(1 - x^2\/a^2)$. The plus and minus of $y$ give the same so by the previous corollary,
  $ "area"(D) = 2 b integral_(-a)^a sqrt(1 - x^2\/a^2) dif x = pi a b, $ where we compute the final integral via a trig substitution.
]

#corollary[
  Let $D = D_1 \\ D_2$ where $partial D_1, partial D_2$ are piecewise $C^1$ with orientations induced from $D_1 + D_2$. If $F = (P, Q)$ a $C^1$ vector field with $(partial Q)/(partial x) = (partial P)/(partial y)$ on $D$, then $ integral_(partial D_1) F dot dif s = integral_(partial D_2) F dot dif s. $
]

#proof[
  With the given orientations, $partial D = partial D_1 - partial D_2$. By Green's, $integral_(partial D) F dot dif s = 0$ since $P_x = Q_y$. On the other hand, by linearity and given the orientations, $integral_(partial D) F dot dif s = integral_(partial D_1) F dot dif s - integral_(partial D_2) F dot dif s$. Combined, these give the answer.
]


#theorem[
  With the same assumptions as in Green's, $ integral_(partial D) F dot n dif s = integral.double_(D) (partial P)/(partial x) + (partial Q)/(partial y) dif A $ where $n$ the inward normal vector to $partial D$.
]

#proof[
  Suppose $partial D$ parametrized by $(x(t), y(t))$ for $t in [a, b]$, so that $n = (-dot(y), dot(x))/(sqrt(dot(x)^2 + dot(y)^2))$.
  $ integral_(partial D) F dot n dif s & = integral_(a)^b (P, Q)(x(t), y(t)) dot n(t) sqrt(x'(t)^2 + y'(t)^2) dif t \
  & = integral_(a)^b (P(x(t), y(t)), Q(x(t), y(t))) dot (y'(t), x(t)) dif t \
  & =integral_(a)^b P(x(t), y(t)) y'(t) dif t - integral_(a)^b Q(x(t), y(t)) x'(t) dif t \
  &= integral_(partial D) tilde(F) dif s, quad tilde(F) := (- Q, P) \
  "Green's" quad &= integral.double_(D) (partial P)/(partial x) + (partial Q)/(partial y) dif A. $ At the penultimate line, one can alternatively arrive at the conclusion by the abuse of notation $ integral_a^b P(x(t), y(t)) y'(t) dif t = integral_(partial D) P dif x = integral.double_(D) (partial P)/(partial x) dif A $ also by Green's.
]

=== Harmonic Functions

Let $laplace = (partial^2)/(partial x^2) + (partial^2)/(partial y^2)$ be the Laplacian operator in two variables. We call a function $u in C^2 (Omega)$ _harmonic_ provided $laplace u equiv 0$ in $Omega$.

#corollary[
  Let $u$ be a harmonic function in a domain $D subset RR^2$ with piecewise $C^1$ domain. Then $integral_(partial D) gradient u dot n dif s = 0$.
]

#proof[
  Take $F = gradient u$ in the previous corollary.
]

#corollary("Green's Identities")[
  Let $phi, psi in C^2 (D)$, where $D subset RR^2$ with piecewise $C^1$ domain with positive orientation. Then the following hold:
  1. $integral.double_(D) phi laplace psi dif A = - integral.double_D gradient phi dot gradient psi dif A + integral_(partial D) phi gradient psi dot n dif s$
  2. $integral.double_(D) [phi laplace psi - psi laplace phi] dif A = integral_(partial D) phi gradient psi dot n - psi gradient phi dot n dif s$
]

#proof[
  1. follows from the previous-previous corollary applied to $F = phi gradient psi$.
  2. follows from 1. by swapping the roles of $phi, psi$ and subtracting the following identities from each other.
]

== Stoke's Theorem

#definition[
  Let $F = (F_1, F_2, F_3) : RR^3 -> RR^3$ a $C^1$-vector field. Define $ "curl" F &:= det mat(e_1, e_2, e_3; partial_x, partial_y, partial_z; F_1, F_2, F_3) \
  &:= (partial_(x_2) F_3 - partial_(x_3) F_2, partial_(x_3) F_1 - partial_(x_1) F_3, partial_(x_1) F_2 -partial_(x_2) F_1). $
]

#theorem("Stoke's")[
  Let $S$ be a compact, oriented surface with positive orientation and piecewise $C^1$ boundary $partial S$. Let $F : S -> RR^3$ a $C^1$ vector field. Then $ integral.double_S "curl" F dot dif S = integral_(partial S) F dot dif s. $
]

#proof[
  Recall that for a vector field $G$, $integral_(S) G dot dif S := integral_S G dot n dif S$ where $n$ the (in this case, outward) unit normal to $S$.

  _Step 1:_ assume first $S$ is $C^2$ and $partial S$ is piecewise $C^1$. Since $S$ regular, for all $p in partial S$, $S$ is locally given by a graph over a a coordinate plane by the implicit function theorem. For instance if, suppose, $S$ is locally given by $z = g(x, y)$, then $Phi(x, y) = (x, y, g(x, y)) in S$ gives a local parametrization of $S$, and induces positive unit normal $ n = (-g_x, - g_y, 1)/sqrt(1 + g_x^2 + g_y^2). $ We can always pick $g$ such that $(0, 0, g(0, 0)) = p$. By compactness, we can decompose $S$ into a finite union of "subsurfaces" $ S = union.big_(ell = 1)^N S_ell. $ such that $S_ell^("int") inter S_k^("int") = nothing$ for all $k eq.not ell$, and such that each $S_ell$ is locally a graph over a coordinate plane for each $ell = 1, dots, N$. Then, we note that $ integral_(partial S) F dot dif s = sum_(ell = 1)^N integral_(partial S_ell) F dot dif s, quad integral.double_(S) "curl" F dot dif S = sum_(ell = 1)^N integral.double_(S_ell) "curl" F dot dif S, $ since the overlapping boundary regions will cancel each other out by orientation. Thus, it suffices to prove Stoke's in the case that $S$ is a graph. By rotation, translating, and rescaling, we may assume that $S$ is a $C^2$ graph over $D subset RR^2_(x, y)$ with $D = [-1, 1] times [0, 1]$. Then, on the one hand, $ integral_S "curl" F dot dif S & = integral.double_(D) (partial_y F_3 - partial_z F_2) (- g_x) + (partial_z F_1 - partial_x F_3) (-g_y) + partial_x F_2 - partial_y F_1 dif A. $ We now consider the integral over $partial S$. We see first that $partial S = Phi(partial D) = {(x, y, g(x, y)) : (x, y) in partial D}$. Thus, by chain rule, $dif s = (dif x, dif y, g_x dif x + dif g_y dif y)$ so $ integral_(partial S) F dot dif s = integral_(partial D) (F_1 + F_3 g_x) dif x + integral_(partial D) (F_2 + F_3 g_y) dif y = integral_(partial D) G dot dif s, $ where $ G(x, y) := (F_1 + F_3 g_x, F_2 + F_3 g_y), $ where, crucially, each $F_i$ is evaluated at $(x, y, g(x, y))$. Applying Green's to this integral and applying a lot of chain and product rule gives the result; one will expect higher-order derivatives of $g$ to appear, but these will (should!) cancel.

  _Step 2:_ Suppose now $S in C^1$ with pw-$C^1$ boundaries. The heuristic idea is to "approximate" $S$ with $C^2$ surfaces and show that this approximation respects the identity. We won't show the details.
]

#corollary[
  Suppose $S_1, S_2$ are two oriented surfaces with $partial S_1 = partial S_2 = gamma$, and suppose $S_1$ and $S_2$ induce opposite orientations on $gamma$. Then, for any $F in C^1$, $ integral.double_(S_1) "curl" F dot dif S = - integral.double_(S_2) "curl" F dot dif S. $
]

#corollary[
  With $S$ as above, suppose $partial S = nothing$ and $F in C^1 (S)$. Then $integral.double_S "curl" F dot dif S = 0$.
]

#corollary[
  Suppose $F = gradient f$ for some $f in C^2$ and $S$ is an oriented surface with $partial S = gamma_1 - gamma_2$. Then $ integral_(gamma_1) F dot dif s = integral_(gamma_2) F dot dif s. $
]

#proof[
  One checks that $"curl"(gradient f) = 0$.
]


== Divergence Theorem

#theorem[
  Let $W subset RR^3$ be a bounded, solid region in $RR^3$ with a piecewise smooth boundary $S = partial W$ with positive orientation, and $F$ a $C^1$ vector field on $W -> RR^3$. Then, $ integral.triple_W "div" F dif V = integral.double_(S) F dot dif S, $ where if $F = (F_1, F_2, F_3)$, $"div"(F) = (partial F_1)/(partial x) + (partial F_2)/(partial y) + (partial F_3)/(partial z)$.
]

#corollary[
  Under the same assumptions as above, if $f, g in C^2 (W)$, then $ integral.triple_W [g laplace f - f laplace g] dif V = integral.double_(partial W) [g gradient f dot dif S - f gradient g dot dif S]. $
]

#proof[
  As in Stoke's theorem, it suffices to prove for $W$ a simple region. Clearly, it suffices to prove that $ integral.triple_(W) (partial F_3)/(partial z) dif V = integral.double_(S) F_3 hat(k) dot dif S, $ where $hat(k) = (0, 0, 1)$, by linearity. Assume $ W = {(x, y, z) : (x, y) in D, g(x, y) <= z <= h(x, y)}. $ Fubini's gives $ integral.triple_(W) (partial F_3)/(partial z) dif V & = integral.double_(D) integral_(g(x, y))^(h(x, y)) (partial F_3)/(partial z) dif z dif x dif y \
  &= integral.double_(D) [F_3 (x, y, h(x, y)) - F_3 (x, y, g(x, y))] dif x dif y. $
  We can decompose the boundary $partial W = S$ into three parts, $ S_1 & = {(x, y, g(x, y)) : (x, y) in D} => n = - (-g_x, -g_y, 1)/(sqrt(1 + g_x^2 + g_y^2)) \
  S_2 & = {(x, y, h(x, y)) : (x, y) in D} => n = (-h_x, -h_y, 1)/(sqrt(1 + h_x^2 + h_y^2)) \
  S_3 & = {angle.l n, k angle.r = 0}. $ The relevant integral over $S_3$ is zero. Over $S_1$, we get $ integral.double_(S_1) F_3 (x, y, h(x, y)) - F_3 (x, y, g(x, y)) dif x dif y, $ since $hat(k) dot n = 1$ in each case.
]

#corollary[
  Suppose $W, W_1, dots, W_k subset RR^n$ are regions as in the previous theorem, with $ W_i sect W_j = nothing, i eq.not j, quad W_j subset W^"int", quad p_j in W_j^"int" forall j = 1, dots, k $ for some points $p_1, dots, p_k$. If $F$ a $C^1$ vector field on $W minus {p_1, dots, p_k}$ and $"div" F = 0$ for all $x in W minus {p_1, dots, p_k}$. Then, $ integral.double_(partial W) F dot dif S = sum_(j=1)^k integral.double_(partial W_j) F dot dif S. $
]

#proof[
  Apply the divergence theorem to $W minus union.big_(j=1)^k W_j$.
]

#exercise("Gauss's Law")[
  Let $r = (x, y, z)$. Then $ integral.double_(partial W) r/(norm(r)^3) dif S = cases(4 pi quad & 0 in W, 0 & "else") $
]

#pagebreak()
= Practice Questions

#question[
  Let $f(x, y) = (x^4 y^2)/(x^2 + y^2)$ when $(x, y) eq.not 0$ and $f(0,0) = 0$. Prove that $f$ is differentiable everywhere in $RR^2$.
]

#solution[
  If $(x, y) eq.not (0,0)$, one can take partial derivatives and find that they are both continuous, thus $f$ differentiable away from $(0,0)$. At $(0,0)$, we claim $D f(0,0) = 0$. For $h = (h_1, h_2) in RR^2$, we find $ abs(f(h_1, h_2) - f(0,0))/(norm(h)) & = underbrace((h_1^4)/((h_1^2 + h_2^2)^(1\/2)), <= h_1^3) underbrace((h_2^2)/(h_1^2 + h_2^2), <= 1) <= h_1^3 ->_(norm(h) -> 0) 0. $
]

#question[
  Given the curve $C = {y^2 + x y + sin x = 1}$, prove that $C$ can be written as $y = g(x)$ for some $C^1$ function $g$ near $(pi/2, 0)$. Is the same true near $(0,1)$?
]

#solution[
  Let $G(x, y) = y^2 + x y + sin x - 1$. This is clearly $C^1$. We compute $ gradient G(x, y) = (y + cos x, 2 y + x). $ At $(pi/2, 0)$, we see $gradient G(pi/2, 0) = (0, pi/2)$
]

#question[Set $f(x, y) = sin(x y)/(x y)$ when $x y eq.not 0$ and $f(0, y) = f(x, 0) = 0$. Prove that $f$ is Riemann integrable on $B := [-1, 1] times [-1, 1]$.]

#solution[
  Its clear that $f(x, y)$ is continuous away from the line segments $L_x = {(x, 0) : -1 <= x <= 1}, L_y = {(0, y) : -1 <= y <= 1} subset B$. Thus, if we can show $"content"(L_x union L_y) = 0$, we'll be done.
  Let $epsilon > 0$. There exists some $N$ such that $[-1, 1]$ is covered by $N$ disjoint open intervals $(x_i, x_(i + 1))$ of length $epsilon$, by compactness. Let $B_i =(x_i, x_(i+1)) times (-1/(2N), 1/(2N))$ be corresponding open boxes. Its clear then that $L_x subset union.big_(i=1)^N B_i$, and moreover $"vol"(B_i) = epsilon/N$ and thus $sum_(i=1)^N "vol"(B_i) = epsilon$. This implies $L_x$ has content zero. It follows identically that $L_y$ has content zero, which completes the proof.
]

#question[
  Find the absolute minimum and maximum values of $f(x_1, dots, x_n) = x_1^3 + dots.c + x_n^3$ in the closed unit ball $overline(B_1 (0)) subset RR^n$.
]

#solution[_(First Solution)_ Notice by triangle inequality $abs(f(x)) <= sum_(i=1)^n x_i^2 abs(x_i) <= 1$ over $overline(B_1 (0))$ so $-1 <= f(x) <= 1$, with $f(-1, 0, dots, 0) = -1$ and $f(1,0,dots, 0) = 1$ which means the absolute min, max of $f$ over $overline(B_1 (0))$ are $-1, 1$ respectively.
]

#solution[_(Second Solution)_ We use Lagrange multipliers. Let $g(x) = x_1^2 + dots.c + x_n^2 - 1$. We compute $gradient g(x) = 2 x$ and $gradient f = 3 (x_1^2, dots, x_n^2)$. Setting $gradient f(x) = lambda gradient g(x)$, we see that $2 x_i = 3 lambda x_i^2$ for all $i$. Let $M = {1 <= i <= n : x_i eq.not 0}$. Note that not all $x_i$'s can be zero so $hash M >= 1$, which means, for all $x_i eq.not 0$, we find $x_i = 2/(3 lambda)$. This implies $ 1 = sum_(i=1)^n x_i^2 = 4/(9 lambda^2) dot hash M => lambda = plus.minus 1/sqrt(hash M) 3/2 $ which implies $ f(x) = sum_(i=1)^n x_i^3 = sum_(i in M) 8/(27 lambda^3)= plus.minus (hash M)/((hash M)^(3\/2)) 8/27 27/8 = plus.minus 1/sqrt(hash M). $ It's clear that this is maximized by minimizing the size of $M$ (which must have size at least 1) and taking the positive root (choosing $lambda$ positive), and minimized by minimizing the size of $M$ as well, but taking the negative root. Thus if $f$ maximized, minimized on $partial B_1 (0)$, it follows that $f(x) = 1, -1$ respectively. On the other hand, if $x in B_1 (0)$, $0 = gradient f(x) = 3 (x_1^2, dots, x_n^2)$ implies $x_i = 0$ for all $i$ and thus $f(x) = 0$. Thus the min, max of $f$ over $overline(B_1 (0))$ are achieved on the boundary, i.e. $min f = -1, max f = 1$.
]

#question[
  Suppose $f in C^2 (RR^n)$ satisfies $ f(x) = 2 forall norm(x) = 1, quad norm(gradient f(x)) = 1, (partial^2 f)/(partial x_1^2) (x) + dots.c + (partial^2 f)/(partial x_n^2) (x) > 0 forall x in B_1 (0). $
  Prove that $1 <= f(x) <= 2$ for all $x in overline(B_1 (0))$.
]

#solution[
  Let $x in overline(B_1 (0))$ and $y in partial B_1 (0)$ the closest point (if multiple exist, choose any) to $x$ on the boundary; in particular $norm(x - y) <= 1$. By mean-value theorem, there exists some $z in B_1 (0)$ such that $ f(x) - 2 = f(x) - f(y) & = gradient f(z) dot (x - y) >= - norm(gradient f (z)) norm(x - y) >= - 1 => f(x) >= 1. $ This proves the first inequality. For the second, we know the inequality is satisfied on the boundary. Suppose it fails inside $B_1 (0)$. This implies, by compactness and continuity of $f$, that $max_(overline(B_1 (0))) f(x) > 2$ and moreover this max is achieved at some $x in B_1 (0)$. Being a maximum, this implies $gradient^2 f(x)$ negative semidefinite, so in particular its eigenvalues are negative hence $ 0 >= sum "eigenvalues of" gradient^2 f(x) = tr(gradient^2 f(x)) = (partial^2 f)/(partial x_1^2) (x) + dots.c + (partial^2 f)/(partial x_n^2) (x). $ But by assumption, the quantity on the right is strictly positive, which is a contradiction. Thus $f$ cannot attain its maximum inside $B_1 (0)$ and thus $f(x) <= 2$ everywhere. This completes the proof.
]
