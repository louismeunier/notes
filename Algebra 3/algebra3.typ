// ! external
#import "../typst/notes.typ": *
#import "../typst/shortcuts.typ": *

// ! configuration
#show: doc => conf(
  course_code: "MATH456",
  course_title: "Algebra 3",
  subtitle: "",
  semester: "Fall 2024",
  professor: "Prof. Henri Darmon",
  doc
)

#set align(left)

// TODO starts here
= Groups

== Review
#definition("Group")[
  A *group* is a set $G$ endowed with a binary composition rule $G times G -> G, (a, b) |-> a star b$, satisfying
  + $exists e in G "s.t." a star e = e star a = a forall a in G$
  + $forall a in G, exists a' in G "s.t." a star a' = a' star a = e$
  + $forall a, b, c in G, (a star b) star c = a star (b star c)$.
  If the operation on $G$ also commutative for all elements in $G$, we say that $G$ is _abelian_ or _commutative_, in which case we typically adopt additive notation (i.e. $a + b$, $a^(-1) = -a$, etc).
]

#example[
  An easy way to "generate" groups is consider some "object" $X$ (be it a set, a vector space, a geometric object, etc.) and consider the set of symmetries of $X$, denoted $"Aut"(X)$, i.e. the set of bijections of $X$ that preserve some desired quality of $X$.

  + If $X$ just a set with no additional structure, $"Aut"(X)$ is just the group of permutations of $X$. In particular, if $X$ finite, then $"Aut"(X) tilde.equiv S_(hash X)$.
  + If $X$ a vector space over some field $FF$, $"Aut"(X) = {T : X -> X | "linear, invertible"}$. If $dim (X) = n < infinity$, $X tilde.equiv FF^n$ as a vector space, hence $"Aut"(X) = "GL"_n (FF)$, the "general linear group" consisting of invertible $n times n$ matrices with entires in $FF$.
  + If $X$ a ring, we can always derive two groups from it; $(R, +, 0)$, which is always commutative, using the addition in the ring, and $(R^times, times, 1)$, the units under multiplication (need to consider the units such that inverses exist in the group).
  + If $X$ a regular $n$-gon, $"Aut"(X)$ can be considered the group of symmetries of the polygon that leave it globally invariant. We typically denote this group by $D_(2n)$.
  + If $X$ a vector space over $RR$ endowed with an inner product $(dot, dot) :V times V -> RR$, with $dim V < infinity$, we have $"Aut"(V) = O(V) = {T : V -> V | T(v dot w) = v dot w forall v, w in V}$, the "orthogonal group".
]

#definition("Group Homomorphism")[
  Given two groups $G_1, G_2$, a _group homomorphism_ $phi : G_1 -> G_2$ is a function satisfying $phi(a b) = phi(a)phi(b)$ for all $a, b in G_1$.

  If $phi$ is bijective, we call it an _isomorphism_ and say $G_1, G_2$ are _isomorphic_. 
]

#proposition[
- $phi(1_(G_1)) = 1_(G_2)$
- $phi(a^(-1)) = phi(a)^(-1)$
]

#example[
  Let $G = ZZ\/n ZZ = {0, dots, n-1}$ be the cyclic group of order $n$. Let $phi in "Aut"(G)$; it is completely determined by $phi(1)$, as $phi(k) = k dot.c phi(1)$ for any $k$. Moreover, it must be then that $phi(1)$ is a generate of $G$, hence $phi(1) in (ZZ\/ n ZZ)^(times)$ (ie the units of the group considered as a ring), and thus $
  "Aut"(G) tilde.equiv ((ZZ\/ n ZZ)^times, ast).
  $
]

== Actions of Groups

#definition("Group Action")[
  An _action_ of $G$ on an object $X$ is a function $G times X -> X, (g, x) |-> g dot.c$ such that 
  - $1 dot.c x = x$
  - $(g_1 g_2) dot.c x = g_1 dot.c (g_2 dot.c x)$
  - $m_g : x |-> g dot.c x$ an _automorphism_ of $X$.
]

#proposition[
  The map $m : G -> "Aut"(X)$, $g |-> m_g$ a group homomorphism.
]

#proof[
  One need show $m_(g_1 g_2) = m_(g_1) compose m_(g_2)$.
]

#definition("G-set")[
  A _$G$-set_ is a set $X$ endowed with an action of $G$.
]

#definition("Transitive")[
  We say a $G$-set $X$ is _transitive_ if $forall x, y in X$, there is a $g in G$ such that $g dot.c x = y$.

  A transitive $G$-subset of $X$ is called on _orbit_ of $G$ on $X$.
]

#proposition[
Every $G$-set is a disjoint union of orbits.
]
#proof[
  Define a relation on $X$ by $x tilde y$ if there exists a $g in G$ such that $g dot.c x = y$. One can prove this is an equivalence relation on $X$. Equivalence relations partition sets into equivalence classes, which we denote in this case by $X\/ G$. The proof is done by remarking that an equivalence class is precisely an orbit.
]

// TODO maybe examples

#remark[
  As with most abstract objects, we are more interested in classifying them up to isomorphism. The same follows for $G$-sets.
]
#definition[An _isomorphism of $G$-sets_ is a map between $G$-sets that respects the group actions. Specifically, if $G$ a group and $X_1$, $X_2$ are $G$-sets, with the action $G$ on $X_1$ denoted $star$ and $G$ on $X_2$ denoted $ast$, then an isomorphism is a bijection $
f : X_1 -> X_2,
$ such that $
f (g star x) = g ast f(x)
$ for all $g in G$, $x in X_1$.]

#definition("Cosets")[Let $H subset.eq G$ be a subgroup of a group $G$. Then $G$ carries a natural structure as an $H$ set; namely we can define $
H times G -> g, #h(1em) (h, g) |-> g dot.c h,
$ which can readily be seen to be a well-defined group action. We call, in this case, the set of orbits of the action of $H$ on $G$ _left cosets_ of $H$ in $G$, denoted $
G \/ H &= {"orbits of" H "acting on" G } \
&= {a H : a in G} = { {a h : h in H} : a in G} subset.eq 2^G.
$ Symmetric definitions give rise to the set of _right cosets_ of $H$ in $G$, denoted $H \\ G$, of orbits of $H$ acting by left multiplication on $G$.
]

#remark[
  In general, $G\/ H eq.not H \\ G$. Further, note that at face value these are nothing more than sets; in general they will not have any natural group structure. They do, however, have a natural structure as $G$-sets, as a theorem to follow will elucidate.
]

#theorem[Let $H subset.eq G$ be a finite subgroup of a group $G$. Then every coset of $H$ in $G$ has the same cardinality.]

#proof[
Define the map $H |-> a H$ by $h |-> a h$. This is a bijection.
]

#remark[
  In general, if one considers the general action of $G$ on some set $X$, then the orbits $X \/ G$ need not all have the same size, though they do partition the set. It is in the special case where $X$ a group and $G$ a subgroup of $X$ that we can guarantee equal-sized partitions.
]

#theorem("Lagrange's")[
Let $G$ be a finite group and $H$ a subgroup. Then $
hash G = hash H dot.c hash (G \/ H).
$ In particular, $hash H | hash G$ for any subgroup $H$.
]
#proof[
  We know that $G \/ H$ is a partition of $G$, so eg $G = H union.sq H_1 union.sq dots.c union.sq H_n$. By the previous theorem, each of these partitions are the same size, hence $
  hash G &= hash ( H union.sq H_1 union.sq dots.c union.sq H_n)\
  &= hash H + hash H_1 + dots.c + hash H_(n-1) #h(1em) "since" H_i"'s disjoint"\
  &= n dot.c hash H #h(1em) "since each" H "same cardinality"\
  &= hash (G \/ H) dot.c hash H.
  $
]

#proposition[
  $G \/H$ has a natural left-action of $G$ given by $
  G times G\/ H -> G \/ H, #h(1em) (g, a H) |-> (g a) H.
  $ Further, this action is always transitive.
]

#proposition[If $X$ is a transitive $G$-set, there exists a subgroup $H subset.eq G$ such that $X tilde.equiv G \/ H$ as a $G$-set. 

In short, then, it suffices to consider coset spaces $G \/ H$ to characterize $G$-sets.]

#proof[
  Fix $x_0 in X$, and define the _stabilizer_ of $x_0$ by $
  H := "Stab"_(G) (x_0) := {g in G : g x_0 = x_0}.
  $ One can verify $H$ indeed a subgroup of $G$. Define now a function $
  f : G \/ H -> X, #h(1em) g H |-> g dot.c x_0,
  $ which we aim to show is an isomorphism of $G$-sets.

  First, note that this is well-defined, i.e. independent of choice of coset representative. Let $g H = g' H$, that is $exists h in H $ s.t. $g = g' h$. Then, $
  f(g H) = g x_0 = (g' h) x_0 = g' (h x_0) = g' x_0 = f(g' H),
  $ since $h$ is in the stabilizer of $x_0$.

  For surjectivity, we have that for any $y in X$, there exists some $g in G$ such that $g x_0 = y$, by transitivity of the group action on $X$. Hence, $
  f (g H) = g x_0 = y
  $ and so $f$ surjective.

  For injectivity, we have that $
  g_1 x_0 = g_2 x_0 &=> g_2^(-1) g_1 x_0 = x_0 \
  &=> g_2^(-1) g_1 in H\
  &=> g_2 h = g_1 "for some" h in H\
  &=> g_2 H = g_1 H,
  $ as required.

  Finally, we have that for any coset $a H$ and $g in G$, that $
  f(g (a H)) = f((g a) H) = (g a) x_0,
  $ and on the other hand $
  g f(a H) = g (a x_0) = (g a) x_0.
  $ Note that we were very casual with the notation in these final two lines; make sure it is clear what each "multiplication" refers to, be it group action on $X$ or actual group multiplication.
]

#corollary[
If $X$ is a transitive $G$ set with $G$ finite, then $hash X | hash G$. More precisely, $
X tilde.equiv G \/ "Stab"_G (x_0)
$ for any $x_0 in X$. In particular, the _orbit-stabilizer formula_ holds:$
hash G = hash X dot.c hash "Stab"_G (x_0).
$
]

The assignment $X -> H$ for subgroups $H$ of $G$ is not well-defined in general; given $x_1, x_2 in X$, we ask how $"Stab"_G (x_1)$, $"Stab"_G (x_2)$ are related?

Since $X$ transitive, then there must exist some $g in G$ such that $x_2 = g x_1$. Let $h in "Stab"(x_2)$. Then, $
h x_1 = x_2 =>  (h g) x_1 = g x_1 => g^(-1) h g x_1 = x_1,
$ hence $g^(-1) h g in "Stab" (x_1)$ for all $g in G$, $h in "Stab"(x_2)$. So, putting $H_i = "Stab" (x_i)$, we have that $
H_2 = g H_1 g^(-1).
$ This induces natural bijections $
{"pointed transitive" G-"sets"} &<-> {"subgroups of" G}\
(X, x_0) &arrow.squiggly H = "Stab"(x_0)\
(G \/ H, H) &arrow.squiggly.l H,
$ and $
{"transitive" G-"sets"} &<-> {"subgroups of" G} \/ "conjugation"\
&H_i = g H_j g^(-1), "some" g in G.
$

Given a $G$, then, we classify all transitive $G$-sets of a given size $n$, up to isomorphism, by classifying conjugacy classes of subgroups of "index $n$" $:= [G : H] = (hash G) / n = hash (G \/ H)$.

#example[
  0. $G, {e}$ are always subgroups of any $G$, which give rise to the coset spaces $X = {star}, G$ respectively. The first is "not faithful" (not injective into the group of permutations), and the second gives rise to an injection $G arrow.hook S_G$.
  1. Let $G = S_n$. We can view $X = {1, dots, n}$ as a transitive $S_n$-set. We should be able to view $X$ as $G \/ H$, where $hash (G \/ H) = hash X = n = (hash G)/ hash (H) = (n!)/(hash H)$, i.e. we seek an $H subset G$ such that $hash H = n! /n = (n-1)!$.

  Moreover, we should have $H$ as the stabilizer of some element $x_0 in {1, dots, n}$; so, fixing for instance $1 in {1, dots, n}$, we have $H = "Stab"(1)$, i.e. the permutations of ${1, dots, n}$ that leave $1$ fixed. But we can simply see this as the permutation group on $n -1$ elements, i.e. $S_(n-1)$, and thus $X tilde.equiv S_n \/ S_(n-1)$. Remark moreover that this works out with the required size of the subgroup, since $hash S_(n-1) = (n-1)!$.
  2. Let $X = $ regular tetrahedron and consider $
  G = "Aut"(X) := {"rotations leaving" X "globally invariant"}.
  $ We can easily compute the size of $G$ without necessarily knowing $G$ by utilizing the orbit-stabilizer theorem (and from there, somewhat easily deduce $G$). We can view the tetrahedron as the set ${1, 2, 3, 4}$, labeling the vertices, and so we must have $
  hash G = hash X dot.c hash "Stab"(1),
  $ where $"Stab"(1) tilde.equiv ZZ\/3 ZZ$. Hence $hash G = 12$.

  From here, there are several candidates for $G$; for instance, $ZZ \/ 12 ZZ$, $D_12$, $A_4$, $dots$. Since $X$ can be viewed as the set ${1, 2, 3, 4}$, we can view $X arrow.squiggly G arrow.hook S_4$, where $arrow.hook$ an injective homomorphism, that is, embed $G$ as a subgroup $S_4$. We can show both $D_12$ and $ZZ \/ 12 ZZ$ cannot be realized as such (by considering the order of elements in each; there exists an element in $D_12$ of order 6, which does not exist in $S_4$, and there exists an element in $ZZ\/12 ZZ$ of order 12 which also doesn't exist in $S_4$). We can embed $A_4 subset S_4$, and moreover $G tilde.equiv A_4$. If we were to extend $G$ to include planar reflections as well that preserve $X$, then our $G$ is actually isomorphic to all of $S_4$.
  4. Let $X$ be the cube, $G = {"rotations of" X}$. There are several ways we can view $X$ as a transitive $G$ sets; for instance $F =$ faces, $E = $ edges, $V = $ vertices, where $hash F = 6, hash E = 12, hash V = 8$. Let's work with $F$, being the smallest. Letting $x_0 in F$, we have that $"Stab" (x_0) tilde.equiv ZZ\/ 4 ZZ$ so the orbit-stabilizer theorem gives $hash G = 24$.

  This seems to perhaps imply that $G = S_4$, since $hash S_4 = 24$. But this further implies that if this is the case, we should be able to consider some group of size 4 "in the cube" on which $G$ acts.

  // TODO diagonals
]

== Homomorphisms, Isomorphisms, Kernels

#proposition[If $phi : G -> H$ a homomorphism, $phi$ injective iff $phi$ has a trivial kernel, that is, $ker phi = {a in G : phi (a) = e_H} = {e}$.]

#definition("Normal subgroup")[A subgroup $N subset G$ is called _normal_ if for all $g in G, h in N$, then $g h g^(-1) in N$.]

#proposition[The kernel of a group homomorphism $phi : G -> H$ is a normal subgroup of G.]

#proposition[Let $N subset G$ be a normal subgroup. Then $G\/ N = N \\ G$ (that is, $g N = N g$) and $G \/ N$ a group under the rule $(g_1 N) (g_2 N) = (g_1 g_2) N$.]

#theorem("Fundamental Isomorphism Theorem")[If $phi : G -> H$ a homomorphism with $N := ker phi$, then $phi$ induces an injective homomorphism $overline(phi) : G \/ N arrow.hook H$ with $overline(phi)(a N) := phi(a)$.]

#corollary[$im (phi) tilde.equiv G\/ N$, by $overline(phi)$ into $im(overline(phi))$.]

#example[We return to the cube example. Let $tilde(G) = tilde("Aut")(X) = $ rotations and reflections that leave $X$ globally invariant. Clearly, $G subset tilde(G)$, so it must be that $hash tilde(G)$ a multiple of $24$. Moreover, remark that relfections reverse orientation, while rotations preserve it; this implies that the index of $G$ in $tilde(G)$ is 2. Hence, the action of $tilde(G)$ on a set $O = {"orientations on "RR^3}$ with $hash O = 2$ is transitive. We then have the induced map $
eta: tilde(G) -> "Aut"(O) tilde.equiv ZZ\/2
$ with kernel given by all of $G$; $G$ fixes orientations after all.

Remark now the existence of a particular element in $tilde(G)$ that "reflects through the origin", swapping each corner that is joined by a diagonal. This is not in $G$, but notice that it actually commutes with every other element in $tilde(G)$ (one can view such an element by the matrix $mat(-1,"","";"",-1,"";"","",-1)$ acting on $RR^3$). Call this element $tau$. Then, since $tau in.not G$, $tau g eq.not g$ for any $g in G$. Hence, we can write $tilde(G) = G union.sq tau G$; that is, $tilde(G)$ is a disjoint union of two copies of $S_4$, and so $
tilde(G) tilde.equiv S_4 times ZZ\/2 ZZ\
f: S_4times ZZ\/2 ZZ -> tilde(G), #h(1em) (g, j) |-> tau^j g.
$
]

== Conjugation and Conjugacy
#definition[Two elements $g_1, g_2 in G$ are _conjugate_ if $exists h in G$ such that $g_2 = h g_1 h^(-1)$.]

Recall that we can naturally define $G$ as a $G$-set in three ways; by left multiplication, by right multiplication (with an extra inverse), and by conjugation. The first two are always transitive, while the last is never (outside of trivial cases); note that if $g^n = 1$, then $(h g h^(-1))^n = 1$, that is, conjugation preserves order, hence $G$ will preserve the order of $1$ of the identity element, and conjugation will thus always have an orbit of size $1$, ${e}$.

An orbit, in this case, is called a _conjugacy class_.

#proposition[Conjugation on $S_n$ preserves cycle shape.]
#proof[
Just to show an example, consider $(13)(245) in S_5$ and let $g in S_5$, and put $sigma := g (13) (245) g^(-1)$. Then, we can consider what $sigma g(k)$ is for each $k$;
$
sigma (g(1)) = g(3)\
sigma (g(3)) = g(1)\
sigma (g(2)) = g(4)\
sigma (g(4)) = g(5)\
sigma (g(5)) = g(2),
$ hence, we simply have $sigma = (g(1) g(3)) (g(2) g(4) g(5))$, which has the same cycle shape as our original permutation. A similar logic holds for general cycles.
]

#definition[The cycle shape of $sigma in S_n$ is the partition of $n$ by $sigma$. For instance, $
1 <-> 1 + 1 + dots + 1\
sigma = (1 2 dots n) <-> n.
$
]

#example[
We compute all the "types" of elements in $S_4$ by consider different types of partitions of 4:
#table(
columns: (1fr, 1fr),
inset: 10pt,
"Partition", "Size of Class",
$1 + 1 + 1+ 1$, $1$,
$2 + 1+ 1$, [$mat(4; 2) = 6$],
$3 + 1$, [$4 dot.c 2 = 8$ (4 points fixed, 2 possible orders)],
$4$, [$3! = 6$ (pick 1 first, then 3 choices, then 2)],
$2 + 2$, $3$
)
]