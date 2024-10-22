// ! external
#import "../typst/notes.typ": *
#import "../typst/shortcuts.typ": *

// ! configuration
#show: doc => conf(
  course_code: "MATH456",
  course_title: "Algebra 3",
  subtitle: "Groups; ring theory; fields.",
  semester: "Fall 2024",
  professor: "Prof. Henri Darmon",
  doc
)

#import "@preview/commute:0.2.0": node, arr, commutative-diagram

#set align(left)

= Groups

== Definitions
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

#proposition[Conjugation on $S_n$ preserves cycle shape.]<prop:cycles>
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
]<ex:s4conjclass>

The converse of @prop:cycles actually holds as well:

#theorem[Two permutations in $S_n$ are conjugate if and only if they induce the same cycle shape.]

#proof[We need to show the converse, that if two permutations have the same cycle shape, then they are conjugate.

We show by example. Let $g = (1 2 3 )(4 5) (6), g' = (6 1 5)(24)(3) in S_6$. We can let $h in S_6$ such that it sends $1 |-> 6$, $2 |-> 1$, $3 |-> 5$, etc; precisely
$
h = (1 6 3 5 4 2).
$ Remark that $h$ need not be unique! Indeed, we could rewrite $g' = (1 5 6) ( 4 2) (3)$ (which is the same permutation of course), but would result in $
h = (1) (2 5) (3 6) ( 4),
$ which is not the same as the $h$ above.
]

#example[We return to @ex:s4conjclass, and recall that $S_4 tilde.equiv "Aut"("cube")$. Can we identify the conjugacy classes of $S_4$ with "classes" of symmetries in the cube?

#table(
  columns: (1fr, 1fr, 1fr),
  [*Conjugation Class*], $hash$, [*Cube Symmetry*],
  $1$, $1$, $id$,
  $(12)$, $6$, "Rotations about edge diagonals",
  $(12)(34)$, $3$, [Rotations about the face centers by $pi$],
  $(123)$, $8$, "Rotations about principal diagonals",
  $(1234)$, $6$, [Rotations about the face centers by $pi/2$]
  // TODO pictures?
)
]

#example[Let $FF$ be a field and consider the vector space $V = FF^n$. Then $
"Aut"(V) = "GL"_n ( FF) = {"invertible" n times n "matrices"}.
$
Recall that linear transformations are described by matrices, after choosing a basis for $V$; i.e. $
{"linear transformations on" V } <--> M_n (FF) := {n times n "matrices with entries in" FF}. 
$ However, this identification _depends_ on the choose of basis; picking a different basis induces a different bijection. Suppose we have two bases $beta, beta'$, then $beta' = P beta$ for some $P in "GL"_n (FF)$ ($P$ called a "change of basis matrix"). Then for $T : V -> V$, and with $M := [T]_beta, M' := [T]_(beta')$, then as discussed in linear algebra, $M' = P M P^(-1)$. Hence, understanding $M_n (FF) <-> "Hom"(V -> V)$ can be thought of as understanding $M_n (FF)$ as a $G$-set of $G = "GL"_n (FF)$ under conjugation; then orbits $<->$ conjugacy classes.

*Conjugacy Invariants*
- The trace $tr$ and determinant $det$ are invariant under conjugation; $tr (P M P^(-1)) = tr (M)$ and $det (P M P^(-1)) = det (M)$
- $"spec" (M) :=$ set of eigenvalues is a conjugate invariant (with caveats on the field, etc)
- Characteristic polynomial, minimal polynomial
]

== The Sylow Theorems

Recall that if $H subset.eq G$ a subgroup, then Lagrange's gives us that $hash H | hash G$. We are interested in a (partial) converse; given some integer $n$ such that $n divides hash G$, is there a subgroup of cardinality $n$?

To see that this is not true in general, let $G = S_5$. $hash G = 120$; the divisors and the (if existing) subgroups:
$
1 &-> {1}\
2 &-> {1, (12)}\
3 &-> ZZ\/3ZZ\
4 &-> ZZ\/4 ZZ, ZZ\/2ZZ times ZZ\/2ZZ\
5 &-> ZZ\/5ZZ\
6 &->angle.l(12)(345)angle.r tilde.equiv ZZ\/6ZZ, S_3\
8 &-> D_8\
10 &->D_10\
12 &-> A_4\
15 &-> "None :("
$
There is a unique group of order 15, $ZZ\/15ZZ$; but this would need an element of order 15, which doesn't exist in $S_5$.

#theorem("Sylow 1")[
  Fix a prime number $p$. If $hash G = p^t dot m$ with $p divides.not m$, then $G$ has a subgroup of cardinality $p^t$.

  We often call such a subgroup a _Sylow-$p$_ subgroup of $G$.
]<thm:sylow1>

#example[
  We consider the Sylow subgroups of several permutation groups. 

  ($S_5$) $hash S_5 = 120 = 2^3 dot 3 dot 5$, so by the Sylow theorem, $S_5$ contains subgroups of cardinality $8$, $3$, and $5$.

  ($S_6$) We have $hash S_6 = 720 = 2^4 dot 3^2 dot 5$, so by the Sylow theorem we have subgroups $H$ of order $16, 9$, and $5$.  

  $hash H =9$ is given by $
  H = angle.l (123), (456) angle.r := {(123)^i (456)^j : 0 <= i, j <= 2} tilde.equiv ZZ\/3 ZZ times ZZ\/3 ZZ,
  $ or similarly for any other two disjoint cycles of three elements.

  $hash H = 16$ is given by $H tilde.equiv D_8 times S_2.$
    
  ($S_7$) We have $hash S_7 = 2^4 dot 3^2 dot 5 dot 7$. Subgroups of size $16, 9, 5$ can be simply realized as those from $S_6$, and of size $7$ as just the cyclic subgroup generated by an element of order 7.

  ($S_8$) We have $hash S_8 = 2^7 dot 3^2 dot 5 dot 7$ so we have subgroups of size $128, 9, 5, 7$. The latter 3 subgroups are easy to find; the first is found by $
  H tilde.equiv angle.l (15)(26)(48)(37), D_8 times D_8 angle.r,
  $ where we can view the first copy of $D_8$ acting on a square labeled $1,2,3,4$, the second acting on a square labeled $5,6,7,8$, and the distinguished permutation swapping all the vertices ?? // TODO
]

#theorem[Fix a group $G$ and a prime $p$. TFAE:
1. There exists a $G$-set $X$ of cardinality prime to $p$ with no orbit of size $1$.
2. There is a transitive $G$-set of cardinality $> 1$ and of cardinality prime to $p$. 
3. $G$ has a proper subgroup of index prime to $p$.
]<thm:tfaegroups>

#proof[
(1. $=>$ 2.) We can write $X = X_1 union.sq X_2 union.sq dots union.sq X_t$ where $X_i$ the orbits of the action; note that the action of $G$ on each $X_i$ transitive. Since $p divides.not hash X$, then $exists i$ for which $p divides.not hash X_i$. $hash X_i > 1$ necessarily, since $X$ was assumed to have no orbit of size 1.

(2. $=>$ 3.) We have $X tilde.equiv G \/ H$ for some subgroup $H$, where $H = "Stab"_G (x_0)$ for some $x_0 in X$. Moreover, $hash X = [G : H]$ hence $p divides.not [G : H]$.

(3 $=>$ 1.) Given $H$, take $X = G \/ H$. Then $G$ necessarily acts transitively on $X$ so $X$ has no orbit of size $1$, and has cardinality $hash X = [G : H]$, so $X$ also has cardinality prime to $p$ as $[G : H]$ prime to $p$.
]

#theorem[For any finite group $G$ and any prime $p divides hash G$ with $hash G = p^t dot m$, $m eq.not 1$, then $(G, p)$ satisfies the properties of the previous theorem.]

#proof[
  It suffices to prove 1. holds. Let $
  X = {"all subsets of" G "of size" p^t}.
  $ $X$ a $G$-set; for any $A in X$, $g A$ also a set of size $p^t$ hence $g A in X$. Moreover, $G$ acts on $X$ without fixed points; that is, there is no element $x$ in $X$ such that $g x = x$ for every $g in G$. We have in addition $
  hash X = mat(p^t dot m; p^t) = ((p^t m)(p^t m - 1) (dots.c) (p^t m - p^t + 1))/(p^t)! = product_(j=0)^(p^t - 1) ((p^t m - j)/(p^t - j)).
  $ The max power of $p$ dividing $p^t m - j$ will be the same as the maximum power of $p$ dividing $j$ itself (since $p | p^t m$), and by the same logic the same power that divides $p^t - j$. That is, then, the max power of $p$ that divides both numerator and denominator in each term of this product for each $j$, hence they will cancel identically in each term. Thus, $p divides.not hash X$ as desired.

]

#proof[(Of @thm:sylow1) Fix a prime $p$ and let $G$ be a group of minimal cardinality for which the theorem fails for $(G, p)$. By 3. of @thm:tfaegroups, there exists a subgroup $H subset.neq G$ such that $p divides.not [G : H]$. We have $hash G = p^t m$, and $hash H = p^t m'$; since $p divides.not (hash G)/(hash H) = (p^t m)/(p^t m') = m/m'$.

 Then, by our hypothesis $H$ contains a subgroup $N$ of cardinality $p^t$; $N$ is also a subgroup of $G$ and thus a Sylow-$p$ subgroup of $G$, contradicting our hypothesis of minimality.
]

#proof[(A Second Proof of @thm:sylow1) We may write $
G = C_1 union.sq C_2 union.sq dots.c union.sq C_h,
$ where $C_j = {g a g^(-1) : g in G}$. We must have (at least one) some $C_j$ where $hash C_j = 1$, so $C_j = {a}$; it must be that $a$ commutes with every $g in G$. Consider the center of $G$, $
Z(G) = {a : a g = g a forall g in G}.
$ Note that $Z(G)$ is a subgroup of $G$; $
G = Z(G) union.sq C_1 union.sq dots.c union.sq C_h',
$ where $C_j$ are the conjugacy classes of size $> 1$ (all the conjugacy classes of size $1$ are included in $Z(G)$). By the orbit-stabilizer theorem, the cardinality of each $C_j$ divides the cardinality of $G$ (and as $Z(G)$ a subgroup, so does the cardinality of $Z(G)$). We call this decomposition a "class equation of $G$".

With this setup, we assume again $G$ is the smallest group for which the theorem fails for $p$. We consider the following cases:

#underline("Case 1:") $p divides.not hash Z(G)$, then at least one $C_j$ must be of cardinality prime to $p$ (if all were divisible by $p$, then we'd have $
hash G equiv_p 0 equiv_p ("not" 0) + 0 + dots.c + 0,
$ which is impossible). Then, $C_j tilde.equiv G \/ H$ for some subgroup $H$ of $G$, with $hash H = p^t m' < hash G$, so by our assumption $H$ has a Sylow $p$-subgroup, and thus so does $G$.

#underline("Case 2"): $p divides hash Z(G)$. $Z(G)$ an abelian subgroup, so there exists a subgroup $Z subset.eq Z(G)$ with $hash Z = p$ (why? For every abelian group with $p | hash Z(G)$, $Z(G)$ has an element of that order, hence take the cyclic subgroup generated by that element; see following lemma). Then, since $Z$ is a normal subgroup, and we may consider $overline(G) = G\/Z$, which is then a group with cardinality $
hash overline(G) = (hash G)/(hash Z) = (p^t m)/(p) = p^(t-1) dot m < hash G,
$ so we may apply the induction hypothesis to $overline(G)$, i.e. $overline(G)$ has a Sylow $p$-subgroup $overline(H)$ of cardinality $p^(t-1)$. We have a natural, surjective homomorphism $
pi : G ->> overline(G) supset.eq overline(H).
$ Take $
H = union.big_(g Z in overline(H)) g Z,
$ or equivalently, $H = pi^(-1) (overline(H))$. We have an induced surjective homomorphism $
pi : H ->> overline(H)
$ with $ker(pi) = Z$, so $overline(H) tilde.equiv H \/ Z$, and thus $hash H = hash overline(H) dot hash Z = p^t$, and thus $H$ a Sylow $p$-subgroup of $G$.
]

#lemma[Let $p$ be prime. If $G$ a finite abelian group and $p | hash G$, then $G$ has an element of order $p$, i.e. there is a subgroup $Z subset G$ of cardinality $p$.]

#proof[
We can write $hash G = p dot m$. Remark that it suffices to find an element $g$ of order $t$ such that $p | t$; indeed, then the element $g^(t/p)$ has order $p$, which exists since then $t/p$ an integer.

Let $g_1, g_2, dots, g_t$ be a set of generators for $G$ and put $n_j := "ord"(g_j)$. Define now $
phi : (ZZ\/n_1 ZZ) times (ZZ\/n_2 ZZ) times dots.c times (ZZ\/n_t ZZ) -> G,\
(a_1, a_2, dots, a_t) |-> g_1^(a_1) g_2^(a_2) dots.c g_t^(a_t).
$ One can show that this is a homomorphism; moreover, it is surjective, since any element in $G$ can be written in terms of these generators. Hence, $hash G divides hash (ZZ\/n_1 ZZ) times (ZZ\/n_2 ZZ) times dots.c times (ZZ\/n_t ZZ) = n_1 n_2 dots.c n_t$. Since $p divides hash G$, then it follows too that $p divides n_1 n_2 dots.c n_t$ and thus there is some $n_i$ such that $p divides n_i$ ("Gauss's Lemma"). Hence, $g_j$ has order divisible by $p$.
]

#theorem("Sylow 2")[If $H_1$, $H_2$ are Sylow $p$-subgroups of $G$, then $exists g in G$ s.t. $g H_1 g^(-1) = H_2$.]

#proof[
  Consider $G \/ H_1$ as an $H_2$-set. We may write $
  G \/ H_1 = X_1 union.sq X_2 union.sq dots.c union.sq X_N,
  $ where the $X_j$'s are disjoint orbits, then $hash X_j | hash H_2$, so $hash X_j = p^a$, some $a <= t$. Then, there must be some orbit $X_j$ of cardinality $1$; since $p | hash X_j$, but $p divides.not G \/ H_1$, but each must be a power of $p$ hence the power $a$ of some cardinality must be $0$. Then, we may write $X_j = {g H_1}$. This is fixed by every element in $H_2$, i.e. $forall h in H_2$, $h g H_1 = g H_1$ i.e. $
  (g^(-1) h g) H_1 = H_1,
  $ i.e. $g^(-1) h g in H_1$ for all $h in H_2$, and thus $g^(-1) H_2 g = H_1$.
]

#theorem("Sylow 3")[The number $N_p$ of distinct Sylow $p$-subgroups satisfies 
+ $N_p | m$,
+ $N_p equiv_p 1$,
where $hash G = p^t m$.
]

#proof[
  1. Let $X = {"all Sylow" p"-subgroups"}$. By Sylow 2, $G$ acts transitively on $X$ by conjugation. Then, by the orbit-stabilizer theorem, $
  hash X = (hash G)/(hash N),
  $ where $N$ the _normalizer_ of $H$ $= {g in G : g H g^(-1) = H}$. We know that $H subset N$, hence $p^t = hash H | hash N$, so $hash X | (hash G)/(hash H) = m$ and so $hash X | m$.

  2. Let $H$ be a Sylow $p$-subgroup and let $X$ be the set of all Sylow $p$-subgroups as above, viewed as a $G$-set by conjugation. Again, this is a transitive action. We can also view $X$ as an $H$-set. Then, $
  X = X_1 union.sq dots.c union.sq X_a,
  $ where $
  hash X_j divides hash H = p^t,
  $ i.e. $hash X_j = 1, p, p^2, dots, p^t$. We claim there is exactly one $X_j$ of size 1. Let $X_j = {H'}$ be an orbit of size 1 (remarking that there exists at least one, namely just $H$ itself.) Then, we must have $a H' a^(-1) = H'$ for all $a in H$. Then, $H$ is contained in the normalizer of $H'$, $N$, $
  H subset N = {a in G : a H' a^(-1) = H'}.
  $ $H' subset N$, but moreover, $H'$ a normal subgroup of $N$. Then, $
  p divides.not hash (N\/ H').
  $ We have the natural map $
  phi : N -> N\/H',
  $ and we consider $phi(H)$; its cardinality must be $1$, since it must simultaneously divide $p^t$ and something prime to $p$. Thus, $H subset ker(phi) = H'$. But $hash H = hash H'$, and thus $H = H'$. Hence, there is a unique orbit of size $1$, just $H$ itself.

  Thus, the cardinality of $X$ will be, modulo $p$, 1.
]

=== Illustrations of the Sylow Theorems
1. $G = S_4$; $hash G = 2^3 dot 3$. The Sylow $8$-subgroup is $D_8$, $
{1, (1234), (13)(24), (1432), (12)(34), (14)(23), (13), (24)}.
$ $N_2$ must divide $3$ and must equal $1$ modulo $2$, so $N_2 = 1$ or $3$. In this case, $N_2 = 3$ indeed; $D_8$ is not normal in $S_4$, which it would have to be if $N_2 = 1$. Inside $S_4$, we also have the "Klein group" $
V = {1, (12)(34), (13)(24), (14)(23)},
$ which is normal in $S_4$. The resulting quotient $
S_4 \/ V
$ is then a group of cardinality $6$, isomorphic to $S_3$. Consider the homomorphism $
phi : S_4 -> S_3.
$ $S_3$ has 3 elements of order 2, $(a b), (a c), (b c)$ which generate subgroups of order 2. If $A$ one of these subgroups of order 2, then $phi^(-1) (A)$ is a Sylow $2$-subgroup.

2. 
#theorem[
  Let $p, q$ be primes with $p < q$, $p divides.not q-1$. If $G$ is a group of cardinality $p dot q$, then $G tilde.equiv ZZ\/p q ZZ$.
]
What if $p divides q - 1$? Consider, for instance, $p = 2, q = 3$, then $S_3$ has cardinality $p dot q$. More generally, suppose $p = 2$ and $q$ any odd prime. Then $p divides q-1$ always, and we may consider $D_(2 q)$.

For $p eq.not 2$, consider the field $FF_q = ZZ\/q ZZ$, and let $
G = {T_(a, b) : FF_q -> FF_q, T_(a, b) (x) := a x + b : a in FF_q^times, b in FF_q}
$ be the group of affine-linear transformations on the field. We have that $hash G = (q - 1) q$ ($q - 1$ choices for $a$, $q$ choices for $b$), and that $G$ _not_ abelian; $
(T_(a_1, b_1) compose T_(a_2, b_2))(x) = a_1 (a_2 x + b_2) + b_1 = a_1 a_2 x + a_2 b_2 + b_1 = T_(a_1 a_2, a_2 b_2 + b_1)(x) eq.not (T_(a_2, b_2) compose T_(a_1, b_1)) (x).
$ There exists a subgroup $H subset FF_q^times$ with $hash H = p$, since $FF_q^times$ abelian and $p | hash FF_q^times = q - 1$, so we may consider the subgroup of $G$ given by $
G_(p q) = {T_(a, b) : FF_q -> FF_q : a in H, b in FF_q} subset G,
$ with $hash G_(p q) = p dot q$. Let us consider the Sylow subgroups of $G_(p q)$. 

A Sylow $p$-subgroup can be given by $P:={T_(a, 0) : a in H}$, and a Sylow $q$-subgroup can be given by ${T_(1, b) : b in FF_q}$. Let $N_p, N_q$ the number of Sylow $p$-, $q$-subgroups. By Sylow 3, we know that $N_p equiv_p 1$ and $N_p | q$, hence it must be that $N_p = 1$ _or_ $q$. Similarly, $N_q equiv_q 1$ and $N_q | p$, so it must be that $N_q = 1$ so the Sylow $q$-subgroup we found is unique, and moreover normal.

Remark that the map $
 T_(a, b) |-> a, wide G -> FF_q^times "and" G_(p q) -> H
$ is a homomorphism.

To further investigate if $N_p = 1$ or $q$, we can see how $P$ behaves under conjugation; if it is normal, then it is unique and so $N_p = 1$, else if we can find any second conjugate subgroup then it must be that $N_p = q$. Consider $
(T_(1, 1) compose T_(a, 0) compose T_(1, -1))(x) = a(x - 1) + 1 = a x - a + 1 = T_(a, - a + 1) (x) in.not P "if" a = 1, 
$hence $P$ not normal and thus $N_p = q$.

== Burnside's Counting Lemma

#definition("Fixed Point Set")[
  Let $G$ a finite group and $X$ a finite $G$-set. Given $g in G$, we denote $
  X^g := {x in X | g x = x}.
  $ the _fixed-point set_ of $g$, and $
  "FP"_X (g) := hash X^g.
  $
]

#example[
  If $G = S_4$ acting on $X = {1, 2, 3, 4}$, then for instance $
  "FP"_X ((12)) = 2, "FP"_X ((12)(34)) = 0.
  $
]

#proposition[
$"FP"_X (h g h^(-1)) = "FP"_X (g)$; we say $"FP"_X$ a _class function_ on $G$, being constant on conjugacy classes.
]

#proof[
  Define $X^g -> X^(h g h^(-1))$ by $x |-> h x$, noting $h g h^(1) h x = x$ for $x in X^(g)$; this is a bijection.
]

#theorem("Burnside")[
  $
  1/(hash G) sum_(g in G) "FP"_X (g)= hash (X\/G) = hash G-"orbits on" X.
  $
]

#proof[
  Let $Sigma subset.eq G times X$ such that $
  Sigma = {(g, x) : g x = x}.
  $ We will count $hash Sigma$ in two different ways, by noting that we can "project" $Sigma$ either to $G$ or $X$ on the first or second coordinate, respectively. On the one hand (the "$G$ view"), we have $
   hash Sigma = sum_(g in G) "FP"_(X) (g),
  $ and on the other (the "$X$ view") $
  hash Sigma = sum_(x in X) hash "Stab"_G (x) &= sum_(sans(O) in X \/ G) sum_(x in sans(O)) hash "Stab"_G (x).
  $ The orbit-stabilizer theorem gives us that for any $x in sans(O)$, $hash "Stab"_G (x) dot hash sans(O) = hash G$, hence further $
  hash Sigma = sum_(sans(O) in X\/G) sum_(x in sans(O)) (hash G)/(hash sans(O)) = sum_(sans(O) in X\/G) hash G,
  $ where the simplification in the final equality comes from the fact that we remove dependence on $x$ in the inner summation, and we are just summing a constant $hash sans(O)$ times. Hence, $
  hash Sigma = hash (X \/ G) dot hash G,
  $ and so bringing in our original computation ("$G$ view"), $
sum_(g in G) "FP"_(X) (g) = hash (X \/ G) dot hash G =>   1/(hash G) sum_(g in G) "FP"_X (g)= hash (X\/G),
  $ completing the proof.
]

// TODO One can view the the theorem as "the average number of fixed points is the number of orbits"
#corollary[If $X$ is a transitive $G$-set with $hash X > 1$, then $exists g in G$ such that $"FP"_(X) (g) = 0$.]

#proof[
  By Burnside's, $
  1/(hash G) sum_(g in G) "FP"_X (g) = 1,
  $ but we have that $"FP"_X (1) = hash X > 1$ since $1$ fixes everything, so there must be at least a $g$ such that $"FP"_X (g) = 0$.
]

#example("Application of Burnside's")[
Let $G = S_4 = "Aut"("cube")$. We can realize several different (transitive) $G$-sets; for instance $X = {1, 2, 3, 4}, F = {"faces"}, E = {"edges"}, V={"vertices"}$. We can compute the number of fixed points $"FP"_X (g)$ of different elements of $G$ on these $G$-sets. Recall that it suffices to check one element per conjugacy class of $G$.

#align(center, 
  table(
  columns: (auto, auto, auto, auto, auto, auto, auto, 1fr),
  inset: 8pt,
  stroke: none,
  align: horizon,
  [*Conj. Class*], $hash$, $X$, $F$, $E$, $V$, [*Geometric Desc.*], [],
  table.hline(start: 0, end: 7),
  $id$, $1$, [4], [6], [12], [8], [$id$], [],
  $(12)$, $6$, [2], [0], [2], [0], [Rotations about\ "edge diagonals"], image("./cuberotee.png", width: 50%),
  $(12)(34)$, $3$, [0], [2], [0], [0], [Rotations about\ "face diagonals", $pi$],image("./cuberotf.png", width: 50%),
  $(123)$, $8$, [1], [0], [0], [2], [Rotations about\ "principal diagonals"],image("./cuberotec.png", width: 50%),
  $(1234)$, $6$, [0], [2], [0], [0], [Rotations about\ "face diagonals", $pi\/2$], image("./cuberotf.png", width: 50%),
  table.hline(start: 0, end: 7),
  [$1/(hash G) sum "FP"_(\"X\") (g):$], [], $1$, $1$, $1$, $1$, [], []
  )
)
The number of orbits, hence, in each case is $1$, as we already knew since $G$ acts transitively on all of these sets.

Remark that for two $G$-sets $X_1, X_2$, $"FP"_(X_1 times X_2) (g) = "FP"_(X_1) (g) dot "FP"_(X_2) (g)$, where the action of $G$ on $X_1 times X_2$ defined by $g (x_1, x_2) = (g x_1, g x_2)$. Using this we can consider actions on "pairs" of elements;

#align(center, 
  table(
  columns: (auto, auto, auto, auto),
  inset: 8pt,
  stroke: none,
  [*Conj. Class*], $F times F$, $F times V$, $V times V$,
  table.hline(start: 0, end: 7),
  [$id$], $36$, $48$, $64$,
  [$(12)$], $0$, $0$, $0$,
  [$(12)(34)$], $4$, $0$, $0$,
  [$(123)$], $0$, $0$, $4$, 
  [$(1234)$], $4$, $0$, $0$,
  table.hline(start: 0, end: 7),
  [$1/(hash G) sum "FP"_(\"X\") (g):$], $3$, $2$, $4$
  )
)
// For $F times F$, the orbits are of the form $(x, x)$, $(x, y)$ for $x, y$ adjacent edges, and $(x, y)$ for $x, y$ opposite edges.
]

#definition([Colorings of a $G$-set])[Let $C := {1, 2, dots, t}$ be a set of "colors". A coloring of $X$ by $C$ is a function $X -> C$. The set of all such functions is denoted $C^X$. Then, $G$ acts on $C^X$ naturally by $
G times C^X -> C^X, wide (g, f) |-> g f : X -> C, wide g f(x) := f (g^(-1) x).
$]


#example[How many ways may we color the _faces_ of a cube with $t$ colors? There are $6$ faces with $t$ choices per face, so $t^6$ faces. More interestingly, how many _distinct_ ways are there, up to an automorphism (symmetry) of the cube? $G$ acts on $F$, and hence on the set of "$t$-colorings". Let $F$ again be the set of faces and $X := C^F$. Then, $
hash X = t^(6).
$ We would like to calculate the number of orbits of $G$ acting on $X$, namely $hash (X \/ G)$. We compute the number of fixed points for each conjugacy class of $G$; in general, $hash (C^F)^g = t^(hash (F\/angle.l g angle.r)) = t^(hash "orbits of" <g> "on" F)$. 
($g <-> (a b c) (d e) (f) (g)$ for each element $a$, say, we have $t$ choices for the coloring of $a$. Then $b$, $c$ must be the same color. This repeats for each transposition. etc // TODO)

#align(center, table(
  align: horizon,
  inset: 8pt,
  columns: 5,
  stroke: none,
  "Conj. Class", $hash$, $F$, [Shape], $X$,
  table.hline(start: 0, end: 5),
  $id$, $1$, $6$, $1^6$, $t^6$,
  $(12)$, $6$, $0$, $(a b)(c d)(e f)$, $t^3$,
  $(12)(34)$, $3$, $2$, $(a b) (c d)$, $t^4$,
  $(123)$, $8$, $0$, $(a b c) (d e f)$, $t^2$,
  $(1234)$, $6$, $2$, $(a b c d)$, $t^3$,
  table.hline(start: 0, end: 5)
)) By Burnside's then, $
hash (C^F \/G) &= 1/24 sum_(g in G) "FP"_(C^F)(g)\
&= 1/24 (t^6 + 6t^3 + 3 t^4 + 8 t^2 + 6 t^3)\
&= 1/(24) (t^6 + 3t^4 + 12 t^3 + 8t^2).
$ Remark that this polynomial does not have integer coefficients, but indeed must have integer outputs for integer $t$'s. This is not obvious.

// We define the set of $t$-colorings by $
// c^F := {c : F -> {1, dots, t}},
// $ ($c$ assigns to each face $F_i$ a color label $i in {1, dots, t}$), and hence we seek to find $
//   hash (c^F \/ G).
// $
]

== The Exceptional Outer Automorphism of $S_6$

We consider the fixed points of $S_5$ acting on various sets, in particular the quotient space $S_5 \/ F_(20)$, where $F_(20)$ the _Frobenius group_ of affine linear transformations $sigma : x |-> a x + b$, $a in FF_5^times$, $b in FF_5$. The possible orders of elements $sigma in F_20 subset S_5$ are $
1 <-> 1^5, 5 <-> (0 1 2 3 4), 4 <-> (1 2 4 3), 2 <-> (14) (23).
$ In particular, each (non-identity) permutation has _at most_ one fixed point. One can verify that elements of these types indeed exist in $F_20$.

  Remark that to find the cycle shape when acting on $S_5 \/ F_(20)$, it suffices to check if the permutation given is conjugate to an element in $F_(20)$, since $(12) g F_(20) = g F_(20) <=> g^(-1) (12) g in F_20$. So, in short, $sigma in C$ for some conjugacy class $C subset S_5$ has no fixed points if it is not conjugate to an element in $F_20$. This holds more generally. 

  #align(center, table(
    columns: 7,
    inset:8pt,
    stroke:none,
    align: horizon,
    $C$, $hash$, ${1,2,3,4,5}$, ${1,2,3,4,5,6}$, $S_5 \/ F_(20)$, [Shape on $S_5 \/ F_(20)$], "Reasoning",
    table.hline(start: 0, end: 7),
    $id$, $1$, $5$, $6$, $6$, $()$, "Identity",
    $(12)$, $10$, $3$, $4$, $0$, $(a b) (c d) (e f)$,"Order 2 with no fixed points",
    $(12)(34)$, $15$, $1$, $2$, $2$, $(a b)(c d)$,[Square of $(1234)$],
    $(123)$, $20$, $2$, $3$, $0$, $(a b c) (d e f)$,"Order 3 with no fixed points",
    $(1234)$, $30$, $1$, $2$, $2$, $(a b c d)$,"Order 4",
    $(12345)$, $24$, $0$, $1$, $1$, $(a b c d e)$,"Order 5",
    $(123)(45)$, $20$, $0$, $1$, $0$, $(a b c d e f)$,"Order 6 with no fixed points",
    table.hline(start: 0, end:7)
  )) 
  
Since $F_20$ of index $6$ in $S_5$, we have then a natural injection $
f: S_5 -> "Aut"(S_5\/F_20) tilde.equiv S_6,
$ with image $tilde(S_5) := im(f) subset S_6$. The cycle shapes of elements in $tilde(S_5)$ are precisely those listed in the 2nd-right-most column above.

Now, we can realize $S_5 subset S_6$ naturally as the permutations that fix, say, $6$. However, its clear that while $S_5 tilde.equiv tilde(S_5)$, they are not conjugate to each other; indeed, $tilde(S_5)$ contains cycle shapes that $S_5$ does not, and since conjugation preserves cycle shape, they certainly cannot be conjugate.

We have that $S_6$ acts transitively on $S_6 \/ S_5$, which is isomorphic as a $G$-set to the typical action of $S_6$ on 6 numbers. This induces a natural map $S_6 -> "Aut"(S_6\/S_5) tilde.equiv S_6$. One can show that this map is actually an automorphism of $S_6$, more specifically an _inner automorphism_, one that may be realized as conjugation by an element of $S_6$. But we can also view $S_6$ acting on $S_6 \/ tilde(S_5)$, which will also be a transitive group action and also induce an automorphism $S_6 -> "Aut"(S_6\/ tilde(S_5)) tilde.equiv S_6$. To view how this automorphism acts on elements of $S_6$, we view how elements of distinct conjugacy classes of $S_6$ affect $tilde(S_5)$. To do so, we need only consider that 1) automorphisms preserve order and 2) automorphisms induce bijections when restricted to conjugacy classes, namely, given a conjugacy class $C$, it must entirely map to another conjugacy class of the same size. We use the notation $("order")("letter if more than one of that order")$ for conjugacy classes.

 #align(center,
table(
  columns: 4,
  stroke: none,
  inset: 0.5em,
  $C$, $hash$, $S_6\/S_5$, $S_6\/tilde(S_5)$,
  table.hline(start: 0, end: 4),
  $1A$, $1$, $()$, $()$,
  $2A$, $15$, $(12)$, $(a b)(c d)(e f)$,
  $2B$, $45$, $(12)(34)$, $(a b)(c d)$,
  $2C$, $15$, $(12)(34)(56)$, $(a b)$,
  $3A$, $40$, $(123)$, $(a b c)(d e f)$,
  $3B$, $40$, $(123)(456)$,$(a b c)$,
  $4A$, $90$, $(1234)$, $(a b c d)$,
  $4B$, $90$, $(1234)(56)$, $(a b c d)(e f)$,
  $5A$, $144$, $(12345)$, $(a b c d e)$,
  $6A$, $120$, $(123456)$, $(a b c)(d e)$,
  $6B$, $120$, $(123)(45)$, $(a b c d e f)$,
)
)
In particular, the automorphism $S_6 -> "Aut"(S_6 \/ tilde(S_5))$ interchanges the conjugacy classes $2A$ and $2C$, $3A$ and $3B$, and $6A$ and $6C$.


  // Hence, the list of elements in the right-most column is precisely the cycle shapes of elements in the "exotic" $S_5 subset S_6$, not conjugate to the typical inclusion $S_5 arrow.hook S_6$.


= Rings and Fields

Groups are to symmetries as rings are to numbers.

== Definitions

#definition("Ring")[
  A _ring_ is a set $R$ endowed with two operations, $+, times : R times R -> R$ satisfying \
- (_addition_) $(R,+)$ is an abelian group, with neutral element $0_R$ and (additive) inverses of $a in R$ denoted $-a$;\
- (_multiplication_) $(R, times)$ is a _monoid_ i.e. it has a neutral element $1_R$ and is associative;
- (_distribution 1_) $a times (b + c) = a times b + a times c$ for all $a,b, c in R$;
- (_distribution 2_) $(b + c) times a = b times a + c times a$ for all $a, b, c in R$.
]

#remark[
 + Conventions differ; some texts do not require $1$, and call such objects with one a "ring with unity".
 + We will blanketly assume $1 eq.not 0$, else $R$ is trivial.
 + 0 is never invertible; $1 times a = (0 + 1) times a = 0 times a + 1 times a => 0 times a = 0$ for any $a in RR$, so in particular there is no $a$ such that $0 times a = 1$.
 + Exercise: show $(-a) times (- b) = a times b$.
]

#example("Examples of Rings")[
+ $ZZ$
+ $QQ$ (essentially $ZZ$ appending inverses)
+ Completions of $QQ$; taking ${"Cauchy Sequences"}\/{"Null Sequences"} = RR$ under the standard distance $d(x, y) = abs(x - y)$. Alternatively, let $p$ be a prime and take the $p$-adic metric $|x - y|_p := p^(-"ord"_p (x - y))$ on $QQ$, and consider the completion with respect to $|dot|_p$, denoted $QQ_p$, called the _field of $p$-adic numbers_.
+ $CC := RR[i] = {a + b i : a, b in RR}$
+ Polynomial rings; given a ring $R$, we may define $R[x] := {a_0 + a_1 x + dots.c + a_n x^n : a_i in R}$ where $x$ a "formal" indeterminate variable.
+ The _Hamilton quaternions_, $HH = {a + b i + c j + d k : a, b, c, d in RR}$, where $i^2 = j^2 = k^2 = -1$ and $i j = -j i = k, j k = -k j = i, i k = - k i = -j$.
+ For any commutative ring $R$, $M_n (R) = n times n$ matrices with entries in $R$ is a ring. In particular, associativity of multiplication in $M_n (R)$ follows from the identification of matrices with $R$-linear functions $R^n -> R^n$ and the fact that function composition is associative.
+ Given a ring $R$, we can canonically associate two groups, $(R, +, 0)$ ("forgetting" multiplication) and $(R^times, times, 1)$ ("forgetting" addition and restricting to elements with inverses, i.e. _units_). 
+ If $G$ is any finite group and $R$ a ring, we may consider $R[G] = {sum_(g in G) a_g g : a_g in R}$, a _group ring_. Addition is defined component-wise, and multiplication $
(sum_(g in G) a_g g)(sum_(h in H) b_h h) = sum_(g, h in G) a_g b_h dot g h = sum_(g in G) (sum_(h_1 dot h_2 = h in G) a_(h_1) b_(h_2))g.
$
]

== Homomorphisms

#definition("Homomorphism of Rings")[
  A _homomorphism_ from a ring $R_1$ to a ring $R_2$ is a map $phi: R_1 -> R_2$ satisfying:
  - $phi(a + b) = phi(a) + phi(b)$ for all $a, b in R_1$ (that is, $phi$ a group homomorphism of the additive groups $(R_1, +)$, $(R_2, +)$)
  - $phi(a b) = phi(a)phi(b)$
  - $phi(1_(R_1)) = phi(1_(R_2))$
]

#definition("Kernel")[The _kernel_ of a ring homomorphism $phi$ is the kernel as a homomorphism of additive groups, namely $
ker(phi) = {a in R_1 : phi(a) = 0_(R_2)}.
$]

#definition("Ideal")[A subset $I subset.eq R$ is an _ideal_ of $R$ if 
+ $I$ an additive subgroup of $(R, +)$, in particular $0 in I$, $I$ closed under addition and additive inverses
+ $I$ closed under multiplication by elements in $R$, i.e. for all $a in R, b in I$, $a b in I$ _and_ $b a in I$ (the second condition only being necessary when $R$ non-commutative.)
]

#proposition[If $phi$ is a ring homomorphism, then $ker(phi)$ is an ideal of $R_1$.]

#proof[The first requirement follows from the fact that $phi$ an additive group homomorphism. For the second, let $a in R_1, b in ker(phi)$, then $phi( a b) = phi(a) phi(b) = phi(a) dot 0 = 0$ so $a b in ker(phi)$.]

#proposition[
  If $I$ an ideal of $R_1$, then there exists a ring $R_2$ and a ring homomorphism $phi : R_1 -> R_2$ such that $I = ker(phi)$.
]

#proof[
  Let $R_2 = R_1 \/ I = {a + I : a in R_1}$ be the quotient group of $R_1$ additively. We can define multiplication by $(a + I) (b + I) := a b + I$. One may verify this indeed makes $R_2$ a ring. Then take $phi$ to be the quotient map $
  phi : R_1 -> R_2, wide a |-> a + I.
  $ Then, this is indeed a (surjective) ring homomorphism, with $ker(phi) = I$.
]

#theorem("Isomorphism Theorem")[Let $R$ be a ring (group) and $phi$ be a surjective homomorphism of rings (groups) $phi : R ->> S$. Then, $S$ is isomorphic to $R \/ ker (phi)$.


#align(center)[#commutative-diagram(
  node((0, 0), $R$),
  node((0, 1), $S$),
  node((1, 0), $R \/ "ker"(phi)$, "quot"),
  arr($R$, $S$, $phi$, "surj"),
  arr("quot", (0, 1), $tilde(phi)$, label-pos: right, "dashed"),
  arr($R$, "quot", $pi$),
)]
]

#proof[
Define $
tilde(phi) : R \/ ker(phi) -> S, wide a + ker(phi) |-> phi(a).
$ One can verify this indeed an isomorphism.
]

== Maximal and Prime Ideals

#definition("Maximal")[An ideal $I subset.eq R$ is _maximal_ if it is not properly contained in any proper ideal of $R$, namely if $I subset.neq I'$ for any other ideal $I'$, then $I' = R$.]

#definition("Prime")[An ideal $I subset.eq R$ is _prime_ if $a b in I$, then $a$ or $b$ in $I$.]

#example[
  Let $R = ZZ$ and $I = (n) = n ZZ = {n a : a in ZZ}$ for some $n in NN$. We claim $(n)$ is prime iff $n$ is prime. If $n$ prime, then if $a b in I$, then $n | a b$. By Gauss's Lemma, then $n$ divides at least one of $a$ or $b$, and hence either $a$ or $b$ in $I$. Conversely, if $n$ not prime, then we may write $n = a b$ where $|a|, |b| < n$. Then, $a, b in I$, but $n$ divides neither and so $a, b in.not I$.
]

#theorem[If $I subset.eq ZZ$ an ideal, then there exists $n in ZZ$ such that $I = (n)$.]
#proof[
  Consider $ZZ\/I$. As an abelian group, it is cyclic, generated by $1 + I$. Let $n = hash (ZZ\/I) = "ord"(1 + I)$. If $n = infinity$, then $ZZ -> ZZ\/I$ is injective and $I = (0)$. Else, $I = (n)$.

  Alternatively, assume that $I eq.not (0)$. Let $n = min {a in I : a > 0}$. Let $a in I$, then we may write $a = q dot n + r$ where $0 <= r < n$. $a in I$ by assumption as is $n$, and thus so must be $q n in I$. Hence, $a - q n = r in I$, and so $r = 0$, by assumption on the minimality of $n$.
]

#definition("Principal Ideal")[An ideal of a ring $R$ which is of the form $a R = (a)$ is called _principal_. A ring in which every ideal is of this type is called a _principal ideal ring_.]

#example[
  $ZZ$ is a principal ideal ring. Another example is $R = FF[x]$ where $FF$ a field.
]

#theorem[If $I$ an ideal of $FF[x]$, then $I$ is a principal ideal.]

#proof[
  Let $f(x) in I$ non-zero and of minimal degree, which necessarily exists if $I eq.not (0)$. Put $d := "deg" f$. If $g(x) in I$, then $g(x) = f(x) q(x) + r(x)$ where $"deg" r < d$. Then, we have that $r in I$, so by minimality of $d$ it must be that $r = 0$.
]

#remark[We conventionally take $deg (0) = -infinity$ for the sake of the formula $deg (f g) = deg f + deg g$ and taking $-infinity + k = 0$ for any $k$.]

#example[
  Consider $phi : ZZ -> ZZ\/n ZZ$. Let $I subset.eq ZZ\/n ZZ$ and consider $phi^(-1) (I)$; this is an ideal of $ZZ$ and so is principal ie $phi^(-1) (I) = (a)$ for some $a in ZZ$. Then, $I =(a + n ZZ) subset.eq ZZ\/n ZZ$.
]
#example[
  Let $R = ZZ[x] = {a_n x^n + dots.c + a_1 x + a_0 : a_i in ZZ}$. Take $I = {f(x) : f(0) "even"} subset.neq ZZ[x]$. We claim this an ideal. The subgroup property is clear. If $f(x) in ZZ[x]$ and $g(x) in I$, then $f(0) g(0) = $ some integer $dot$ even integer $=$ even. Elements of $I$ include $2$, $x$, $dots$ any polynomial with $a_0$ even. If $I$ were principal, then there must exist some element in $R$ dividing both $2$ and $x$; the only possibilities are $1$ and $-1$. This would imply, then, that $I = R$, which is not possible and so $I$ not principal. We may say, however, that $I$ is generated by $2$ elements, $I = (2, x) = 2 ZZ[x] + x ZZ[x]$.
]

#example[
  Let $R = FF[x, y]$. Consider $(x, y) = R x + R y = {f : f(0,0) = 0}$ with typical element $x f(x, y) + y g(x, y)$; these will not have constant terms.
]

#proposition[
  $I$ is a prime ideal of $R$ iff $R\/I$ has no zero divisors (namely an element $x eq.not 0$ such that $x y = 0$ for some $y eq.not 0$); such a ring is called an _integral domain_.
]

#proof[
  Given $a + I, b + I in R\/I$, $(a + I)(b + I) = 0 => a b + I = 0 => a b in I$. By primality of $I$, then at least one of $a, b in I$, so at least one of $a + I, b + I = 0$.
]

#remark[
  If $R$ an integral domain, then it satisfies the "cancellation law", namely $forall a eq.not 0, a x = a y => x = y$, since we may write $a (x - y) = 0$ hence it must be $ x- y = 0 => x = y$.
]

#theorem[$I$ is a maximal ideal $<=>$ $R\/I$ is a field.]

#proof[
  ($=>$) Let $a + I in R \/ I$. If $a + I eq.not 0$, then consider the ideal $R a + I supset.neq I$. By maximality of $I$, it must be that $R a + I = R$. So, anything in $R$ can be written as a "multiple" of $a$ plus an element of $I$, so in particular $1 in R$ may be written $1 = b a + i$ for some $i in I, b in R$. Passing to the quotient, we find $
  1 + I = (b + I)(a + I) => b + I = (a + I)^(-1) in R\/I,
  $ so we indeed have multiplicative inverses.\
  ($impliedby$) Given $J supset.neq I$, let $a in J minus I$. Then, $a + I eq.not 0 in R\/I$, so there exists a $b$ such that $b a + I = 1 + I$ since $R\/I$ a field, and hence $1 in J$ so $J = R$ and thus $I$ maximal.
]

== Quotients

#example[
  Let $R = ZZ, I = (n)$, and consider $
  R\/I = ZZ\/n ZZ &= { a + n ZZ : a + ZZ}\
  &= {0, 1, 2, dots, n - 1} thin (mod n).
  $
  Let $R = FF[x], I = (f(x))$, and consider $
  R\/I = FF[x]\/(f(x)) &= {p(x) + f(x) FF[x]}\
  &= {p(x) : "deg" p <= d - 1 "where" d := deg f }.
  $
]

#remark[
  In $R\/I, a+I = b+I<-> a - b in I$. If $I = (d)$ principal, then $a + I = b + I <=> d | b - a$. For more general quotients (namely, more general ideals) this is a more difficult question.
]

#example[
  Let $R = ZZ[x], I = (2, x) = {f(x) : f(0) "even"}$, then $ZZ[x]\/I$ has precisely two elements, and indeed is isomorphic to $ZZ\/2 ZZ$. To see this, consider the map $
  phi : ZZ[x] -> ZZ\/2 ZZ, wide f(x) |-> f(0) "mod" 2,
  $ a surjective homomorphism, with $
  ker (phi) = {f(x) : f(0) equiv_2 0} = {f(x) : f(0) "even"} = I,
  $ so by the isomorphism theorem, $ZZ[x]\/ker(phi) tilde.equiv im(phi) => ZZ[x]\/I tilde.equiv ZZ\/2ZZ$.
]

#example[
  Let $R = FF[x, y] = {sum_(i,j = 1)^N a_(i,j) x^i y^j : a_(i,j) in FF}$ and $I = (x, y) = {f(x, y) : f(0,0) = 0}$. Then, $R\/I tilde.equiv FF$ by the map $f(x, y) + I |-> f(0,0)$.
]

#example[
  Let $R = FF[x_1, dots, x_n]$ and $I = (f_1, dots, f_t)$, for $f_j (x_1, dots, x_n) in R$. Then, consider $R\/I$; this is hard. Let $
  V(I) := {(x_1, dots, x_n) : f_i (x_1, dots, x_n) = 0 "for all" i = 1, dots, t}.
  $ Then, we may identify $R\/I -> $ functions on $V(I)$.
]

== Adjunction of Elements

#theorem[Given a ring $R$ and $p(x) in R[x]$, there exists a ring $S$ containing both $R$ and a root of $p(x)$.]

#proof[
  Let $S = R[x]\/(p(x))$, $R -> S$ by $a |-> a + (p(x))$. Let $alpha = x + (p(x))$; then $p(alpha) = p(x) + (p(x)) = 0 + (p(x))$.
]

#example[
  Let $R = RR$ and $p(x) = x^2 + 1$. Then, $RR[x]\/(x^2 + 1) = CC$.
]

= Midterm Review
== $A_5$ has no normal subgroups

#proposition[
  $A_5$, the group of even permutations on 5 letters, contains no normal subgroups.
]
Normal subgroups are always unions of conjugacy classes, so we begin by analyzing these. Remark that for any $x in A_5$, the conjugacy class $C_A (x)$ of $x in A_5$ is a subset of $C_S (x)$ of $x in S_5$. However, we cannot simply assume they are the same, since while two elements may be conjugate in $S_5$, the element needed to conjugate between them may not be in $A_5$.

Let $x in A_5$. Then, by the orbit-stabilizer theorem, $
hash C_A (x) = (hash A_5)/(hash "Stab"_A (x))
$ since $A_5$ acts on $C_A (x)$ transitively by conjugation. Similarly, $
hash C_S (x) = (hash S_5)/(hash "Stab"_S (x)).
$ Note that $"Stab"_S (x) supset.eq "Stab"_A (x)$ a subgroup, hence $hash "Stab"_S (x) = k dot "Stab"_A (x)$ for some $k in NN$. Moreover, since $hash S_5 = 2 dot hash A_5$, we may combine the expressions above and find $
hash C_S (x) = 2/k hash C_A (x) => k = 1, 2.
$ So, in particular, $hash C_A (x)$ is either equal to or half of $hash C_S (x)$. Since we know $C_A (x) subset C_S (x)$, then if the two are of the same size they are therefore equal.

We can now specialize to particular elements in $A_5$. 

- $(a b)(c d)$: there are $15$ such elements in $A_5$, hence $hash C_S ((a b)) = 15$. This isn't divisble by 2, hence it must be that $C_S ((a b)) = C_A ((a b))$. (We can also see this by noting that $(a b)$ stabilizes $(a b)(c d)$ but isn't contained in $A_5$, so the formula above gives the same result).
- $(a b c)$: there are 20 3-cycles in $A_5$, so we need to do a little more work here. Notice that by our work above $
C_S (x) = C_A (x) <=> hash "Stab"_S (x) = 2 dot hash "Stab"_A (x) <=> "Stab"_A (x) subset.neq "Stab"_S (x),
$ so to show the conjugacy classes are equal, it suffices to show that the stabilizers _aren't_ equal. Remark that, for instance, $(1 2) in "Stab"_S ((345))$, but $(12) in.not A_5$ so certainly $(1 2) in.not "Stab"_A ((3 4 5))$. It follows that the two subgroups are not equal, and thus $C_A ((3 4 5)) = C_S ((3 4 5)) = C_S ((a b c))$.
- $(a b c d e)$: there are 24 such elements in $A_5$; but remark that $24 divides.not hash A_5 = 60$, hence it can't be that $A_5$ acts transitively on the set of $5$-cycles. It follows then by our work above that there must be precisely two distinct conjugacy classes, each of size 12, of $5$-cycles in $A_5$, which we can represent, for instance, by $C_A ((12345)), C_A ((12354))$.\ \ We can see this more explicitly another way. Put $sigma := (1 2 3 4 5)$ and consider again $"Stab"_S (sigma)$. Clearly, $sigma^t in "Stab"_S (sigma)$ for $t = 0, dots, 4$, so $"Stab"_S (sigma) >= 5$; remark that each of these elements in $A_5$ as well. Suppose $g in "Stab"_S (sigma)$. Then, for every $k in {1, dots, 5}$, $
sigma = g^(-1) sigma g &<=> sigma (k) = g^(-1) sigma g(k)\
& <=> g (k + 1) = g (k) + 1,
$ since $sigma$ just "shifts" elements (mod $5$). In particular, such $g$'s are uniquely determined by their effect on a single element, since then we can apply this recursive relation to find its affects on the others. So, we have $5$ choices for, say, $g(1)$, and so in particular $hash "Stab"_S (sigma) <= 5$, and thus equals $5$. Hence, since every element in the stabilizer also in $A_5$, we conclude that $"Stab"_A (sigma) = "Stab"_S (sigma)$, and thus $hash C_A (sigma) = 1/2 hash C_S (sigma)$.

In summary, we have the following table:

#align(center, table(
  columns: 2,
  stroke: none,
  inset: .5em,
  "Conj. Class", $hash$,
  table.hline(start: 0, end: 2),
  $()$, $1$,
  $(12)(34)$, $15$,
  $(123)$, $20$,
  $(12345)$, $12$,
  $(12354)$, $12$,
  table.hline(start: 0, end: 2),
  "", $60$
))

We can now use the fact that normal subgroups are always unions of conjugacy classes and that the order of a subgroup always divides the order of the group to conclude that $A_5$ has no normal subgroups. Indeed, the possible orders of subgroups of $A_5$ would be the divisors of $60$, namely, $
1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30,
$ none of which cannot be achieved by adding cardinalities of conjugacy classes.

== Sylow 2-subgroups of $S_(n-1), S_n$

#proposition[
  Let $n$ odd. Then, $S_(n-1)$ and $S_n$ have the same Sylow 2-subgroup, and the number of Sylow 2-subgroups in $S_n$ is precisely $n$ times that in $S_(n-1)$.
]

We have the natural inclusion $S_(n-1) subset S_n$ by fixing an element, hence any Sylow 2-subgroups of $S_(n-1)$ are necessarily contained in $S_n$. Moreover, we have that $
(hash S_n)/(hash S_(n-1)) = (n!)/((n-1)!) = n,
$ by assumption odd, hence the powers of two in $n!, (n-1)!$ are the same, and so the Sylow 2-subgroups of the two must be the same as well.

To show the second claim, let $
X_n := {"Sylow" 2"-subgroups of" S_n}, quad X_(n-1) := {"Sylow" 2"-subgroups of" S_(n-1)}.
$ Fix some $P in X_(n-1)$, noting that $P in X_(n)$ as well. Then, we have that $
hash X_n = (hash S_n)/(hash "Stab"_(S_n) (P)), wide hash X_(n-1) =  (hash S_(n-1))/(hash "Stab"_(S_(n-1)) (P)),
$ Since $X_n, X_(n-1)$ are transitive $S_n, S_(n-1)$ sets respectively. Clearly, $"Stab"_(S_(n-1)) (P) subset "Stab"_(S_(n)) (P)$, so $hash "Stab"_(S_(n)) (P) = k dot hash "Stab"_(S_(n-1)) (P)$ for some $k in NN$. This implies then that $
hash X_n = (n dot hash S_(n-1))/(k dot hash "Stab"_(S_(n-1)) (P)) = n/k hash X_(n-1),
$ so in particular, $hash X_n <= n dot hash X_(n-1)$. I claim that $k = 1$, namely that $"Stab"_(S_n) (P) = "Stab"_(S_(n-1)) (P)$. Clearly, we have $"Stab"_(S_n) (P) supset.eq "Stab"_(S_(n-1)) (P)$. Suppose there existed some $sigma in "Stab"_(S_n) (P) minus "Stab"_(S_(n-1)) (P)$; namely, then, $sigma in S_(n) - S_(n-1)$ i.e. $sigma$ doesn't fix $n$. Let $p in P$, then remark that $
sigma^(-1) p sigma (n) &= n <=> p sigma (n) = sigma (n) <=> p "fixes" sigma(n)
$ $sigma(n) eq.not n$ by assumption, so this means that $p$ fixes some non-$n$ element. I claim this is impossible. I claim that $P$ acts upon ${1, dots, n - 1}$ without fixed points. Suppose towards a contradiction that there exists some $x in {1, dots, n-1}$ (wlog, $x = n-1$) such that $p x = x$ for every $p in P$. Then, this implies we can embed $P subset S_(n-2)$. However, $hash P = 2^t$ and $hash S_(n-2) = (hash S_(n))/(n(n-1)) = 2^t m/(n(n-1))$ so $hash P divides.not hash S_(n-2)$ so this is impossible. Hence, $p$ acts upon ${1, dots, n - 1}$ without fixed points, and thus such a $sigma$ cannot exist. We conclude $"Stab"_(S_n) (P) = "Stab"_(S_(n-1)) (P)$ indeed. The proof follows.