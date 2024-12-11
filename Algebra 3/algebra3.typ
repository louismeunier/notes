// ! external
#import "../typst/notes.typ": *
#import "../typst/shortcuts.typ": *

// ! configuration
#show: doc => conf(
  course_code: "MATH456",
  course_title: "Algebra 3",
  subtitle: "Groups; ring theory; fields; modules.",
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
(sum_(g in G) a_g g)(sum_(h in G) b_h h) = sum_(g, h in G) a_g b_h dot g h = sum_(g in G) (sum_(h_1 dot h_2 = h in G) a_(h_1) b_(h_2))g.
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
  Let $R = ZZ$ and $I = (n) = n ZZ = {n a : a in ZZ}$ for some $n in NN$. We claim $(n)$ is prime iff $n$ is prime. If $n$ prime, then if $a b in I$, then $n | a b$. By Gauss's Lemma, then $n$ divides at least one of $a$ or $b$, and hence either $a$ or $b$ in $I$. Conversely, if $n$ not prime, then we may write $n = a b$ where $|a|, |b| < n$. Then, $a dot b in I$, but $n$ divides neither and so $a, b in.not I$.
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


#theorem[Let $FF$ a field and $f(x) in FF[x]$ an irreducible, non-zero polynomial. Then, there is a field $KK supset FF$ such that $KK$ contains a root of $f(x)$]

#proof[
  Let $KK = FF[x]\/(f(x))$. 
  
  1. This is a field, since $(f(x))$ maximal. To see this, suppose otherwise that $(f(x)) subset.neq I subset.neq FF[x]$ for some ideal $I$ of $FF[x]$. Since $FF[x]$ principal, then $I = (g(x))$ for some $g in FF[x]$. Then, $g(x)|f(x)$ by assumption, but by irreducibility $g(x) = 1$, which implies $I = FF[x]$, or $g(x) = lambda dot f(x)$ for some non-zero $lambda in FF$, which implies $I = (f(x))$. In either case, we conclude $(f(x))$ indeed maximal.

  2. $FF arrow.hook KK$ by the map $lambda |-> lambda + (f(x))$.
  3. We can view $f(t) in FF[t] subset KK[t] = (FF[x]\/(f(x)))[t]$; indeed, $f$ gains a root in $KK[t]$. Let $alpha = x + (f(x)) in KK$. $f(t)$, again viewed as an element of $KK[t]$, evaluated at this $alpha in KK$, gives $
  f(alpha) = f(x + (f(x))) = f(x) + (f(x)) = (f(x)) = 0 in KK,
  $ i.e. $alpha$ indeed a root of $f(x)$.
]

#remark[
  In some general $R\/I$ with $f(x) in R[x]$, $
  f(a+I) = f(a) + I
  $ for any coset $a + I in R\/I$. To see this, we have $(a+I)^k = (a+I)(a+I) dots.c (a+I) = a^k + I$; we can expand this for more general polynomials in the same manner.
]

#example[
  Let $R = RR$ and $p(x) = x^2 + 1$. Then, $
  CC = RR[x]\/(x^2 + 1) = {a + b x + (x^2 + 1) : a, b in RR}.
  $ We have that for $x in CC$, $x^2 = -1 mod x^2 + 1$.
]

#example[
  Let $FF = QQ$ and $f(x) = x^2 - 2$. $sqrt(2)$ irrational so $f$ irreducible over $FF[x]$. Then $
  KK = QQ[x] \/ (x^2 - 2) =: QQ[sqrt(2)] = {a + b sqrt(2) : a, b in QQ}.
  $ We can verify this indeed a field; for some arbitrary element $a+b sqrt(2)$, $1/(a + b sqrt(2))$ a naive inverse, which is indeed equal to $(a - b sqrt(2))/(a^2 - 2b^2)$ which one can check indeed in $QQ[sqrt(2)]$.
]

== Finite Fields

#proposition[If $FF$ a finite field, then $hash FF = p^t$ where $p$ a prime number.]

#proof[
  If $R$ is any ring, then there is a unique homomorphism $ZZ -> R$ entirely determined by the necessary $0 |-> 0_R, 1 |-> 1_R$. Then, the map $phi: ZZ -> FF$ can never be injective, since $ZZ$ infinite and $FF$ not. Put $I = ker(phi)$. Then we have an induced injection $overline(phi) : ZZ\/I arrow.hook FF$ by the first isomorphism theorem for rings. We can view then $ZZ\/I$ as a subring of $FF$, and since $FF$ an integral domain so must be $ZZ\/I$ and thus $I$ a prime ideal. Prime ideals in $ZZ$ are necessarily generated by some prime $p$, namely $I = (p)$.

  Then, $FF$ contains the subfield $ZZ\/p ZZ$. We can view $FF$ as a vector space over $ZZ\/p ZZ$, necessarily finite dimensional. Let $t = "dim"(FF)$, the dimension as a vector space. Then, we have $FF tilde.equiv (ZZ\/p ZZ)^t$ as a vector space, and thus the cardinality of $FF$ is $p^t$.
]

#remark[
  One may ask the converse; given $p, t$, is there a field of cardinality $p^t$? If so, how many?

  If we can find $f(x) in ZZ\/p ZZ [x]$ irreducible of degree $t$, then we'd have $FF = ZZ\/p ZZ [x] \/ (f(x))$ a field of cardinality $p^t$.
]

#theorem[For all primes $p$ and integers $t >= 1$, there exists a unique field $KK$ with $hash KK = p^t$.]

= Modules and Vector Spaces

Groups $G$ are to $G$-sets as rings $R$ are to $R$-modules.

== Modules

#definition("Module")[An _$R$-module_ is an abelian group $M$ equipped with a map $R times M -> M$ satisfying, for $lambda in R, m_1, m_2, m in M$:
+ $lambda (m_1 + m_2) = lambda m_1 + lambda m_2$;
+ $lambda (- m) = - lambda m$;
+ $lambda dot 0_M = 0_M$;
(that is, for all fixed $lambda in R$, left-multiplication by $lambda$ $M -> M, m |-> lambda m$ is a group homomorphism from $M$ to itself) and for all $lambda_1, lambda_2 in R, m in M$, 
4. $(lambda_1 + lambda_2) m = lambda_1 m + lambda_2 m$;
5. $(lambda_1 lambda_2 ) m = lambda_1 (lambda_2 m)$;
6. $1_R dot m = m$.
(that is, multiplication $R times M -> M$ defines a ring homomorphism $R -> "End"(M)$)
]

#remark[For an abelian group $M$, $
"End"(M) := {f : M -> M | f "a group homomorphism"}
$ is a _ring_, with pointwise addition $(f+g) (m) := f(m) + g(m)$ and multiplication given by composition $(f compose g) (m) := f(g(m))$.
]

#remark[
  When $R$ a field, we call $M$ a vector space.
]

#definition("Spanning Set")[
  Let $M$ an $R$-module. A set $Sigma subset M$ is called a _spanning set_ if for all $m in M$, there exists $m_1, dots, m_t in Sigma$ and $lambda_1, dots, lambda_t in R$ such that $
  m = lambda_1 m_1 + dots.c + lambda_t m_t.
  $
]

#remark[We do not assume $Sigma$ finite.]

#definition("Linear Dependence")[
  A set $Sigma subset M$ is _linearly independent_ if for all $m_1, dots, m_t in Sigma$ and $lambda_1, dots, lambda_t$, $
  lambda_1 m_1 + dots.c + lambda_t m_t = 0 => lambda_1 = lambda_2 = dots.c = lambda_t = 0.
  $
]

#definition("Basis")[
  A set $Sigma subset M$ is a _basis_ if it is both a spanning set and linearly independent.

  Equivalently, $Sigma$ a basis if every element in $M$ may be written in a unique way with elements in $Sigma$ and scalars in $R$.
]

#theorem[
  If $R = FF$ a field and $V$ a vector space over $FF$, then $V$ has a basis.
]

#proof[
  Let $cal(L)$ be the set of all linearly independent subsets of $V$. Inclusion gives a partial ordering on $cal(L)$ ($W_1 <= W_2$ for $W_1 subset.eq W_2 in cal(L)$). With this order, $(cal(L), <=)$ satisfies the "maximal chain condition"; namely, if $S subset.eq cal(L)$ totally ordered under $<=$, then there exists an element $Sigma in cal(L)$ such that $Sigma supset.eq B$ for every $B in S$. Indeed, simply taking $Sigma = union.big_(B in S) B$ satisfies this condition, remarking that $Sigma in cal(L)$ indeed.

  We appeal now to Zorn's Lemma; since the maximal chain condition holds, there is an element $B$ in $cal(L)$ which is maximal in the sense that  if $B subset.neq B'$, then $B' in.not cal(L)$. We claim $B$ a basis for $V$. By definition, it is linearly independent (being a member of $cal(L)$) so it remains to show $B$ spans.

  Suppose $B$ is not spanning. Then, there exists some $v in V$ such that $v in.not "Span"(B)$. Consider the set $B union {v}$; this set is linearly independent. To see this, suppose we take $v$ and $v_1, dots, v_n in B$, and scalars $lambda_0, lambda_1, dots, lambda_n$ such that $lambda_0 v + dots.c + lambda_n v_n = 0$.

  If $lambda_0 = 0$, then by linear independence of $B$ $lambda_1 = dots.c = lambda_n = 0$.

  Otherwise, if $lambda_0 eq.not 0$, then _since $FF$ a field_, we may invert $lambda_0$ and write $
  v = - lambda_0^(-1) lambda_1 v_1 + dots.c + - lambda_0^(-1) lambda_n v_n => v in "span" (B),
  $ a contradiction. Hence, $B$ indeed spanning, and thus a basis.
]

#example[
  + $V$ is _finitely generated_ if it admits a finite spaning set.
  + Suppose $V = RR$ over $FF = QQ$; this is called the "Hamel basis".
]

#remark[Existence of bases is _not true_ in general for modules over rings; notice in our proof we used the existence of inverses.]

#remark[
  If $M subset R$, then $M$ is an $R$-module if it is an ideal of $R$.
]

#example[
  + Consider $M = ZZ^n$ as a $ZZ$-module; this has a basis, the standard ${e_i : i = 1, dots, n}$ $e_i$ the vector with all zero entries but the $i$th.
  + Consider $M = QQ$ as a $ZZ$-module. Notice that 
    (a) Any two elements in $M$ are linearly  dependent; given $a/b, c/d in QQ$, $
    (c b) (a/b) - (a d)(c/d) = 0.
    $
    (b) Any finite set in $QQ$ does not span $QQ$ over $ZZ$. For instance, if we had $
    S = {(a_1)/(b_1), dots, (a_N)/(b_N)} subset QQ,
    $ then, for instance, $
    1/(b_1 b_2 dots.c b_N + 1) in.not "Span"(S).
    $
    As such, $QQ$ has no basis over $ZZ$.
  + Consider $M = ZZ\/n ZZ$ as a $ZZ$-module, and consider ${1}$. It spans $ZZ\/n ZZ$, but is not linearly independent, since for instance, taking $n in ZZ$, $n dot 1 = n equiv 0$ in $ZZ\/ n ZZ$.
  + If $I$ is an ideal of $R$, $I$ has a basis iff $I$ is principal, $I = (a)$, and $a$ is not a zero divisor. If $a, b in I$, then $b a - a b = 0$ so $a, b$ necessarily linearly dependent.
]

#definition([$R$-module homomorphism])[An _$R$-module homomorphism_ is a map $
f : M_1 -> M_2
$ between two $R$-modules $M_1, M_2$, such that 
+ $f$ a group homomorphism;
+ $f(lambda m) = lambda f (m)$ for every $lambda in R, m in M$.
Define $
ker(f) = {m in M_1 | f(m) = 0}.
$
]

#proposition[$ker(f)$ a subgroup of $M_1$, closed under scalar multiplication. In particular, it is an _$R$-submodule_ of $M_1$.]
#proof[
  The subgroup property comes from the fact that $f$ a group homomorphism. For $lambda in R, m in ker(f)$, $f(lambda m) = lambda f (m) = lambda 0 = 0 => lambda m in ker(f)$.
]

We have in summary the following general properties concerning kernels of homomorphisms in the different categories we've discussed so far:
#align(center, 
  table(
    columns: 3,
    stroke: none,
    [], [kernels], [closure property],
    table.hline(start:0, end:4),
    table.vline(x:1,start:0, end:4),
    "Non-Abelian Groups", "Normal subgroup", [Conjugation by $G$],
    "Rings", "Ideal", [Multiplication by $R$],
    [$R$-modules], [$R$-submodules],[Multiplication by $R$]
  )
)

Just as with groups and rings, we can similarly talk about quotienting modules by submodules.
== Quotients

#definition[
  If $N subset M$ are $R$-modules, then $M\/N$ is an $R$-module with operation defined $
  lambda in R, a + N in M\/N => lambda (a + N) = lambda a + N.
  $
]

#theorem("Isomorphism Theorem")[
  If $f : M_1 -> M_2$ an $R$-module homomorphism, then it induces an injective homomorphism $
  overline(f) : M_1\/"ker"(f) -> M_2, wide a + ker(f) |-> f(a).
  $
]

#proof[
  We just check injectivity. $
  overline(f)(a + ker(f)) = 0 => f(a) = 0 => a in ker(f) => a + ker(f) = 0 in M_1\/ker(f),
  $ i.e. $overline(f)$ has trivial kernel and so is injective.
]

== Free Modules
#definition([Free Module])[An $R$-module $M$ is said to be _free_ if it has a basis.

If $M$ is free with a finite basis $e_1, dots, e_n$, then as a module, $M tilde.equiv R^n$.
]

#theorem[If $M$ is a free $R$-module with a finite basis, then any two bases of $M$ have the same cardinality.]

#proof[
  Let $I$ be a proper maximal ideal of $R$ (which exists by a similar argument to the existence of a basis of a vector space, i.e. via Zorn's Lemma argument). Let $F = R\/I$; this is a field by maximality. Let $
  I M := "span"{lambda m : lambda in I, m in M}.
  $ $I M$ is an $R$-submodule of $M$. Consider $M \/ I M$; this is an $R$-module as well, but is in fact actually an $F$-vector space, since $I$ acts as 0 on $M\/ I M$. That is, for $lambda in R$, $
  (lambda + I) (m + I M) = lambda m + I M.
  $ If $M$ has a basis of size $n$, $M tilde.equiv R^n$. Then, $
  M \/ I M tilde.equiv F^n
  $ as an $F$-vector space. Then, supposing $M$ has bases ${e_1, dots, e_n}, {f_1, dots, f_m}$ are two bases of $M$, then we have that $
  M tilde.equiv R^n tilde.equiv R^m
  $ and so $
  M\/ I M tilde.equiv F^n tilde.equiv F^m
  $ as $F$-vector spaces, but by the same theorem for specifically vector spaces, it must be that $n = m$.
]

#definition("Rank")[
  If $M$ is free, the cardinality of a basis is called the _rank_ of $M$ over $R$.
]

#remark[
  If $M, N$ are free over $R$, then $M\/N$ need not be free.

  For instance, taking $M = ZZ, N = m ZZ$, for some $m$, both are free (generated by $1, m$ resp.), but $M\/N = ZZ\/n ZZ$ is not free, as any element is linearly dependent.

  However, if $R = F$ a field and $W subset V$ are $F$-vector spaces, then $V\/W$ a vector space, and moreover $dim (V) = dim (W) + dim (V\/W)$:
]

#theorem[
  $dim (V) = dim (W) + dim (V\/W)$, where $V supset W$ are vector spaces over a field $F$.
]

#proof[
  Let $m := dim (W), n := dim (V)$. Let ${v_1, dots, v_m}$ a basis for $W$. We complete this to a basis ${v_1, dots, v_m, v_(m+1), dots, v_n}$ for $V$ (note that this is a procedure we _cannot_ do, in general, for modules). We claim that $
  {v_(m+1) + W, dots, v_n + W}
  $ defines a basis for $V\/W$.

  - Spanning: given $v + W in V\/W$, $v = lambda_1 v_1 + dots + lambda_n v_n$ so $v + W = lambda_(m+1) (v_(m+1) + W) + dots.c + lambda_n (v_n + W)$.
  - Linear independence: suppose $lambda_(m+1), dots, lambda_n in F$ are such that $lambda_(m+1) (v_(m+1) + W) + dots.c + lambda_n (v_n + W) = 0$. We may rewrite as $
  (lambda_(m+1) v_(m+1) + dots.c + lambda_n v_n) + W = 0,
  $ so there exist $lambda_1, dots, lambda_m in F$ such that $
  lambda_(m+1) v_(m+1) + dots.c + lambda_n v_n = - lambda_1 v_1 - dots.c - lambda_m v_m,
  $ which gives a linear combination of our original basis vectors, hence is only possible if $lambda_1 = dots.c = lambda_n = 0$, and independence follows.

  Hence, indeed our basis is a basis for $V\/W$ and so $dim (V\/W) = n - m = dim(V) - dim(W)$.
]

=== Changing Bases
Given a basis $B = (m_1, dots, m_n)$ of an $R$-module $M$, we have a natural isomorphism
$
R^n ->^(phi_B) M, wide vec(lambda_1, dots.v, lambda_n) |-> B dot vec(lambda_1, dots.v, lambda_n) = lambda_1 m_1 + dots.c + lambda_n m_n.
$ Namely, such an isomorphism is dependent on $B$. Given another basis $B' = (m'_1 , dots, m'_n)$, then there exists some invertible matrix $P in "GL"_n (R)$ such that $
B' = B P, wide (m'_1, dots, m'_n) = (m_1, dots, m_n) P
$ thinking of $B, B'$ as vectors, where the $j$th column of $P$ is the coordintes of $m'_j$ relative to $B$.

=== Homomorphisms Between Free Modules

#definition("Free Module Homomorphism")[
A map $
T : M_1 -> M_2
$ between two free $R$-modules of rank $n, m$ respectively is a _free module homomorphism_ if $T$ a group homomorphism and is $R$-linear, i.e. $
T(lambda m) = lambda T(m)
$ for every $lambda in R$, $m in M$.
]

#definition("Matrix Representation of Module Homomorphism")[
  If $B_1 = (e_1, dots, e_n)$ and $B_2 = (f_1, dots, f_m)$ bases for $M_1, M_2$ resp., and $T : M_1 -> M_2$ a free module homomorphism, then let $
  M_(T, B_1, B_2) in M_(m times n) (R)\
  M_(T, B_1, B_2)^((j)) := j"-th column of" M_(T, B_1, B_2) = "coordinates of " T(e_j) "relative to" B_2 =: [T(e_j)]_(B_2).
  $
In other words, the following diagram commutes:
#align(center)[#commutative-diagram(
  node((0, 0), $M_1$),
  node((0, 1), $M_2$),
  node((1, 0), $R^n$),
  node((1, 1), $R^m$),
  arr($M_1$, $M_2$, $T$),
  arr($R^n$, $M_1$, $phi_B_1$),
  arr($R^m$, $M_2$, $phi_B_2$, label-pos: right),
  arr($R^n$, $M_1$, $≀$, label-pos: right),
  arr($R^m$, $M_2$, $≀$, label-pos: left),
  arr($R^n$, $R^m$, $\ \ \ M_(T, B_1, B_2)$, label-pos: "below"),
  // arr("quot", (0, 1), $tilde(phi)$, label-pos: right, "dashed"),
  // arr($R$, "quot", $pi$),
)]
i.e., $M_(T, B_1, B_2) = phi_B_2^(-1) compose T compose phi_(B_1)$.
]

#proposition[
Suppose $M_1 = M_2 =: M$, and $B_1 = B_2 =: B$, i.e. $T$ a homomorphism from $M$ to itself. Consider $M_(T, B) := M_(T, B, B) in M_n (R)$. Given another basis $B'$, then $M_(T, B), M_(T, B')$ are conjugate, namely there exists some $P in "GL"_n (R)$ such that $
M_(T, B) = P M_(T, B') P^(-1).
$
]

#proof[
  Let $P$ be such that $B' = B P$. Then for $vec(x_1, dots.v, x_n) in R^n$, $
  phi_(B') (vec(x_1, dots.v, x_n)) = B' dot vec(x_1, dots.v, x_n) =  B P vec(x_1, dots.v, x_n) = (phi_B compose P) (vec(x_1, dots.v, x_n)),
  $  i.e. $phi_(B') = phi_B compose P$. We have too $M_(T, B) = phi_B^(-1) T phi_B, M_(T, B') = phi_B'^(-1) T phi_B'$, so in particular $
  M_(T, B') = phi_B'^(-1) T phi_B' = P^(-1) (phi_(B)^(-1) compose T compose phi_B) P = P^(-1) M_(T, B) P,
  $ so indeed, $
  M_(T, B) = P M_(T, B') P^(-1).
  $
]

=== Matrices Up To Conjugation
Given $M, M' in "M"_n (R)$, we'd like to be able to tell when two matrices are conjugate. In particular, we'd like to study $"M"_n (R)$ (which is a free $R$-module of rank $n^2$), modulo conjugation. Namely, we can view $"GL"_n (R)$ acting naturally on $"M"_n (R)$ by conjugation, and we'd like to study the orbits of this action, namely the set $
"M"_n (R)\/ "GL"_n (R).
$
Suppose for now $R = F$ a field. Given $M in M_n (F)$, consider an "evaluation" homomorphism $
"ev"_M : F[x] -> M_n (F), &wide f(x) |-> f(M), \
f(x) := a_n x^n + dots.c + a_1 x + a_0 &|-> a_n M^n + dots.c + a_1 M + a_0 I_n =: f(M).
$

#proposition[
  $"ev"_M$ is a homomorphism from $F[x]$ to $M_n (F)$.
]

$"ev"_M$ is not injective; notice that $F[x], M_n (F)$ are both vector spaces over $F$, but $"dim"_F (F[x]) = infinity$ (we actually have an explicit basis $B = {1, x, x^2, dots}$) and $"dim"_F (M_n (F)) = n^2$ (with basis ${E_(i, j) :1 <= i, j <= n}$). Hence, $ker("ev"_M)$ is an infinite-dimensional ideal of $F[x]$. $F[x]$ a principal ideal domain, so it must be that $
ker("ev"_M) = (p_M (x)),
$ for some $p_M (x) in F[x]$; let us require that $p_M (x)$ monic, namely the coefficient of its highest power is $1$. We can always do this, and in particular makes the generator $p_M$ unique.
// TODO why vector space?

#definition("Minimal Polynomial")[
  $p_M (x)$ is called the _minimal polynomial_ of $M$.
]

#proposition[
  $p_M (M) = 0$. In particular, if $f(M) = 0$ for some other $f in F[x]$, then $p_M|f$.
]
#proof[This follows from the fact that $p_M$ is a generator for the kernel of $"ev"_M$.]

#proposition[Let $T : F^n -> F^n$ be a linear map, $B$ a basis for $F^n$ and $M = [T]_B in M_n (F)$. Then, for any $A in "GL"_n (F)$, then $
p_(A M A^(-1)) = p_M,
$ namely, the minimal polynomial of a linear transformation is independent of the choice of basis used to represent it as a matrix; namely $p_T$, the _minimal polynomial of $T$_, is well-defined.
]

#proof[
  If $f in F[x]$, then notice that since $
  (A M A^(-1))^k = A M^k A^(-1),
  $ and in addition, since conjugation by $A$ linear (namely $A (M_1 + M_2)A^(-1) = A M_1 A^(-1) + A M_2 A^(-1)$), the map $M |-> A M A^(-1)$ is an automorphism of $M_n (F)$. So, in particular we have that $
  f(A M A^(-1)) = A f(M) A^(-1),
  $ so the following commutes,
  #align(center)[#commutative-diagram(
  node((0, 0), $F[x]$),
  node((0, 1), $M_n (F) \ $),
  // node((1, 0), $R^n$),
  arr($F[x]$, $M_n (F) \ $, $"ev"_M$),
  node((1, 1), $M_n (F)$),
  arr($F[x]$, $M_n (F)$, $"ev"_(A M A^(-1))$),
  arr($M_n (F) \ $, $M_n (F)$, $P |-> A P A^(-1)$),
  // arr($F[x]$, $M_n (F)$, $"ev"_M$),
  // arr($R^n$, $M_1$, $phi_B_1$),
  // arr($R^m$, $M_2$, $phi_B_2$, label-pos: right),
  // arr($R^n$, $M_1$, $≀$, label-pos: right),
  // arr($R^m$, $M_2$, $≀$, label-pos: left),
  // arr($R^n$, $R^m$, $\ \ \ M_(T, B_1, B_2)$, label-pos: "below"),
  // arr("quot", (0, 1), $tilde(phi)$, label-pos: right, "dashed"),
  // arr($R$, "quot", $pi$),
)] i.e. $ker("ev"_M) = ker("ev"_(A M A^(-1)))$, and thus have the same generators.
]

#definition("Minimal Polynomial of a Transform")[The minimal polynomial $p$ of $T$ is the unique monic polynomial over $F$ satisfying 
+ $p(T) = 0$; and
+ if $f(T) = 0$ then $p | f$.
]

More abstractly, we may consider, basis-free, the evaluation homomorphism $
"ev"_T : F[x] -> "End"_F (V), wide f(x) |-> f(T),
$ where $"End"_F (V)$ the ring of endomorpisms of $V$ as a $F$-vector space. We can then equivalently define the minimal polynomial as that which generates $ker("ev"_T)$.

Note that $
"deg" p_T = "smallest non-zero linear combination of" I, T, T^2, T^3, dots.
$ Hence, in particular since $
dim_F "End"_F (V) = n^2,
$ then certainly $
"deg" p_T <= n^2,
$ since if it were any more, then some power of $T$ would be linearly dependent on another. However, we can bound this further; indeed, we clam that the map $"ev"_T$ is never surjective (if $n > 1$).

To see this, note that by the isomorphism theorem, $
im("ev"_T) tilde.equiv F[x]\/ (p_T (x)).
$ But notice that $F[x]\/(p_T (x))$ is a commutative ring, while $"End"_F (V)$ is not. Hence, it certainly can't be that $im("ev"_T)$ equals the whole $"End"_F (V)$. What is it?

#theorem[
  $deg(p_T (x)) <= n$
]<thm:degpt>

#proof[(A first proof) Recall that $f_T (x) := det(x I - T)$, the characteristic polynomial of $T$, has degree $n$. By the Cayley-Hamilton theorem, $f_T (T) = 0$, and thus $p_T | f_T$ and so $"deg" p_T <= n$.
]

#example[
  Let $T in "GL"_3 (FF_2)$ of order $7$. What is the minimal polynomial of $T$?

  We know $T^7 - 1 = 0$, so $
  p_T | f(x) = (x+1)(x^3+x^2+1)(x^3+x+1).
  $ These resulting polynomials on the RHS are irreducible, hence we know $p_T$ to be some combination of these.

  Claim: $deg p_T <= 3$
  - $p_T (1) eq.not 0$. If it were, then $T$ has 1 as an eigenvalue, i.e. $exists v$ such that $T v = v$. Hence, $T in "Stab"_("GL"_3 (FF_2)) (v)$, but $hash "Stab"_("GL"_3 (FF_2)) (v) = 168/7 = 24$, and $7 divides.not 24$ so this is impossible. It follows that $x+1$ not a factor of $p_T$.

  - For any $v eq.not 0$, $v, T(v), T^2 (v)$ are linearly independent, hence are a basis for $V$. Suppose otherwise, that there exists $a_0, a_1, a_2 in FF_2$ such that $a_0 v + a_1 T(v) + a_2 T^2 (v) = 0$. Then, letting $f(x) = a_2 x^2 + a_1 x + a_0$, we equivalently claim that $f(T)(v) = 0$.\
  But we know that $gcd(f, p_T) = 1$ since $f$ irreducible. By the lemma below, $f(T)$ invertible, but this contradicts the fact that there is some $v$ such that $f(T)(v) = 0$, i.e. $f(T)$ has nontrivial kernel. We conclude that indeed ${v, T(v), T^2 (v)}$ linearly independent.

  In short, then, we have that every vector $v$ is a _cyclic vector_ for $T$, namely ${v, T v, T^2 v}$ is a basis for $V$. In particular, there is some $f(x) = x^3 + a_2 x^2 + a_1 x + a_0 in FF_2[x]$ such that $f(T)(v) = 0$ i.e. $a_0 v + a_1 T(v) + a_2 T^2 (v) + T^3 (v) = 0$. We claim $f(T) equiv 0$. Indeed, we have that $
  0 = T compose f(T) (v) = f(T)(T v) = 0 => T v in ker(f(T)),
  $ and similarly $T^2 v in ker(f(T))$, hence $ker(f(T)) = V$, namely, $f(T)(w) = 0$ for every $w in V$. Hence, $
  f(T) = 0,
  $ so we conclude indeed that $p_T$ indeed of degree at most 3.

  So, $p_T$ is one of $x^3 + x^2 + 1$ or $x^3 + x + 1$; it could be either, for general $T$.

  Indeed, there are 2 conjugacy classes in $"GL"_3 (FF_2)$ of order $7$, with the minimal polynomial of those in one conjugacy class $x^3 + x^2 + 1$, the other $x^3 + x + 1$.
]

#lemma[If $gcd(f, p_T) = 1$, then $f$ is invertible.]

#proof[
Appealing to the euclidean algorithm, there exist $a, b in FF[x]$ such that $1 = a f + b p_T$. Evaluating on $T$, we find $
I = a(T) f(T) + cancel(b(T) p_T (T)) => I = a(T) f(T) => a(T) = (f(T))^(-1).
$
]

#proof[(A second proof of @thm:degpt)
If $V$ has a cyclic vector $v$ for $T$, then we are done, since then $
{v, T v, dots, T^(n-1) v}
$ a basis for $V$, and so there is some $f(x) in FF[x]$ of degree $n$ such that $
f(T)(v) = 0 => f(T)(T^k v) = T^k f(T)(v) = T^k (0) = 0,
$ i.e. $f(T) equiv 0$, and thus $p_T | f$ and $deg p_T <= deg f = n$.

Otherwise, we proceed by induction on $dim V$. We prove the statement $
P_n: "if" T in "End"(V) "with" dim "End"(V) = n, "then" deg p_T <= n.
$ Suppose The case for $P_(n-1)$ and let $V$ be of dimension $n$. Let $v in V - {0}$, and let $
W = "span"{v, T v, T^2 v, dots}.
$ If $v$ was cyclic, we are in the previous case and we are done, hence assume $W subset.neq V$. Remark $W$ a $T$-stable subspace; $T$ maps vectors in $W$ to vectors in $W$. Let $T_W : W -> W$ denote the restriction of $T$ to $W$. This induces a linear transformation $
overline(T) : V \/ W -> V\/W, wide v + W |-> T v + W,
$ which is well defined, since if $v_1 + W = v_2 + W$, then $v_1, v_2$ differ by something in $W$, i.e. $v_1 - v_2 in W$ so $T(v_1 - v_2) in W$ as well since $W$ stable under $T$. It follows that $T(v_1) - T(v_2) in W$.

We know that $deg p_T_W <= dim W$ and likewise $deg p_overline(T) <= dim (V \/ W)$ by the induction hypothesis. We claim $p_T_W p_(overline(T))$ vanishes on $T$, namely $p_T | p_T_W p_(overline(T))$.

Note that $p_overline(T) (T)$ maps $V$ to $W$, and $p_T_W (T)$ maps $W$ to zero. Hence, $
p_(T_W) (T) compose p_overline(T) (T) = 0,
$ and so indeed $p_T_W p_(overline(T))$ vanishes on $T$ and so a multiple of $p_T$.

So, it follows that $deg p_T <= deg p_(T_W) + deg p_overline(T)$; by the induction hypothesis, $deg p_T_W <= dim W$ and $deg p_T <= dim V\/W$ and thus $deg p_T <= dim W + dim V\/W = dim V$, as we aimed to show.
// We have that $
// p_(overline(T)) (overline(T)) = 0 &=> p_(overline(T)) (overline(T)) (v + W) = 0\
// &=>  p_overline(T) (T)(v) + W = 0\
// &=>p_overline(T) (T)(v) in W,
// $ for any $v in W$.
]

#lemma[
  If $T : V -> V$ a linear transformation and $W$ a $T$-stable subspace, then $T$ induces $
  overline(T) : V\/W -> V\/W, wide v + W |-> T(v) + W.
  $
]

#remark[
  It is _not_ always true that $W$ has a $T$-stable complement.

  For instance let $V = F^2$ and $T(vec(1,0))= vec(1,0), T(vec(0,1)) = vec(1,1)$, i.e. $T = mat(1,1;0,1)$. Then, $W = F vec(1,0)$ is stable, and $W' = F vec(lambda, 1)$ is complementary. But notice $T vec(lambda, 1) = vec(lambda + 1, 1) in.not W'$, for any $lambda$, hence $W'$ not $T$-stable.
]

=== Zeros of the Minimal Polynomial


#definition("Eigenvalue")[
  $lambda$ is an _eigenvalue_ of $T$ if there is a non-zero vector $v in V$ with the property $T v = lambda v$.
]

#theorem[If $p_T (lambda) = 0$ for some $lambda in F$, then $lambda$ an eigenvalue of $T$.
]
#proof[
  $p_T (lambda) = 0$ hence $p_T (x) = (x - lambda) q(x)$ for some polynomial $q$ of one degree smaller than $p_T$. Then, $
  0 = p_T (T) &= (T - lambda I) compose q(T).
  $ Note that $q(T) eq.not 0$, by assumption of minimality of $p_T$. Hence, we have in particular that $im (q(T))$ contained in $ker(T - lambda I)$. Let $v in im (q(T))$ non-zero. Then, $(T - lambda I) v = 0 => T v = lambda v$.
]

The converse holds as well:

#theorem[
  If $lambda$ is an eigenvalue of $T$, then $p_T (lambda) = 0$.
]

#proof[
  Let $v$ be such that $T v = lambda v$. Let $g(x)$ be any polynomial in $F[x]$. Then, $g(T) (v) = g(lambda) v$, namely, $g(lambda)$ an eigenvalue of $g(T)$ with vector $v$. Specify $g$ to be $p_T$. Then, $
  0 = p_T (T) (v) = p_T (lambda) v.
  $ but $v eq.not 0$ hence $p_T (lambda) = 0$ as desired.
]

== The Primary Decomposition Theorem

#theorem("Primary Decomposition")[
  Let $T : V -> V$ a linear transformation on a vector space $V$ over a field $F$. Suppose $p_T (x) = p_1 (x) p_2 (x)$ with $gcd(p_1, p_2) = 1$. Then, there exists unique subspaces $V_1, V_2 subset.eq V$ such that 
  1. $V = V_1 plus.circle V_2$
  2. $V_j$ is stable under $T$, and the minimal minimal polynomial of $T_j := T|_(V_j)$ is $p_j (x)$.
]<thm:primarydecomp>

#example[
  If $T$ idempotent i.e. $T^2 = T$, then $p_T (x) = x^2 - x = x(x-1)$, $p_1 (x) = x$, $p_2 (x) = x - 1$. Then, $V_1 = ker(T), V_2 = im(T)$; on $V_1$, $T$ acts as $0$, on $V_2$, $T$ acts as the identity.
]

#proposition("Chinese Remainder Theorem")[
$
F[x]\/(p_T (x)) tilde.equiv F[x]\/(p_1(x)) times  F[x]\/(p_2(x)).
$
]
#proof[
  Consider $phi: F[x] -> F[x]\/(p_1(x)) times  F[x]\/(p_2(x))$ given by $f(x) |-> (f(x)+(p_1 (x)), f(x)+(p_2 (x)))$. This has kernel $
  ker(phi)= {f : p_1|f, p_2|f} = {f : p_1 p_2|f} = {f : p_T|f} = (p_T (x)),
  $ since $p_1, p_2$ relatively prime. Hence, we have an induced injection $
  overline(phi) : F[x]\/(p_T(x)) arrow.hook F[x]\/(p_1 (x)) times F[x]\/(p_2 (x)).
  $ Moreover, as a vector space $
  dim F[x]\/(p_T (x)) = deg(p_T (x)), wide dim (F[x]\/(p_1 (x)) times F[x]\/(p_2 (x))) = deg(p_1 (x))+ deg(p_2 (x)),
  $ // TODO why is this sufficient?
  and since $deg(p_T) = deg(p_1) +deg(p_1)$, the dimensions of both sides agree. Hence, the map $overline(phi)$ also surjective and thus the isomorphism we sought.
]

#remark[
  Given $R_1, R_2$ rings, $R_1 times R_2$ a ring. If $M_1, M_2$ are modules over $R_1, R_2$, then $M_1 times M_2$ is an $(R_1 times R_2)$-module by the action $(lambda_1, lambda_2) (m_1, m_2) = (lambda_1 m_1, lambda_2 m_2)$.
]

#theorem[If $M$ is any module over $R_1 times R_2$, then there are $R_j$-modules $M_j$, $j = 1, 2$, such that $M tilde.equiv M_1 times M_2$.]

#proof[
  Consider $i_1 : R_1 -> R_1 times R_2, a |-> (a, 0)$. This is _not_ a ring homomorphism ($1 arrow.not 1$), but does include $R_1 subset R_2$ as an ideal in $R_1 times R_2$. Define $M_1 = (1, 0) M, M_2 = (0, 1) M$. We claim $M = M_1 times M_2$.

  Given $m in M$, $m = (1, 1)m = (1, 0)m + (0, 1)m$. Putting $m_1 := (1, 0) m, m_2 := (0, 1)m$ gives $m = m_1 + m_2$ with $m_1, m_2 in M_1, M_2$ resp, hence $M_1 times M_2$ spans $M$.

  We now wish to show $M_1 sect M_2 = {0}$. Let $m in M_1 sect M_2$. Then, $m = (1,0) m_1 = (0, 1)m_2$. Multiplying both sides by $(1, 0)$ gives that $m = (1, 0) m_1 = 0$, and the claim follows.
]

#proof[(Of @thm:primarydecomp) If $p_T (x) = p_1 (x) p_2 (x)$ as given, notice $V$ is a module over $F[x]\/(p_T (x)) = F[x]\/(p_1 (x)) times F[x]\/(p_2 (x))$. By the previous theorem, then, $V = V_1 plus.circle V_2$, where $V_1$ a $F[x]\/(p_1 (x))$-module, $V_2$ a $F[x]\/(p_2 (x))$-module. On $V_i$, $p_i (T) = 0$.
]

#theorem("PDT 2")[
  If $p_T (x) = p_1 (x)^(e_1) dots.c p_t (x)^(e_t)$ where $p_1, dots, p_t$ irreducible, then $
  V = V_1 plus.circle dots.c plus.circle V_t,
  $ where $
    p_T|_(V_j) = p_j (x)^(e_j)
  $ for each $j = 1, dots, t$.
]
#theorem("PDT 3")[
  Suppose $F$ is algebraically closed, so $
  p_T (x) = (x - lambda_1)^(e_1) dots.c (x-lambda_t)^(e_t),
  $ then $
  V = V_1 plus.circle dots.c plus.circle V_t,
  $ where $
  p_T|_(V_j) = (x - lambda_j)^(e_j).
  $ If $e_1 = dots.c = e_t = 1$, then $T|_(V_j) = $ multiplication by $lambda_j$, so in particular $V_j$ the eigenspace for $lambda_j$ and $T$ diagonalizable.
]

#corollary[
  If $p_T (x) = (x - lambda_1) dots.c (x - lambda_t)$ where $lambda_1, dots, lambda_t$ distinct, then $T$ is diagonalizable.
]
#remark[
  More concretely, we may construct $
  V_i := ker(p_(i)).
  $ Notice $V_i$ $T$-stable. Since $gcd(p_1, p_2) = 1$, we have find $a, b in F[x]$ such that $
  1 = a p_1 + b p_2.
  $ Evaluating on $T$, we find $
  I = a(T) p_1 (T) + b(T) p_2 (T)
  $ and evaluating further on some arbitrary $v in V$, we find $
  v  =  underbrace(a(T) p_1 (T)(v), in V_2) + underbrace(b(T) p_2 (T) (v), in V_1),
  $ i.e. $V_1 union V_2 = V$ indeed. Moreover, suppose $v in V_1 sect V_2$. Then, $a(T)p_1 (T)(v) = 0$ _and_ $b(T)p_2(T)(v) = 0$, hence $v = 0$ itself. We conclude $V_1 sect V_2 = {0}$ as desired.
]

#corollary[
  If $F$ algebraically closed, then $V$ is a direct sum of generalized eigenspaces, $
  V = V_1 plus.circle dots.c plus.circle V_t,
  $ where $V_j = ker((T - lambda_j)^(e_j))$ for some $lambda_j in F, e_j >= 1$.
]

#definition("Generalized Eigenspace")[
  Given $T : V -> V$, $lambda in F$, the eigenspace of $T$ attached to $lambda$ is $
  V_lambda := {v in V : T v = lambda v} = ker(T - lambda).
  $ The _generalized eigenspace_ attached to $lambda$ is $
  V_((lambda)) := {v in V : (T - lambda)^m (v) = 0 "some" m >= 1} = union.big_(m>=1) ker((T - lambda)^m).
  $
]

#theorem("Jordan Canonical Form")[
  There is a basis for $V_((lambda))$ for which the matrix of $T$ is of the form $
  mat(
      J_(1, lambda), 0, 0, 0;
      0, J_(2, lambda), 0, 0;
      0, 0, dots.down, 0;
      0, 0, 0, J_(m, lambda) 
  ),
  $ where $
  J_(1, lambda) = mat(lambda, 1, 0, 0, 0; 0, lambda, 1, 0, 0; 0, 0, dots.down, 1,0 ; 0, 0,0, lambda, 1; 0, 0, 0,0, lambda),
  $ a $d_1 times d_1$ matrix with diagonals $lambda$ and upper-diagonal $1$'s, and $d_1 + d_2 + dots + d_m = dim (V_((lambda)))$.
]

== Modules over Principal Ideal Domains

#definition("Finitely Generated")[
A module $M$ over a ring $R$ is _finitely generated_ if it has a finite spanning set.
]

#theorem[
Let $M$ be a finitely generated module over a PID $R$. Then, there exists elements $a_1|a_2|dots.c|a_t$ and an integer $m >= 0$ such that $
M tilde.equiv R\/(a_1) plus.circle R\/(a_2) plus.circle dots.c plus.circle R\/(a_t) plus.circle R^m.
$ $a_1, dots, a_t$ are called the _elementary divisors_ of $M$, and $m$ is called the _rank_ of $M$ over $R$.
]<thm:moduletheorem>

#remark[
  $M$ free $<=>$ $t = 0$.
]

#remark[
  If $G$ is a finitely-generated abelian group, then $
  G tilde.equiv ZZ\/n_1 plus.circle dots.c plus.circle ZZ\/n_t plus.circle ZZ^m.
  $ $G$ finite $<=>$ $m = 0$.
]

#remark[
  If $V$ a generalized eigenspace for $T$ with eigenvalue $lambda$, then $
  V = F[x]\/((x-lambda)^(n_1)) plus.circle dots.c plus.circle F[x]\/((x-lambda)^(n_t)) plus.circle F[x]^m,
  $ where actually $m = 0$ (since $V$ finite dimensional) and $n_1 <= n_2 <= dots.c <= n_t$.
]

#theorem[
If $M$ a finitely generated $R$-module, then it is a quotient of a free $R$-module.
]

#proof[
  Let $m_1, dots, m_t$ be a system of $R$-module generators for $M$. Then consider $
  phi: R^t -> M, wide (lambda_1, dots, lambda_t) |-> lambda_1 m_1 + dots.c + lambda_t m_t.
  $ Since $m_1, dots, m_t$ generate $M$, this is a surjective module homomorphism. This gives $
  M tilde.equiv R^t\/(ker(phi)).
  $
]

#definition([Cyclic $R$-module])[
  An $R$-module is said to be _cyclic_ if it is isomorphic to $R\/I$ for some ideal $I subset R$. In particular, $R$ is cyclic if it can be generated by a single element, namely $1+I$.
]


#proposition[If $N$ an $R$-submodule of a free $R$-module of rank $n$, then $N$ is also free, of rank $<= n$.]
  #proof[
    We prove by induction on $n$. If $n = 1$ and $N subset.eq R$ an $R$-submodule, then in particular $N$ is an ideal. Since $R$ a PID, there is some $a in R$ such that $N = (a)$. If $a$ is zero, then $N$ is the zero module so free. Else, consider the map $R -> N$, $lambda |-> lambda a$. It is clearly surjective, and its kernel is trivial because $a$ is not a zero divisor.\
    Suppose the case for $n$ and take $N subset.eq R^(n+1)$. Consider the $R$-module homomorphism $phi : R^(n+1) -> R$, $(lambda_1, dots, lambda_(n+1)) |-> lambda_(n+1)$. $phi(N)$ is an ideal of $R$ so $phi(N) = (a)$ for some $a in R$. Let $m_(n+1) in N$ be such that $phi(m_(n+1)) = a$. Consider $N sect ker(phi)$. The kernel is given by all elements of the form $(lambda_1, dots, lambda_n, 0)$ for $lambda_i in R$, which is isomorphic to $R^n$.\
    If $a = 0$, then $N subset ker(phi) tilde.equiv R^n$, so we may directly apply the inductive hypothesis and find that $N$ is free of rank $<= n < n+1$.\
    Else if $a eq.not 0$, then by the induction hypothesis, we know that $N sect ker(phi)$ is free of rank $<= n$, being a submodule of $R^n$. On the other hand, we claim $N tilde.equiv (N sect ker(phi)) plus.circle R $. Consider the map $
    eta : (N sect ker(phi)) plus.circle R -> N, wide (n_0, lambda) |-> n_0 + lambda m_(n+1).
    $ Given $n in N$, note that $phi(n) in (a)$ hence there is some $lambda in R$ such that $phi(n) = lambda a$. Then, taking $n_0 := n - lambda m_(n+1) in ker(phi)$, and so $
    eta(n_0, lambda) = n_0 + lambda m_(n+1) = n,
    $ so $eta$ surjective. For injectivity, suppose $phi(n_0, lambda) = 0 => n_0 + lambda m_(n+1) = 0$. Applying $phi$ to both sides, we find $phi(n_0) + lambda phi(m_(n+1)) = 0$. $n_0 in ker(phi)$, so we find $lambda a  = 0$, but $a eq.not 0$ hence $lambda = 0$. It follows that $n_0 = 0$, and thus $(n_0, lambda) = (0, 0)$.\
    So, we find that $N tilde.equiv N_0 plus.circle R$, where $N_0 subset.eq R^n$. Applying the inductive hypothesis to $N_0$, we find $N_0$ free of rank $m <= n$, ie $N_0 tilde.equiv R^m$, and thus $N tilde.equiv R^(m+1)$ of rank $m+1<= n + 1$, completing the proof.
  ]

// #proposition("Diagonlization")[
//   There exists a basis $e_1, dots, e_n$ of $R^n$ such that $d_1 e_1, dots, d_m e_m$ is a basis for $N$, such that $d_1|d_2|dots.c|d_m$.
// ]
We now have a fairly simple representation of our module as $R^n \/ R^m$. To ultimately obtain the proof we seek, we wish to simplify the structure of $R^m$ even further. We approach this by considering the image of our module under invertible matrices.

// #proof[
Let $e_1, dots, e_n$ be a basis of $R^n$.
  Let $v_1, dots, v_m$ a basis for $N$, where $
v_i = vec(a_(1 i), dots.v, a_(n i)), wide i = 1, dots, m,
$ and let $v_(j) = 0$ for $j = m+1, dots, n$, and so consider the matrix with columns $v_i$, $A = (a_(i j))_(1<=i,j<=n) in M_n (R)$. Then, our finitely generated $R$-module $Omega = R^n \/ A R^n$. We have the following:
+ If $Q in "GL"_n (R)$, then $R^n\/ A Q^(-1) R^n = R^n \/ A R^n$, since $Q^(-1)$ induces an isomorphism on $R^n$, hence $Q^(-1) R^n = R^n$.
+ If $P in "GL"_n (R)$, then $R^n\/ P A R^n tilde.equiv R^n\/A R^n$, by considering the map $R^n\/ A R^n -> P R^n \/ P A R^n = R^n\/ P A R^n, v |-> P v$.
In short, we have an action $"GL"_n (R) times "GL"_n (R)$ acting on $X = M_n (R)$ by $(P, Q) (A) = P A Q^(-1)$.

We claim, then, that for any $A in M_n (R)$, the orbit of $A$ contains a diagonal matrix with entries $d_1|d_2|dots.c|d_n$, where the $d_i$'s may be 0.

We wish to study $"GL"_n (R)\\M_n (R)\/"GL"_n (R)$, that is, the orbits of $M_n (R)$ under this action. This is difficult, so we instead consider the restricted orbits $"SL"_n (R)\\M_n (R)\/"SL"_n (R)$.
// We consider the more restricted action $"SL"_n (R)$
//   Let $e_1, dots, e_n$ be a basis of $R^n$ and $f_1, dots, f_m$ an $R$-basis for $N$, with $
//     f_1 = a_(1 1 ) e_1 + dots.c + a_(n 1) e_n,\
//     f_2 = a_(1 2) e_1 + dots.c + a_(n 2) e_n, \
//     dots.down\
//     f_m = a_(1 m) e_1 + dots.c + a_(n m) e_m.
//   $ I.e. $
//   M\/N tilde.equiv R^n\/im(underbrace(mat(a_(1 1), a_(1 2), dots.c, a_(1 m); a_(2 1), a_(2 2), dots.c, a_(2 m); dots.v, dots.v, dots.down, dots.v; a_(n 1), a_(n 2), dots.c, a_(n m)), =: A)).
//   $ Remark that:
//   - If $P in "GL"_(n) (R)$, then $R^n\/im(A) = R^n \/im(P A)$;
//   - If $Q in "GL"_m (R)$, then $R^n\/im(A) = R^n\/im(A Q^(-1))$.
//   In other words, $"GL"_n (RR) times "GL"_m (R)$ acts on $"Mat"_(n times m) (R)$ by the rule, $
//   (P, Q)(X) = P X Q^(-1).
//   $ We claim that every orbit of this action contains a diagonal matrix. 
// // ]
// ]

#theorem[Let $M = R^n$ and let $N subset.eq M$ a (free) $R$-submodule. Then, there exists a basis for $M$ $m_1, dots, m_n$ such that $N$ is spanned by $d_1 m_1, d_2 m_2, dots, d_n m_n$ with $d_1|d_2|dots.c|d_n$.]

#remark[If $v = lambda_1 m_1 + dots.c + lambda_n m_n in M$, then $v in N <=> d_1|lambda_1, d_2|lambda_2, dots, d_n|lambda_n$. Hence, $M\/N tilde.equiv R^n\/mat(d_1, 0, 0; 0, dots.down, 0; 0, 0, d_n)R^n tilde.equiv (R\/ d_1 R) times (R\/d_2 R) times dots.c times (R\/ d_n R)$.
]
#remark[
  If $d_1, dots, d_t$ are non-zero, then $d_1 m_1, dots, d_t m_t$ are linearly independent; however, in general, there may be some $d_i$'s equal to zero.
]
#proof[
  We prove by induction on $n$. If $n = 1$, $M = R$ and $N subset.eq R$. Let $m_1 = 1$. $N$ an ideal of $R$, so $N = (d_1) = d_1 R$ for some $d_1 in R$, then $N$ spanned by $d_1 m_1$.

// TODO maybe change induction step
  Suppose the claim for $n$. Let $M = R^(n+1)$. Given $phi in "Hom"(M, R)$, $I(phi) := im(phi|_N) = {phi(n) : n in N} subset.eq R$. This is an $R$-submodule of $R$, hence an ideal, so we may write $I(phi) = (d_phi)$. Let $
  Sigma := {I(phi) : phi in "Hom"(M, R)}.
  $ $Sigma$ is partially ordered by inclusion (or equivalently divisibility of generators), and so satisfies the maximal chain property.  Let $(d_1) = I(phi_1)$ be a maximal element of $Sigma$, i.e. $d_1$ minimal for divisibility. Let $n_1 in N$ be such that $phi_1 (n_1) = d_1$. We claim that $n_1$ is divisible $d_1$, i.e. there is an $m_1 in M$ such that $n_1 = d_1 m_1$.

  Let $eta_1, dots, eta_(n+1)$ be the natural projections $M -> R$, $eta_j (lambda_1, dots, lambda_(n+1)) := lambda_j$. So, if $n_1 = (x_1, dots, x_(n+1))$, we need to show that $d_1|x_j = eta_j (n_1)$ for each $j = 1,dots, n+1$. Let $d = eta_j (n_1)$. Let $d_0 = gcd(d_1, d)$, which we can write $d_0 = r d_1 + s d$ for some $r, s in R$. We have, unpacking definitions, $
  d_0 &= r phi_1 (n_1) + s eta_j (n_1) \ 
  &= (r phi_1 + s eta_j)(n_1).
  $ The map $r phi_1 + s eta_j in "Hom"(M, R)$, hence $(d_0) in Sigma$. We have too that $d_0|d_1$, and by maximality of $d_1$, $d_1|d_0$ hence it must be $(d_0) = (d_1)$. In addition, $d_0|d$ and thus $d_1|d$. This holds for all $d = eta_j (n_1)$'s, hence it follows that $d_1|n_1$.

  Let $m_1$ then be such that $d_1 m_1 = n_1$. Recall $phi_1 (n_1) = d_1$. Then, $
  phi_1 (d_1 m_1) = phi_1 (n_1) = d_1 \ 
  => d_1 phi_1 (m_1) = d_1 => phi_1 (m_1) = 1.
  $ We claim, then, $M tilde.equiv R m_1 plus.circle ker(phi_1)$. Consider the map $
  M -> R m_1 plus.circle ker(phi_1), wide m |-> (phi_1 (m) m_1, m - phi_1 (m) m_1),
  $ noticing that $
  phi_1 (m - phi_1 (m) m_1) = phi_1 (m) - phi_1 (phi_1 (m) m_1) = phi_1 (m) - phi_1 (m) underbrace((phi_1 (m_1)), = 1) = 0.
  $ Let $M_2 := ker(phi_1)$, noting then $M_2 tilde.equiv R^n$. We can write then $N = R n_1 plus.circle (ker(phi_1) sect N)$; given $n in N$, we have, recalling $phi_1 (N) = (d_1)$, $
  n = (underbrace((phi_1 (n))/d_1, "since" phi_1 (n) in (d_1))  n_1, n - (phi_1 (n))/d_1 n_1 ).
  $ Let $N_2 := (ker(phi_1) sect N)$. $N_2$ a submodule of $M_2 tilde.equiv R^n$. By the induction hypothesis, there is a basis $m_2, dots, m_(n+1)$ for $M_2$ and $d_2, dots, d_(n+1) in R$ with $d_2|d_3|dots.c|d_(n+1)$ such that $n_2 := d_2 m_2, dots, n_(n+1) := d_(n+1) m_(n+1)$ spans $N_2$. Then, $m_1, dots, m_(n+1)$ a basis for all of $M$, and $d_1 m_1, dots, d_(n+1) m_(n+1)$ spans $N$, so it remains to show that $d_1|d_2$.

  Consider $eta_j$ be the $j$th coordinate homomorphism relative to our basis $m_1, dots, m_(n+1)$, i.e. if $m = lambda_1 m_1 + dots.c + lambda_(n+1) m_(n+1)$, $eta_j (m) = lambda_j$. Then, remark since $n_1 = m_1 d_1$ $
  eta_1 (n_1) = d_1, wide eta_2 (n_1) = 0
  $ and since $n_2 in M_2$, $
  eta_1 (n_2) = 0, wide eta_2 (n_2) = d_2.
  $ Let $d_0 = gcd(d_1, d_2) = r d_1 + s d_2$ for some $r, s in R$. Let $eta = r eta_1 + s eta_2 in "Hom"(M, R)$. Then, $
  eta(n_1 + n_2) = d_0.
  $ Hence $(d_0) in Sigma$, since $n_1 + n_2 in N$. By maximiality of $d_1$, $d_1|d_0$, but also $d_0|d_2$ hence $d_1|d_2$, as we needed to show.
]

#corollary[
  $M\/N = R^n\/(d_1 R plus.circle dots.c plus.circle d_n R) = (R\/d_1 R) plus.circle dots.c  plus.circle (R\/d_n R)$.
]

#example[
  Let $A$ be a finitely generated abelian group; $A$ then just a fg $ZZ$-module. Then, $A tilde.equiv ZZ\/d_1 plus.circle dots.c plus.circle ZZ\/d_t plus.circle ZZ^m$. In particular, if $A$ is finite, then $m = 0$. Then, $d_1 dots.c d_t = hash A$, and $d_t a = 0$ for any $a in A$, and indeed the smallest such integer with this property (called the _exponent_ of $A$). 

  Note that $A$ is _not_ characterized by its exponent and cardinality; if two groups have the same exponent and cardinality, they need not be isomorphic. For instance, consider $
  ZZ\/3 times ZZ\/3 times ZZ\/9, wide ZZ\/9 times ZZ\/9,
  $ which are not isomorphic but have the same cardinality, $81$, and exponent, $9$.
]

#example[
  Let $R = FF[x]$ for some field $FF$, and $
  M = FF[x]\/(d_1 (x)) plus.circle dots.c  plus.circle FF[x]\/(d_t (x))  plus.circle FF[x]^r,
  $ where $r = 0 <=> dim_FF (M) < infinity$ as a vector space. In particular, $
  dim_FF (M) = deg d_1 + dots.c + deg d_t.
  $ In particular, we have a correspondence $
  "fg" FF[x] "module", r = 0 &<--> (V, T), dim_FF (V) < infinity "and" T : V -> V\
  M = V, f(x) dot v := f(T)(v) &arrow.l.squiggly.long (V, T) \ 
  V & arrow.r.squiggly.long V, T(v) := x dot v.
  $
  The maximal divisor $d_t (x)$ is the minimal polynomial of $T$.
]

#proposition[$d_1 (x) dots.c d_t (x)$ the characteristic polynomial of $T$.]

#proof[
  We let $p_T$ the minimal polynomial, $f_T$ the characteristic polynomial. Recall that $p_T|f_T$, $deg f_T = dim V$, and if $V = V_1 plus.circle V_2$ as a $FF[x]$-module (namely, $V_1, V_2$ respectively stable under the action of $FF[x]$), then $f_T = f_T|_V_1 dot f_T|_V_2$.

  If $t = 1$, $V = FF[x]\/(p(x))$, with $p_T (x) = p(x)$. Since $p_T|f_T$ and $deg f_T = dim_FF V = deg p_T$ so $p_T = f_T$.

  For general $t$, $V = FF[x]\/(p_1 (x)) plus.circle dots.c plus.circle FF[x]\/(p_t (x)) =: V_1 plus.circle dots.c plus.circle V_t$, then $f_T (x)$ is just $f_T|_(V_1) dots.c f_T|_(V_t)$, and since $f_T|_(V_i) = p_i$ as per the $t = 1$ case, the proof follows.
]

We summarize our interpretations of the structures that arise from the theorem:
#align(center, table(
  columns: 3,
  stroke: none,
  inset: 8pt,
  "", $ZZ$, $FF[x]$,
  table.hline(start: 0, end:3),
  "fg modules", "fg abelian groups", [fg $F[x]$-modules],
  $r=0$, "finite abelian groups", [finite dimensional $(V, T)$],
  $d_t$, "exponent", "minimal polynomial",
  $d_1 dots.c d_t$, "cardinality", "characteristic polynomial"
)
)

#proposition[
Given two matrices $M_1, M_2 in M_n (FF)$, $M_1$ is conjugate to $M_2$ if and only if the associated $FF[x]$-modules have the same elementary divisors.
]

#proof[
With $M_1, M_2 : V -> V$, $V$ can be viewed as an $FF[x]$-module in two different ways. We denote these modules $V_i$, where $f(x) v = f(M_i)(v)$ for $i = 1, 2$. Suppose that $V_1, V_2$ have the same elementary divisors, $d_1, dots, d_t$. This implies $
V_1 tilde.equiv FF[x]\/(d_1) plus.circle dots.c plus.circle FF[x]\/(d_t) tilde.equiv V_2,
$ _as $FF[x]$-modules_. Hence, there exists some isomorphism, $j : V_1 -> V_2$ of $FF[x]$-modules, so in particular $
j(x v) = x dot j(v)
$ for all $v in V_1$, but recalling that the action of $FF[x]$ is, we have  $
j(M_1 v) = M_2 j (v),
$ hence, $
j compose M_1 = M_2 compose j,
$ and so $M_1, M_2$ indeed conjugate.

More concretely, $j$ restricts to an isomorphism of $FF$-vector spaces, which as we know can simply be realized as multiplication by an invertible matrix, hence $J M_1 = M_2 J$ where $J$ the matrix realization of such an isomorphism.

For the converse, suppose $M_2 = P M_1 P^(-1)$ for some $P in "GL"_n (FF)$. Denote by $V_1$, $V_2$ the $FF[x]$-modules induced by the multiplication by $M_1$, $M_2$ respectively. We need to show $V_1, V_2$ are isomorphic as $FF[x]$-modules. Consider the map $
phi : V_1 -> V_2, wide A |-> P A.
$ We claim this a $FF[x]$-module homomorphism. Indeed, for $v in V_1, f(x) in FF[x]$, $
phi(f(x) dot v) &= phi (f(M_1) v) \
&= P f(M_1) v \ 
&= f(P M_1) v \
&= f(M_2 P) v \ 
&= f(M_2) P v \
&= f(M_2) phi(v) \ 
&= f(x) dot phi(v).
$
]

#example[
  Let $G = "GL"_3 (FF_2)$. Recall $hash G = 168$. Conjugacy classes in $G$ are, by the previous theorem, in bijection with possible sequences of elementary divisors $(d_1, dots, d_t)$, such that $d_1|d_2|dots.c|d_t$ and $deg(d_1 d_2 dots.c d_t) = deg(d_1) + dots.c + deg(d_t) = 3$. In particular, since the elements of $G$ are invertible, $x$ cannot be a root of any of the divisors.

  _t=1_: $d_1 (x)$ a polynomial of degree three with coefficients in $FF_2$. Since $T$ must be invertible, $x divides.not d_1$, so we have $
  d_1(x) = x^3 + ? x^2 + ? x + 1
  $ where $? in {0, 1}$. We go through all possibilities:
  #align(center, table(
    stroke: none, 
    inset: 5pt, 
    columns: 3,
    table.vline(start:0, end: 5, x:1),
    table.vline(start:0, end: 5, x:2),
    [], [$d_1(x)$], [$C$],
    table.hline(start:0, end: 5),
    [(a)], [$x^3 + 1 = (x + 1)(x^2 + x + 1)$], [3A],
    [(b)], [$x^3+x+1$], [7A],
    [(c)], [$x^3+x^2+1$], [7B],
    [(d)], [$x^3+x^2+x+1$], [4A],
  ))
  - By the PDT, $T$ with minimal polynomial (a) splits $V = V_1 plus.circle V_2$ where $T$ acts on $V_1$ as the identity. Let $T_2 = T|_V_2$. Then, since $x^2 + x + 1$ the minimal polynomial of $T_2$, it must be that $T_2^3 = 1$. Hence, $T$ is an element of order 3.
  - For (b), (c), we've seen that these polynomials are irreducible over $FF_2$. In particular, if $T$ has such a minimal polynomial, then $T$ of order 7.
  - For (d), $x^3 + x^2 + x + 1 = (x + 1)(x^2 + 1) = (x + 1)^3$. Then, $T^3 = T^2 + T + 1$ so $T^4 = T^3 + T^2 + T = T^2 + T + T^2 + T + 1 = 1$, hence $T$ of order 4.

_$t = 2$:_ consider ($d_1$, $d_2$). It must be that $d_1 (x) = x + 1$, and so $d_2 (x)= (x+1)^2$ is the only possibility. Then, $FF_2^3 = FF_2[x]\/(x+1) plus.circle FF_2[x]\/((x+1)^2) = FF_2 plus.circle FF_2[epsilon]\/(epsilon^2)$. Then, $T <-> (1, 1 + epsilon)$, $T^2 <-> (1, 1 + 2 epsilon + epsilon^2) = (1, 1)$, so $T$ of order $2$. We have #align(center, table(
    stroke: none, 
    inset: 5pt, 
    columns: 3,
    table.vline(start:0, end: 5, x:1),
    table.vline(start:0, end: 5, x:2),
    [], [$(d_1(x), d_2 (x))$], [$C$],
    table.hline(start:0, end: 5),
    [(e)], [$(x+1, (x+1)^2)$], [2A]
  ))

_$t=3$:_ it must be $(d_1, d_2, d_3) = (x + 1, x+ 1, x+1)$. Such a transformation must be the identity.
#align(center, table(
    stroke: none, 
    inset: 5pt, 
    columns: 3,
    table.vline(start:0, end: 5, x:1),
    table.vline(start:0, end: 5, x:2),
    [], [$(d_1(x), d_2 (x), d_3 (x))$], [$C$],
    table.hline(start:0, end: 5),
    [(f)], [$(x+1, x+1, x+1)$], [1A]
  ))
]

#theorem[If $t = 1$, then $Z_G (A) = (FF[x]\/(d_1 (x)))^times$.]

#proof[
  We know $V tilde.equiv FF[x]\/(d_1 (x))$ as an $FF[x]$-module. Then, $Z_G (A) = "Aut"_(FF[x]) (V) = "Aut"_FF[x] (FF[x]\/(d_1 (x))) = (FF[x]\/(d_1))^times$. 

  We have that $M in Z_G (A) <=> M A = A M <=> M A v = A M v$ for every $v in V$. Thinking of these as $FF[x]$-modules, this is equivalent to taking $M (x v) = x M v$, or equivalently $M$ an automorphism of $V$ as an $FF[x]$-module, i.e. respects $FF[x]$ scalar multiplication.
]

#example[
  We compute the size of the conjugacy classes of $"GL"_3 (FF_2)$ found above.

  _3A:_ By the previous theorem, $
  Z_G ("3A") &= (FF_2[x]\/(x^3+1))^times = (FF_2 times FF_2[x]\/(x^2 + x + 1))^times = FF_2^times times FF_4^times = 1 times ZZ\/3 ZZ.
  $

  _7A:_ Similarly, $
  Z_G ("7A") &= (FF_2[x]\/(x^3 + x + 1))^times \ 
  &= (FF_8)^times = ZZ\/7ZZ.
  $

  _7B:_ $
  Z_G ("7B") &= (FF_2[x]\/(x^3 + x^2 + 1))^times = (FF_8)^times = ZZ\/7ZZ.
  $

  _4A:_ $
  Z_G ("4A") &= (FF_2[x]\/((x+1)^3))^times = (FF_2[epsilon]\/(epsilon^3))^times.
  $ The ring $FF_2[epsilon]\/(epsilon^3) = {a + b epsilon + c epsilon^2 : a, b, c in FF_2}$. An element is invertible if and only if $a = 1$, so $(FF_2[epsilon]\/(epsilon^3))^times = {1 + b epsilon + c epsilon^2 : b, c in FF_2}$, with $
  (1 + b epsilon + c epsilon^2)^(-1) = 1 + (b epsilon + c epsilon^2) + (b epsilon + c epsilon^2)^2.
  $ So, we have that $hash Z_G ("4A") = 4$, namely only the powers of the element itself.

  In particular, this gives $hash 3 A = 56, hash 7 A = 24, hash 7 B = 24, hash 4 A = 42$ (by taking $hash G$ divided by $hash Z_G$).

  For $g in 2 A$, we have $
  Z_G (g) = "End"_(FF[x]) (FF[x]\/(x + 1) plus.circle FF[x]\/((x+1)^2))^times.
  $ 
]

More generally, consider a commutative ring $R$ and $M = M_1 plus.circle M_2$ where $M_1, M_2$ are $R$-modules. Then, for $f in "End"_R (M_1 plus.circle M_2)$, we write $f(m_1, m_2) = (f_1 (m_1, m_2), f_2 (m_1, m_2))$ where $f_i (m_1, m_2) in M_i$, and $f_i in "Hom"(M_1 plus.circle M_2, M_i)$. Note that $f_1 (m_1, m_2) = f_1 ((m_1, 0) + (0, m_2)) = f_1(m_1, 0) + f_1 (0, m_2)$,namely, $f_1$ completely determined by its effect on elements of the form $(m_1, 0), (0, m_2)$. Similar holds for $f_2$. Define $
f_(11) : M_1 -> M_1, wide f_11 (m_1) = f_1 (m_1, 0),\
f_12 : M_2 -> M_1, wide f_12 (m_2) = f_1 (0, m_2), \
f_21 : M_1 -> M_2, wide f_21 (m_1) = f_2 (m_1, 0),\
f_22 : M_2 -> M_2, wide f_22 (m_2) = f_2 (0, m_2).
$ Then, theres a clear association with matrices with entries $mat(f_11, f_12; f_21, f_22)$, namely, $
"End"_R (M_1 plus.circle M_2) = {mat(f_11, f_12; f_21, f_22): f_(i j) in "Hom"_R (M_j, M_i), i, j = 1, 2}.
$

#example[
   We now specialize to our case above, letting $M_1 = FF[x]\/(x+ 1) = FF$, with the action $f(x) dot 1 = f(1) 1$. With $epsilon = x + 1$, we can view $M_1 = FF[epsilon]\/(epsilon) = FF$ by the rule $f(epsilon) dot 1 = f(0) 1$. Then, $M_2 = FF[x]\/((x+1)^2) = FF[epsilon]\/(epsilon^2)$. We have $
   "End"_(FF[epsilon]) (M_1) = FF[epsilon]\/(epsilon) = FF.\
   "End"_(FF[epsilon]) (M_2) = "End"_(FF[epsilon]) (FF[epsilon]\/(epsilon^2)) = FF[epsilon]\/(epsilon^2).\
   "Hom"(M_2, M_1) = "Hom"_(FF[epsilon]) (FF[epsilon]\/(epsilon^2), FF) = FF. \ 
   "Hom"(M_1, M_2) = "Hom"_(FF[epsilon]) (FF, FF[epsilon]\/(epsilon^2)) = (epsilon FF[epsilon])\/(epsilon^2).
   $ So, $
   "End"_(FF[epsilon]) (FF plus.circle FF[epsilon]\/(epsilon^2)) = {mat(f_11, f_12; f_21, f_12) : f_11 in FF, f_12 in FF, f_21 in (epsilon FF[epsilon])\/(epsilon^2), f_21 in FF[epsilon]\/(epsilon^2)},
   $ so in particular,  $hash "End"_(FF[epsilon]) (FF plus.circle FF[epsilon]\/(epsilon^2)) = hash FF dot hash FF dot hash (epsilon FF[epsilon])\/(epsilon^2) dot hash FF[epsilon]\/(epsilon^2) = 2 dot 2 dot 2 dot 4 = 32$.

   We consider now $"Aut"_(FF[epsilon]) (M) = "End"_(FF[epsilon]) (M)^times$. Given a matrix $f = mat(f_11, f_12; f_21, f_22)$, we claim that $f$ iff $f_11 f_22 - f_12 f_21 in FF$. $f_12 f_21 = 0$ so we actually want $f_11 f_22 in FF^times$ i.e. $f_11 f_22 = 1 mod epsilon$ namely $f_11 = 1, f_22 = 1 + d epsilon$. This gives that $hash "Aut"_FF[epsilon] (M) = 1 dot 2 dot 2 dot 2 = 8$.

   #align(center, 
    table(
      columns: 4,
      stroke: none,
      inset: 10pt,
      [$(d_1, dots.c)$], $C$, $hash Z_G (g)$, $hash C$,
      table.hline(start:0, end: 5),
      $x^3 + 1$, $3A$, $3$, $56$,
      $x^3+x+1$, $7A$, $7$, $24$,
      $x^3+x^2+1$, $7B$, $7$, $24$,
      $x^3+x^2+x+1$, $4A$, $4$, $42$,
      $(x+1, (x+1)^2)$,$2A$, $8$, $21$,
      $(x+1, x+1,x+1)$, $1A$, $168$, $1$
    )
  )

  $V tilde.equiv FF[x]\/(x+1)plus.circle FF[x]\/((x+1)^2) = FF plus.circle FF[epsilon]\/(epsilon^2)$.

  Two generators, as $FF[x]$ ($epsilon$) module, $(1, 0), (0, 1)$. If $f in "End"_(FF[epsilon]) (V)$, $f(e_1) = a e_1 + beta e_2$ for som $a in FF, beta in FF[epsilon]\/(epsilon^2)$.

  But $epsilon e_1 = 0$ so $0 = f(epsilon e_1) = epsilon f(e_1) = epsilon a e_1 + epsilon beta e_2 = epsilon beta e_2$. So, it must be that $epsilon beta = 0$ i.e. $epsilon beta in (epsilon^2)$ so $beta = epsilon dot b$ some $b in FF$. So, $f(e_1) = a e_1 + b epsilon e_2$ for some $a, b in FF$.

  $f(e_2) = c e_1 + delta e_2$ for $c in FF, delta in FF[epsilon]$. 

  We can identify then $
  "End"_(FF[epsilon]) (V) = {mat(a, c; b epsilon, delta) : a, b, c in FF, delta = d_1 + d_2 epsilon in FF[epsilon]\/(epsilon^2)}.
  $

  Consider the quotient module $overline(V) := V\/(epsilon) V tilde.equiv FF plus.circle FF$.

]

#example[

  If $f in "End"_(FF[epsilon]) (V)$, it restricts to $overline(f) : overline(V) -> overline(V)$, represented by $mat(a, c ; 0, d_1)$, where now all the entries are in the field. Hence, $overline(f)$ invertible $=> a = d_1 = 1$. Hence, $"End"(V)^times subset {mat(1, c ; b epsilon, 1 + d_2 epsilon) : c, b, d_2 in FF}$. One can show all such elements are invertible, and thus $"End"(V)^times$ is precisely this set, which turns out to be a group of order 8 isomorphic to $D_8$.


]

#remark[
  If $FF$ is any field, $"End"_(FF[x]) (FF[x]\/(f_1) plus.circle FF[x]\/(f_2)) =:"End"_(FF[x]) (M_1 plus.circle M_2)  = {mat(a_11, a_12; a_21, a_22) : a_(i j) in "Hom"_(FF[x]) (M_j, M_i)}$.
]

#theorem[
  $"Hom"_(FF[x]) (FF[x]\/(f_1), FF[x]\/(f_2)) = f_2/("gcd" (f_1, f_2)) dot FF[x]\/(f_2)$. In particular, $
  "Hom"_(FF[x]) (FF[x]\/(f_1), FF[x]\/(f_2)) = cases(
    0 wide & "if" gcd (f_1, f_2) = 1,
    f_2/f_1 FF[x]\/(f_2)&  "if" f_1|f_2,
    FF[x]\/(f_2) & "if" f_2|f_1.
  )
  $
]

== Jordan Canonical Form
Let $T : V-> V$ over an _algberaically closed_ field $FF$. Then, the minimal polynomial $p_T (x) = (x - lambda_1)^(d_1) dots.c (x - lambda_r)^(d_r)$ factors into linear polynomials.

Since $(x - lambda_1)^(d_1), dots, (x - lambda_r)^(d_r)$ are pairwise relatively prime, the primary decomposition theorem tells us we may write $
V = V_(lambda_1) plus.circle dots.c plus.circle V_lambda_r,
$ where $
T_j = T|_V_lambda_j : V_lambda_j -> V_lambda_j
$ is $V_lambda_j$-stable, and $p_T_j (x) = (x - lambda_j)^(d_j)$. $V_lambda_j$ is called the generalized eigenspace associated to $lambda_j$.

Let $lambda$ be some eigenvalue and $V_lambda$ the corresponding generalized eigenspace. This is a $FF[x]$-module by the rule $x dot v = T(v)$. By the structure theorem, we have that $
V_lambda tilde.equiv FF[x]\/(d_1 (x)) plus.circle dots.c plus.circle FF[x]\/(d_t (x)).
$ We have that $d_t (x) = (x - lambda)^(d_lambda)$, and the remaining divisors $d_1 (x) = (x - lambda)^(e_1), d_2 (x) = (x - lambda)^(e_2), dots, d_t (x) = (x - lambda)^(e_t)$ where $e_1 <= e_2 <= dots.c <= e_t$, $e_t = d_lambda$, and $e_1 + e_2 + dots.c + e_t = dim V_lambda$.

#definition[
  A $T$-stable subspace of $V_lambda$ isomorphic to $FF[x]\/((x-lambda)^e)$ is called a _cyclic subspace_ or a _Jordan subspace_.
]

Given a Jordan subspace $W = FF[x]\/((x - lambda)^e)$, we call the basis $
B := (v_1, dots, v_e) = ((x - lambda)^(e - 1), (x - lambda)^(e - 2), dots, (x - lambda), 1)
$ the _Jordan basis_ for $W$. In this basis, $
(T - lambda)(v_1) &= (x - lambda)(x - lambda)^(e - 1) = 0 \
(T - lambda)(v_2) &= (x - lambda)^(e-1) = v_1\
dots.down \ 
(T - lambda)(v_e) &= (x - lambda) = v_(e - 1).
$ So in this basis, $
[T - lambda]_B = mat(
  0, 1, dots.c, 0;
  0, 0, dots.down, 0;
  dots.v, dots.down, dots.down, 1;
  0, 0, 0, 0
),
$ and so $
[T]_beta = [T - lambda]_B + lambda I = mat(
  lambda, 1, "", "", "";
  "", lambda, 1, "", "";
  "", "", dots.down, dots.down "";
  "", "", "", dots.down , 1;
  "", "", "", "",lambda
).
$

#theorem[
  If $V_lambda$ is the generalized eigenspace for $T$ attached to $lambda$, then there is a basis for $V_lambda$ such that $
  M_(T, V_lambda) = mat(
    J_(lambda, e_1), "", "", "";
    "", J_(lambda, e_2) "", "";
    "", "", dots.down, "";
     "", "", "", J_(lambda, e_t);
  ),
  $ where $
  J_(lambda, e_j) = mat(
  lambda, 1, "", "", "";
  "", lambda, 1, "", "";
  "", "", dots.down, dots.down "";
  "", "", "", dots.down , 1;
  "", "", "", "",lambda
)
  $ a $e_j times e_j$ matrix and $e_1 <= e_2 <= dots.c <= e_t$.
]

// ! Ending
#pagebreak()
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

== Midterm Questions

#proposition[
  Describe two non-abelian groups of cardinality 8 and show that they are not isomorphic.
]

#proof[
  Consider $D_8$ (symmetry group of the square) and $HH$ (the quaternions). Argue on the order of elements.
]

#proposition[
  Write down the class equation for the symmetric group $S_4$ on $4$ elements and use this to give a complete list of the normal subgroups of $S_4$.
]

#proof[
  $
  S_4 = {1} union.sq {"transpositions"}  union.sq {3"-cycles"} union.sq {2,2"-cycles"} union.sq {4"-cycles"}\
  hash S_4 = 1 + binom(4, 2) + 2dot binom(4,3) + 3 +3!
  $
  A subgroup is normal if it a union of conjugacy classes, so it suffices to check the possible unions of conjugacy classes. Should give ${1}, S_4, A_4, K_4$.
]

#proposition[
  Give a formula for the number of distinct ways of coloring the 8 corners (i.e. vertices) of a cube with $t$ distinct colors. (Note that the class equation computed in Question 2 can and should be used to assist you with this question.)
]

#proof[
  // Use the fact that 
]

#proposition[
  Let $p$ be a prime number. State the Sylow theorem for $p$. Starting with the fact (which was proven in class, and which you may assume for this question) that every finite group of cardinality not a power of $p$ can be made to act transitively on a set whose cardinality is neither $1$ nor divisible by $p$, show that eery finite group contains a Sylow $p$-subgroup.
]

#proposition[
  Show that $S_5$ can be made to act transitively on a set $X$ of size $6$, and describe how the elements of order 3 and 6 in $S_5$ act on $X$. (I.e. describe their cycle shapes.)
]

= Final Review

#proposition[
  Let $T$ be a linear transformation over a field $F$ having $(x - lambda)^2$ as minimal polynomial, for some $lambda in F$, and let $g(x)$ be a polynomial in $F[x]$. Show that 
$
g(T) = g(lambda)I + g'(lambda)(T - lambda I)
$
where $I$ is the identity transformation. Can you generalize this formula to the case where the minimal polynomial is $(x - lambda)^k$?
]

#proof[
Let $g in FF[x]$, then by Taylor expanding around $lambda$ and assuming $deg g = n$, $
g(x) = g(lambda) + g'(lambda)(x - lambda) + (g''(lambda))/2 (x - lambda)^2 + dots.c + (g^((n))(lambda))/n! (x - lambda)^n.
$ If $p_T (x) = (x - lambda)^k$, plugging $T$ into $g$ cancels all terms for which the degree is greater than or equal to $k$, so $
g(T) &= g(lambda) + g'(lambda)(x - lambda) + (g''(lambda))/2 (x - lambda)^2 + dots.c + (g^((k-1))(lambda))/((k-1)!) (x - lambda)^(k-1) \
&= sum_(i=0)^(k-1) (g^((k)) (x - lambda)^i)/i!.
$ 
// Since $p_T (x) = (x - lambda)^2$, it follows that $
// 0 = T^2 - 2 lambda T + lambda^2.
// $ If $g(x) = g_m x^m + dots.c + g_1 x + g_0 in FF[x]$, then $
// g(lambda) I + g' (lambda) (T - lambda I) &= (g_m lambda^m + dots.c + g_0) + (m g_m lambda^(m-1) + dots.c + g_1) (T - lambda I).
// $ Let us compare coefficients of $g$.
]

#proposition[Show that an element of $ZZ[i]$ is irreducible if and only if it is either of the form $i^n p$ where $p$ a prime of the form $4 k + 3$ or of the form $a + b i$ where $a^2 + b^2$ is either 2 or a prime of the form $4 k + 1$.]

#proof[
($=>$) Suppose $i^n p = x y$ where $p$ a prime of the form $4 k + 3$. Then $N(i^n p) = p^2 = N(x) N(y)$. Suppose $N(x) = N(y) = p$. 

Suppose $a + b i = x y$ where $a^2 + b^2$ a prime of the form $4 k + 1$. Then, $N(a + b i) = p = N(x) N(y)$ so it must be that one of $x, y$ a unit and $a + b i$ prime.

($impliedby$) Let $z in ZZ[i]$ irreducible. If $N(z) = p$ for some prime $p$, 
]

#proposition[
  Factor the element $-31 + 51 i$ into prime elements of $ZZ[i]$.
]

#proof[
  $(-1 - i)(-3 + 2 i)(-4 + 11 i)$.
]

#proposition[
  Let $R = ZZ[alpha]$ be the ring generated over $ZZ$ by a complex number $alpha$ satisfying the polynomial $x^2 + x + 6 = 0$. Show that the ideal $I = (2, alpha)$ is not principal, and the same is true for $I^2$, but that $I^3$ is not a principal ideal. What is a generator for this ideal?
]

#proof[
  Since $alpha$ satisfies $x^2 + x + 6 = 0$, it follows that $alpha = (-1 plus.minus sqrt(-23))/(2)$. We can take either positive or negative root so just take the positive. We can then define the norm of any element $r = a + b alpha in R$ by $
  N(a + b alpha) = (a + b alpha)(a + b overline(alpha)) = a^2 + a b (alpha + overline(alpha)) + b^2 alpha overline(alpha).
  $ Notice that $
  alpha + overline(alpha) = -1,
  $ and $
  alpha overline(alpha) = 6
  $ so $
  N(a + b alpha) = a^2 - a b + 6 b^2.
  $ If $a >= b$, then $a^2 >= a b$ so $
 N(r) = a^2 - a b + 6 b^2 >= 6 b^2
  $ and if $a <= b$, $b^2 >= a b$ so $
  N(r) = a^2 + 5 b^2 + b^2 - a b >= a^2 + 5 b^2.
  $ STAC $I = (r)$. Then it must be that $r|2$ so in particular $N(r)|N(2)$ by multiplicativity. But $N(2) = 4$, and so by the bounds found above it must be that $b = 0$. But then $r = a$ and $N(r) = a^2$, and the only way for $a|2$ is that $a = 1$ or $2$ (plus or minus). 

  One can verify that $r =plus.minus 2$ cannot divide $alpha$ since $N(r) = 4$ and $N(alpha) = 6$, so the only case to consider is $r = plus.minus 1$. If this were the case, $I$ would be the whole ring. But notice $
  R\/I = (ZZ[x]\/(x^2 + x + 6))\/(2, x) = ZZ_2 [x]\/(x) = ZZ_2 eq.not nothing,
  $ hence $I$ a proper ideal. We conclude $I$ not a principal ideal.

  We have $I^2 = (4, 2 alpha, - alpha - 6)$. One can similarly verify that if $r = a + b alpha$ a generator, then $N(r)$ must divide $N(4) = 16$, $N(2 alpha) = 24$ and $N(- alpha - 6) = 42$. The only possibilities are $plus.minus 1$ and $plus.minus 2$. One can verify similarly to the previous case that neither of these are possible, and that $I^2$ a proper ideal so not principal.

  We have finally $I^3 = (8, 4 alpha, - 12 - 2 alpha, 6 - 5 alpha)$. We claim $r = 2 + alpha$ a generator. Notice first that $2 + alpha = 8 - (6 - 5 alpha) - 4 alpha$ so $(2 + alpha) subset.eq I^3$. We need to show that every element in $I^3$ a multiple of $2 + alpha$, or equivalently that $2 + alpha$ divides each of the generators. We can find $
  8/(2 + alpha) &= 2 + overline(alpha) \ 
  (4 alpha)/(2 + alpha) &= alpha + 6 \
  (-12 - 2 alpha)/(2 + alpha) &= -3 + alpha \ 
  (6 - 5 alpha)/(2 + alpha) &= -1 - 2 alpha,
  $ by multiplying each numerator, denominator by $2 + overline(alpha)$ and simplifying.
 ]

#proposition[
  The regular icosahedron is a regular solid in three-dimensional space whose faces are isosceles triangles. The group of rotations which preserve this figure is isomorphic to the alternating group $A_5$ on five elements, and it acts transitively on the edges, vertices, and faces of the icosahedron. Each vertex is contained in five faces, and every face is preserved by a rotation of order 3. From this information, compute the number of faces, edges and vertices in the regular icosahedron. (A competent latinist might guess at the answer, but please indicate a mathematical reasoning!) 
]

#proof[
  Let $E, V, F$ denote the set of edges, vertices, faces and $G = A_5$. Then there are subgroups $H_E, H_V$ and $H_F$ such that $E tilde.eq G\/H_E$, etc. where $H_E = "Stab"(e)$ of some typical $e in E$. Since $f in F$ fixed by some $(a b c) in G$, it must be that $angle.l (a b c) angle.r subset H_F$ so in particular $3|hash H_F$. $hash H_F|hash G = 60$ as well so it must be that $hash H_F$ one of $3, 6, 12, 15, 30, 60$ so $hash F$ one of $20, 10, 5, 4, 2, 1$. $hash F$ obviously can't be $1, 2, 4$ or $5$ else this would contradict that each vertex is contained in precisely 5 faces. If $hash F = 20$, we have by Euler's formula $
  V - E + F = 2 => E - V = 18.
  $ In addition, $E$ and $V$ must each other be divisors of $60$. The only choices to make this hold are $E = 20, 30$ and respectively $V = 2, 12$. Two vertices is again impossible. $12$ vertices and $30$ edges is possible. We check the other case, when $hash F = 10$. This would imply that $E - V = 8$ so $E = 20, 12, 10$ and respectively $V = 12, 4, 2$. The $2, 4$ vertices cases are impossible so the last case is $V = 12, E = 20$.
  // TODO
]

#proposition[
  Let $T:V->V$ be a linear transformation on a finite-dimensional vector space $V$ over a field $F$. Show that the set of linear transformations that commute with $T$, i.e., satisfy $S T=T S$, is a subring of the ring $"End"_F (V)$. Give a necessary and sufficient condition on $T$ for this ring to be commutative.
]

#proof[
Let $X = {S in "End"_F (V) : S T = T S}$. It is a subring. Notice that multiplication by a constant (diagonal matrix with all entries a constant) commutes with $T$ always so we can realize $F subset X$ as a subring, so in particular we can view $X$ as a $F$-vector space. I claim $T$ $X$-invariant. Indeed, if $S in X$, the element $T S$ commutes with $T$ since $(T S) T = T (S T)$. Hence, we can consider the restriction $T_X$. This gives that $X$ also a $F[x]$-module by the rule $f(x) dot S = f (T_X) S$ for $f in F[x], S in X$.

By structure theorem for modules over PIDs (in this case the module being $X$ over the PID $F[x]$), $
X tilde.eq F[x]\/(p_1) plus.circle dots.c plus.circle F[x]\/(p_r).
$ Now, $X$ is commutative if and only if there is a single divisor, namely iff $
X tilde.eq F[x]\/(p).
$ In particular, $p$ is the minimal polynomial of $T_X$; then $p|p_T$ being the minimal polynomial of $T$.

Notice that all polynomials in $T$ commute with $T$, hence $F[x]\/(p_T) subset.eq X$.
]

#proposition[
   Let $G="GL"_3 (F_2)$ be the group of order 168 consisting of the invertible $3 times 3$ matrices with coefficients in the field with 2 elements. Describe all the conjugacy classes in $G$ and their sizes, and write down the class equation for $G$.
]

#proposition[
   Describe a Sylow 3-subgroup of $"GL"_3 (F_p)$ where $F_p$ is the field with $p$ elements and $p$ is a prime of the form $1+3k$ with $k$ not divisible by 3. 
]

#proof[
  
  $
  hash "GL"_3 (F_p) &= (p^3 - 1)(p^3 - p)(p^3 - p^2) \ 
  &= 3^4 k^3 (1 + 3 k)^2 (1 + 3 k + 3 k^2) (2 + 9 k + 9 k^2) =: 3^4 m
  $ where $3 divides.not m$.

  Note that $hash (F_p)^times = p-1 = 3 k$ hence by Sylow there is a subgroup, call it $H subset (F_p)^times$, of cardinality $3$ since $3 divides.not k$. 
  

  Consider $
  S = {mat(a, "", ""; "", b, ""; "", "", c) : a,b, c in H} union {mat("", a, ""; "", "", b; c, "", "") : a, b, c in H} union {mat("","", a; b, "", ""; "", c, "") : a, b, c in H}.
  $ Multiplication of matrices of these types result in the same type. Because all of the coefficients are in a (multiplicative) subgroup of $F_p$, the entries of products of matrices in $S$ will stay in $H$ and thus $S$ closed under multiplication. It clearly contains the identity and thus is a subgroup.
  // Let $
  // R := {mat(a, "", ""; "", b, ""; "", "", c) : a,b, c in H} subset "GL"_3 (F_p).
  // $ Then, its clear to see $R$ a subgroup of size $3^3$. Moreover, by Sylow it must be that the Sylow subgroup we seek, call it $S$, contains $R$ as a subgroup.

]

#proposition[
   Let $R$ be a principal ideal domain. Show that there is no infinite strictly increasing sequence of ideals $I_1 subset I_2 subset dots.c$ ordered by inclusion. 
]

#proof[
  Let $I = union.big_(n=1)^infinity I_n$. One can verify that $I$ an ideal of $R$ so there exists some generator $a$, i.e. $I = (a)$. But then, $a in I_n$ for some $n >= 1$ and so $(a) subset.eq I_n$. But also $I_n subset.eq I = (a)$, hence it must be that $I_n = (a)$, and so any $I_(i)$ for $i > n$ cannot be proper supsets of $I_n$.
]

#proposition[
  An $R$-submodule $N$ of an $R$-module $M$ is said to be a direct summand in $M$ if there is a submodule $N'$ of $M$ with $M=N plus.circle N'$. Let $R$ be a PID. Show that an $R$-submodule $N$ of a finitely generated free $R$-module $M$ is a direct summand in $M$ if and only if the quotient $M\/N$ is free over $R$. 
]

#proof[
  ($=>$) Since $N$ a submodule of a free module, it itself is free, let ${m_1, dots, m_t}$ its basis, same with $N'$, let ${m_(t+1), dots, m_(n)}$ its basis. Then, I claim that $M\/N$ has ${m_(t + 1) + N, dots, m_n + N}$ as basis. This proves $M\/N$ free.

  ($impliedby$) $M\/N$ free, let ${m_1 + N, dots, m_t + N}$ a basis. Let $beta = {m_1, dots, m_t}$ and $N' = "span" beta$. I claim that $M = N plus.circle N'$. 

  If $m in N$, then $m + N in M\/N$ so exist scalars $a_1, dots, a_t$ such that $m + N = a_1 m_1 + dots.c + a_t m_t + N$ so in particular $m = a_1 m_1 + dots.c + a_t m_t + n$ for some $n in N$, in particular $m in N' union N$, so $M subset.eq N' union N$, hence we have equality as the converse inclusion comes for free.

  Suppose $m in N' sect N$. Then, $m = a_1 m_1 + dots.c + a_t m_t$ for some $a_i$'s such that $m in N$. Passing to the quotient, it must be that $m + N = N$ i.e. $a_1 (m_1 + N) + dots.c + a_t (m_t + N)$. But $m_i + N$ a basis for $M\/N$, so in particular there is a unique way to write the zero vector $0 + N$, and it must be that $a_1 = dots.c = a_t = 0$ and so $m$ itself must be the zero 0 vector. It follows that $N' sect N = {0}$ and thus $M = N plus.circle N'$.
]