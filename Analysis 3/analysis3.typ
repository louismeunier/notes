// ! external
#import "../typst/notes.typ": *
#import "../typst/shortcuts.typ": *

#import "@preview/cetz:0.2.2"

// ! configuration
#show: doc => conf(
  course_code: "MATH454",
  course_title: "Analysis 3",
  subtitle: "",
  semester: "Fall 2024",
  professor: "Prof. Linan Chen",
  doc
)

#set align(left)

// TODO starts here
= Sigma Algebras and Measures

== A Review of Riemann Integration

Let $f : RR-> RR$ and $[a,b] subset RR$. Define a *partition* of $[a,b]$ as the set $
"part"([a,b]) := {a =: x_0 < x_1 < dots.c < x_N := b}.
$
We can then define the upper and lower Riemann integrals of $f$ over the region $[a,b]$ as $
"upper:" #h(2em) overline(integral_a^b) f(x) dif x := inf_("part"([a,b])) {sum_{i=1}^N sup_(x in [x_(i-1), x_(i)]) f(x) dot.c (x_i - x_(i-1))}\
"lower:" #h(2em) underline(integral_a^b) f(x) dif x := sup_("part"([a,b])) {sum_{i=1}^N inf_(x in [x_(i-1), x_(i)]) f(x) dot.c (x_i - x_(i-1))}.
$
We then say $f$ *Riemann integrable* if these two quantities are equal, and denote this value by $integral_a^b f(x) dif x$.

Many "nice-enough" functions are Riemann integrable, but many that we would like to be able to "integrate" are simply not, for instance Dirichlet's fucntion $x |-> cases(
  1  x in QQ \\ [a, b]\
0  x in QQ^c \\ [a,b]).$ Hence, we need a more general notion of integration.
// TODO

// TODO pictures

== Sigma Algebras

#definition("Sigma algebra")[
Let $X$ be a _space_ (a nonempty set) and $cal(F)$ a collection of subsets of $X$. $cal(F)$ a _sigma algebra_ or simply $sigma$-algebra of $X$ if the following hold:
+ $X in cal(F)$
+ $A in cal(F) => A^c in cal(F)$ (closed under complement)
+ ${A_n}_(n in NN) subset.eq cal(F) => union.big_(n=1)^infinity A_n in cal(F)$ (closed under countable unions)
]

#proposition[
4. $nothing in cal(F)$
5. ${A_n}_(n in NN) subset.eq cal(F) => sect.big_(n=1)^infinity A_n in cal(F)$
6. $A_1, dots, A_n in cal(F) => union.big_(n=1)^infinity A_n, sect.big_(n=1)^infinity A_n in cal(F)$
7. $A, B in cal(F) => A \\ B, B \\ A in cal(F)$
]

#example[
  The "largest" sigma algebra of a set $X$ is the power set $2^X$, the smallest the trivial ${nothing, X}$. 

  Given a set $A subset X$, the set $cal(F)_A := {nothing, X, A, A^c}$ is a sigma algebra; given two disjoint sets $A, B subset X$, then $cal(F)_(A, B) := {nothing, X, A, A^c, B, B^c, A union B, A^c sect B^c}$ a sigma algebra.
]

#definition("Generating a sigma algebra")[
  Let $X$ be a nonempty set, and $cal(C)$ a collection of subsets of $X$. Then, the $sigma$-algebra _generated_ by $cal(C)$, denoted $sigma(cal(C))$, is such that
  + $sigma(cal(C))$ a sigma algebra with $cal(C) subset.eq sigma(cal(C))$
  + if $cal(F)'$ a sigma algebra with $cal(C) subset.eq cal(F)'$, then $cal(F)' supset.eq sigma(cal(C))$

  Namely, $sigma(cal(C))$ is the smallest sigma algebra "containing" (as a subset) $cal(C)$.
]

#proposition[
  + $sigma(cal(C)) = sect.big {cal(F) : cal(F) " a sigma algebra containing " cal(C)}$
  + if $cal(C)$ itself a sigma algebra, then $sigma(cal(C)) = cal(C)$
  + if $cal(C)_1, cal(C)_2$ are two collections of subsets of $X$ such that $cal(C)_1 subset.eq cal(C)_2$, then $sigma(cal(C)_1) subset.eq sigma(cal(C)_2)$
]

#definition("The Borel sigma-algebra")[
The _Borel $sigma$-algebra_, denoted $frak(B)_RR$, on the real line is given by $
frak(B)_RR := sigma({"open subsets of " RR}).
$
We call sets in $frak(B)_RR$ _Borel sets_.
]

#proposition[
  $frak(B)_RR$ is also generated by the sets 
  - ${(a, b) : a < b in RR}$
  - ${(a, b] : a < b in RR}$
  - ${[a, b] : a < b in RR}$
  - ${[a, b) : a < b in RR}$ $ast.circle$
  - ${(-infinity, c) : c in RR}$
  - ${(-infinity, c] : c in RR}$
  - etc.
]

#proof[
We prove just $ast.circle$. It suffices to show that the generating sets of each $sigma$-algebra is contained in the other $sigma$-algebra. Let $a < b in RR$. Then, $
(a, b) = union.big_(n=1)^infinity underbrace([a + 1/n, b), in ast.circle) in sigma({[a, b)})  => frak(B)_RR subset.eq sigma({[a, b)}).
$
Conversely, $
[a, b) = sect.big_(n=1)^infinity (a - 1/n, b) in frak(B)_RR.
$
]

#proposition[
  All intervals (open, closed, half open, half closed, finite, etc) are Borel sets; any set obtained from countable set operations of intervals are Borel; all singletons are Borel; any finite and countable sets are Borel.
]

== Measures

#definition("Measurable Space")[
Let $X$ be a space and $cal(F)$ a $sigma$-algebra. We call the tuple $(X, cal(F))$ a _measurable space_.
]

#definition("Measure")[
Let $(X, cal(F))$ be a measurable space. A _measure_ is a function $mu : cal(F) -> [0, infinity]$ satisfying

(i) $mu(nothing) = 0$;

(ii) if ${A_n} subset.eq cal(F)$ a sequence of (pairwise) disjoint sets, then $
mu(union.big_(n=1)^infinity A_n) = sum_(n=1)^infinity mu(A_n),
$
i.e. $mu$ is _countably additive_. We further call $mu$
- _finite_ if $mu(X) < infinity$,
- a _probability measure_ if $mu(X) = 1$,
- $sigma$-finite if $exists {A_n} subset.eq cal(F)$ such that $X = union.big_(n=1)^infinity A_n$ with $mu(A_n) < infinity forall n >= 1$,
and call the triple $(X, cal(F), mu)$ a _measure space_.
]

#example[
  The measure on $frak(B)_RR$ given by $A |-> cases(|A| "if" A "finite"\ infinity " else")$ is called the _counting measure_. 

  Fix $x_0 in RR$, then the measure on $frak(B)_RR$ given by $A |-> cases(1 "if" x_0 in A\ 0 "else")$ is called the _point mass at $x_0$_.
]

#theorem("Properties of Measures")[
  Fix a measure space $(X, cal(F), mu)$. The following properties hold:
  + (finite additivity) For any sequence ${A_n}_(n=1)^N subset.eq cal(F)$ of disjoint sets, $
  mu(union.big_(n=1)^N A_n) = sum_(n=1)^N mu(A_n).
  $
  + (monotonicity) For any $A subset.eq B in cal(F)$, then $mu(A) <= mu(B)$.
  + (countable/finite subadditivity) For any sequence ${A_n} subset.eq cal(F)$ (*not* necessarily disjoint), $
  mu(union.big_(n=1)^infinity A_n) <= sum_(n=1)^infinity mu(A_n),
  $ an analogous statement holding for a finite collection of sets $A_1, dots, A_N$.
  + (continuity from below) For ${A_n} subset.eq cal(F)$ such that $A_n subset.eq A_(n+1) forall n >= 1$ (in which case we say ${A_n}$ "increasing" and write $A_n arrow.t$) we have $
  mu(union.big_(n=1)^infinity A_n) = lim_(n-> infinity) mu(A_n).
  $
  + (continuity from above) For ${A_n} subset.eq cal(F), A_n supset.eq A_(n+1) forall n >= 1$ (we write $A_n arrow.b$) we have that *if* $mu(A_1) < infinity$ ,
  $
  mu(sect.big_(n=1)^infinity A_n) = lim_(n-> infinity) mu(A_n).
  $
]

== Contructing the Lebesgue Measure on $RR$

#definition("Lebesgue outer measure")[
For all $A subset.eq RR$, define $
m^ast (A) := inf { sum_(n=1)^infinity ell(I_n) : A subset.eq union.big_(n=1)^infinity I_n, I_n "open intervals"},
$ called the _Lebesgue outer measure_ of $A$ (where $ell(I)$ is the length of interval $I$, i.e. the absolute value of the difference of its endpoints, if finite, or $infinity$ if not).
]

#proposition[
  The following properties of $m^ast$ hold:
  + $m^ast (A) >= 0$ for all $A subset.eq RR$, and $m^ast (nothing) = 0$.
  + (monotonicity) For $A subset.eq B$, $m^ast (A) lt.eq m^ast (B)$.
  + (countable subadditivity) For ${A_n}, A_n subset.eq RR$, $m^ast (union.big_(n=1)^infinity A_n) lt.eq sum_(n=1)^infinity m^ast (A_n)$.#footnote([More generally, any set function on $2^RR$ that satisfies 1., 2., and 3. is called an _outer measure_.])
  + If $I subset.eq RR$ an interval, then $m^ast (I) = ell(I)$.
  + $m^ast$ is translation invariant; for any $A subset.eq R, x in RR$, $m^ast (A) = m^ast (A + x)$ where $A + x := {a + x : a in A}$.
  + For all $A subset.eq RR$, $m^ast (A) = inf {m^ast (B) : A subset.eq B subset.eq R, B - "open"}$.
  + If $A = A_1 union A_2 subset.eq RR$ with $d(A_1, A_2) > 0,$#footnote("Remark: this is a stronger requirement than disjointness!") then $m^ast (A_1) + m^ast (A_2) = m^ast (A)$.
  + If $A = union.big_(k=1)^infinity J_k$ where $J_k$'s are "almost disjoint intervals" (i.e. share at most endpoints), then $m^ast (A) = sum_(k=1)^infinity m^ast (J_k) = sum_(k=1)^infinity ell(J_k).$
]

#proof[
3. If $m^ast (A_n) = infinity$, for any $n$, we are done, so assume wlog $m^ast (A_n) < infinity$ for all $n$. Then, for each $n$ and $epsilon > 0$, one can choose open intervals ${I_(n,i)}_(i >= 1)$ such that $A_n subset.eq union.big_(i=1)^infinity I_(n, i)$ and $sum_(i=1)^infinity ell(I_(n,i)) lt.eq m^ast (A_n) + epsilon/(2^n)$. Hence $
union.big_(n=1)^infinity A_n subset.eq union.big_(n=1, i = 1)^infinity I_(n, i)\
=> m^(ast) (union.big_(n=1)^infinity A_n) lt.eq sum_(n, i = 1)^infinity ell(I_(n, i)) = sum_(n=1)^infinity sum_(i=1)^infinity ell(I_(n, i)) lt.eq sum_(n=1)^infinity (m^ast (A_n) + epsilon/(2^n)) = sum_(n=1)^infinity m^(ast) (A_n) + epsilon,
$
and as $epsilon$ arbitrary, the statement follows.

4. We prove first for $I = [a, b]$. For any $epsilon > 0$, set $I_1 = (a - epsilon, b + epsilon)$; then $I subset.eq I_1$ so $m^ast (I) lt.eq ell(I_1) = (b - 1) + 2 epsilon$ hence $m^ast (I) lt.eq b - a = ell(I)$. Conversely, let ${I_n}$ be any open-interval convering of $I$ (wlog, each of finite length; else the statement holds trivially). Since $I$ compact, it can be covered by finitely many of the $I_n$'s, say ${I_n}_(n=1)^N$, denoting $I_n = (a_n, b_n)$ (with relabelling, etc). Moreover, we can pick the $a_n, b_n$'s such that $a_1 < a, b_N > b$, and generally $a_n < b_(n-1) forall 2 <= n <= N$. Then, $
sum_(n=1)^infinity ell(I_n) gt.eq sum_(n=1)^N ell(I_n) &= b_1 - a_1 + sum_(n=2)^N (b_n - a_n)\
& >= b_1 - a_1 + sum_(n=2)^N (b_n - b_(n-1)) \
&= b_N - a_1 >= b- 1 = ell(I),
$ hence since the cover was arbitrary, $m^(ast) (A) >= ell(I)$, and equality holds.

Now, suppose $I$ finite, with endpoints $a < b$. Then for any $(b-a)/2 > epsilon > 0$, then $
[a + epsilon, b - epsilon] subset.eq I subset.eq [a - epsilon, b + epsilon],
$ hence by monotonicity and the previous part of this proof $
m^ast ([a + epsilon, b - epsilon]) = b - a -2epsilon <= m^ast (I) <= b - a + 2 epsilon = m^ast ([a - epsilon, b + epsilon]),
$ from which it follows that $m^ast (I) = b - a = ell(I)$.

Finally, suppose $I$ infinite. Then, $forall M >= 0, exists$ closed, finite interval $I_M$ with $I_M subset.eq I$ and $ell(I_M) >= M$. Hence, $m^ast (I) >= m^ast (I_M) >= M$ and thus as $M$ arbitrary it must be that $m^ast (I) = infinity = ell(I)$.

6. Denote $tilde(m) (A) := inf {m^ast (B) : A subset.eq B subset.eq R, B - "open"}$. For any $A subset.eq B subset.eq RR$ with $B$ open, monotonicity gives that $m^ast (A) <= m^ast (B)$, hence $m^ast (A) <= tilde(m) (A)$. Conversely, assuming wlog $m^ast (A) < infinity$ (else holds trivially), then for all $epsilon > 0$, there exists ${I_n}$ such that $A subset.eq union.big_(n=1)^infinity I_n$ with $sum_(n=1)^infinity ell(I_n) <= m^ast (A) + epsilon$. Setting $B := union.big_(n=1)^infinity I_n$, we have that $A subset.eq B$ and $m^ast (B) = m^ast (union.big I_n) <=$ (by finite subadditivity) $sum_(n=1)^infinity m^ast (I_n) = sum_(n=1)^infinity ell(I_n) <= m^ast (A) + epsilon$  hence $m^ast (B) <= m^ast (A)$ for all $B$. Thus $m^ast (A) >= tilde(m)(A)$ and equality holds.

7. Put $delta := d(A_1, A_2) > 0$. Clearly $m^ast (A) <= m^ast (A_1) + m^ast (A_2)$ by finite subadditivity. wlog, $m^ast (A) < infinity$ (and hence $m^ast (A_i) < infinity, i = 1, 2$) (else holds trivially). Then $forall epsilon > 0, exists {I_n} : A subset.eq union.big I_n$ and $sum ell(I_n) <= m^ast (A) + epsilon$. Then, for all $n$, we consider a "refinement" of $I_n$; namely, let ${I_(n, i)}_(i >= 1)$ such that $I_n subset.eq union.big_(i) I_(n, i)$ and $ell(I_(n, i)) < delta$ and $sum_(i) ell(I_(n, i)) <= ell(I_n) + epsilon/(2^n)$. Relabel ${I_(n, i) : n, i >= 1} arrow.squiggly {J_m : m >= 1}$ (both are countable). Then, ${J_m}$ defines an open-interval cover of $A$, and since $ell(J_m) < delta$ for each $m$, $J_m$ intersects at most one $A_i$. For each $m$ and $p = 1, 2$, put $
M_p := {m : J_m sect A_p eq.not nothing},
$ noting that $M_1 sect M_2 = nothing$. Then ${J_m : m in M_p}$ is an open covereing of $A_p$, and so $
m^ast (A_1) + m^ast (A_2) &<= sum_(m in M_1) ell(J_m) + sum_(m in M_2) ell(J_m) \
& <= sum_(m=1)^infinity ell(J_m) = sum_(n, i = 1)^infinity ell(I_n, i)\
& <= sum_(n) (ell(I_n) + epsilon/(2^n))\
& = sum_(n) ell(I_n) + epsilon \
& <= m^ast (A) + 2 epsilon,
$ and hence equality follows.
8. If $ell(J_k) = infinity$ for some $k$, then since $J_k subset.eq A$, subadditivity gives us that $m^ast (J_k) <= m^ast (A)$ and so $m^ast (A) = infinity = sum_(k=1)^infinity ell(J_k)$ (since if any $J_k$ infinite, the sum of the lengths of all of them will also be infinite).

Suppose then $ell(J_k) < infinity$ for all $k$. Fix $epsilon > 0$. Then for all $k >= 1$, choose $I_k subset.eq J_k$ such that $ell(J_k) <= ell(I_k) + epsilon/(2^k)$. For any $N >= 1$, we can choose a subset ${I_1, dots, I_N}$ of intervals such that all are disjoint, with strictly positive distance between them, and so $
union.big_(k=1)^N I_k subset.eq union.big_(k=1)^N I_k subset.eq A\
=> m^ast (A) >= m^ast (union.big_(k=1)^N I_k ) &>= sum_(k=1)^N ell(I_k) \
&>= sum_(k=1)^N (ell (J_k) - epsilon/(2^k))\
& >= sum_(k=1)^N ell(J_k) - epsilon\
implies m^ast (A) >= sum_(k=1)^infinity ell(J_k),
$ the second inequality following from finite subadditivity. The converse of the final inequality holds trivially.
]

== Lebesgue-Measurable Sets

#definition[$A subset.eq RR$ is _$m^ast$-measurable_ if $forall B subset.eq RR$, $
m^ast (B) = m^ast (B sect A) + m^ast (B sect A^c).
$]

#remark[
By subadditivity, $<=$ always holds in the definition above.
]

#theorem("Carathéodary's Theorem")[
  Let $
  cal(M) := {A subset.eq RR : A m^ast-"measurable"}.
  $ Then, $cal(M)$ is a $sigma$-algebra of subsets of $RR$.

  Define $m : cal(M) -> [0, infinity]$, $m(A) = m^ast (A)$. Then, $m$ is a measure on $cal(M)$, called the _Lebesgue measure_ on $RR$. We call sets in $cal(M)$ _Lebesgue-measurable_ or simply _measurable_ (if clear from context) accordingly. We call $(RR, cal(M), m)$ the _Lebesgue measure space_.
]

#proof[
The first two $sigma$-algebra axioms are easy. We have for any $B subset.eq RR$ that $
m^ast (B sect RR) + m^ast (B sect RR^c) = m^ast (B) + m^ast (B sect nothing) = m^ast (B)
$ so $RR in cal(M)$. Further, $A in cal(M) => A^c in cal(M)$ by the symmetry of the requirement for sets to be in $cal(M)$.

The final axiom takes more work. We show first $cal(M)$ closed under finite unions; by induction it suffices to show for $2$ sets. Let $A_1, A_2 in cal(M)$. Then, for all $B subset.eq RR$, $
m^ast (B) &= m^ast (B sect A_1) + m^ast (B sect A_1^c) \
&=  m^ast (B sect A_1) + m^ast (B sect A_1^c sect A_2) + m^ast (B sect A_1^c sect A_2^c)\
&=  m^ast (B sect A_1) + m^ast (B sect A_1^c sect A_2) + m^ast (B sect (A_1 union A_2)^c)
$ Note that $(B sect A_1) union (B sect A_1^c sect A_2^c) = B sect (A_1 union A_2)$, hence by subadditivity, $
m^ast (B) >= m^ast (B sect (A_1 union A_2)) + m^ast (B sect (A_1 union A_2)^c),
$ and since the other direction of the inequality comes for free, we conclude $A_1 union A_2 in cal(M)$.

Let now ${A_n} subset.eq cal(M)$. We "disjointify" ${A_n}$; put $B_1 := A_1$, $B_n := A_n /\ union.big_(i=1)^(n-1) A_i, n >= 2$, noting $union.big_n A_n = union.big_n B_n$, and each $B_n in cal(M)$, as each is but a finite number of set operations applied to the $A_n$'s, and thus in $cal(M)$ as demonstrated above. Put $E_n := union.big_(i=1)^n B_i$, noting again $E_n in cal(M)$. Then, for all $B subset.eq RR$, $
m^ast (B) &= m^ast (underbrace(B sect E_n, "chop up" B_n)) +m^ast ( underbrace(B sect E_n^c, E_n subset.eq union B_n => E_n^c supset.eq (union B_n)^c))\
&>= m^ast (B sect underbrace(E_n sect B_n, = B_n)) + m^ast (B sect underbrace(E_n sect B_n^c, = E_(n-1))) + m^ast (B sect (union.big_(n=1)^infinity B_n)^c)\
& >= m^ast (B sect B_n) + m^ast (underbrace(B sect E_(n-1), "chop up" B_(n-1))) + m^ast (B sect (union.big_(n=1)^infinity B_n)^c)\
& >= m^ast (B sect B_n) + m^ast (B sect E_(n-1) sect B_(n-1)) \
& #h(2em)+ m^ast (B sect E_(n-1) sect B_(n-1)^c) + m^ast (B sect (union.big_(n=1)^infinity B_n)^c).
$ Notice that the last line is essentially the second applied to $B_(n-1)$; hence, we have a repeating (essentially, "descending") pattern in this manner, which we repeat until $n -> 1$. We have, thus, that $
m^ast (B) >= sum_(i=1)^n [ m^ast (B sect B_i)] + m^ast (B sect (union.big_(n=1)^infinity B_n)^c),
$ so taking $n -> infinity$, $
m^ast (B) &>=  sum_(i=1)^infinity [ m^ast (B sect B_i)] + m^ast (B sect (union.big_(n=1)^infinity B_n)^c)\
& >= m^ast (B sect (union.big_(n=1)^infinity B_n)) + m^ast (B sect (union.big_(n=1)^infinity B_n)^c).
$ As usual, the inverse inequality comes for free, and thus we can conclude $union.big_(n=1)^infinity B_n$ also $m^ast$-measurable, and thus so is $union.big_(n=1)^infinity A_n$. This proves $cal(M)$ a $sigma$-algebra.

We show now $m$ a measure. By previous propositions, we have that $m >= 0$ and $m(nothing) = 0$ (since $m = m^ast |_cal(M)$), so it remains to prove countable subadditivity.

Let ${A_n} subset.eq cal(M)$-disjoint. Following precisely the same argument as above, used to prove that $cal(M)$ closed under countable unions, shows that for any $n >= 1$ $
m (union.big_(i=1)^n A_i) = sum_(i=1)^n m(A_i),
$ that is, finite additivity holds, and thus by subadditivity $
m (union.big_(i=1)^infinity A_i) >= m (union.big_(i=1)^n A_i)  =sum_(i=1)^n m(A_i),
$ and so taking the limit of $n -> infinity$, we have 
$
m (union.big_(i=1)^infinity A_i) >= sum_(i=1)^infinity m(A_i),
$ with the converse inequality coming for free. Thus, $m$ indeed a measure on $cal(M)$.
]

#proposition[
$cal(M), m$ translation invariant; for all $A in cal(M)$, $x in RR$, $x + A = {x  + a : a in A} in cal(M)$ and $m (A) = m(A + x)$.
]
#remark[
  We would like this to hold, heuristically, since if we shift sets on the real line, we should expect their length to remain constant.
]

#proof[
For all $B subset.eq RR$, we have (since $m^ast$ translation invariant) $
m^ast (B) = m^ast (B - x) &= m^ast (underbrace((B - x) sect A, = B sect (A + x))) +m^ast (underbrace((B - x) sect A^c, = B sect (A^c + x) = B sect (A + x)^c))\
&= m^ast (B sect (A + x)) + m^ast (B sect (A + x)^c),
$ thus $A + x in cal(M)$, and since $m^ast$ translation invariant, it follows that $m$ is.
]

#theorem[
$forall a, b in RR$ with $a< b$, $(a, b) in cal(M)$, and $m((a, b)) = b - a$.
]
#remark[
  Again, we'd like this to hold, heuristically, since we would like the measure of an interval to simply be its length; we'd moreover like to be able to measure intervals, i.e. have intervals be contained in $cal(M)$.
]
#corollary[$frak(B)_RR subset.eq cal(M)$]

#proof[
  $frak(B)_RR$ is generated by open intervals of the form $(a, b)$. All such intervals are in $cal(M)$ by the previous theorem, and hence the proof.
]

== Properties of the Lebesgue Measure

#proposition([Regularity Assumptions on $m$])[For all $A in cal(M)$, the following hold.
- For all $epsilon >0, exists G$ open such that $A subset.eq G$ and $m(G\\A) < epsilon$.
- For all $epsilon > 0$, $exists F$-closed such that $F subset.eq A$ and $m(A\\F) <= epsilon$.
- $m(A) = inf {m(G) : G "open", G supset.eq A}$.
- $m(A) = sup {m(K) : K "compact", K subset.eq A}$.
- If $m (A) < infinity$, then for all $epsilon > 0$, $exists K subset.eq A$ compact, such that $m (A \\ K) < epsilon$.
- If $m(A) < infinity$, then for all $epsilon >= 0$, $exists$ finite collection of open intervals $I_1, dots, I_N$ such that $m(A triangle.t.small (union.big_(n=1)^N I_n)) <= epsilon$.
]

#proposition([Completeness of $m$])[$(RR, cal(M), m)$ is _complete_, in the sense that for all $A subset.eq RR$, if $exists B in cal(M)$ such that $A subset.eq B$ and $m(B) = 0$, then $A in cal(M)$ and $m(A) = 0$. 

Equivalently, any subset of a null set is again a null set.
]

// TODO proof
#remark[In general, $A in cal(F), B subset.eq A cancel(=>) B in cal(F)$.]

#proposition[Up to rescaling, $m$ is the unique, nontrivial measure on $(RR, frak(B)_RR)$ that is finite on compact sets and is translation invariant, i.e. if $mu$ another such measure on $(RR, frak(B)_RR)$ with $mu = c dot.c m$ for $c > 0$, then $mu = m$.]

#remark[Such a $c$ is simply $c = mu((0,1))$.]

To prove this proposition, we first introduce some helpful tooling:
#theorem([Dynkin's $pi$-d])[Given a space $X$, let $cal(C)$ be a collection of subsets of $X$. $cal(C)$ is called a _$pi$-system_ if $A, B in cal(C) => A sect B in cal(C)$ (that is, it is closed under finite intersections).

Let $cal(F) = sigma (cal(C))$, and suppose $mu_1, mu_2$ are two finite measures on $(X, cal(F))$ such that $mu_1 (X) = mu_2 (X)$ and $mu_1 = mu_2$ when restricted to $cal(C)$. Then, $mu_1 = mu_2$ on all of $cal(F)$.
]

#proposition[${nothing} union {(a, b) : a < b  in RR}$ a $pi$-system.]

#proposition[If $mu$ a measure on $(RR, frak(B)_RR)$ such that for all intervals $I$, $mu (I) = ell (I)$, then $mu = m$.]

#proof[Consider for all $n >= 1$ $mu|_(frak(B)_([-n,n]))$. Clearly, $mu ([-n, n]) = m([-n, n]) = 2n$, and for all $a, b in RR$, $mu((a, b) sect [-n,n]) = ell ((a, b) sect [-n, n]) = m((a, b) sect [-n, n])$. Thus, by the previous theorem, $mu$ must match $m$ on all of $frak(B)_([-n,n])$.

Let now $A in frak(B)_RR$. Let $A_n := A sect [-n, n] in frak(B)_([-n,n])$. By continuity of $m$ from below, $
mu(A) &= lim_(n-> infinity) mu(A_n)\
&= lim_(n -> infinity) m(A_n)\
&= m(A),
$ hence $mu = m$.
]

#proposition[If $mu$ a measure on $(RR, borel)$ assigning finite values to compact sets and is translation invariant, then $mu = c m$ for some $c > 0$.]

#remark[
  This proposition is also tacitly stating that $borel$ translation invariant; this needs to be shown.
]
#lemma[$borel$ translation invariant; for any $A in borel, x in RR, A + x in borel$.]

#proof[
  We employ the "good set strategy"; fix some $x in RR$ and let $
  Sigma := {B in borel : B + x in borel}.
  $
  One can check that $Sigma$ a $sigma$-algebra, and so $Sigma subset.eq borel$. But in addition, its easy to see that ${(a, b) : a <b in RR} subset.eq Sigma$, since a translated interval is just another interval, and since these sets generate $borel$, it must be further that $borel subset.eq Sigma$, completing the proof.
]

#proof[(of the proposition) Let $c = mu((0, 1])$, noting that $c > 0$ (why? Consider what would happen if $c = 0$).

This implies that $forall n >= 1$, $mu ((0, 1/n]) = c/n$ (obtained by "chopping up" $(0, 1]$ into $n$ disjoint intervals); from here we can draw many further conclusions: $
&forall m = 1, dots, n - 1, mu((0, m/n]) = m/n c\
&=> forall q in QQ sect (0, 1], mu((0, q]) = q c\
&=> forall q in QQ^+, mu ((0, q]) = q dot c "(translate)"\
&=> forall a in RR, mu((a, a + q]) = q dot c\
&=> forall "intervals" I, mu(I) = c dot ell (I) "(continuity)"\
&=> forall n >= 1, a, b in RR, mu((a, b) sect [-n, n]) = c dot ell ((a, b) sect [-n, n]) = c dot m ((a, b) sect [-n, n]),
$
but then, $mu = c dot m$ on $borel_[-n,n]$, and by appealing again the Dynkin's, $mu = c dot m$ on all of $borel$.
]

#proposition("Scaling")[$m$ has the _scaling property_ that $forall A in cal(M)$, $c in RR$, $c dot A = {c x : x in A} in cal(M)$, and $m (c dot A) = |c| m(A)$.]

#proof[Assume $c eq.not 0$. Given $A subset.eq RR$, remark that ${I_n}$ an open interval cover of $A$ iff ${c I_n}$ and open interval cover of $c A$, and $ell (c I_n) = |c| ell(I_n)$, and thus $m^ast (c A) = |c| m^ast (A)$.

Now, suppose $A in cal(M)$. Then, we have for any $B subset.eq RR$, $
m^ast (B) = |c| m^ast (1/c B) &= |c| m^ast (1/c B sect A) + |c| m^ast (1/c B sect A^c)\
&= m^ast (B sect c A) + m^ast (B sect  (c A)^c),
$ so $c A in cal(M)$.
]

== Relationshion between $borel$ and $cal(M)$

#definition[Given $(X, cal(F), mu)$, consider the following collection of subsets of $X$, $
cal(N) := {B subset.eq X : exists A in cal(F) "s.t." mu(A) =0, B subset.eq A}.
$ Put $overline(cal(F)) := sigma (cal(F) union cal(N))$; this is called the _completion_ of $cal(F)$ with respect to $mu$.
]

#proposition[$overline(cal(F)) = {F subset.eq X : exists E, G in cal(F) "s.t." exists E subset.eq F subset.eq G "and" m(G \\ E) = 0}$.]

#proof[
Put $cal(G)$ the set on the right; one can check $cal(G)$ a $sigma$-algebra. Since $cal(F) subset.eq cal(G)$  and $cal(N) subset.eq cal(G)$, we have $overline(cal(F)) subset.eq cal(G)$.

Conversely, for any $F in cal(G)$, we have $E, G in cal(F)$ such that $E subset.eq F subset.eq G$ with $m(G \\ E) = 0$. We can rewrite $
F = underbrace(E, in cal(F)) union underbrace((F \\ E), subset.eq G \\ E \ => mu (F \\ E )= 0 \ => G\\E in cal(N)),
$ hence $F in cal(F) union cal(N)$ and thus in $cal(F)$, and equality holds.
]

#definition[Given $(X, cal(F), mu)$, $mu$ can be _extended_ to $overline(cal(F))$ by, for each $F in overline(cal(F))$ with $E subset.eq F subset.eq G$ s.t. $mu(G\\E) = 0$, put $
mu(F) = mu(E) = mu(G).
$ We call then $(X, cal(F), mu)$ a _complete measure space_.]

#remark[It isn't obvious that this is well defined a priori; in particular, the $E, G$ sets are certainly not guaranteed to be unique in general, so one must check that this definition is valid regardless of choice of "sandwich sets".]

#theorem[$(RR, cal(M), m)$ is the completion of $(RR, borel, m)$.]

#proof[
  Given $A in cal(M)$, then $forall n >= 1, exists G_n$-open with $A subset.eq G_n$ s.t. $m^ast (G_n \\ A) <= 1/n$ and $exists F_n$-closed with $F_n subset.eq A$ s.t. $m^ast (A \\ F_n) <= 1/n$.

  Put $C := sect.big_(n=1)^infinity G_n$, $B := sect.big_(n=1)^infinity F_n$, remarking that $C, B in borel$, $B subset.eq A subset.eq C$, and moreover $
  m(C \\ A) <= 1/n, m(A \\ B) <= 1/n\
  => m(C \\ B) = m(C\\A) + m(A \\ B) <= 2/n,
  $
  but $n$ can be arbitrarily large, hence $m (C \\ B) = 0$; in short, given a measurable set, we can "sandwich it" arbitrarily closely with Borel sets. Thus, $A in overline(borel) => cal(M) subset.eq overline(borel)$. But recall that $cal(M)$ complete, so $borel subset.eq cal(M) => overline(borel) subset.eq overline(cal(M)) = cal(M)$, and thus $overline(borel) = cal(M)$ indeed.

  Heuristically, this means that any measurable set is "different" from a Borel set by at most a null set.
]

== Some Special Sets

Remark that for any countable set $A in cal(M)$, $m(A) = 0$. One naturally asks the opposite question, does there exist a measurable, uncountable set with measure 0? We construct a particular one here, the Cantor set, $C$.

This requires an "inductive" construction. Define $C_0 = [0, 1]$, and define $C_k$ to be $C_(k-1)$ after removing the middle third from each of its disjoint components. For instance $C_1 = [0, 1/3] union [2/3, 1]$, then $C_2 = [0, 1/9] union [2/9, 1/3] union [2/3, 7/9] union [8/9, 1]$, and so on. This may be clearest graphically:

#align(center,
  cetz.canvas({
    import cetz.draw: *
    line((0, 5), (5, 5))

    line((0, 4), (5/3, 4))
    line((2*5/3, 4), (2*5/3+5/3, 4))

    line((0, 3), (5/9, 3))
    line((2*5/9, 3), (2*5/9+5/9, 3))
    line((0+2*5/3, 3), (5/9+2*5/3, 3))
    line((2*5/9+2*5/3, 3), (2*5/9+5/9+2*5/3, 3))

    content((5/3/2, 2), $dots.v$)
    content((5-5/6, 2), $dots.v$)

    content((6, 5), $C_0$)
    content((6, 4), $C_1$)
    content((6, 3), $C_2$)
    content((6, 2), $dots.v$)
  })
)

 Remark that the $C_n arrow.b$. Put finally $
C := sect.big_(n=1)^infinity C_n.
$

#proposition[The follow hold for the Cantor set $C$:

+ $C$ is closed (and thus $C in borel$);
+ $m(C) = 0$;
+ $C$ is uncountable.
]

#proof[
1. For each $n$, $C_n$ is the countable (indeed, finite) union of $2^n$-many disjoint, closed intervals, hence each $C_n$ closed. $C$ is thus a countable intersection of closed sets, and is thus itself closed.

2. For each $n$, each of the $2^n$ disjoint closed intervals in $C_n$ has length $1/3^n$, hence $
m(C_n) = 2^n / 3^n = (2/3)^n.
$ Since ${C_n} arrow.b$, by continuity of $m$ we have $
m(C) = lim_(n=> infinity) m(C_n) = lim_(n-> infinity) (2/3)^n = 0.
$

3. This part is a little trickier. Notice that for any $x in [0, 1]$, we can define a sequence $(a_n)$ where each $a_n in {0, 1, 2}$, and such that $
x = sum_(n=1)^infinity a_n/3^n;
$ in particular, this is just the base-3 representation of $x$, which we denote $(x)_3 = (a_1 a_2 dots.c)$.

I claim now that $
C = {x in [0, 1] : (x)_3 "has no" 1"'s"}.
$ Indeed, at each stage $n$ of the construction of the Cantor set, we get rid of the segment of the real line that would correspond to the $a_n = 1$. One should note that $(x)_3$ not necessarily unique; for instance $(1/3)_3 = (1, 0, 0, dots) = (0, 2, 2, dots)$, but if we specifically consider all $x$ such that there _exists_ a base three representation with no 1's, i.e. like $1/3$, then $C$ indeed captures all the desired numbers.

Thus, we have that $
"card" (C) = "card" ({{ a_n} : a_n = 0, 2}).
$ Define now the function $
f : C -> [0, 1], #h(1em) x |-> sum_(n=1)^infinity a_n/2 1/2^n, "where" (x)_3 = (a_n)
$ i.e., we "squish" the base-3 representation into a base-2 representation of a number. This is surjective; for any $y in [0, 1]$, $(b_n) := (y)_2$ contains only 0's and 1's, hence $(2 b_n)$ contains only $0$'s and $1$'s, so let $x$ be the number such that $(x)_3 = (2 b_n)$. This necessarily exists, indeed, we simply take our definitions backwards: $
x := sum_(n=1)^infinity (2 b_n)/3^n,
$ which maps to $y$ under $f$ and is contained in $C$. Hence, $"card"(C) >= "card"([0, 1])$; but $[0, 1]$ uncountable, and thus so must $C$.
]