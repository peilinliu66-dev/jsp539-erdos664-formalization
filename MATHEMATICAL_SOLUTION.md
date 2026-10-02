# JSP539 / Erdős #664: an exact-design counterexample for every real bound

This note explains the proof implemented in the source. Its main construction
is a fixed-bound specialization of Jiaxi Nie's
[Block Designs with Large Transversal–Block Intersections, Theorem 1.2](https://arxiv.org/html/2609.07736v1).
The implementation uses an affine plane, a locally proved finite
Campos–Samotij container algorithm, and a disjoint-trace probability argument.
The constants and elementary estimates below are those of this implementation.

## 1. Statement and original questions

A transversal of a finite indexed family $A_1,\ldots,A_m\subseteq S$ is a
set $Q\subseteq S$ meeting every block. An exact pairwise-balanced design
requires each pair of distinct points of $S$ to belong to exactly one
indexed block.

The endpoint `JSP539.exists_bad_fin_design_real` asserts that for every
real $K$ and every natural number $n_0$, there are natural numbers
$n\ge n_0$ and $m$,
and a family $A:\operatorname{Fin}m\to\mathcal P(\operatorname{Fin}n)$ with:

1. $|A_i|>\frac25\sqrt n$ for every $i$;
2. every distinct point pair contained in exactly one indexed block;
3. $|A_i\cap A_j|\le1$ for $i\ne j$;
4. for every transversal $Q$, some block satisfying $|Q\cap A_i|>K$.

The family is constructed after $K$ and $n_0$ are supplied. Its obstruction
quantifies over every transversal of that same family. It provides
arbitrarily large ground sets, without requiring every prescribed integer
to occur as the size of a construction.

The original linear-family assertion has the form

$$
\forall c\in(0,1)\ \exists K\in\mathbb R\ \forall n,m,A,\quad
\left[
\begin{array}{l}
|A_i|>c\sqrt n\quad\text{for all }i,\\
|A_i\cap A_j|\le1\quad\text{for }i\ne j
\end{array}
\right]\Longrightarrow
\exists Q\ \forall i,\ 1\le|Q\cap A_i|\le K.
$$

The 1981 block-design assertion quantifies over all positive real $c$ and
uses exact pair coverage in place of the linearity hypothesis.
`OriginalScope.erdos_664_real` and `OriginalScope.block_design_real`
negate these assertions. Choosing $c=2/5$ in either supposed assertion
contradicts the displayed construction. This preserves the original
quantifier ranges; it does not assert that every positive $c$ separately
admits this construction.

See the [official JSP539 entry](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#JSP-000539),
the [Erdős #664 page](https://www.erdosproblems.com/664), and Erdős's
[1981 paper](https://www.renyi.hu/~p_erdos/1981-16.pdf).
Alon's [earlier paper](https://web.math.princeton.edu/~nalon/PDFS/remark191.pdf)
resolves the linear-family version. Nie is credited for the mathematical
resolution of the exact-design version.

## 2. Explicit affine geometry

First take $K\in\mathbb N$ and set $k=K+2\ge2$. Choose a sufficiently large
prime $q$ after the estimates below. The points are
$V=\mathbb F_q\times\mathbb F_q$, and the lines are $x=b$ and $y=ax+b$.
The code uses `ZMod q × ZMod q` and
`Option (ZMod q) × ZMod q`, with `none` denoting a vertical line.

There are $q^2$ points and $q(q+1)$ lines; each line has $q$ points and each
point lies on $q+1$ lines. Two distinct points with equal first coordinate
determine a vertical line. Otherwise their slope is
$(y_2-y_1)/(x_2-x_1)$, with nonzero denominator. Subtraction of the line
equations also proves uniqueness. Consequently distinct lines intersect
in at most one point. Double counting gives, for any $X\subseteq V$,

$$
\sum_\ell|X\cap\ell|=(q+1)|X|.
$$

A $k$-arc is a set $I$ such that $|I\cap\ell|<k$ for every affine line.
These facts are proved from the finite-field definitions in
`AffinePlane.lean`.

## 3. Constructed chunks and balanced hypergraphs

At any node $X\subseteq V$ with $|X|>2kq$, put
$\gamma=\lfloor|X|/(2q)\rfloor$. Then

$$
\gamma\ge k\ge2,\qquad
2\gamma q\le|X|<2(\gamma+1)q\le3\gamma q.
$$

Partition each $X\cap\ell$ into disjoint $\gamma$-element chunks and a
remainder of size less than $\gamma$. The finite partition is constructed
by successively removing an actual $\gamma$-element subset, also proving
the quotient and remainder counts.

If $J$ is the number of complete chunks over all lines, incidence counting
gives

$$
(q+1)|X|
=\gamma J+\sum_\ell|\mathrm{remainder}_\ell|
\le\gamma J+\gamma q(q+1).
$$

Together with $|X|\ge2\gamma q$, this implies
$J\ge q(q+1)\ge q^2$. A chunk of size at least two cannot occur on two
distinct lines. Distinct chunks on one line are disjoint, while chunks
on distinct lines intersect in at most one point.

Let $H$ consist of every $k$-element subset of every chunk. Since $k\ge2$,
no edge is repeated. With $e=|H|$ and $N=|X|$, the actual counts give

$$
e\ge q^2\binom{\gamma}{k},\qquad
\Delta_1(H)\le(q+1)\binom{\gamma-1}{k-1},\qquad
\Delta_t(H)\le\binom{\gamma-t}{k-t}\quad(2\le t\le k).
$$

A point belongs to at most one chunk on each of its $q+1$ lines. A set of
at least two points belongs to at most one chunk. Every $k$-arc is
independent in $H$, since each edge is $k$ collinear points.
`GroundHypergraph.lean` transports $H$ to the finite subtype $X$, with
ambient cardinality $N$ and exactly preserved edges and codegrees.

The falling-factorial ratio satisfies

$$
\frac{\binom{\gamma-t}{k-t}}{\binom{\gamma}{k}}
=\prod_{j=0}^{t-1}\frac{k-j}{\gamma-j}
\le\left(\frac{k}{\gamma}\right)^t.
$$

Hence

$$
\frac{N\Delta_1(H)}e\le6k\le10k,\qquad
\frac{N\Delta_t(H)}e\le\frac{3k^t}{\gamma^{t-1}q}.
$$

Set $l=\log q$, $L=l^3$, and $p=1/(\gamma L)$. The finite conditions

$$
l\ge1,\qquad L\ge8k,\qquad q\ge12k^kL^{k-1}
$$

give $0<p\le1/(8k^2)$ and, for $2\le t\le k$,

$$
\Delta_t(H)\le\frac e{4N}p^{t-1}.
$$

For the latter, $q\ge12k^tL^{t-1}$ follows from $k,L\ge1$ and $t\le k$.
All three finite conditions hold eventually for each fixed $k$.

## 4. A proved finite container machine

`ContainerCore.theoremA` implements the finite algorithm underlying
Campos and Samotij's [Towards an optimal hypergraph container lemma,
Theorem A and Section 3](https://arxiv.org/abs/2408.06617).
Its existence, quantitative bound and reconstruction are proved locally.

Let $H_0$ be an $r$-uniform hypergraph on a finite universe of size $N$,
with $r>0$ and $0<p\le1/(8r^2)$. Define

$$
w_p(G)=\sum_{E\in G}p^{|E|},\qquad
C(G)=\{v:\{v\}\notin G\}.
$$

The state contains an antichain $G$ of nonempty edges of size at most $r$
and a fingerprint $S$. Initially $G=H_0$, $S=\varnothing$. Given an
independent input $I$, stop exactly when
$w_p(G^{>1})\le p|C(G)|$, where $G^{>1}$ contains the nonsingleton edges.

At a nonterminal state, weighted incidence counting yields

$$
w_p(G^{>1})
\le\sum_{a=2}^r a\,w_p(G_a)
=\sum_{v\in C(G)}p\sum_{a=2}^r
     w_p(\operatorname{link}_{G_a}\{v\}).
$$

A vertex forbidden by a singleton contributes zero by the antichain
property. The failed stop test and finite averaging produce a heavy
singleton seed. Choose the least layer $a$ supporting a heavy nonempty
seed, then an inclusion-maximal such seed $T$ in that layer, where

$$
T\notin G,\quad
T\subseteq E\text{ for some }E\in G_a,\quad
w_p(\operatorname{link}_{G_a}T)\ge\frac1{4r}.
$$

Finite minimization and maximization prove existence. Fix a selection
depending only on the current family, independently of the input $I$.

For a replacement family $F$, update by
$G\leftarrow(G\setminus\uparrow F)\cup F$, removing the old edges that
contain a member of $F$.
If $T\subseteq I$, accept: take $F=\operatorname{link}_{G_a}T$ and add $T$
to $S$. Otherwise reject: take $F=\{T\}$ and keep $S$.
An accepting link edge inside $I$, together with $T\subseteq I$, would put
its original edge inside $I$. A rejected seed is not inside $I$.
Thus both branches preserve independence of $I$.
Their inserted edges are proper subsets of old antichain edges and lie
outside the old generated up-set. The antichain, nonempty-edge and rank
invariants are also preserved.

The low-link invariant is

$$
w_p(\operatorname{link}_{G_b}U)\le\frac1{2r}
\quad(b<r,\ 0<|U|<b).
$$

It initially holds because $H_0$ has no layers below $r$.
A replacement is uniform of rank $u<a$. At other layers its update only
deletes edges. In layer $u$, the old proper link has weight less than
$1/(4r)$ by minimality of $a$. A rejecting singleton family contributes
at most $p\le1/(4r)$ to such a link. For an accepting replacement, an empty
proper link has weight zero. A nonempty proper link forces $U$ to be
disjoint from $T$, and is the original link at the strictly larger seed
$T\cup U$, of weight less than $1/(4r)$ by maximality of $T$.
This proves preservation of the bound $1/(2r)$.

Use the potential $\Phi(G)=w_p(G^{<r})$. Summing the lower-layer link
bounds shows that for each nonempty inserted edge $E$,

$$
w_p(\{A\in G^{<r}:E\subsetneq A\})
=p^{|E|}w_p(\operatorname{strictLink}_{G^{<r}}E)
\le\tfrac12p^{|E|}.
$$

Every deleted old edge counted by $\Phi$ can be charged to an inserted
edge it contains.
The new edges are outside the old up-set, have rank below $r$, and
cannot equal old edges. Therefore

$$
\Phi(G_{\mathrm{new}})\ge\Phi(G)+\tfrac12w_p(F).
$$

Accepting increases $\Phi$ by at least $1/(8r)$ and adds at most $r$
vertices to $S$. Rejecting does not decrease $\Phi$ and keeps $S$.
The invariant $|S|\le8r^2\Phi(G)$ follows by induction.

Each active update strictly enlarges $\uparrow G$, a family with at most
$2^N$ members. Bounded-fuel recursion with $2^N+1$ rounds therefore reaches
a terminal state. This is a finite termination proof; the final theorem
does not require execution of an exponentially large search.
At termination,

$$
w_p(G)=p(N-|C(G)|)+w_p(G^{>1})\le pN,
$$

so $|S|\le8r^2pN$. Since $I$ remains independent, $I\subseteq C(G)$.
The final generated up-set contains the original one. Thus every edge
of $H_0[C(G)]$ contains an edge of $G$, which cannot be a singleton because
its vertices lie in $C(G)$. Accordingly $F=G^{>1}$ covers $H_0[C(G)]$,
has edges inside $C(G)$ of size at least two, and satisfies
$w_p(F)\le p|C(G)|$.

Replay the algorithm with input equal to its final fingerprint $S$.
Every originally accepted seed lies in $S$. Every originally rejected
seed fails to lie in $I$, hence also fails to lie in $S\subseteq I$.
Induction gives the same state and next query at every round.
The complete output, and hence its container, is determined by $S$ alone.
The finite family of actual fingerprints of all independent inputs, mapped
under this reconstruction, covers every independent set.

## 5. Shrinking, full tree and count

Apply the finite theorem with $r=k$ to the chunk hypergraph on $X$.
For a resulting container $C$ and light cover $F$, an edge $E\in F$ with
$|E|>k$ has degree zero. All other cover edges have size at least two,
so the proved codegree bounds imply

$$
p\,e(H[C])
\le\sum_{E\in F}p\,\deg_H(E)
\le\frac e{4N}\sum_{E\in F}p^{|E|}
\le\frac e{4N}p|C|\le\frac14pe.
$$

It follows that $e(H[C])\le e/4$. Each edge lost by restriction contains
a deleted vertex. Thus

$$
\tfrac34e\le(N-|C|)\Delta_1(H)
\le(N-|C|)\frac{10ke}N.
$$

Since $e>0$, $|C|\le(1-\delta)N$ for $\delta=3/(40k)$.
The fingerprint bound is $|S|\le8k^2pN\le24k^2q/L$.
Put

$$
M=\left\lfloor\frac{24k^2q}{L}\right\rfloor,\quad
B=(q^2+1)^{M+1},\quad D=\lceil40k\log q\rceil+1.
$$

A finite insertion recursion bounds the number of subsets of at most $M$
vertices by $(N+1)^{M+1}\le B$. Deterministic reconstruction bounds each
node's entire child family by $B$.

Start the tree at $V$. A node of size at most $2kq$ has one self-child;
every other node is replaced by its full shrinking family.
Induction proves covering of all $k$-arcs at every level, and at most
$B^d$ nodes at depth $d$.
A branch still nonterminal at depth $D$ has size at most

$$
(1-\delta)^Dq^2\le e^{-\delta D}q^2\le q\le2kq,
$$

using $\delta D\ge3\log q\ge\log q$.
Every final container is therefore small. For $\log q\ge1$,

$$
\log|\mathcal C|
\le D(M+1)\log(q^2+1)
\le3(40k+2)\left(\frac{24k^2q}{\log q}+(\log q)^2\right).
$$

The last expression divided by $q$ tends to zero for fixed $k$.
Consequently, for every $\varepsilon>0$ and sufficiently large prime $q$,
there is an actual finite family $\mathcal C$ satisfying

$$
\forall I\text{ a }k\text{-arc}\ \exists C\in\mathcal C,\ I\subseteq C,
\qquad(\forall C\in\mathcal C,\ |C|\le2kq),
\qquad|\mathcal C|\le e^{\varepsilon q}.
$$

The entire family is constructed before the random restriction.

## 6. One fair-bit space and both union bounds

Use $\Omega=\{0,1\}^V$, with every function equally likely, and let
$R_f=\{v:f(v)=1\}$. Probabilities are normalized finite counts.
The finite-sum product rule proves independence for events supported on
disjoint coordinate sets.

Fix $C\in\mathcal C$. Its incidence sum is at most $2kq(q+1)$, so at least
$q^2/2$ lines have $|C\cap\ell|<4k$. If any trace $C\cap\ell$ is empty,
$C\cap R_f$ cannot meet every line and its success probability is zero.

Otherwise consider the nonempty short traces. Each has at most $4k$ points,
and each point belongs to at most $q+1$ traces.
Each trace's intersection neighbourhood has at most $4k(q+1)$ members.
A maximum disjoint subfamily intersects every input trace, since otherwise
one more disjoint trace could be added. Counting these neighbourhoods
gives a disjoint packing of size $t$ with

$$
t\ge\frac{q^2}{8k(q+1)}\ge\frac q{16k}.
$$

For a selected trace of size $s\le4k$, its hit probability is
$1-2^{-s}\le1-2^{-4k}$. Since selected traces use disjoint coordinates,
putting $a_k=2^{-4k}$ and $c_k=a_k/(16k)>0$ gives

$$
\Pr[C\cap R_f\text{ meets every line}]
\le(1-a_k)^t\le e^{-a_kt}\le e^{-c_kq}.
$$

Choose the family estimate with $\varepsilon=c_k/2$.
The union bound over every container gives

$$
\Pr[\exists C\in\mathcal C:
 C\cap R_f\text{ meets every line}]
\le|\mathcal C|e^{-c_kq}\le e^{-c_kq/2}.
$$

For the second event, fix a line $\ell$ and put $X_\ell=|R_f\cap\ell|$.
Direct factorization of its finite moment sum gives

$$
\mathbb E e^{-tX_\ell}
=\left(\frac{1+e^{-t}}2\right)^q.
$$

For $t=\log(11/10)>0$, finite exponential Markov yields

$$
\Pr[X_\ell\le2q/5]
\le e^{(2q/5)t}\left(\frac{21}{22}\right)^q.
$$

Since $\log x\le x-1$ for $x>0$,
$t\le1/10$ and $\log(21/22)\le-1/22$. The exponent is at most

$$
q\left(\frac1{25}-\frac1{22}\right)
=-\frac{3q}{550}\le-\frac q{200}.
$$

All $q(q+1)$ lines are included in the second union bound:

$$
\Pr[\exists\ell:|R_f\cap\ell|\le2q/5]
\le q(q+1)e^{-q/200}.
$$

Both event families use the same $\Omega$.
Their total upper bound

$$
e^{-c_kq/2}+q(q+1)e^{-q/200}
$$

tends to zero for fixed $k$. Choose $q$ large enough that it is less than
one. The finite union bound proves existence of one sample avoiding both
events simultaneously; it needs neither conditioning nor independence
between the two families. Its retained set $R$ has

$$
|R\cap\ell|>2q/5\text{ for every line},\qquad
C\cap R\text{ fails to meet all lines for every }C\in\mathcal C.
$$

## 7. Keep all lines and extract the exact design

Require also $q\ge3n_0+5$. Use $R$ as ground set and retain the trace of
every affine line as a block, without discarding any lines.
Writing $n=|R|\le q^2$, we have

$$
|R\cap\ell|>\tfrac25q\ge\tfrac25\sqrt n.
$$

Since $q\ge5$, each trace has size strictly greater than two, hence at
least three. Two distinct lines cannot have the same trace, as that would
give them two common points. Thus all $q(q+1)$ lines yield distinct
actual blocks.
Every retained point pair still has its unique ambient line and unique
trace block. Distinct blocks meet in at most one point.
Any one trace also proves

$$
n\ge|R\cap\ell|>\tfrac25q
\ge\tfrac25(3n_0+5)>n_0.
$$

If a transversal $Q\subseteq R$ had all block intersections at most $K$,
then $|Q\cap\ell|\le K<K+2=k$ for every line, making $Q$ a $k$-arc.
Hence $Q\subseteq C$ for a container $C\in\mathcal C$.
Every point witnessing that $Q$ hits a block also witnesses that $C\cap R$
hits that line, contradicting the chosen sample's container-event exclusion.
Therefore every transversal has a block intersection larger than $K$.

There are primes above every finite threshold, completing the construction
for every natural $K,n_0$. `FiniteDesignTransport.lean` constructs the
bijections to `Fin n` and `Fin m`, preserving cardinalities and every
candidate transversal. Its uniqueness conclusion is uniqueness of a block
index, because the block enumeration is injective.

## 8. Real bounds and full original negations

For any real $K$, including negative values, let $J=\lceil K\rceil_+\in
\mathbb N$ be its nonnegative natural ceiling. After coercion,
$K\le J$. The natural construction for $J,n_0$ gives, for every transversal,

$$
K\le J<|Q\cap A_i|
$$

for some block. This is the explicit proof of
`exists_bad_fin_design_real`.
A supposed original positive assertion, applied at $c=2/5$ and its
claimed real $K$, would produce a transversal with all intersections at
most $K$ in this same design, a contradiction.
The source includes the natural versions, explicit two-fifths variants,
and both fully quantified real-bound original negations.

The arbitrary-bound result suffices to settle the original questions.
Nie's stronger $\log n/\log\log n$ rate is a mathematical source result,
rather than an endpoint claimed by this implementation. Actual
compilation, expanded statements and axiom dependencies are documented
by the selected release's verification records.
