#import "../../template.typ": *
#show: doc => template(doc, hidden: (), slides: false)

#let poly = math.op("poly")
#let ip(a, b) = $angle.l #a, #b angle.r$
#let ket(arg) = $#h(0.2pt) | #h(0.2pt) arg #h(0.2pt) angle.r$
#let bra(arg) = $angle.l #h(0.2pt) arg #h(0.2pt) | #h(0.2pt)$
#let braket(..args) = $angle.l #h(1pt) #args.pos().join(h(1pt) + "|" + h(1pt)) #h(1pt) angle.r$
#let Ket(arg) = $lr(| #h(1pt) arg #h(1pt) angle.r)$
#let Bra(arg) = $lr(angle.l #h(1pt) arg #h(1pt) |)$
#let Braket(..args) = $lr(angle.l #h(1pt) #args.pos().join(h(1pt) + "|" + h(1pt)) #h(1pt) angle.r)$
#let span = $op("span")$
#let conj(arg) = $arg^*$
#let expected(arg) = $angle.l arg angle.r$
#let vd(vector) = $bold(vector)$
#let nl = [\ ]
#let End = $"End"$
#let tp = $times.circle$
#let QFT = math.op("QFT")
#let Pr = math.op("Pr")
#let gen(..gens) = $angle.l #gens.pos().join(",") angle.r$
#let Aut = math.op("Aut")

#set terms(indent: 16pt)

= Hidden subgroup problem

== Review of Shor's algorithm

#definition[
    The *factoring problem* is: given a positive integer $N$, find a non-trivial factor ($!= 1, N$) in time polynomial in $n$ (i.e. $O(poly(n))$), where $n = O(log N)$ is the length of the description of the problem input (memory/space used to store it).
]<def:factoring-problem>
#definition[
    An *efficient problem* is one that can be solved in polynomial time.
]<def:efficient-problem>
#remark[
    Clasically, the best known factoring algorithm runs in $e^(O(n^(1\/3) (log n)^(2\/3)))$. Shor's algorithm (quantum) runs in $O(n^3)$ by converting factoring into period finding:
    - Given input $N$, choose $a < N$ which is coprime to $N$.
    - Define $f: ZZ -> ZZ\/N$, $f(x) = a^x mod N$. $f$ is periodic with period $r$ (the order of $a mod N$), i.e. $f(x + r) = f(x)$ for all $x in ZZ$. Finding $r$ allows us to factor $N$.
]

== Period finding

#problem("Periodicity Determination")[
    Given an oracle for $f: ZZ\/M -> ZZ\/N$ with promises:
    - $f$ is periodic with period $r < M$ (i.e. $forall x in ZZ\/M$, $f(x + r) = f(x)$),
    - $f$ is one-to-one in each period (i.e. $forall 0 <= x < y < r$, $f(x) != f(y)$),
    find $r$ in time $O(poly(m))$, where $m = O(log M)$.

    Clasically, this requires takes time $O\(sqrt(M)\)$.
]<prb:periodicity-determination>
#definition[
    Let $f: ZZ\/M -> ZZ\/N$. Let $H_M$ and $H_N$ be quantum state spaces with orthonormal state bases ${ket(i): i in ZZ\/N}$ and ${ket(j): j in ZZ\/M}$. Define the unitary *quantum oracle* for $f$ by $U_f$ by $
        U_f ket(x) ket(z) = ket(x) ket(z + f(x)).
    $ The first register $ket(x)$ is the *input register*, the last register $ket(z)$ is the *output register*.
]<def:quantum-oracle>
#definition[
    The *quantum query complexity* of an algorithm is the number of times it queries $f$ (i.e. uses $U_f$).
]<def:quantum-query-complexity>
#definition[
    The *quantum Fourier transform* over $ZZ\/M$ is the unitary defined by its action on the computational basis: $
        U_"QFT" ket(x) = 1/sqrt(M) sum_(y = 0)^(M - 1) omega^(x y) ket(y),
    $ where $omega = e^(2pi i\/M)$. Note that $U_"QFT"$ requires only $O\((log M)^2\)$ gates to implement, whereas a general unitary requires $O(4^n \/ n)$ elementary gates.
]<def:quantum-fourier-transform>
#lemma[
    Let $alpha = e^(2pi i y\/M)$. Then $
        sum_(j = 0)^(k - 1) alpha^j = cases(
            (1 - alpha^k)/(1 - alpha) = 0 & "if" alpha != 1 "i.e." M divides.not y,
            k & "if" alpha = 1 "i.e." M divides y
        ).
    $
]
#lemma("Boosting success probability")[
    If a process succeeds with probability $p$ on one trial, then $
        Pr("at least one success in" t "trials") = 1 - (1 - p)^t > 1 - delta
    $ for $t = log(1\/d)/p$.
]
#theorem("Co-primality Theorem")[
    The number of integers less than $r$ that are coprime to $r$ is $O(r\/log log r)$ for large $r$.
]
#algorithm("Quantum Period Finding")[
    Let $f: ZZ\/M -> ZZ\/N$ be periodic with period $r < M$ and one-to-one in each period. Let $A = M/r$ be the number of periods. We work over the state space $H_M tp H_N$.
    + Construct the state $1/sqrt(M) sum_(i = 0)^(M - 1) ket(i) ket(0)$.
    + Query $U_f$ on the state, giving $1/sqrt(M) sum_(i = 0)^(M - 1) ket(i) ket(f(i))$.
    + Measure second register in computational basis, giving outcome $y in ZZ\/N$, and input state collapses to $ket("per") = 1/sqrt(A) sum_(j = 0)^(A - 1) ket(x_0 + j r)$, where $f(x_0) = y$ and $0 <= x_0 < r$. TODO: add diagram showing amplitudes for this state.
    + Apply the Quantum Fourier Transform to $ket("per")$: $
        QFT ket("per") & = 1/sqrt(M) sum_(y = 0)^(M - 1) 1/sqrt(A) sum_(j = 0)^(A - 1) omega^((x_0 + j r) y) ket(y) \
        & = 1/sqrt(M A) sum_(y = 0)^(M - 1) omega^(x_0 y) sum_(j = 0)^(A - 1) omega^(j r y) ket(y) \
        & = sqrt(A/M) sum_(k = 0)^(r - 1) omega^(x_0 k M\/r) ket(k M\/r)
    $ Note now the outcomes and probabilities are independent of $x_0$, so carry useful information about $r$. TODO add diagram showing amplitudes for this state.
    + Measure $QFT ket("per")$, yielding outcome $c = k_0 M\/r$ for some $0 <= k_0 < r$. So $c/M = k_0/r$. If $k_0$ is corpime to $r$, then the denominator $r_0$ of the simplified fraction $c/M$ is equal to $r$.
    + By the coprimality theorem, the probability that $k_0$ is coprime to $r$ is $O(1\/log log r)$.
    + To check if the computed value $r_0$ of $r$ is correct, compute/query $U_f$ to check if $f(0) = f(r_0)$ (this works since $f$ is periodic and one-to-one in each period, and $r_0 <= r$).
    + Repeat the previous steps $O(log log r) = O(log log M) = O(log m)$ times. This obtains the correct value of $r$ with high probability.
]

== Analysis of QFT part of period finding algorithm

#notation[
    For $R = {0, r, ..., (A - 1)r} subset.eq ZZ\/M$ ($A r = M$), write $ket(R)$ for the uniform superposition of all computational basis states in $R$: $
        ket(R) = 1/sqrt(A) sum_(k = 0)^(A - 1) ket(k r).
    $
]
#definition[
    For each $x_0 in ZZ\/M$, define the lienar map by its action on the computational basis states: $
        U(x_0): H_M & -> H_M, \
        ket(k) & |-> ket(x_0 + k).
    $
]
#definition[
    Note that since $(ZZ\/M, +)$ is abelian, all $U(x_i)$ commute: $U(x_1) U(x_2) = U(x_1 + x_2) = U(x_2) U(x_1)$. Hence, they have a simultaneous basis of eigenvectors ${ket(chi_k): k in ZZ\/M}$, i.e. for all $k, x_0 in ZZ\/M$, $U(x_0) ket(chi_k) = w(x_0, k) ket(chi_k)$, where $abs(w(x_0, k)) = 1$. The $ket(chi_k)$ are called *shift-invariant states* and form an orthonormal basis for $H_M$. The $ket(chi_k)$ are given explicitly by $
        ket(chi_k) = 1/sqrt(M) sum_(ell = 0)^(M - 1) e^(-2pi i k ell\/M) ket(ell).
    $
]<def:quantum-fourier-characters>
#proposition[
    The explicit definition of the $ket(chi_k)$ indeed satisfies the property $forall k, x_0 in ZZ\/M$, $U(x_0) ket(chi_k) = w(x_0, k) ket(chi_k)$, and we have $w(x_0, k) = omega^(k x_0)$, where $omega = e^(2pi i\/M)$.
]
#proofhints[
    Straightforward.
]
#proof[
    We have that $
        U(x_0) ket(chi_k) & = 1/sqrt(M) sum_(ell = 0)^(M - 1) e^(-2pi i k ell\/M) ket(x_0 + ell) \
        & = 1/sqrt(M) sum_(tilde(l) = 0)^(M - 1) e^(-2pi i(tilde(l) - x_0) k\/M) ket(tilde(l)) \
        & = e^(2pi i k x_0 \/M) ket(chi_k) \
        & =: w(x_0, k) ket(chi_k)
    $
]
#remark[
    Let $U: H_M -> H_M$ be the unitary mapping the shift-invariant basis to the computational basis: $U: ket(chi_k) |-> ket(k)$. The matrix representation of $U^(-1)$ with respect to the computational basis has entries $
        (U^(-1))_(j k) = braket(j, U^(-1), k) = braket(j, chi_k) = 1/sqrt(M) e^(-2pi i j k\/M)
    $ So the matrix representation of $U$ with respect to the same basis has entries $U_(k j) = overline((U^(-1))_(j k)) = 1/sqrt(M) e^(2pi i j k\/M)$. Hence, we have $
        U ket(k) = 1/sqrt(M) sum_(j = 0)^(M - 1) e^(2pi i j k\/M) ket(j),
    $ and so $U$ is precisely the QFT $mod M$.
]

== The hidden subgroup problem (HSP)

#problem([Discrete Logarithm Problem (DLP) on $ZZ\/p^times$])[
    Let $p$ be prime.
    / Input: $g, x in ZZ\/p^times$.
    / Promise: $g$ is a generator of $ZZ\/p^times$.
    / Task: Find $log_g x$, i.e. find $L in ZZ\/(p - 1)$ such that $x = g^L$.
]<prb:dlp>
#notation[
    Write $[n]$ for ${1, ..., n}$. Write e.g. $i j$ for the set ${i, j}$.
]
#definition[
    Let $Gamma_1 = ([n], E_1)$ and $Gamma_2 = ([n], E_2)$ be (undirected) graphs. $Gamma_1$ and $Gamma_2$ are *isomorphic* if there exists a permutation $pi in S_n$ such that for all $1 <= i, j < n$, $i j in E$ iff $pi(i) pi(j) in E$.
]<def:graph.isomorphic>
#definition[
    Let $Gamma = ([n], E)$ be a graph. The *automorphism group* of $Gamma$ is $
        Aut(Gamma) = {pi in S_n: i j in E "iff" pi(i) pi(j) in E quad forall i, j in [n]}.
    $ $Aut(Gamma)$ is a subgroup of $S_n$, and $pi in Aut(Gamma)$ iff $pi$ leaves $Gamma$ invariant as a labelled graph.
]<def:graph-automorphism-group>
#definition[
    The *adjacency matrix* of a graph $Gamma = (V, E)$ is the $n times n$ matrix $M_A$ defined by its entries: $
        (M_A)_(i j) := cases(
            1 quad & "if" i j in E,
            0 & "otherwise"
        ).
    $
]<def:adjacency-matrix>
#problem("Graph Isomorphism Problem")[
    / Input: Adjacency matrices $M_1$ and $M_2$ of graphs $Gamma_1 = ([n], E_1)$ and $Gamma_2 = ([n], E_2)$.
    / Task: Determine whether $Gamma_1$ and $Gamma_2$ are isomorphic.
]<prb:graph-isomorphism>
#remark[
    The best known classical algorithm for solving the graph isomorphism problem has quasi-polynomial time complexity $n^(O((log n)^2))$.
]
#problem("Hidden Subgroup Problem (HSP)")[
    Let $G$ be a finite group.
    / Input: An oracle for a function $f: G -> X$.
    / Promise: There is a subgroup $K < G$ such that:
        + $f$ is constant on the (left) cosets of $K$ in $G$.
        + $f$ takes a different value on each coset.
    / Task: Determine $K$.
]
#remark[
    - To find $K$, we either find a generating set for $K$, or sample a uniformly random element from $K$.
    - We want to determine $K$ with high probability in $O(poly log |G|)$ queries. Using $O(|G|)$ queries is easy, as we just query all values $f(g)$ and find the "level sets" (sets where $f$ is constant).
]
#example[
    The following problems are special cases of HSP:
    - The period finding problem: $G = ZZ\/M$, $K = gen(r) = {0, r, ..., (A - 1)r}$. The cosets are $x_0 + K = {x_0, x_0 + r, ..., x_0 + (A - 1) r}$ for each $0 <= x_0 < r$.
    - The DLP on $(ZZ\/p)^times$: let $f: ZZ\/(p - 1) times ZZ\/(p - 1) -> (ZZ\/p)^times$ be defined by $f(a, b) = g^a x^(-b) = g^(a - L b)$. $G = ZZ\/(p - 1) times ZZ\/(p - 1)$, the hidden subgroup is $K = {lambda (L, 1): lambda in ZZ\/(p - 1)}$. (Note that if we know $K$, we can pick any $(c, d) = (lambda L, lambda) in G$ and compute $L = c/d$ to find $L$.)
    - The graph isomorphism problem: $G = S_n$, hidden subgroup is $K = Aut(G)$. Let $f_Gamma: S_n -> X$ where $X$ is set of adjacency matrices of labelled graphs on $[n]$, defined by $f_Gamma (pi) = pi(A)$. Note $abs(S_n) = abs(G) = n!$, so $log abs(G) approx n log n$, so $O(poly log abs(G)) = O(poly n)$.
]
#definition[
    An *irreducible representation (irrep)* of a finite abelian group $G$ is a homomorphism $chi: G -> CC^times$.
]<def:irrep>
#theorem[
    - Let $chi: G -> CC^times$ be an irrep. For all $g in G$, $chi(g)$ is a $abs(G)$-th root of unity.
    - There are always exactly $abs(G)$ distinct irreps. In particular, we can label each irrep uniquely by some $g in G$.
]
#theorem("Schur's Lemma")[
    Let $chi_i$ and $chi_j$ be irreps of $G$. Then $
        1/abs(G) sum_(g in G) chi_i (g) overline(chi_j) (g) = delta_(i j).
    $
]<thm:schurs-lemma>
#example[
    $chi_0: G -> CC^times$, $chi_0(g) = 1$ is the *trivial irrep*. Note that for any $chi_i != chi_0$, $sum_(g in G) chi_i (g) = 0$ by Schur's lemma.
]
#definition[
    For finite abelian $G$, we define the *shift operators* on $H_abs(G)$ for each $k in G$ by $
        U(k): H_abs(G) & -> H_abs(G), \
        ket(g) & |-> ket(k + g).
    $ Note that since $G$ is abelian, the $U(k)$ commute: $U(k) U(l) = U(l) U(k)$ for all $k, l in G$. Hence, they have simultaneous eigenstates, which gives an orthonormal basis for $H_abs(G)$.
]
#proposition[
    For each $k in G$, consider the state $
        ket(chi_k) = 1/sqrt(abs(G)) sum_(g in G) overline(chi_k (g)) ket(g).
    $ The $ket(chi_k)$ are shift-invariant (invariant up to a phase under the action of all $U(g)$, $g in G$).
]
#proofhints[
    Straightforward.
]
#proof[
    - Note that $overline(chi_k (g)) = chi_k (-g)$.
    - We have $
        U(g_0) ket(chi_k) & = 1/sqrt(abs(G)) sum_(g in G) overline(chi_k (g)) ket(g_0 + g) \
        & = 1/sqrt(abs(G)) sum_(g' in G) overline(chi_k (g' - g_0)) ket(g') \
        & = 1/sqrt(abs(G)) sum_(g' in G) overline(chi_k (g')) chi_k (g_0) ket(g') \
        & = chi_k (g_0) ket(chi_k).
    $
]
#definition[
    The *quantum Fourier transform (QFT)* on $H_abs(G)$ is the unitary implementing the change of basis from the shift-invariant states ${ket(chi_g): g in G}$ to the computational basis ${ket(g): g in G}$.

    Note that $QFT^(-1) ket(g) = ket(chi_g)$. So $(QFT^(-1))_(k g) = braket(k, chi_g) = 1/sqrt(abs(G)) overline(chi_g (k))$, so $QFT_(k g) = 1/sqrt(abs(G)) chi_k (g)$. So the explicit form is $
        QFT ket(g) = 1/sqrt(abs(G)) sum_(k in G) chi_k (g) ket(k).
    $
]
#example[
    - For $G = ZZ\/M$, we can check that $chi_a (b) = e^(2pi i a b\/M)$ are irreps. So the irreps of $ZZ\/M$ are naturally labelled by $a in ZZ\/M$ and this gives the usual $QFT mod M$ as defined earlier.
    - Similarly, for $G = ZZ\/(M_1) times dots.c times ZZ\/(M_r)$, $chi_g (h) = e^(2pi i (g_1 h_1 \/M_1 + dots.c + g_r h_r \/M_r))$ are the irreps.
]
#algorithm([Quantum HSP solver for finite abelian $G$])[
    - We work in the state space $H_abs(G) tp H_abs(X)$.
    - Prepare the state $
        1/sqrt(abs(G)) sum_(g in G) ket(g) ket(0)
    $
    - Query $f$ on the state, giving $
        1/sqrt(abs(G)) sum_(g in G) ket(g) ket(f(g))
    $
    - Measure the output register, yielding a uniformly random value $f(g_0)$ from $f(G)$. The state collapses to a *coset state* $
        ket(g_0 + K) = 1/sqrt(abs(K)) sum_(k in K) ket(g_0 + k).
    $
    - Apply QFT $mod thick abs(G)$, and measure the input register, yielding some $g in G$. We have $ket(K) = sum_(g in G) a_g ket(chi_g)$, so $ket(g_0 + K) = U(g_0) ket(K) = sum_(g in G) a_g chi_g (g_0) ket(chi_g)$. So applying QFT gives $sum_(g in G) a_g chi_g (g_0) ket(g)$, so probability of measuring outcome $k$ is $abs(a_k chi_k (g_0))^2 = abs(a_k)^2$. Now $
        QFT ket(K) & = 1/sqrt(abs(K)) sum_(k in K) QFT ket(k) \
        & = 1/sqrt(abs(G) abs(K)) sum_(g in G) (sum_(k in K) chi_g (k)) ket(g)
    $ Note that irreps of $G$ restricted to $K$ are irreps of $K$. The trivial irrep $chi_0: G -> CC$ remains the trivial irrep $chi_0$ for $K$. But there may be other irreps that become the trivial irrep on restriction to $K$. Hence $
        sum_(k in K) chi_g (k) = cases(
            abs(K) quad & "if" chi_g|_K = chi_0|_K,
            0 & "otherwise"
        )
    $ Hence $
        QFT ket(K) = sqrt(abs(K)/abs(G)) sum_(g in G \ chi_g|_K = chi_0|_K) ket(g)
    $ and measuring in the computational basis on this state yields random $g in G$ such that $forall k in K$, $chi_g (k) = 1$.

    If $K$ has generators $k_1, ..., k_m$ (note that for an arbitrary group, we have $m = O(log abs(G))$), then we have a set of equations $chi_g (k_i) = 1$ for all $i in [m]$. We can show that $O(log abs(G))$ such $g$ are drawn uniformly at random, then with probability at least $2\/3$, we have enough equations to determine $k_1, ..., k_m$.
]
#example[
    Let $G = ZZ\/M_1 times dots.c times ZZ\/M_r$. The irreps are $chi_g (h) = e^(2pi i (g_1 h_1 \/ M_1 + dots.c + g_r h_r \/ M_r))$. For $k in K$, $chi_g (k) = 1$ iff $(g_1 k_1)/M_1 + dots.c + (g_r k_r)/M_r = 0 mod 1$. This is a homogenous linear equation in $k$, and $O(log abs(G))$ independent such equations determine $K$ as the nullspace.
]
#remark[
    We can implement QFT over abelian groups (and some non-abelian groups, including $S_n$) using circuits with $O((log abs(G))^2)$ elementary gates.

    In the non-abelian case, we can still easily prepare coset states with one query to $f$. But the shift operators $U(g_0)$ no longer commute, so we don't have a (canonical) shift-invariant basis.
]
#definition[
    A *$d$-dimensional unitary representation* of a finite group $G$ is a homomorphism $
        chi: G -> U(d)
    $ where $U(d)$ is the group of $d times d$ unitary matrices.
]<def:unitary-representation>
#definition[
    A $d$-dimensional unitary representation $chi$ of $G$ is *irreducible* if no non-trivial subspace of $CC^d$ is invariant under the action of $\{chi(g_1), ..., chi\(g_(abs(G))\)\}$ (i.e. we cannot simultaneously block diagonalise all the $chi(g)$ matrices by a basis change).
]<def:unitary-representation.irreducible>
#definition[
    A set of irreps ${chi_1, ..., chi_m}$ is a *complete set of irreps* if each $chi_i, chi_j$ are unitarily equivalent to each other, i.e. for some $V in U(d)$, $forall g in G, chi_i (g) = V chi_j (g) V^dagger$.
]<def:complete-irreps>
#theorem[
    Let the dimensions of a complete set of irreps $chi_1, ..., chi_m$ be $d_1, ..., d_m$. Then $d_1^2 + dots.c + d_m^2 = abs(G)$.
]
#theorem("Schur Orthogonality")[
    Let $chi_1, ..., chi_m$ be a complete set of irreps for $G$, and $i, j, k in [m]$. Then $
        sum_(g in G) chi_(i, j, k) chi_(i, j, k)(g) overline(chi_(i', j', k')(g)) = abs(G) delta_(i i') delta_(j j') delta_(k k').
    $
]