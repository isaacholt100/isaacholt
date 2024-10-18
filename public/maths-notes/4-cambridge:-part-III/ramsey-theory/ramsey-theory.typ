#import "../../template.typ": *
#show: doc => template(doc, hidden: (), slides: false)

#let clr(c) = [
    #set text(fill: eval(c))
    #c
]
#let Clr(c) = smallcaps(c)

= Monochromatic sets

== Ramsey's theorem

#notation[
    $NN$ denotes the set of positive integers, $[n] = {1, ..., n}$, and $X^((r)) = {A subset.eq X: |A| = r}$. Elements of a set are written in ascending order, e.g. ${i, j}$ means $i < j$. Write e.g. $i j k$ to mean the set ${i, j, k}$ with the ordering (unless otherwise stated) $i < j < k$.
]
#definition[
    A *$k$-colouring* on $A^((r))$ is a function $c: A^((r)) -> [k]$.
]
#example[
    - Colour ${i, j} in NN^((2))$ red if $i + j$ is even and blue if $i + j$ is odd. Then $M = 2 NN$ is a monochromatic subset.
    - Colour ${i, j} in NN^((2))$ red if $max{n in NN: 2^n | (i + j)}$ is even and blue otherwise. $M = {4^n: n in NN}$ is a monochromatic subset.
    - Colour ${i, j} in NN^((2))$ red if $i + j$ has an even number of distinct prime divisors and blue otherwise. No explicit monochromatic subset is known.
]
#theorem(name: "Ramsey's Theorem for Pairs")[
    Let $NN^((2))$ are $2$-coloured by $c: NN^((2)) -> {1, 2}$. Then there exists an infinite monochromatic subset $M$.
]<thm:ramseys-theorem-for-pairs>
#proof[
    - Let $a_1 in A_0 := NN$. There exists an infinite set $A_1 subset.eq A_0$ such that $c(a_1, i) = c_1$ for all $i in A_1$.
    - Let $a_2 in A_1$. There exists infinite $A_2 subset.eq A_1$ such that $c(a_2, i) = c_2)$ for all $i in A_2$.
    - Repeating this inductively gives a sequence $a_1 < a_2 < dots.c < a_k < dots.c$ and $A_1 supset.eq A_2 supset.eq dots.c$ such that $c(a_i, j) = c_i$ for all $j in A_i$.
    - One colour appears infinitely many times: $c_(i_1) = c_(i_2) = dots.c = c_(i_k) = dots.c = c$.
    - $M = \{a_(i_1), a_(i_2), ...\}$ is a monochromatic set.
]
#remark[
    - The same proof works for any $k in NN$ colours.
    - The proof is called a "2-pass proof".
    - An alternative proof for $k$ colours is split the $k$ colours $1, ..., k$ into $2$ colours: $1$ and "$2 "or" ... "or" k$", and use induction.
]
#note[
    An infinite monochromatic set is *very* different from an arbitrarily large finite monochromatic set.
]
#example[
    Let $A_1 = {1, 2}$, $A_2 = {3, 4, 5}$, etc. Let ${i, j}$ be red if $i, j in A_k$ for some $k$. There exist arbitrarily large monochromatic red sets but no infinite monochromatic red sets.
]
#example[
    Colour ${i < j < k}$ red iff $i | (j + k)$. A monochromatic subset $M = {2^n: n in NN_0}$ is a monochromatic set.
]
#theorem(name: [Ramsey's Theorem for $r$-sets])[
    Let $NN^((r))$ be finitely coloured. Then there exists a monochromatic infinite set.
]
#proof[
    - $r = 1$: use pigeonhole principle.
    - $r = 2$: Ramsey's theorem for pairs.
    - For general $r$, use induction.
    - Let $c: NN^(r) -> [k]$ be a $k$-colouring. Let $a_1 in NN$, and consider all $r - 1$ sets of $NN \\ {a_1}$, induce colouring $c': (NN \\ {a_1})^((r - 1)) -> [k]$ via $c'(F) = c(F union {a_1})$.
    - By inductive hypothesis, there exists $A_1 subset.eq NN \\ {a_1}$ such that $c'$ is constant on it (taking value $c_1$).
    - Now pick $a_2 in A_1$ and induce a colouring $c': (A_1 \\ {a_2})^((r - 1)) -> [k]$ such that $c'(F) = c(F union {a_2})$. By inductive hypothesis, there exists $A_2 subset.eq A_1 \\ {a_2}}$ such that $c'$ is constant on it (taking value $c_2$).
    - Repeating this gives $a_1, a_2, ...$ and $A_1, A_2, ...$ such that $A_(i + 1) subset.eq A_i \\ {a_(i + 1)}$ and $c(F union {a_i}) = c_i$ for all $F subset.eq A_(i + 1)$, for $|F| = r - 1$.
    - One colour must appear infinitely many times: $c_(i_1) = c_(i_2) = dots.c = c$.
    - $M = {a_(i_1), a_(i_2), ...}$ is a monochromatic set.
]

== Applications of Ramsey's theorem

#example[
    In a totally ordered set, any sequence has monotonic subsequence.
]
#proof[
    - Let $(x_n)$ be a sequence, colour ${i, j}$ red if $x_i <= x_j$ and blue otherwise.
    - By Ramsey's theorem for pairs, $M = {i_1 < i_2 < dots.c}$ is monochromatic. If $M$ is red, then the subsequence $x_(i_1), x_(i_2), ...$ is increasing, and is strictly decreasing otherwise.
    - We can insist that $\(x_(i_j)\)$ is either concave or convex: $2$-colour $NN^((3))$ by colouring ${j < k < ell}$ #clr("red") if $(i, x_(i_j)), (j, x_(i_k)), (k, x_(i_ell))$ form a convex triple, and #clr("blue") if they form a concave triple. Then by Ramsey's theorem for $r$-sets, there is an infinite convex or concave subsequence.
]
#theorem(name: "Finite Ramsey")[
    Let $r, m, k in NN$. There exists $n in NN$ such that whenever $[n]^((r))$ is $k$-coloured, we can find a monochromatic set of size (at least) $m$.
]<thm:finite-ramsey>
#proof[
    - Assume not, i.e. $forall n in NN$, there exists colouring $c_n: [n]^((r)) -> [k]$ with no monochromatic $m$-sets.
    - There are only finitely many ($k$) ways to $k$-colour $[r]^((r))$, so there are infinitely many of colourings $c_r, c_(r + 1), ...$ that agree on $[r]^((r))$: $c_i |_([r]^((r))) = d_r$ for all $i$ in some infinite set $A_1$, where $d_r$ is a $k$-colouring of $[r]^((r))$.
    - Similarly, $[r + 1]^((r))$ has only finitely many possible $k$-colourings. So there exists infinite $A_2 subset.eq A_1$ such that for all $i in A_2$, $c_i |_([r + 1]^((r))) = d_(r + 1)$, where $d_(r + 1)$ is a $k$-colouring of $[r + 1]^((r))$.
    - Continuing this process inductively, we obtain $A_1 supset.eq A_2 supset.eq dots.c supset.eq A_n$. There is no monochromatic $m$-set for any $d_n: [n]^((r)) -> [k]$ (because $d_n = c_i|_([n]^((r)))$ for some $i$).
    - These $d_n$'s are nested: $d_ell|_([n]^((r))) = d_n$ for $ell > n$.
    - Finally, we colour $NN^((r))$ by the colouring $c: NN^((r)) -> [k]$, $c(F) = d_n (F)$ where $n = max(F)$ (or in fact $n >= max(F)$, which is well-defined by above). So $c$ has no monochromatic $m$-set (since $M$ was a monochromatic $m$-set, then taking $ell = max(M)$, $d_ell$ has a monochromatic $m$-set), which contradicts Ramsey's Theorem for $r$-sets.
]
#remark[
    - This proof gives no bound on $n = n(k, m)$, there are other proofs that give a bound.
    - It is a proof by compactness (essentially, we proved that ${0, 1}^NN$ with the product topology, i.e. the topology derived from the metric $d(f, g) = 1/min{n in NN: f(n) != g(n)}$, is sequentially compact).
]
#remark[
    Now consider a colouring $c: NN^((2)) -> X$ with $X$ potentially infinite. This does not necessarily admit an infinite monochromatic set, as we could colour each edge a different colour. Such a colouring would be injective. We can't guarantee either the colouring being constant or injective though, as $c(i j) = i$ satisfies neither.
]
#theorem(name: "Canonical Ramsey")[
    Let $c: NN^((2)) -> X$ be a colouring with $X$ an arbitrary set. Then there exists an infinite set $M subset.eq NN$ such that:
    + $c$ is constant on $M^((2))$, or
    + $c$ is injective on $M^((2))$, or
    + $c(i j) = c(k l)$ iff $i = k$ for all $i < j$ and $k < l$, $i, j, k, l in M$, or
    + $c(i j) = c(k l)$ iff $j = l$ for all $i < j$ and $k < l$, $i, j, k, l in M$.
]
#proofhints[
    - First consider the $2$-colouring $c_1$ of $NN^((4))$ where $i j k l$ is coloured #Clr("same") if $c(i j) = c(k l)$ and #Clr("diff") otherwise. Show that an infinite monochromatic set $M_1 subset.eq NN$ (why does this exist?) coloured #Clr("same") leads to case 1.
    - Assume $M_1$ is coloured #Clr("diff"), consider the $2$-colouring of $M_1^((4))$, which colours $i j k l$ #Clr("same") if $c(i l) = c(j k)$ and #Clr("diff") otherwise. Show an infinite monochromatic $M_2 subset.eq M_1$ (why does this exist?) must be coloured #Clr("diff") by contradiction.
    - Consider the $2$-colouring of $M_2^((4))$ where $i j k l$ is coloured #Clr("same") if $c(i k) = c(j l)$ and #Clr("diff") otherwise. Show an infinite monochromatic set $M_3 subset.eq M_2$ (why does this exist?) must be coloured #Clr("diff") by contradiction.
    - $2$-colour $M_3^((3))$ by: $i j k$ is coloured #Clr("same") if $c(i j) = c(j k)$ and #Clr("diff") otherwise. Show an infinite monochromatic set $M_4 subset.eq M_3$ (why does this exist) must be coloured #Clr("diff") by contradiction.
    - $2$-colour $M_4^((3))$ by the other two similar colourings to above, obtaining monochromatic $M_6 subset.eq M_5 subset.eq M_4$.
    - Consider 4 combinations of these colourings on $M_6$, show 3 lead to one of the cases in the theorem, and the other leads to contradiction.
]
#proof[
    - $2$-colour $NN^((4))$ by: $i j k l$ is red if $c(i j) = c(k l)$ and blue otherwise. By Ramsey's Theorem for $4$-sets, there is an infinite monochromatic set $M_1 subset.eq NN$ for this colouring.
    - If $M_1$ is red, then $c$ is constant on $M_1^((2))$: for all pairs $i j, i' j' in M_1^((2))$, pick $m < n$ with $j, j' < m$, then $c(i j) = c(m n) = c(i' j')$.
    - So assume $M_1$ is blue.
    - Colour $M_1^((4))$ by giving $i j k l$ colour green if $c(i l) = c(j k)$ and purple otherwise. By Ramsey's theorem for $4$-sets, there exists an infinite monochromatic $M_2 subset.eq M_1$ for this colouring.
    - Assume $M_2$ is coloured green: if $i < j < k < l < m < n in M_2$, then $c(j k) = c(i n) = c(l m)$ (consider $i j k n$ and $i l m n$): contradiction, since $M_1$ is blue.
    - Hence $M_2$ is purple, i.e. for $i j k l in M_2^((4))$, $c(i l) != c(j k)$.
    - Colour $M_2$ by: $i j k l$ is orange if $c(i k) = c(j l)$, and pink otherwise.
    - By Ramsey's theorem for $4$-sets, there exists infinite monochromatic $M_3 subset.eq M_2$ for this colouring.
    - Assume $M_3$ is orange, then for $i < j < k < l < m < n in M_3$, we have $c(j m) = c(l n)$ (consider $j l m n$) and $c(j m) = c(i k)$ (consider $i j k m$): contradiction, since $M_3 subset.eq M_1$.
    - Hence $M_3$ is pink, i.e. for $i j k l$, $c(i k) != c(j l)$.
    - Colour $M_3^((3))$ by: $i j k$ is yellow if $c(i j) = c(j k)$ and grey otherwise. By Ramsey's theorem for $3$-sets, there exists infinite monochromatic $M_4 subset.eq M_3$ for this colouring.
    - Assume $M_4$ is yellow: then (considering $i j k l in M_4^((4))$) $c(i j) = c(j k) = c(k l)$: contradiction, since $M_4 subset.eq M_1$.
    - So for any $i j k in M_4^((3))$, $c(i j) != c(j k)$.
    - Finally, colour $M_4^((3))$ by: $i j k$ is gold if $c(i j) = c(i k)$ and $c(i k) = c(j k)$, silver if $c(i j) = c(i k)$ and $c(i k) != c(j k)$, bronze if $c(i j) != c(i k)$ and $c(i k) = c(j k)$, and platinum if $c(i j) != c(i k)$ and $c(i k) != c(j k)$.
    - By Ramsey's theorem for $3$-sets, there exists monochromatic $M_5 subset.eq M_4$. $M_5$ cannot be gold, since then $c(i j) = c(j k)$: contradiction, since $M_5 subset.eq M_4$. If silver, then we have case 3 in the theorem. If bronze, then we have case 4 in the theorem. If platinum, then we have case 2 in the theorem.
]
#remark[
    - A more general result of the above theorem states: let $NN^((r))$ be arbitrarily coloured. Then we can find an infinite $M$ and $I subset.eq [r]$ such that for all $x_1 ... x_r in M^((r))$ and $y_1 ... y_r in M^((r))$, $c(x_1 ... x_r) = c(y_1 ... y_r)$ iff $x_i = y_i$ for all $i in I$.
    - In canonical Ramsey, $I = emptyset$ is case 1, $I = {1, 2}$ is case $2$, $I = {1}$ is case 3 and $I = {2}$ is case 4.
    - These $2^r$ colourings are called the *canonical colourings* of $NN^((r))$.
]
#exercise[
    Prove the general statement.
]

== Van der Waerden's theorem

#remark[
    We want to show that for any $2$-colouring of $NN$, we can find a monochromatic arithmetic progression of length $m$ for any $m in NN$. By compactness, this is equivalent to showing that for all $m in NN$, there exists $n in NN$ such that for any $2$-colouring of $[n]$, there exists a monochromatic arithmetic progression of length $m$. (If not, there for each $n$, there is a colouring $c_n: [n] -> {1, 2}$ with no monochromatic arithmetic progression of length $m$. Infinitely many agree on $[1]$, infinitely many agree on $[2]$, and so on - we obtain a $2$-colouring of $NN$ with no monochromatic arithmetic progression of length $m$).

    We will prove a slightly stronger result: whenever $NN$ is $k$-coloured, there exists a monochromatic arithmetic progression, i.e. for any $k, m in NN$, there exists $n in NN$ such that whenever $[n]$ is $k$-coloured, we have a length $m$ monochromatic progression.
]
#definition[
    Let $A_1, ..., A_k$ be length $m$ arithmetic progressions: $A_i = {a_i, a_i + d_i, ..., a_i + (m - 1)d_i}$. $A_1, ..., A_k$ are *focussed* at $f$ if $a_i + m d_i = f$ for all $i$.
]<def:arithmetic-progression.focussed>
#example[
    ${4, 8}$ and ${6, 9}$ are focussed at $12$.
]
#definition[
    If length $m$ arithmetic progressions $A_1, ..., A_k$ are focused at $f$ and are monochromatic with each a different colour (for a given colouring), they are called *colour-focussed* at $f$.
]<def:arithmetic-progression.colour-focussed>
#theorem[
    Whenever $NN$ is $k$-coloured, there exists a monochromatic arithmetic progression of length $3$, i.e. for all $k in NN$, there exists $n in NN$ such that any $k$-colouring of $[n]$ admits a length $3$ monochromatic progression.
]
#proof[
    - We claim that for all $r <= k$, there exists an $n$ such that if $[n]$ is $k$-coloured, then either:
        - There exists a monochromatic arithmetic progression of length $3$.
        - There exist $r$ colour-focussed arithmetic progressions of length $2$.
    - We prove the claim by induction on $r$:
        - $r = 1$: take $n = k + 1$, then by pigeonhole, some two elements of $[n]$ have the same colour, so form a length two arithmetic progression.
        - Assume true for $r - 1$ with witness $n$. We claim that $N = 2n (k^(2n) + 1)$ works for $r$.
        - Let $c: [2n (k^(2n) + 1)] -> [k]$ be a colouring. We partition $[N]$ into $k^(2n) + 1$ sets: $B_1 = {1, ..., 2n}$, $B_2 = {2n + 1, ..., 4n}$, ....
        - Assume there is no length $3$ monochromatic progression for $c$. By inductive hypothesis, each $B_i$ has $r - 1$ colour-focussed arithmetic progressions of length $2$.
        - Since $|B_i| = 2n$, each block also contains their focus. For a set $M$ with $|M| = 2n$, there are $k^(2n)$ ways to $k$-colour $M$. So by pigeonhole, there are blocks $B_s$ and $B_(s + t)$ that have the same colouring.
        - Let ${a_i, a_i + d_i}$ be the $r - 1$ colour-focussed arithmetic progressions in $B_s$, then ${a_i + 2n t, a_i + d_i + 2n t}$ is the corresponding set in $B_(s + t)$. Let $f$ be the focus in $B_s$, then $f + 2n t$ is the focus in $B_(s + t)$.
        - Now ${a_i, a_i + d_i + 2n t}$, $i in [r - 1]$, are $r - 1$ arithmetic progresions colour-focused at $f + 4 n t$. Also, ${f, f + 2n t}$ is monochromatic of a different colour to the $r - 1$ colours used. Hence, there are $r$ arithmetic progressions of length $2$ colour-focussed at $f + 4 n t$.
        - TODO finish proof.
]
#remark[
    The idea of looking at all possible colourings of a set is called a *product argument*.
]
#definition[
    The *Van der Waerden* number $W(k, m)$ is the smallest $n$ such that for any $k$-colouring of $[n]$, there exists a monochromatic arithmetic progression of length $m$.
]
#remark[
    The above theorem gives a tower-type upper bound $W(k, 3) <= k^(k^(dots.up)^(k^(4k)))$.
]


= Partition regular systems




= Euclidean Ramsey theory