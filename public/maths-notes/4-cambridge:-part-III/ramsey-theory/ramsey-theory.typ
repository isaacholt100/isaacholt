#import "../../template.typ": *
#show: doc => template(doc, hidden: (), slides: false)

#let clr(c) = [
    #set text(fill: eval(c))
    #c
]
#let Clr(c) = smallcaps(c)
#set align(left)

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
#theorem("Ramsey's Theorem for Pairs")[
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
#theorem([Ramsey's Theorem for $r$-sets])[
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
#theorem("Finite Ramsey")[
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
#theorem("Canonical Ramsey")[
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
    We want to show that for any $2$-colouring of $NN$, we can find a monochromatic arithmetic progression of length $m$ for any $m in NN$. By compactness, this is equivalent to showing that for all $m in NN$, there exists $n in NN$ such that for any $2$-colouring of $[n]$, there exists a monochromatic arithmetic progression of length $m$. (If not, then for each $n in NN$, there is a colouring $c_n: [n] -> {1, 2}$ with no monochromatic arithmetic progression of length $m$. Infinitely many of these colourings agree on $[1]$, infinitely many of those agreeing in $[1]$ agree on $[2]$, and so on - we obtain a $2$-colouring of $NN$ with no monochromatic arithmetic progression of length $m$).

    We will prove a slightly stronger result: whenever $NN$ is $k$-coloured, there exists a length $m$ monochromatic arithmetic progression, i.e. for any $k, m in NN$, there exists $n in NN$ such that whenever $[n]$ is $k$-coloured, we have a length $m$ monochromatic progression.
]
#definition[
    Let $A_1, ..., A_k$ be length $m$ arithmetic progressions: $A_i = {a_i, a_i + d_i, ..., a_i + (m - 1)d_i}$. $A_1, ..., A_k$ are *focussed* at $f$ if $a_i + m d_i = f$ for all $i$.
]<def:arithmetic-progression.focussed>
#example[
    ${4, 8}$ and ${6, 9}$ are focussed at $12$.
]
#definition[
    If length $m$ arithmetic progressions $A_1, ..., A_k$ are focused at $f$ and are monochromatic, each with a different colour (for a given colouring), they are called *colour-focussed* at $f$.
]<def:arithmetic-progression.colour-focussed>
#remark[
    We use the idea that if $A_1, ..., A_k$ are colour-focussed at $f$ (for a $k$-colouring) and of length $m - 1$, then some $A_i union {f}$ is a length $m$ monochromatic arithmetic progression.
]
#theorem[
    Whenever $NN$ is $k$-coloured, there exists a monochromatic arithmetic progression of length $3$, i.e. for all $k in NN$, there exists $n in NN$ such that any $k$-colouring of $[n]$ admits a length $3$ monochromatic progression.
]
#proofhints[
    - Prove by induction the claim: $forall r <= k$, $exists n in NN$ such that for any $k$-colouring of $[n]$, there exists a monochromatic arithmetic progression of length $3$, or $r$ colour-focussed arithmetic progressions of length $2$.
        - $r = 1$ case is straightforward.
        - Let claim be true for $r - 1$ with witness $n$, let $N = 2n(k^(2n) + 1)$.
        - Partition $N$ into blocks of equal size, show that two of these blocks must have the same colouring.
        - Using the inductive hypothesis, merge the $r - 1$ colour-focussed arithmetic progressions from these two blocks into a new set of $r - 1$ colour-focussed arithmetic progressions.
        - Find another length $2$ monochromatic arithmetic progression, reason that this is of different colour.
    - Reason that this claim implies the result.
]
#proof[
    - We claim that for all $r <= k$, there exists an $n in NN$ such that if $[n]$ is $k$-coloured, then either:
        - There exists a monochromatic arithmetic progression of length $3$.
        - There exist $r$ colour-focussed arithmetic progressions of length $2$.
    - This claim implies the result by the above remark.
    - We prove the claim by induction on $r$:
        - $r = 1$: take $n = k + 1$, then by pigeonhole, some two elements of $[n]$ have the same colour, so form a length two arithmetic progression.
        - Assume true for $r - 1$ with witness $n$. We claim that $N = 2n (k^(2n) + 1)$ works for $r$.
        - Let $c: [2n (k^(2n) + 1)] -> [k]$ be a colouring. We partition $[N]$ into $k^(2n) + 1$ blocks of size $2n$: $B_i = {2n(i - 1) + 1, ..., 2n i}$ for $i = 1, ..., k^(2n) + 1$.
        - Assume there is no length $3$ monochromatic progression for $c$. By inductive hypothesis, each block $B_i$ has $r - 1$ colour-focussed arithmetic progressions of length $2$.
        - Since $|B_i| = 2n$, each block also contains their focus. For a set $M$ with $|M| = 2n$, there are $k^(2n)$ ways to $k$-colour $M$. So by pigeonhole, there are blocks $B_s$ and $B_(s + t)$ that have the same colouring.
        - Let ${a_i, a_i + d_i}$ be the $r - 1$ arithmetic progressions in $B_s$ colour-focussed at $f$, then ${a_i + 2n t, a_i + d_i + 2n t}$ is the corresponding set of arithmetic progressions in $B_(s + t)$, each colour-focussed at $f + 2n t$.
        - Now ${a_i, a_i + d_i + 2n t}$, $i in [r - 1]$, are $r - 1$ arithmetic progresions colour-focused at $f + 4 n t$. Also, ${f, f + 2n t}$ is monochromatic of a different colour to the $r - 1$ colours used (since there is no length $3$ monochromatic progression for $c$). Hence, there are $r$ arithmetic progressions of length $2$ colour-focussed at $f + 4 n t$.
]
#remark[
    The idea of looking at all possible colourings of a set is called a *product argument*.
]
#definition[
    The *Van der Waerden* number $W(k, m)$ is the smallest $n in NN$ such that for any $k$-colouring of $[n]$, there exists a monochromatic arithmetic progression in $[n]$ of length $m$.
]
#remark[
    The above theorem gives a *tower-type* upper bound $W(k, 3) <= k^(k^(dots.up)^(k^(4k)))$.
]
#theorem("Van der Waerden's Theorem")[
    For all $k, m in NN$, there exists $n in NN$ such that for any $k$-colouring of $[n]$, there is a length $m$ monochromatic arithmetic progression.
]
#proofhints[
    - Use induction on $m$.
    - Given induction hypothesis on $m - 1$, prove the claim: for all $r <= k$, there exists $n in NN$ such that for any $k$-colouring of $[n]$, we have either a monochromatic length $m$ arithmetic progression, or $r$ colour-focussed arithmetic progressions of length $m - 1$. Reason that this claim implies the result.
    - Use induction on $r$. Give an explicit $n$ for $r = 1$.
    - Let $n$ be the witness for $r - 1$, let $N = W(k^(2n), m - 1) dot 2n$. Assume a $k$-colouring of $[N]$, $c: [N] -> [k]$, has no arithmetic progressions of length $m$.
    - Partition $[N]$ into the obvious choice of $W(k^(2n), m - 1)$ blocks $B_i$, each of length $2n$.
    - Colour the indices $1 <= i <= W(k^(2n), m - 1)$ of the blocks by $
        c'(i) = (c(2n(i - 1) + 1), c(2n(i - 1) + 2) ...., c(2n i))
    $
    - Reason that we can find monochromatic arithmetic progression $s, s + t, ..., s + (m - 2)t$ of length $m - 1$ (w.r.t $c'$), and that this corresponds to sequence of blocks $B_s, B_(s + t), ..., B_(s + (m - 2)t)$, each identically coloured.
    - Reason that $B_s$ contains $r - 1$ colour-focussed length $m - 1$ arithmetic progressions $A_i$ together with their focus $f$.
    - Let $A'_i$ be the same arithmetic progression but with common difference $2n t$ larger than that of $A_i$. Show the $A'_i$ are colour-focussed at some focus in terms of $f$.
    - Find another length $m - 1$ arithmetic progression, show this must be monochromatic and of different colour to all $A'_i$. Show it also has same focus as all $A'_i$.
]
#proof[
    - By induction on $m$. $m = 1$ is trivial, $m = 2$ is by pigeonhole principle. $m = 3$ is the statement of the previous theorem.
    - Assume true for $m - 1$ and all $k in NN$.
    - For fixed $k$, we prove the claim: for all $r <= k$, there exists $n in NN$ such that for any $k$-colouring of $[n]$, either:
        - There is a monochromatic arithmetic progression of length $m$, or
        - There are $r$ colour-focussed arithmetic progressions of length $m - 1$.
    - We will then be done (by considering the focus).
    - To prove the claim, we use induction on $r$.
    - $r = 1$ is the claim of the first inductive hypothesis: take $n = W(k, m - 1)$.
    - Assume the claim holds for $r - 1$ with witness $n$, and assume there is no monochromatic arithmetic progression of length $m$. We will show that $N = W(k^(2n), m - 1) 2n$ is sufficient for $r$.
    - Partition $[N]$ into $W(k^(2n), m - 1)$ blocks of length $2n$: $B_i = {2n(i - 1) + 1, ..., 2n i}$ for $i = 1, ..., W(k^(2n), m- 1)$.
    - Each block has $k^(2n)$ possible colourings. Colour the blocks as $
        c'(i) = (c(2n(i - 1) + 1), c(2n(i - 1) + 2) ...., c(2n i))
    $ By definition of $W$, there exists a monochromatic arithmetic progression of length $m - 1$ (w.r.t. to $c'$): ${alpha, alpha + t, ..., alpha + (m - 2)t}$. The repsective blocks $B_alpha, ..., B_(alpha + (m - 2)t)$ are identically coloured.
    - $B_alpha$ has length $2n$, so by induction $B_alpha$ contains $r - 1$ colour-focussed arithmetic progressions of length $m - 1$, together with their focus (as length of block is $2n$).
    - Let $A_1, ..., A_(r - 1)$, $A_i = {a_i, a_i + d_i, ..., a_i + (m - 2)d_i}$, be colour-focussed at $f$.
    - Let $A'_i = {a_i, a_i + (d_i + 2n t), ..., a_i + (m - 2)(d_i + 2n t)}$ for $i = 1, ..., r - 1$. The $A'_i$ are monochromatic as the blocks are identically coloured and the $A_i$ are monochromatic. Also, $A_i$ and $A'_i$ have the same colouring, and the $A_i$ are colour-focussed, hence the $A'_i$ have pairwise distinct colours.
    - The $A_i$ are focussed at $f$ and the colour of $f$ of different than the colour of all $A_i$. $f = a_i + (m - 1)d_i$ for all $i$.
    - Now ${f, f + 2n t, f + 4n t, ..., f + 2n(m - 2)t}$ is an arithmetic progression of length $m - 1$, is monochromatic and of a different colour to all the $A'_i$.
    - It is enough to show that $a_i + (m - 1)(d_i + 2n t) = f + 2n(m - 1)t$ for all $i$, but this is equivalent to $a_i + (m - 1)d_i = f$, which is true as all $A_i$ were focussed at $f$.
]
#corollary[
    For any $k$-colouring of $NN$, there exists a colour class containing arbitrarily long arithmetic progressions.
]
#remark[
    We can't guarantee infinitely long arithmetic progressions, e.g.
    - $2$-colour $NN$ by $1$ red, $2, 3$ blue, $4, 5, 6$ red, etc.
    - The set of infinite arithmetic progressions in $NN$ is countable (since described by two integers: the start term and step). Enumerate them by $(A_k)_(k in NN)$. Pick $x_1 < y_1 in A_1$, colour $x_1$ red and $y_1$ blue. Then pick $x_2, y_2 in A_2$ with $y_1 < x_2 < y_2$, colour $x_2$ red, $y_2$ blue. Continue inductively.
]
#theorem("Strengthened Van der Waerden")[
    Let $m, k in NN$. There exists $n in NN$ such that for any $k$-colouring of $[n]$, there exists a monochromatic length $m$ arithmetic progression whose common difference is the same colour (i.e. there exists $a, a + d, ..., a + (m - 1), d$ all of the same colour).
]<thm:strengthened-van-der-waerden>
#proofhints[
    - Use induction on $k$.
    - If $n$ is the witness for $k - 1$ colours, show that $N = W(k, n(m - 1) + 1)$ is a witness for $k$ colours, by considering $n$ different multiples of the step of a suitable arithmetic progression.
]
#proof[
    - Fix $m in NN$. We use induction on $k$. $k = 1$ case is trivial.
    - Let $n$ be witness for $k - 1$ colours.
    - We will show that $N = W(k, n(m - 1) + 1)$ is suitable for $k$ colours.
    - If $[N]$ is $k$-coloured, there exists a monochromatic (say red) arithemtic progression of length $n(m - 1) + 1$: $a, a + d, ..., a + n(m - 1)d$.
    - If $r d$ is red for any $1 <= r <= n$, then we are done (consider $a, a + r d, ..., a + (m - 1)r d$).
    - If not, then ${d, 2d, ..., n d}$ is $k - 1$-coloured, which induces a $k - 1$ colouring on $[n]$. Therefore, there exists a monochromatic arithmetic progression $b, b + s, ..., b + (m - 1) s$ (with $s$ the same colour) by induction, which translates to $d b, d b + d s, ..., d b + d(m - 1)s$ and $d s$ being monochromatic. 
]
#remark[
    The case $m = 2$ of strengthened Van der Waerden is *Schur's theorem*: for any $k$-colouring of $NN$, there are monochromatic $x, y, z$ such that $x + y = z$. This can be proved directly from Ramsey's theorem for pairs: let $c: NN -> [k]$ be a $k$-colouring, then induce $c': NN^((2)) -> [k]$ by $c' (i j) = c(j - i)$. By Ramsey, there exist $i < j < k$ such that $c'(i j) = c'(i k) = c'(j k)$, i.e. $c(j - i) = c(k - i) = c(k - j)$. So take $x = j - i$, $z = k - i$, $y = k - j$.
]

== The Hales-Jewett theorem

#definition[
    Let $X$ be finite set. We say $X^n$ consists of *words of length $n$ on alphabet $X$*.
]<def:length-n-words>
#definition[
    Let $X$ be finite. A *(combinatorial) line* in $X^n$ is a set $L subset.eq X^n$ of the form $
        L = {(x_1, ..., x_n) in X^n: forall i in.not I, x_i = a_i "and" forall i, j in I, x_i = x_j }
    $ for some non-empty set $I subset.eq [n]$ and $a_i in X$ (for each $i in.not I$). $I$ is the set of *active coordinates* for $L$.

    Note that a combinatorial line is invariant under permutations of $X$.
]<def:combinatorial-line>
#example[
    Let $X = [3]$. Some lines in $X^2$ are:
    - $I = {1}$: ${(1, 1), (2, 1), (3, 1)}$ (with $a_2 = 1$), ${(1, 2), (2, 2), (3, 2)}$ (with $a_2 = 2$), ${(1, 3), (2, 3), (3, 3)}$ (with $a_2 = 3$).
    - $I = {2}$: ${(1, 1), (1, 2), (1, 3)}$ (with $a_1 = 1$), ${(2, 1), (2, 2), (2, 3)}$ (with $a_1 = 2$), ${(3, 1), (3, 2), (3, 3)}$ (with $a_1 = 3$).
    - $I = {1, 2}$: ${(1, 1), (2, 2), (3, 3)}$.
    Note that ${(1, 3), (2, 2), (3, 1)}$ is *not* a combinatorial line.
]
#example[
    Some sets of lines in $[3]^3$ are:
    - $I = {1}$: ${(1, 2, 3), (2, 2, 3), (3, 2, 3)}$ (with $a_2 = 2, a_3 = 3$).
    - $I = {1, 3}$: ${(1, 3, 1), (2, 3, 2), (3, 3, 3)}$ (with $a_2 = 3$).
]
#definition[
    In a line $L$, write $L^-$ and $L^+$ for the smallest and largest points in $L$ (with respect to the ordering on $[m]^n$ where $x <= y$ if $x_i <= y_i$ for all $i$).
]
#definition[
    Lines $L_1, ..., L_k$ are *focussed* at $f$ if $L_i^+ = f$ for all $i in [k]$. They are *colour-focussed* if they are focussed and $L_i \\ {L_i^+}$ is monochromatic for all $i in [k]$.
]
#example[
    In $[4]^2$, three lines colour-focussed at $f$ are shown below: TODO insert diagram.
]
#theorem("Hales-Jewett")[
    Let $m, k in NN$ (we use alphabet $X = [m]$), then there exists $n in NN$ such that for any $k$-colouring of $[m]^n$, there exists a monochromatic combinatorial line.
]
#proof[
    By induction on $m$. The case $m = 1$ is trivial as $abs([m]^n) = 1$. Assume that $"HJ"(m - 1, k')$ exists for all $k' in NN$. We claim that for all $1 <= r <= k$, there exists $n in NN$ such that for any $k$-colouring of $[m]^n$, we have either:
    - a monochromatic line, or
    - $r$ colour-focussed lines.
    We can then take $r = k$ and consider the focus.

    We prove the claim by induction on $r$. For $r = 1$, $n = "HJ"(m - 1, k)$ suffices. Let $n$ be a witness for $r - 1$. Let $n' = "HJ"(m - 1, k^(m^n))$. We will show $N = n + n'$ is suitable for $r$. Let $c: [m]^N -> [k]$ be a $k$-colouring with no monochromatic lines. Writing $[m]^N = [m]^n times [m]^(n')$, colour $[m]^(n')$ by $c': [m]^(n') -> [k]^(m^n)$, $c'(b) = (c(a_1, b), ..., c(a_(m^n), b))$ (where $[m]^n = {a_1, ..., a_(m^n)}$). By the inductive hypothesis, there eixsts a line $L$ with active coordinates $I$ such that $c(a, b) = c'(a, b')$ for all $a in [m]^n$ and for all $b, b' in L \\ {L^+}$. But now this induces a colouring $c'': [m]^n -> [k]$, $c''(a) = c(a, b)$ for any $b in L \\ {L^+}$. By definition of $n$, there exist $r - 1$ lines $L_1, ..., L_(r - 1)$ colour-focussed (w.r.t $c''$) at $f$, with active coordinates $I_1, ..., I_(r - 1)$.

    Finally, look at the lines that start at $(L_i^-, L^-)$ with active coordinates $I_i union I$, and at the line that starts at $(f, L^-)$ with active coordinate $I$. These are all focussed at $(f, L^+)$, so we are done.
]
#notation[
    Denote the smallest such $n$ by $"HJ"(m, k)$.
]
#corollary[
    Hales-Jewett implies Van der Waerden's theorem. 
]
#proofhints[
    For a colouring $c: NN -> [k]$, consider the induced colouring $c'(x_1, ..., x_n) = c(x_1 + dots.c + x_n)$ of $[m]^n$.
]
#proof[
    Let $c$ be a $k$-colouring of $NN$. For sufficiently large $n$ (i.e. $n >= "HJ"(m, k)$), induce a $k$-colouring $c'$ of $[m]^n$ by $c'(x_1, ..., x_n) = c(x_1 + dots.c + x_n)$. By Hales-Jewett, a monochromatic (with respect to $c'$) combinatorial line $L$ exists. This gives a monochromatic (with respect to $c$) length $m$ arithmetic progression in $NN$. The step is equal to the number of active coordinates. The first term in the arithmetic progression corresponds to the point in $L$ with all active coordinates equal to $1$, the last term corresponds to the point in $L$ with all active coordinates equal to $m$.
]
#exercise[
    Show that the $m$-in-a-row noughts and crosses game cannot be a draw in sufficiently high dimensions, and that the first player can always win.
]
#definition[
    A *$d$-dimensional subspace* (or *$d$-point parameter set*) $S subset.eq X^n$ is a set such that there exist pairwise disjoint $I_1, ..., I_d subset.eq [n]$ and $a_i in X$ for all $i in [n] - (I_1 union dots.c union I_d)$, such that $
        S = {x in X^n: & x_i = a_i quad forall i in [n] - (I_1 union dots.c union I_d), \ "and" & x_i = x_j quad forall i, j in I_k "for some" k in [d]}.
    $
]<def:combinatorial-subspace>
#theorem("Extended Hales-Jewett")[
    For all $m, k, d in NN$, there exists $n in NN$ such that for any colouring of $[m]^n$, there exists a monochromatic $d$-dimensional subspace.
]
#proof[
    We can view $X^(d n')$ as $(X^d)^(n')$. A line in $(X^d)^n'$ (on alphabet $Y = X^d$) corresponds to a $d$-dimensional subspace in $X^(d n')$ (on alphabet $X$). Hence, we can take $n = "HJ"(n^d, k)$.
]
#example[
    Let $X = [3]$, $d = 3$. $Y = [3]^3$. Up to rearranging the active coordinate indices, a line in $Y^n$ is (TODO look at scan).
]
#definition[
    Let $S subset.eq NN^d$ be finite. A *homothetic copy* of $S$ is a set of the form $a + lambda S$ where $a in NN^d$ and $lambda in NN$.
]
#theorem("Gallai")[
    Let $S subset.eq NN^d$ be finite. For every $k$-colouring of $NN^d$, there exists a monochromatic homothetic copy of $S$.
]
#proof[
    Let $S = {S_1, ..., S_m}$. Let $c: NN^d -> [k]$ be a $k$-colouring. For $n$ large enough (i.e. $n >= "HJ"(m, k)$), colour $[m]^n$ by $c(x_1, ..., x_n) = c(S_(x_1) + dots.c + S_(x_m))$. By Hales-Jewett, there exists a monochromatic line in $[m]^n$ with active coordinates $I$. So $c(sum_(i in.not I) S_i + abs(I) S_j)$ is the same colour for all $j in [m]$. So we are done, as $sum_(i in.not I) S_i + abs(I) S$ is a homothetic copy of $S$.
]


= Partition regular systems




= Euclidean Ramsey theory