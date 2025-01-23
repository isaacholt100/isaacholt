#import "../../template.typ": *
#let name-abbrvs = (
    "Rado": "Rado's Theorem",
    "Consistency": "Consistency Theorem"
)
#show: doc => template(doc, hidden: (), slides: false, name-abbrvs: name-abbrvs)
#set document(
    title: "Ramsey Theory Notes",
    author: "Isaac Holt",
    keywords: ("ramsey theory", "colourings")
)

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
    Lines $L_1, ..., L_k$ are *focussed* at $f$ if $L_i^+ = f$ for all $i in [k]$. They are *colour-focussed* if they are focussed and $L_i \\ {L_i^+}$ is monochromatic for all $i in [k]$, with each $L_i \\ {L_i^+}$ a different colour.
]<def:combinatorial-line.focussed>
#theorem("Hales-Jewett")[
    Let $m, k in NN$ (we use alphabet $X = [m]$), then there exists $n in NN$ such that for any $k$-colouring of $[m]^n$, there exists a monochromatic combinatorial line.
]<thm:hales-jewett>
#notation[
    Denote the smallest such $n$ by $"HJ"(m, k)$.
]
#proofhints[
    - Induction on $m$. Prove by induction the claim that for all $1 <= r <= k$, there exists $n in NN$ such that for any $k$-colouring of $[m]^n$, we have either a monochromatic line, or $r$ colour-focussed lines (reason that this claim implies the result).
    - State why claim holds for $r = 1$.
    - Let $n$ be witness for $r - 1$, $n' = "HJ"(m - 1, k^(m^n))$. Want to show that $n + n'$ is witness for $r$.
    - Write $[m]^(n + n') = [m]^n times [m]^n'$.
    - For a colouring $c: [m]^(n + n') -> [k]$, induce a suitable colouring $c': [m]^n' -> [k]^(m^n)$ and consider what the definition of $n'$ implies. Use this to induce a colouring $c'': [m]^n -> [k]$.
    - Using the inductive hypothesis and the previous point, construct $r - 1$ lines in $[m]^(n + n')$ which are colour-focussed. Find another line in $[m]^(n + n')$ (which should have first $n$ coordinates constant) of different colour which has the same focus point.
]
#proof[
    By induction on $m$. The case $m = 1$ is trivial as $abs([m]^n) = 1$. Assume that $"HJ"(m - 1, k')$ exists for all $k' in NN$. We claim that for all $1 <= r <= k$, there exists $n in NN$ such that for any $k$-colouring of $[m]^n$, we have either:
    - a monochromatic line, or
    - $r$ colour-focussed lines.
    We can then take $r = k$ and consider the focus.

    We prove the claim by induction on $r$. For $r = 1$, $n = "HJ"(m - 1, k)$ suffices. Let $n$ be a witness for $r - 1$. Let $n' = "HJ"(m - 1, k^(m^n))$. We will show $N = n + n'$ is a witness for $r$. Let $c: [m]^N -> [k]$ be a $k$-colouring with no monochromatic lines. Writing $[m]^N = [m]^n times [m]^(n')$, colour $[m]^(n')$ by $c': [m]^(n') -> [k]^(m^n)$, $c'(b) = (c(a_1, b), ..., c(a_(m^n), b))$ (where $[m]^n = {a_1, ..., a_(m^n)}$). By the inductive hypothesis, there exists a line $L$ in $[m]^n'$ with active coordinates $I$ such that $
        forall a in [m]^n, forall b, b' in L \\ {L^+}, quad c(a, b) = c(a, b').
    $ But now this induces a (well-defined) colouring $c'': [m]^n -> [k]$, $c''(a) = c(a, b)$ for any $b in L \\ {L^+}$. By definition of $n$, there exist $r - 1$ lines $L_1, ..., L_(r - 1)$ colour-focussed (w.r.t $c''$) at $f$, with active coordinates $I_1, ..., I_(r - 1)$.

    Finally, consider the $r - 1$ lines $L'_i$, $1 <= i <= r - 1$ in $[m]^N$ that start at $(L_i^-, L^-)$ with active coordinates $I_i union I$, and the line $L'$ in $[m]^N$ that starts at $(f, L^-)$ with active coordinates $I$. By the construction of $c''$, the colour of each point in $L'_i$ is determined by the first $n$ coordinates which form a point lying in $L_i$. Hence, since the $L_i$ are colour-focussed, the $L'_i$ are colour-focussed. As for $L'$, the first $n$ coordinates are constant (always equal to $f$), and so again by the construction of $c''$, the colour of each point in $L'$ is equal to $c''(f)$, which is a different colour to each colour of the $L'_i$. Hence all $L'_1, ..., L'_(r - 1), L'$ colour-focussed at $(f, L^+)$, so we are done.
]
#corollary[
    Hales-Jewett implies Van der Waerden's theorem. 
]<cor:hales-jewett-implies-van-der-waerden>
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
#example[
    Two $2$-dimensional subspaces in $X^3$ are ${(x, y, 2): x, y in X}$ ($I_1 = {1}, I_2 = {2}$) and ${(x, x, y): x, y in X}$ ($I_1 = {1, 2}, I_2 = {3}$).
]
#theorem("Extended Hales-Jewett")[
    For all $m, k, d in NN$, there exists $n in NN$ such that for any colouring of $[m]^n$, there exists a monochromatic $d$-dimensional subspace.
]<thm:extended-hales-jewett>
#proofhints[
    Use Hales-Jewett on $m^d$ and $k$.
]
#proof[
    We can view $X^(d n')$ as $(X^d)^(n')$. A line in $(X^d)^n'$ (on alphabet $Y = X^d$) corresponds to a $d$-dimensional subspace in $X^(d n')$ (on alphabet $X$). (Each inactive coordinate in the line corresponds to $d$ adjacent inactive coordinates in the subspace, and each active coordinate in the line corresponds to $d$ adjacent active coordinates in the subspace). Hence, we can take $n = d dot "HJ"(m^d, k)$.
]
#definition[
    Let $S subset.eq NN^d$ be finite. A *homothetic copy* of $S$ is a set of the form $a + lambda S$ where $a in NN^d$ and $lambda in NN$ ($l != 0$).
]
#theorem("Gallai")[
    Let $S subset.eq NN^d$ be finite. For every $k$-colouring of $NN^d$, there exists a monochromatic homothetic copy of $S$.
]
#proofhints[
    Let $S = {S_1, ..., S_m}$, consider colouring $c': [m]^n -> [k]$ (for suitable $n$) given by $c'(x_1, ..., x_n) = c\(S_(x_1), ..., S_(x_m))$.
]
#proof[
    Let $S = {S_1, ..., S_m}$. Let $c: NN^d -> [k]$ be a $k$-colouring. For $n$ large enough (i.e. $n >= "HJ"(m, k)$), colour $[m]^n$ by $c'(x_1, ..., x_n) = c(S_(x_1) + dots.c + S_(x_m))$. By Hales-Jewett, there exists a monochromatic line (with respect to $c'$) in $[m]^n$ with active coordinates $I$. So $c(sum_(i in.not I) S_i + abs(I) S_j)$ is the same colour for all $j in [m]$. So we are done, as $sum_(i in.not I) S_i + abs(I) S$ is a homothetic copy of $S$.
]
#remark[
    - Gallai's theorem can also be proven with a focussing + product colouring argument.
    - For $S = {(x, y) in NN^2: x, y in {1, 2}}$, Gallai's theorem proves the existence of a monochromatic square whereas extended Hales-Jewett only guarantees a monochromatic rectangle.
]


= Partition regular systems

== Rado's theorem

Strengthened Van der Waerden says that the system $x_1 + x_2 = y_1, x_1 + 2x_2 = y_2, ..., x_1 + m x_2 = y_m$ has a monochromatic solution in $x_1, x_2, y_1, ..., y_m$. We want to find when a general system of equations is partition regular.

#definition[
    Let $A in QQ^(m times n)$ be a $m times n$ matrix. $A$ is *partition regular (PR)* if for any finite colouring of $NN$, there exists a monochromatic $vd(x) in NN^n$ such that $A vd(x) = vd(0)$.
]<def:partition-regular-matrix>
#example[
    - Schur's theorem says that $x + y = z$ has a monochromatic solution for any finite colouring of $NN$, and so that $(1, 1, -1)$ is PR.
    - Strengthened Van der Waerden states that $
        mat(1, 1, -1, 0, ..., 0; 1, 2, 0, -1, ..., 0; dots.v, dots.v, dots.v, dots.v, dots.down, dots.v; 1, m, 0, 0, ..., -1)
    $ is PR.
    - $(a, b, -(a + b))$ is PR for any $a, b$ (a monochromatic solution is $x = y = z$).
    - $(2, -1)$ is not PR: colour $NN$ by $n$ is #clr("red") if $max{m in NN: 2^m | n}$ is even, and #clr("blue") otherwise. Then if $2x = y$, $x$ and $y$ must have different colours.
]
#definition[
    A rational matrix $A$ with columns $vd(c)_1, ..., vd(c)_n in QQ^m$ has the *column property (CP)* if there exists a partition $B_1 union.sq dots.c union.sq B_r$ of $[n]$ such that:
    + $sum_(i in B_1) vd(c)_i = vd(0)$.
    + For all $s in {2, ..., r}$, $sum_(i in B_s) vd(c)_i in span{vd(c)_j: j in B_1 union.sq dots.c union.sq B_(s - 1)}$ (note we can take the linear span over $RR$ or over $QQ$ here, as if a rational vector is a real linear combination of rational vectors, then it is also a rational linear combination of them).
]
#example[
    - $(1, 1, -1)$ has CP, with $B_1 = {1, 3}$, $B_2 = {2}$.
    - The matrix $
        mat(1, 1, -1, 0, ..., 0; 1, 2, 0, -1, ..., 0; dots.v, dots.v, dots.v, dots.v, dots.down, dots.v; 1, m, 0, 0, ..., -1)
    $ from Strengthened Van der Waerden has CP, with $B_1 = {1, 3, ..., n}$ and $B_2 = {2}$.
    - $(3, 4, -7)$ has CP with $B_1 = {1, 2, 3}$.
    - $(lambda, -1)$ has CP iff $lambda = 1$.
    - $(3, 4, -6)$ doesn't have CP.
]
#example[
    $
        mat(1, -1, 3; 2, -2, a; 4, -4, b)
    $ has CP iff $(a, b) = (6, 12)$.
]
#remark[
    $vd(x) = (a_1, ..., a_n)$ is PR iff $lambda vd(x)$ is PR (for any $lambda in QQ^times$), so we can assume that each $a_i in ZZ$. Also, $vd(x)$ has CP iff there exists $emptyset != I subset.eq [n]$ such that $sum_(i in I) a_i = 0$. We may also assume WLOG each $a_i != 0$. We will first show that if $vd(x)$ is PR, then it has CP. Even in the $1 times n$ matrix case of Rado's theorem, neither direction is easy.
]
#notation[
    For $p$ prime and $x = (a_k ... a_0)_p in NN$, write $e(x)$ for the rightmost non-zero digit in the base-$p$ expansion of $x$, i.e. $e(x) = a_(t(x))$, where $t(x) = min{i: a_i != 0}$.
]
#proposition[
    Let $a_1, ..., a_n in QQ^*$. If $(a_1, ..., a_n)$ is PR, then it has CP.
]<prop:pr-implies-cp-for-single-row-matrices>
#proofhints[
    For $p$ large enough (determine later a bound for $p$), colour $NN$ by giving $x$ colour $e(x)$, and consider $min{t(x_1), ..., t(x_n)}$.
]
#proof[
    Let $p$ be a large prime ($p > sum_(i = 1)^n abs(a_i)$). Define a $(p - 1)$-colouring of $NN$ giving $x$ colour $e(x)$. By assumption, there are $x_1, ..., x_n$ of the same colour $d$ such that $sum_(i = 1)^n a_i x_i = 0$. Let $t = min{t(x_1), ..., t(x_n)}$, and let $I = {i in [n]: t(x_i) = t}$ (note $I$ is non-empty). So when summing $sum_(i = 1)^n a_i x_i = 0$ and considering the last digit in the base $p$ expansion, we have $sum_(i = 1)^n a_i x_i = 0 mod p^(t + 1)$ and so obtain $sum_(i in I) a_i d = 0 mod p$, so $sum_(i in I) a_i = 0$ (since $p$ is prime and was chosen large enough).
]
#remark[
    There is no other known proof of this proposition.
]
#lemma[
    Let $lambda in QQ$. Then $(1, lambda, -1)$ is partition regular, i.e. for any finite colouring of $NN$, there exists monochromatic $(x, y, z) in NN^3$ such that $x + lambda y = z$.
]<lem:one-lambda-minus-one-is-pr>
#proofhints[
    - Reason that we can assume $lambda > 0$. Write $lambda = r\/s$, $r, s in NN$.
    - Use induction on number of colours $k$: given $n$ such that any $(k - 1)$-colouring of $[n]$ admits monochromatic solution, show that $N = W(k, n r + 1)n s$ works for $k$ colours, by considering the definition of $W$ and $i s d$ for eacah $i in [n]$.
]
#proof[
    The case $lambda = 0$ is trivial, and if $lambda < 0$, we may rewrite the equation as $z - lambda y = x$, so we may assume that $lambda > 0$, so let $lambda = r/s$ for $r, s in NN$. In fact, we show that for any $k$-colouring of $[n]$ (for some $n$ depending on $k$), there is a monochromatic solution.

    We seek a monochromatic solution to $x + r/s y = z$ for some finite colouring $c: NN -> [k]$. We use induction on the number of colours $k$. For $k = 1$, $n = max{s, r + 1}$ is sufficient, with monochromatic solution $(1, s, r + 1)$. Assume $n$ is a witness for $k - 1$ colours. We will show $N = n s W(k, n r + 1)$ is suitable for $k$ colours. By definition of $W$, given a $k$-colouring of $[N]$, there is a monochromatic AP inside $[W(k, n r + 1)] subset.eq [N]$ of length $n r + 1$: $a, a + d, ..., a + n r d$, coloured red.
    
    Consider $i s d$ for each $i in [n]$. Note that $i s d <= n s W(k, n r + 1)$ so each $i s d$ does indeed have a colour. If some $i s d$ is also red, then $(a, i s d, a + i r d)$ is a monochromatic solution. If no $i s d$ is red, then ${s d, ..., n s d}$ is $(k - 1)$-coloured, so by the inductive hypothesis, there exists $i, j, k in [n]$ such that ${i s d, j s d, k s d}$ is monochromatic and $i s d + lambda j s d = k s d$, so $(i s d, j s d, k s d)$ is a monochromatic solution.
]
#remark[
    - Note the similarity to the proof of Strengthened Van der Waerden.
    - The case $lambda = 1$ is Schur's theorem, which can be proven directly by Ramsey's theorem; however, there is no known proof using Ramsey's theorem for general $lambda in QQ$.
]
#theorem("Rado's Theorem for Single Equations")[
    Let $a_1, ..., a_n in QQ \\ {0}$. $(a_1, ..., a_n)$ is PR iff it has CP.
]
#proofhints[
    For $<==$: for the obvious choice of $I subset.eq [n]$, fix $i_0 in I$, and define $vd(x) in NN^n$ componentwise: $
        x_i = cases(
            x quad & "if" i = i_0,
            y & "if" i in.not I,
            z & "if" i in I \\ {i_0}
        ).
    $ Show that $vd(x)$ is a solution to $sum_(i = 1)^n a_i x_i = 0$.
]
#proof[
    $==>$ is by @prop:pr-implies-cp-for-single-row-matrices. For $<==$: we have that $sum_(i in I) a_i = 0$ for some $emptyset != I subset.eq [n]$. Given a colouring $c: NN -> [k]$, we need to show that there are monochromatic $x_1, ..., x_n$ such that $sum_(i = 1)^n a_i x_i = 0$.

    Fix $i_0 in I$. We construct the following vector $vd(x) in NN^n$ by defining its components: $
        x_i = cases(
            x quad & "if" i = i_0,
            y & "if" i in.not I,
            z & "if" i in I \\ {i_0}
        )
    $ for some fixed suitable $x, y, z$. We need $x, y, z$ to be monochromatic and $
        & a_(i_0) x + sum_(i in.not I) a_i y + sum_(i in I \\ {i_0}) a_i z & = 0 \
        <==> & a_(i_0) x - z a_(i_0) + sum_(i in.not I) a_i y & = 0 \
        <==> & x + (sum_(i in.not I) a_i)/(a_(i_0)) y - z & = 0
    $ and this holds, since $x, y, z$ exist by the above lemma.
]
#conjecture("Rado's Boundedness Conjecture")[
    Let $A$ be an $m times n$ matrix that is not PR (so there exists a "bad" colouring, i.e. a $k$-colouring with no monochromatic solution to $A vd(x) = vd(0)$ for some $k in NN$). Is $k$ bounded (for given $m, n$)?

    This is known for $1 times 3$ matrices: 24 colours suffice.
]<cjt:rado-boundedness>
#proposition[
    Let $A in QQ^(m times n)$. If $A$ is PR, then it has CP.
]<prop:pr-implies-cp>
#proofhints[
    - Let $vd(x) in NN^n$ be the monochromatic solution to $A vd(x) = vd(0)$. For fixed prime $p$, partition $[n]$ into $B_1, ..., B_r$ by grouping $i, j in [n]$ by $t(x_i), t(x_j)$ (and preserving the ordering).
    - Reason that the same partition exists for infinitely many $p$.
    - Considering $sum_(i = 1)^n x_i vd(c)_i = vd(0) mod p$ for infinitely many $p$, show that $sum_(i in B_1) vd(c)_i = 0$, and $
        p^t sum_(i in B_k) vd(c)_i + sum_(i in B_1, ..., B_(k - 1)) x_i d^(-1) vd(c)_i equiv vd(0) mod p^(t + 1).
    $
    - By taking the dot product with $vd(u) in NN^m$ for appropriate $u$, show by contradiction that $sum_(i in B_k) vd(c)_i in span{vd(c)_i: i in B_1, ..., B_(k - 1)}$.
]
#proof[
    Let $vd(c)_1, ..., vd(c)_n in QQ^m$ be the columns of $A$. For fixed prime $p$, colour $NN$ as before by $c(x) = e(x)$. By assumption, there exists a monochromatic $vd(x) in NN^n$ such that $sum_(i = 1)^n x_i vd(c)_i = vd(0)$. We partition the columns (by partitioning $[n] = B_1 union.sq dots.c union.sq B_r$) as follows:
    - $i, j in B_k$ iff $t(x_i) = t(x_j)$.
    - $i in B_k$, $j in B_ell$ for $k < ell$ iff $t(x_i) < t(x_j)$.
    We do this for infinitely many primes $p$. Since there are finitely many partitions of $[n]$, for infinitely many $p$, we will have the same blocks $B_1, ..., B_r$.
    
    Consider $sum_(i = 1)^n x_i vd(c)_i = vd(0)$ performed in base $p$. Each $i in [n]$ has the same colour $d = e(x_i) in [1, p - 1]$. So $sum_(i in B_1) d vd(c)_i = 0 mod p$ (by collecting the rightmost terms in base $p$), hence $sum_(i in B_1) c_i = 0 mod p$. But this holds for infinitely many $p$, hence $
        sum_(i in B_1) vd(c)_i = 0.
    $ Now $sum_(i in B_k) p^t d vd(c)_i + sum_(i in B_1, ..., B_(k - 1)) x_i vd(c)_i = vd(0) mod p^(t + 1)$ for some $t$. So $
        p^t sum_(i in B_k) vd(c)_i + sum_(i in B_1, ..., B_(k - 1)) x_i d^(-1) vd(c)_i equiv vd(0) mod p^(t + 1).
    $ We claim that $sum_(i in B_k) vd(c)_i in span{vd(c)_i: i in B_1, ..., B_(k - 1)}$. Suppose not, then there exists $vd(u) in NN^m$ such that $vd(u) . vd(c)_i = 0$ for all $i in B_1, ..., B_(k - 1)$, but $vd(u) . (sum_(i in B_k) vd(c)_i) != 0$. Then dotting with $vd(u)$, we obtain $p^t vd(u) . (sum_(i in B_k) vd(c)_i) equiv 0 mod p^(t + 1)$, so $vd(u) . sum_(i in B_k) vd(c)_i equiv 0 mod p$. But this holds for infinitely many $p$, so $vd(u) . sum_(i in B_k) vd(c)_i = 0$: contradiction.
]
#definition[
    For $m, p, c in NN$, an *$(m, p, c)$-set* $S subset.eq NN$ with generators $x_1, ..., x_m in NN$ is of the form $
        S = {sum_(i = 1)^m lambda_i x_i: exists j in [m]: lambda_j = c, lambda_i = 0 thick forall i < j, "and" lambda_k in [-p, p] thick forall k > j}
    $ where $[-p, p] = {-p, -(p - 1), ..., p}$. So $S$ consists of $
        c x_1 + lambda_2 x_2 + & lambda_3 x_3 + dots.c + & lambda_m x_m, & quad lambda_i in [-p, p], \
        c x_2 + & lambda_3 x_3 + dots.c + & lambda_m x_m, & quad lambda_i in [-p, p], \
        & & dots.v & & \
        &  & c x_m. &
    $ These are the *rows* of $S$. We can think of $S$ as a "progression of progressions".
]<def:mpc-set>
#example[
    - A $(2, p, 1)$-set with generators $x_1, x_2$ is of the form ${x_1 - p x_2, x_1 - (p - 1) x_2, ..., x_1 + p x_2, x_2}$, so is an AP of length $2p + 1$ together with its step.
    - A $(2, p, 3)$-set with generators $x_1, x_2$ is of the form ${3x_1 - p x_2, 3x_1 - (p - 1)x_2, ..., 3x_1, ..., 3x_1 + p x_2, 3x_2}$, so is an AP of length $2p + 1$, whose middle term is divisible by $3$, together with three times its step.
]
#theorem[
    Let $m, p, c in NN$. For any finite colouring of $NN$, there exists a monochromatic $(m, p, c)$-set.
]<thm:every-finite-colouring-of-naturals-admits-monochromatic-mpc-set>
#proofhints[
    - Reason that an $(m', p, c)$-set contains an $(m, p, c)$-set for $m' >= m$. With $M = k(m - 1) + 1$, reason that if we can find an $(M, p, c)$-set with each row monochromatic, then we can find an monochromatic $(m, p, c)$-set.
    - Let $A_1 = {c, 2c, ..., floor(n\/c) c}$, reason that $A_1$ contains a set of the form $R_1 = {c x_1 - n_1 d_1, c x_1 - (n_1 - 1)d_1, ..., c x_1 + n_1 d_1}$ for some large $n_1$.
    - Let $B_1 = {d_1, 2d_1, ..., floor(n_1 / ((M - 1)p)) d_1}$. We have $c x_1 + lambda_1 b_1 + dots.c + lambda_(M - 1) b_(M - 1) in R_1$, explain why these are monochromatic.
    - Inside $B_1$, define $
        A_2 = {c d_1, 2 c d_1, ..., floor(n_1 / ((M - 1)p c)) c d_1}.
    $ and apply the argument as before, where the divisor in the $floor(dot)$ expression in the new $B_2$ is $(M - 2)p$.
    - Argue that after a certain number of steps, we have formed an $(M, p, c)$-set with each row monochromatic.
]
#proof[
    Let $c: NN -> [k]$ be the colouring of $NN$ with $k$ colours. Note that an $(m', p, c)$-set with $m' >= m$ contains an $(m, p, c)$-set (by taking any $m$ rows, and setting some suitable $lambda_i$ to $0$). Let $M = k(m - 1) + 1$. It is enough to find a $(M, p, c)$-set such that each row is monochromatic.

    Let $n$ be large (large enough to apply the argument that follows). Let $A_1 = {c, 2c, ..., floor(n\/c) c}$. By Van der Waerden, $A_1$ contains a monochromatic AP $R_1$ of length $2n_1 + 1$ where $n_1$ is large enough: $
        R_1 = {c x_1 - n_1 d_1, c x_1 - (n_1 - 1)d_1, ..., c x_1 + n_1 d_1}.
    $ has colour $k_1$. Now we restrict our attention to $
        B_1 = {d_1, 2d_1, ..., floor(n_1 / ((M - 1)p)) d_1}.
    $ Observe that $
        c x_1 + lambda_1 b_1 + dots.c + lambda_(M - 1) b_(M - 1) in R_1
    $ for all $lambda_i in [-p, p]$ and $b_i in B_1$, so all these sums have colour $k_1$. Inside $B_1$, look at $
        A_2 = {c d_1, 2 c d_1, ..., floor(n_1 / ((M - 1)p c)) c d_1}.
    $ By Van der Waerden, $A_2$ contains a monochromatic AP $R_2$ of length $2n_2 + 1$ with colour $k_2$: $
        R_2 = {c x_2 - n_2 d_2, c x_2 - (n_2 - 1)d_2, ..., c x_2 + n_2 d_2}.
    $ Note that $x_2 subset.eq B_1$. Now we restrict our attention to $
        B_2 = {d_2, 2d_2, ..., floor(n_2 / ((M - 2)p)) d_2}.
    $ Again, note that for all $lambda_i in [-p, p]$ and $b_i in B_2$, we have $
        c x_2 + lambda_1 b_1 + dots.c + lambda_(M - 2) b_(M - 2) in R_2
    $ so has colour $k_2$.

    We iterate this process $M$ times, and obtain $M$ generators $x_1, ..., x_M$ such that each row of the $(M, p, c)$-set generated by $x_1, ..., x_M$ is monochromatic. But now $M = k(m - 1) + 1$, so $m$ of the rows have the same colour.
]
#remark[
    Being extremely precise in this proofs (such as considering $floor(dot)$) is much less important than the ideas in the proof. (Won't be penalised in the exam for small details like this).
]
#corollary("Folkman's Theorem")[
    Let $m in NN$ be fixed. For every finite colouring of $NN$, there exists $x_1, ..., x_m in NN$ such that $
        "FS"(x_1, ..., x_m) := {sum_(i in I) x_i: emptyset != I subset.eq [m]}
    $ is monochromatic.
]
#proofhints[
    A specific case of @thm:every-finite-colouring-of-naturals-admits-monochromatic-mpc-set.
]
#proof[
    By the $(m, 1, 1)$ case of @thm:every-finite-colouring-of-naturals-admits-monochromatic-mpc-set.
]
#remark[
    - The case $n = 2$ of Folkman's theorem is Schur's theorem.
    - For a colouring $c: NN -> [k]$, we induce a colouring $c': NN -> [k]$ by $c'(n) = c(2^n)$. Then by Folkman's theorem for $c'$, there exists $x_1, ..., x_m$ such that $
        "FP"(x_1, ..., x_m) = {product_(i in I) x_i: emptyset != I subset.eq [m]}.
    $
    - It is not known whether the same result holds for $"FS"(x_1, ..., x_m) union "FP"(x_1, ..., x_m)$. However, it does not hold for infinite sets ${x_n: n in NN}$, and does hold for colourings of $QQ$.
]
#proposition[
    Let $A$ have CP. Then there exist $m, p, c in NN$ such that every $(m, p, c)$-set contains a solution $vd(y)$ to $A vd(y) = vd(0)$, i.e. all $y_i$ belong to the $(m, p, c)$-set.
]
#proof[
    Let $vd(c)_1, ..., vd(c)_n$ be the columns of $A$. By assumption, there is a partition $B_1 union.sq dots.c union.sq B_r$ of $[n]$ such that $forall k in [r]$, $
        sum_(i in B_k) vd(c)_i & in span{vd(c)_i: in B_1 union dots.c union B_(k - 1)} \
        ==> sum_(i in B_k) vd(c)_i & = sum_(i in B_1 union dots.c union B_(k - 1)) q_(i k) vd(c)_i quad "for some" q_(i k) in QQ \
        ==> sum_(i = 1)^n d_(i k) vd(c)_i & = vd(0)
    $ where $
        d_(i k) = cases(
            0 quad & "if" i in.not B_1 union dots.c union B_(k - 1),
            1 & "if" i in B_k,
            -q_(i k) & "if" i in B_1 union dots.c union B_(k - 1)
        ).
    $ Take $m = r$. Let $x_1, ..., x_r in NN$, and let $y_i = sum_(k = 1)^r d_(i k) x_k$ for each $i in [n]$. Now $vd(y) = (y_1, ..., y_n)$ is a solution to $A vd(y) = vd(0)$: we have $
        sum_(i = 1)^n y_i vd(c)_i & = sum_(i = 1)^n sum_(k = 1)^r d_(i k) x_k vd(c)_i \
        & = sum_(k = 1)^r x_k sum_(i = 1)^n d_(i k) vd(c)_i = vd(0).
    $ Let $c$ be the LCD of all the $q_(i k)$. Now $c y_i = sum_(k = 1)^n c d_(i k) x_k$ is an integral linear combination of the $x_k$, and $c vd(y)$ is a solution since $vd(y)$ is. Let $p$ be $c$ times maximum of the absolute values of the numberators of the $q_(i k)$. By definition of the $d_(i k)$, $c vd(y)$ is in the $(m, p, c)$-set generated by $x_1, ...., x_r$.
]
#theorem("Rado")[
    $A in QQ^(m times n)$ is PR iff it has CP.
]<thm:rado>
#proof[
    $==>$ is by @prop:pr-implies-cp. For $<==$, let $c': NN -> [k]$ be a finite colouring of $NN$. Also, by the above proposition, since $A$ has CP, there exists $m, p, c in NN$ such that $A vd(x) = vd(0)$ has a solution $vd(x)$ in any $(m, p, c)$-set by the above theorem. By @thm:every-finite-colouring-of-naturals-admits-monochromatic-mpc-set, there is a monochromatic $(m, p, c)$-set with respect to $c'$. This gives a monochromatic solution $vd(x)$ to $A vd(x) = vd(0)$.
]
#remark[
    From the proof of @thm:rado, we obtain that if $A$ is PR for the "$mod p$" colourings, then it is PR for _any_ colouring. There is no proof of this fact that is more direct than using Rado's theorem.
]
#theorem("Consistency")[
    Let $A$ and $B$ be rational PR matrices. Then the matrix $
        mat(A, 0; 0, B)
    $ is PR.
]<thm:consistency>
#proofhints[
    @thm:rado.
]
#proof[
    This is a trivial check of the CP given the CP of $A$ and $B$, then we are done by @thm:rado.
]
#remark[
    The @thm:consistency says that if we can find monochromatic solutions $vd(x)$ and $vd(x')$ to $A vd(x) = vd(0)$ and $B vd(y) = vd(0)$, then we can find monochromatic solutions $vd(x')$ and $vd(y')$, of the same colour, to $A vd(x') = vd(0)$ and $B vd(y') = vd(0)$.
]
#theorem[
    For any finite colouring of $NN$, some colour class contains solutions to _all_ PR equations.
]
#proofhints[
    Use the @thm:consistency.
]
#proof[
    For a given $k$-colouring of $NN$, let $NN = C_1 union.sq dots.c union.sq C_k$ be the colour classes. Assume the contrary, so for each $1 <= i <= k$, there exists a PR matrix $A_i$ such that $A_i vd(x) = vd(0)$ has no monochromatic solution of the same colour as $C_i$. But then by inductively applying the consistency theorem, the matrix $
        mat(A_1, , 0; , dots.down, ; 0, , A_k)
    $ has a monochromatic solution of the same colour as some $C_j$. But then $C_j vd(x) = vd(0)$ has a solution $vd(x)$ of the same colour as $C_j$: contradiction.
]

== Ultrafilters

#definition[
    A *filter* on $NN$ is a non-empty collection $cal(F)$ of subsets of $NN$ such that:
    - $emptyset in.not cal(F)$,
    - If $A in cal(F)$ and $A subset.eq B$, then $B in cal(F)$, i.e. $cal(F)$ is an *up-set*.
    - If $A, B in cal(F)$ then $A sect B in cal(F)$, i.e. $cal(F)$ is closed under finite intersections.
    A filter is a notion of "large" subsets of $NN$.
]<def:filter>
#example[
    - $cal(F)_1 = {A subset.eq NN: 1 in A}$ is a filter.
    - $cal(F)_2 = {A subset.eq NN: 1, 2 in A}$ is a filter.
    - $cal(F)_3 = {A subset.eq NN: A^c "finite"}$ is a filter, called the *cofinite filter*.
    - $cal(F)_4 = {A subset.eq NN: A "infinite"}$ is not a filter, since it contains $2 NN$ and $2 NN + 1$ but not $emptyset = (2 NN) sect (2 NN + 1)$.
    - $cal(F)_5 = {A subset.eq NN: 2 NN \\ A "finite"}$ is a filter.
]
#definition[
    An *ultrafilter* is a maximal filter.
]
#definition[
    For $x in NN$, the *principal ultrafilter at $x$* is $
        cal(U)_x := {A subset.eq NN: x in A}.
    $
]
#proposition[
    The principal ultrafilter at $x$ is indeed an ultrafilter.
]
#proofhints[
    Straightforward.
]
#proof[
    If $B in.not cal(U)_x$, then $x in B^c$ so $B^c in cal(U)_x$, but $B^c sect B = emptyset$, so $cal(U)_x union {B}$ is not a filter.
]
#example[
    - $cal(F)_1 = {A subset.eq NN: 1 in A}$ is an ultrafilter.
    - $cal(F)_2 = {A subset.eq NN: 1, 2 in A}$ is not an ultrafilter as $cal(F)_1$ extends it.
    - $cal(F)_3 = {A subset.eq NN: A^c "finite"}$ is not an ultra filter, as $cal(F)_5$ extends it.
    - $cal(F)_5 = {A subset.eq NN: 2 NN \\ A "finite"}$ is not an ultrafilter, as ${A subset.eq NN: 4 NN \\ A "finite"}$ extends it.
]
#proposition[
    A filter $cal(F)$ is an ultrafilter iff for all $A subset.eq NN$, either $A in cal(F)$ or $A^c in cal(F)$.
]<prop:ultrafilter-iff-contains-each-set-xor-complement>
#proofhints[
    $<==$: straightforward. $==>$: show if $A in.not cal(F)$, then $exists B in cal(F)$ such that $A sect B = emptyset$.
]
#proof[
    $<==$: since $A sect A^c = emptyset in.not cal(F)$.

    $==>$: let $cal(F)$ is an ultrafilter. We cannot have $A, A^c in cal(F)$ as $A sect A^c = emptyset in.not cal(F)$. Suppose there is $A subset.eq NN$ such that $A, A^c in.not cal(F)$. By maximality of $cal(F)$, since $A in.not cal(F)$, then $exists B in cal(F)$ such that $A sect B = emptyset$ (suppose not, then $cal(F)' = {S subset.eq NN: S supset.eq A sect B "for some" B in cal(F)}$ extends $cal(F)$). Similarly, $exists C in cal(F)$ such that $A^c sect C = emptyset$. So we have $C subset.eq A$, so $B sect C = emptyset in.not cal(F)$: contradiction (or also $C subset.eq A ==> A in cal(F)$: contradiction).
]
#corollary[
    Let $cal(U)$ be an ultrafilter and $A = B union C in cal(U)$. Then $B in U$ or $C in U$.
]<crl:union-in-ultrafilter-has-element-in-ultrafilter>
#proofhints[
    Straightforward.
]
#proof[
     If not, then $B^c, C^c in cal(U)$ by @prop:ultrafilter-iff-contains-each-set-xor-complement, hence $B^c sect C^c = (B union C)^c = A^c in cal(U)$: contradiction.
]
#proposition[
    Every filter is contained in an ultrafilter.
]<prop:every-filter-is-contained-in-ultrafilter>
#proofhints[
    Use Zorn's Lemma.
]
#proof[
    Let $cal(F)_0$ be a filter. By Zorn's Lemma, it is enough to show that every non-empty chain of filters has an upper bound. Let ${cal(F)_i: i in I}$ be a chain of filters in the poset of filters containing $cal(F)_0$, partially ordered by inclusion, and set $cal(F) = union.big_(i in I) cal(F)_i$.
    - $emptyset in.not cal(F)$ since $emptyset in.not cal(F)_i$ for each $i in I$.
    - If $A in cal(F)$ and $A subset.eq B$, then $A in cal(F)_i$ for some $i in I$, so $B in cal(F)_i$, so $B in cal(F)$.
    - Let $A, B in cal(F)$, so $A in cal(F)_i$ and $B in cal(F)_j$ for some $i, j$. WLOG, $cal(F)_i subset.eq cal(F)_j$, so $A sect B in cal(F)_j$, so $A sect B in cal(F)$.
    $cal(F)$ is an upper bound for the chain, so we are done.
]
#proposition[
    Let $cal(U)$ be an ultrafilter. Then $cal(U)$ is non-principal iff $cal(U)$ extends the cofinite filter $cal(F)_C$.
]<prop:ultrafilter-is-non-principal-iff-extends-cofinite-filter>
#proofhints[
    $<==$: straightforward. $==>$: use @crl:union-in-ultrafilter-has-element-in-ultrafilter.
]
#proof[
    $<==$: if $cal(U) = cal(U)_x$ is principal, then we have ${x} in cal(U)$ so ${x}^c in.not cal(U)$ by @prop:ultrafilter-iff-contains-each-set-xor-complement, but also ${x}^c in cal(F)_C$: contradiction.

    $==>$: let $A in cal(F)_C$, so $A^c = {a_1, ..., a_k}$ is finite. Assume $A in.not cal(U)$, then $A^c in cal(U)$, so by @crl:union-in-ultrafilter-has-element-in-ultrafilter, some $a_i in cal(U)$. But then by definition of a filter, each set containing $a_i$ is in $cal(U)$, so $cal(U)$ is principal: contradiction.
]
#notation[
    Let $beta NN$ denote the set of all ultrafilters on $NN$.
]<ntn:set-of-ultrafilters>
#definition[
    Define a topology on $beta NN$ by its base (basis), which consists of $
        C_A := {cal(U) in beta NN: A in cal(U)}
    $ for each $A subset.eq NN$. The sets above indeed form a base: we have $union.big_(A subset.eq NN) C_A = beta NN$, and $C_A sect C_B = C_(A sect B)$, since $A sect B in cal(U)$ iff $A, B in cal(U)$. The open sets are of the form $union.big_(i in I) C_(A_i)$ and the closed sets are of the form $sect.big_(i in I) C_(A_i)$.
]<def:topology-on-ultrafilters>
#remark[
    $beta NN \\ C_A = C_(A^c)$, since $A in.not cal(U)$ iff $A^c in cal(U)$. We can view $NN$ as being embedded in $beta NN$ by identifying $n in NN$ with $tilde(n) := cal(U)_n$, the principal ultrafilter at $n$. Each point in $NN$ under this correspondence is isolated in $beta NN$, since $C_({n}) = {tilde(n)}$ is an open neighbourhood of $tilde(n)$. Also, $NN$ is dense in $beta NN$, since for every $n in A$, $tilde(n) in C_A$, so every non-empty open set in $beta NN$ intersects $NN$.
]
#theorem[
    $beta NN$ is a compact Hausdorff topological space.
]<thm:topology-on-ultrafilters-is-compact-and-hausdorff>
#proof[
    Hausdorff: let $cal(U) != cal(V)$ be ultrafilters, so there is $A in cal(U)$ such that $A in.not cal(V)$. But then $A^c in cal(V)$, so $cal(U) in C_A$, $cal(V) in C_(A^c)$, and $C_A sect C_(A^c)$ is open.

    Compact: it is compact iff every open admits a finite subcover iff a collection of open sets such that no finite subcollection covers $beta NN$, they don't cover $beta NN$ iff for every collection of closed sets such that they have finite intersection property ($(F_i)_(i in I)$, $sect_(i in J) F_i != emptyset$ for all $J$ finite), then their intersection is non-empty. We can assume each $F_i$ is a basis set, i.e. $F_i = C_(A_i)$ for some $A_i in NN$. Suppose ${C_(A_i): i in I}$ have teh finite intersection property. First, $C_(A_(i_1)) sect dots.c sect C_(A_(i_k)) = C_(A_(i_1) sect dots.c sect A_(i_k)) != emptyset$, hence $sect.big_(j = 1)^k A_(i_j) != emptyset$. So let $cal(F) = {A: A supset.eq A_(i_1) sect dots.c sect A_(i_k) "for some" A_(i_1), ..., A_(i_n)}$. We have $emptyset in.not cal(F)$, if $B supset.eq A in cal(F)$ then $B in cal(F)$, and if $A, B in cal(F)$, then $A sect B in cal(F)$. Hence $cal(F)$ is a filter. $cal(F)$ extends to an ultrafilter $cal(U)$. Note that $(forall i, A_i in cal(U)) <==> (cal(U) in C_(A_i) forall i)$. So $U in sect C_(A_i)$, so $sect C_(A_i) != emptyset$.
]
#remark[
    - $beta NN$ can be viewed as a subset of ${0, 1}^(powset(NN))$ (so each ultrafilter is viewed as a function $powset(NN) -> {0, 1}$). The topology on $beta NN$ is the restriction of the product topology on ${0, 1}^powset(NN)$. Also, $beta NN$ is a closed subset of ${0, 1}^powset(NN)$, so is compact by Tychonov's theorem (TODO: look up statement of this theorem).
    - $beta NN$ is the largest compact Hausdorff topological space in which (the embedding of) $NN$ is dense. In other words, if $X$ is compact and Hausdorff, and $f: NN -> X$, there exists a unique continuous $tilde(f): beta NN -> X$ extending $f$. TODO: insert diagram.
    - $beta NN$ is called the *Stone-Čech compactification* of $NN$.
]
#definition[
    Let $p$ be a statement and $cal(U)$ be an ultrafilter. $forall_cal(U) x med p(x)$ to mean ${x in NN: p(x)} in cal(U)$ and say $p(x)$ "for most $x$" or "for $cal(U)$-most $x$".
]
#example[
    - For $cal(U) = tilde(n)$, we have $forall_(cal(U)) x med p(x)$ iff $p(n)$.
    - For non-principal $cal(U)$, we have $forall_cal(U) x med (x > 4)$ (if not, then ${1, 2, 3} = {x in NN: x > 4}^c in cal(U)$, so ${i} in cal(U)$ for some $i = 1, 2, 3$, so $cal(U)$ is principal: contradiction).
]
#proposition[
    Let $cal(U)$ be an ultrafilter and $p, q$ be statements. Then
    + $forall_cal(U) x med (p(x) and q(x))$ iff $(forall_cal(U) x med p(x)) and (forall_cal(U) x med q(x))$.
    + $forall_cal(U) x med (p(x) or q(x))$ iff $(forall_cal(U) x med p(x)) or (forall_cal(U) x med q(x))$.
    + $not (forall_cal(U) x med p(x))$ iff $forall_cal(U) x med (not p(x))$.
]<prop:ultrafilter-quantification-distributes-over-logical-connectives>
#proof[
    Let $A = {x in NN: p(x)}$ and $B = {x in NN: q(x)}$. We have
    + $A sect B in cal(U)$ iff $A in cal(U)$ and $B in cal(U)$ by definition.
    + $A union B in cal(U)$ iff $A in cal(U)$ and $B in cal(U)$ by (find result).
    + $A in.not cal(U)$ iff $A^c in cal(U)$ by (find result).
]
#note[
    $forall_cal(U) x forall_cal(V) y med p(x, y)$ is not necessarily the same as $forall_cal(V) y forall_cal(U) x med p(x, y)$, even when $cal(U) = cal(V)$. For example, let $cal(U)$ be non-principal, and $p(x, y) = (x < y)$. Then $forall_cal(U) x (forall_cal(U) y med (x < y))$ is true, as every $x$ satisfies $forall_cal(U) y med (x < y)$. But $forall_cal(U) y forall_cal(U) x med (x < y)$ is false, as no $y$ has $forall_cal(U) x med (x < y)$. So *don't swap quantifiers!*.
]
#definition[
    Given ultrafilters $cal(U), cal(V)$, define their sum to be $
        cal(U) + cal(V) := {A subset.eq NN: forall_cal(U) x forall_cal(V) y med (x + y in A)}.
    $
]<def:ultafilter-sum>
#example[
    We have $tilde(m) + tilde(n) = tilde(m + n)$.
]
#proposition[
    For any ultrafilters $cal(U)$ and $cal(V)$, $cal(U) + cal(V)$ is an ultrafilter.
]
#proof[
    We have $emptyset in.not cal(U) + cal(V)$. If $A in cal(U) + cal(V)$ and $A subset.eq B$, then $B in cal(U) + cal(V)$. If $A, B in cal(U) + cal(V)$, then $(forall_cal(U) x forall_cal(V) y med (x + y in A)) and (forall_cal(U) x forall_cal(V) y med (x + y in B))$, so by above proposition, we have $forall_cal(U) x forall_cal(V) y (x + y in A and x + y in B)$, i.e. $forall_cal(U) x forall cal(V) y med (x + y in A sect B)$, i.e. $A sect B in cal(U) + cal(V)$. Hence $cal(U) + cal(V)$ is a filter.

    Suppose that $A in.not cal(U) + cal(V)$, i.e. $not (forall_cal(U) x forall_cal(V) y med (x + y in A))$. Then by above proposition twice, we have $forall_cal(U) x forall_cal(V) y med not (x + y in A)$. So $forall_cal(U) x forall_cal(V) y med (x + y in A^c)$, i.e. $A^c in cal(U) + cal(V)$.
]
#proposition[
    Ultrafilter addition is associative.
]
#proof[
    Let $A subset.eq cal(U) + (cal(V) + cal(W))$, so $forall_cal(U) x forall_(cal(V) + cal(W)) med (x + y in A)$. So $B := {y: x + y in A} in cal(V) + cal(W)$, i.e. $forall_cal(V) y_1 forall_cal(W) y_2 med (y_1 + y_2 in B)$. So we have $forall_cal(U) x forall_cal(V) y_1 forall_cal(W) y_2 med (x + y_1 + y_2 in A)$. So $
        cal(U) + (cal(V) + cal(W)) = {A subset.eq NN: forall_cal(U) x forall_cal(V) y forall_cal(W) z med (x + y + z in A)} = (cal(U) + cal(V)) + cal(W).
    $
]
#proposition[
    Ultrafilter addition is left-continuous: for fixed $cal(V)$, $cal(U) |-> cal(U) + cal(V)$ is continuous.
]
#proof[
    For $A subset.eq NN$, we have $
        cal(U) + cal(V) in C_A & <==> A in cal(U) + cal(V) \
        & <==> forall_cal(U) x forall_cal(V) y med (x + y in A) \
        & <==> B := {x in NN: forall_cal(V) y med (x + y in A)} in cal(U) \
        & <==> cal(U) in C_B
    $ hence the preimage of $C_A$, which is $C_B$, is open.
]
#proposition("Idempotent Lemma")[
    There exists an idempotent ultrafilter $cal(U) in beta NN$ (i.e. $cal(U) = cal(U) + cal(U)$).
]<prop:idempotent-lemma>
#proof[
    For $M subset.eq beta NN$, define $M + M := {x + y: x, y in M}$. We seek a non-empty, compact $M subset.eq beta NN$ which is minimal such that $M + M subset.eq M$, and hope to show that $M$ is a singleton.

    Such an $M$ exists ($beta NN$ is one such), so the set of all such $M$ is non-empty. By Zorn's Lemma, it suffices to show that if ${M_i: i in I}$ is a chain of such sets, then $M = sect.big_(i in I) M_i$ (an upper bound with respect to the partial ordering $supset.eq$) is another such set. This $M$ will be compact as an intersection of closed sets, since $beta NN$ is compact and Hausdorff, so any subspace is closed iff it is compact. Also, $M + M subset.eq M$: for $x, y in M$, we have $x, y in M_i$ so $x + y in M_i + M_i subset.eq M_i$ for all $i in I$, so $x + y in M$. Finally, $M$ is non-empty: ${M_i: i in I}$ have the finite intersection property, as they are a chain, and are closed, so their intersection is non-empty.

    So by Zorn's lemma, there exists such a minimal $M$. Given $x in M$, we have $M + x = M$, since $M + x != emptyset$, $M + x$ is compact (as the continuous image of a compact set) and $(M + x) + (M + x) = (M + x + M) + x subset.eq (M + M + M) + x subset.eq M + x$, so by minimality of $M$, $M + x = M$.

    In particular, there exists $y in M$ such that $y + x = x$. Let $T = {y in M: y + x = x}$. We claim that $T = M$, and since $T subset.eq M$, it is enough to show that $T$ is compact, non-empty and $T + T subset.eq T$, by minimality of $M$. Indeed, $y in T$, so $T != emptyset$, $T$ is the pre-image of a singleton which is compact, hence closed, so $T$ is closed, so compact. Finally, for $y, z in T$, we have $y + x = x = z + x$ so $y + z + x = y + x = x$, so $y + z in T$, so $T + T subset.eq T$.

    Hence, $y + x = x$ for all $y in M$, hence $x + x = M$. In fact, $M = {x}$.
]
#remark[
    The finite subgroup problem asks whether we can find a non-trivial subgroup of $beta NN$ (e.g. find $cal(U)$ with $cal(U) + cal(U) != cal(U)$ but $cal(U) + cal(U) + cal(U) = cal(U)$). This was recently proven to be negative.
]
#remark[
    It has been recently shown that there exist $cal(U) != cal(V)$ such that $cal(U) + cal(U) = cal(U) + cal(V) = cal(V) + cal(U) = cal(V) + cal(V) = cal(V)$.
]
#theorem("Hindman")[
    For any finite colouring of $NN$, there exists a sequence $(x_n)_(n in NN)$ such that $
        "FS"({x_n: n in NN}) = {sum_(i in I) x_i: I subset.eq NN "finite", I != emptyset}.
    $
]<thm:hindman>
#proof[
    Let $cal(U)$ be an idempotent ultrafilter, and partition $NN$ into its colour classes: $NN = A_1 union.sq dots.c union.sq A_k$. Since $emptyset in.not cal(U)$ by definition, we have $A_1 union dots.c union A_k in NN in cal(U)$ by @prop:ultrafilter-iff-contains-each-set-xor-complement. So by @crl:union-in-ultrafilter-has-element-in-ultrafilter, $A := A_i in cal(U)$ for some $i in [k]$. We have $forall_cal(U) y med (y in A)$ by definition. Thus:
    + $forall_cal(U) x forall_cal(U) y med (y in A)$.
    + $forall_cal(U) x forall_cal(U) y med (x in A)$.
    + $forall_cal(U) x forall_cal(U) y med (x + y in A)$ since $A in cal(U) + cal(U) = cal(U)$.
    @prop:ultrafilter-quantification-distributes-over-logical-connectives then gives that $forall_cal(U) x forall_cal(V) y med ("FS"(x, y) subset.eq A)$. Fix $x_1 in A$ such that $forall_cal(U) y med ("FS"(x_1, y) subset.eq A)$.

    Now assume we have found $x_1, ..., x_n$ such that $forall_cal(U) y med ("FS"(x_1, ..., x_n, y) subset.eq A)$, i.e. $B := {y in NN: "FS"(x_1, ..., x_n, y) subset.eq A} in cal(U) = cal(U) + cal(U)$, i.e. $forall_cal(U) x forall_cal(U) y med (x + y in B)$ by definition. We have:
    + $forall_cal(U) x forall_cal(U) y med ("FS"(x_1, ..., x_n, y) subset.eq A)$.
    + $forall_cal(U) x forall_cal(U) y med ("FS"(x_1, ..., x_n, x) subset.eq A)$.
    + For each $z in "FS"(x_1, ..., x_n, y)$, we have $forall_cal(U) y med (z + y in A)$, so $forall_cal(U) x forall_cal(U) y med (z + x + y in A)$.
    @prop:ultrafilter-quantification-distributes-over-logical-connectives then gives that $
        forall_cal(U) x forall_cal(U) y med ("FS"(x_1, ..., x_n, x, y) subset.eq A).
    $ The result follows by induction.
]


= Euclidean Ramsey theory

If we $2$-colour $RR^2$, there are 2 points of distance at most $1$ of the same colour (consider equilateral triangel).

If we $3$-colour $RR^3$, there are $2$ points of distance at most $1$ of the same colour (consider regular tetrahedron)

If we $k$-colour $RR^k$, then by considering the regular simplex with $k + 1$ vertices such that any $2$ points have distance $1$ between them, $2$ points have the same colour.

#definition[
    $X'$ is an *isometric copy* of $X$ if there exists a bijection $phi: X -> X'$ which prserves distances: $
        forall x, y in X, quad d(x, y) = d(phi(x), phi(y)).
    $
]
#definition[
    A finite set $X subset.eq RR^m$ is *(Euclidean) Ramsey* if for all $k in NN$, there exists a finite set $S subset.eq RR^n$ ($n$ could be very large) such that for any $k$-colouring of $S$, there exists a monochromatic isometric copy of $X$.
]
#example[
    - ${0, 1}$ is Ramsey, by the above simplex argument.
    - The equilateral triangle of side length $1$ is Ramsey, by considering the $2k$-dimensional unit simplex.
    - Any ${0, a}$ is Ramsey.
    - By the same argument, any regular simplex is Ramsey.
]
#remark[
    - If $X$ is infinite, then (exercise) we can construct a $2$-colouring of $RR^n$ with no monochromatic isometric copy of $X$.
    - Above, we took $S$ to be in $RR^k$ for $k$ colours. Can we do better? We can't do it for ${0, 1}$ in $RR$: consider the colouring $x |-> floor(x) mod 2$. For ${0, 1}$ with $3$ colours, can do this in $RR^2$: look at diagram. Actually this shows $chi(RR^2) >= 4$. Can show $chi(RR^2) <= 7$ by hexagonal argument. We know $chi(RR^2) >= 5$. In general, $1.2^n <= chi(RR^n) <= 3^n$. The upper bound easily follows from a hexagonal colouring.
]
#proposition[
    $X$ is Euclidean Ramsey iff $forall k in NN$, $exists n in NN$ such that for any $k$-colouring of $RR^n$, there exists a monochromatic isometric copy of $X$.
]
#proof[
    If $X$ is Euclidean Ramsey then take $S$ finite in $RR^n$ (for $k$ colours).

    $<==$: we use a compactness proof. Suppose not, therefore for any finite $S subset.eq RR^n$, there is a bad $k$-colouring (i.e. no monochromatic isometric copy of $X$). The space of all $k$-colourings is $[k]^((RR^n))$, which is compact by Tychonov (TODO: add this statement). Consider the set $C_(X')$ of colourings under which $X'$ is not monochromatic. $C_(X')$ is closed. Look at ${C_(X'): X' "isometric copy of" X}$. It has the finite intersection property, because any finite $S$ has a bad $k$-colouring. Therefore, $sect.big C_(X') != emptyset$, so there exists a $k$-colouring of $RR^n$ with no monochromatic isometric copy of $X$ in $S$.
]
#lemma[
    If $X subset.eq RR^n$ and $Y subset.eq RR^m$ are both Ramsey, then $X times Y subset.eq RR^(n + m)$ is also Ramsey.
]
#proof[
    Let $c$ be a colouring of $S times T$, where $S$ is $k$-Ramsey for $X$ and $T$ is $k^abs(S)$-Ramsey for $Y$. $k^abs(S)$-colour $T$ as follows: $c'(t) = (c(s_1, t), ..., c(s_abs(S), t))$. By choice of $T$, there is a monochromatic (with respect to $c'$) isometric copy $Y'$ of $Y$. So $c(s, y) = c(s, y')$ for all $y, y' in Y$ and $s in S$. Now $k$-colour $S$ by $c''(s) = c(s, y)$ for any $y in Y$ (note this is well-defined). By choice of $S$, there is a monochromatic (with respect to $c''$) isometric copy $X'$ of $X$, so $X' times Y'$ is monochromatic with respect to $c$.

    TODO: convince yourself that this is a very standard product argument.
]
#remark[
    Since any ${0, a}$ and ${0, b}$ are Ramsey, any rectangle is Ramsey, so any right-angle triangle is Ramsey (since it is embedded in a rectangle). Similarly, any cuboid is Ramsey, and so any acute triangle (which is embedded in a cuboid) is Ramsey.
]
#remark[
    In general, to prove sets are Ramsey, we will first embed them in "nicer" sets (with useful symmetry groups) and show instead that those sets are Ramsey. We will show:
    - any triangle is Ramsey
    - any regular $n$-gon is Ramsey
    - any Platonic solid is Ramsey
]
#proposition[
    $X = {0, 1, 2}$ is not Ramsey.
]
#proof[
    Recall in $RR^n$ we have $norm(x + y)_2^2 + norm(x - y)_2^2 = 2 norm(x)_2^2 + 2 norm(x)_2^2$. Every isometric copy of ${0, 1, 2}$ in any $RR^n$ is of the form ${x - y, x, x + y}$ with $norm(y)_2 = 1$. So $
        norm(x + y)_2^2 + norm(x - y)_2^2 = 2 norm(x)_2^2 + 2.
    $ If we can find a colouring $phi$ of $RR_(>= 0)$ such that there is no monochromatic solutions to $a + b = 2c + 2$. Colouring $RR^n$ by $c(x) = phi(norm(x)_2^2)$. We $4$-colour $RR_(>= 0)$ by $phi(x) = floor(x) thick mod 4$. Suppose $a, b, c$ all have colour $n in {0, 1, 2, 3}$. Then if $a + b = 2c + 2$, writing $a = floor(a) + {a}$, $b = floor(b) + {b}$, $c = floor(c) + {c}$, we have $2 = a + b - 2c = 4k + {a} + {b} - 2{c}$ for some $k in ZZ$, which is impossible as $-2 < {a} + {b} - 2{c} < 2$.
]
#remark[
    - The proof shows that for all $n$, there is a $4$-colouring of $RR^n$ which stops every isometric copy of $X = {0, 1, 2}$ from being monochromatic.
    - It is very important that in $a + b = 2c + 2$, the $2$ in the equation is not $0$.
    - It will turn out that the property that made ${0, 1, 2}$ not Ramsey is "it does not lie on a sphere".
]
#definition[
    A finite set $X subset.eq RR^n$ is called *spherical* if it lies on the surface of a sphere.
]
#example[
    Any triangle, rectangle, and non-degenerate simplex is spherical.
]
#definition[
    $x_1, ..., x_d in RR^n$ form a simplex if ${x_1 - x_d, x_2 - x_d, ..., x_(d - 1) - x_d}$ are linearly independent, i.e. if $x_1, ..., x_d$ do not lie in a $(d - 2)$-dimensional affine subspace.
]
#remark[
    We want to show that if $X$ is Ramsey, then it is spherical.
]
#lemma[
    ${x_1, ..., x_d} in RR^n$ is not spherical iff there exist $c_i in RR$, not all zero, such that:
    + $sum_(i = 1)^d c_i = 0$.
    + $sum_i c_i x_i = 0$.
    + $sum_i c_i norm(x_i)_2^2 != 0$.
]
#proof[
    $==>$: let ${x_1, ..., x_d}$ be not spherical. Since ${x_1, ..., x_d}$ are not the vertices of a simplex, there exist $c_1, ..., c_d in RR$ such that $sum_i c_i (x_i - x_d) = 0$ since $sum_(i = 1)^(d - 1) c_i x_i + (-c_1 - dots.c - c_(d - 1)) x_d = 0$. This gives the first two conditions. Note that all three conditions are invariant under translation by $v in RR^n$: $sum_i c_i (x_i + v) = 0$, $sum_i c_i norm(x_i + v)_2^2 = sum_i c_i norm(x_i)^2 + 2 c_i x_i dot v_ + c_i norm(v)_2^2 = sum_i c_i norm(x_i)^2$.

    Look at a minimal subset of ${x_1, ..., x_d}$ that is not spherical. If we can show the result for WLOG ${x_1, ..., x_k}$, $k <= d$, then we can take $c_i = 0$ for all $i in [k + 1, d]$. Now ${x_2, ..., x_k}$ is spherical by minimality. Say it lies on the sphere of radius $r$, centred at $v$. By translation invariance, then we can translate the set such that ${x_2, ..., x_k}$ is centred at $0$. ${x_1, ..., x_d}$ is not spherical so does not form a $(d - 1)$-simplex, so there exist $c_i$ such that $sum_i c_i (x_i - x_k) = 0$ so $c_1 x_1 + dots.c + c_(k - 1) x_(k - 1) + (-c_1 - dots.c - c_(k - 1)) x_k = 0$. WLOG, we have $c_1 != 0$ (can assume this since the same $c_i$ work after translation). Now $
        sum_(i = 1)^k c_i norm(x_i)^2 = c_1 norm(x_1)^2 + r^2 sum_(i = 2)^k c_i != 0
    $ as $norm(x_1) != r$, since ${x_1, ..., x_k}$ is not spherical.

    $<==$: assume for a contradiction that ${x_1, ..., x_d}$ are spherical, and lie on the sphere of radius $r$ centred at $v$. By the above argument, we can translate the set so that they are centred at the origin: this prserves all conditions and does not change the value of $sum_i c_i norm(x_i)^2$. We have $norm(x_i)^2 = r^2$ for all $i$, so $sum_i c_i norm(x_i)^2 = r^2 sum_i c_i = 0$: contradiction.
]
#remark[
    In the previous proof, we had $c = (1, 1, -2)$ and $sum_i c_i norm(x_i)_2^2 = 2$.
]
#corollary[
    Let $X = {x_1, ..., x_n}$ be non-spherical. Then there exist $c_1, ..., c_n$ not all $0$ with $sum_i c_i = 0$ and a $b != 0$ such that $sum_i c_i norm(x_i)^2 = b$.
]
#remark[
    The above corollary is true for every isometric copy $X'$ of $X$ with _the same witnesses $c_i$ and $b$_: if $phi(X)$ is a copy of $X$ (for distance-preserving bijection $phi$), we can translate (as in proof of above lemma) and the $c_i$ and $b$ are unaffected, in such a way that $phi(0) = 0$. After that, applying a matrix $A$ that corresponds to rotation/reflection.
]
#theorem[
    If $X = {x_1, ..., x_n}$ is Ramsey, then $X$ is spherical.
]
#proof[
    Suppose $X$ is not spherical. Then by above lemma, there exist $c_i$ not all zero such that $sum_i c_i norm(x_i)^2 = b != 0$ and $sum_i c_i = 0$. This is also true for any isometric copy of $X'$. We will split $[0, 1)$ into $[0, delta)$, $[delta, 2 delta), ...$ for small $delta$ and colour depending on where $c_i norm(x)^2$ lies. It is enough to construct a colouring $c: RR_+ -> [k]$ such that $sum_i c_i y_i = b$ does not have a monochromatic solution, where $sum_i c_i = 0$. If we show this, then we define a colouring $c': RR^n -> [k]$ by $c' (x) = c(norm(x)^2)$.

    We have $sum_(i = 1)^(n - 1) c_i (y_i - y_n) = b$. By rescaling the $c_i$, we may assume that $b = 1 \/ 2$. Now we split $[0, 1)$ into intervals $[0, delta)$, $[delta, 2 delta), ...$ where $delta$ is very small. Define the colouring $c(y) = ("interval where" {c_i y} "is", "interval where" {c_2 y} "is", ...)$. This is a a $floor(1 / delta)^(n - 1)$-colouring. Assume $y_1, ..., y_(n - 1)$ are monochromatic under $c$ such that $sum_i c_i (y_i - y_n) = 1 \/ 2$. The sum is within $(n - 1) delta$ of an integer, which is $!= 1/2$ for $delta$ small enough.
]
What about spherical $=>$ Ramsey? This is open.

It is known that triangles, simplices, and any $n$-gon is Ramsey.

We want to show that any regular $m$-gon $X = {v_1, ..., v_m}$ (with side length $1$) is Ramsey. Idea: first find a copy of $X$ such that $v_1$ and $v_2$ are monochromatic, then use a product argument to get an isometric copy of $X^N$, where $N$ is very large, such that the colouring is invariant under swapping around $v_1$ and $v_2$. Use this to find copy of $X$ on for which $v_1, v_2, v_3$ are monochromatic.

#definition[
    For a finite $A subset.eq X$, a colouring $c$ of $X^n$ is *$A$-invariant* if it is invariant under permuting the coordinates within $A$, i.e. for $vd(x) = (x_1, ..., x_n)$ and $vd(x') = (x'_1, ..., x'_n)$, if for all $i in [n]$, either $x_i = x'_i$ or $x_i, x'_i in A$, then $c(x') = c(x)$.

    Note if $c$ is $X$ invariant, then $X$ is monochromatic under $c$.
]
#proposition[
    Let $X subset.eq RR^d$ be finite and $A subset.eq X$. Suppose $forall k in NN$, there exists a finite $S subset.eq RR^c$ such that whenever $S$ is $k$-coloured, there exists an isometric copy of $X$ that is constant on $A$. Then $forall n, k in NN$, there exists finite $S'$ such that whenever $S'$ is $k$-coloured, there exists a copy of $X^n$ that is $A$-invariant.

    So we are "boosting the colouring from $A$-constant to $A$-invariant".
]
#proof[
    We use induction on $n$ (and all $k$ at once). $n = 1$ is by assumption. Suppose it is true for $n - 1$. Fix $k in NN$. Let $S$ be a finite set such that whenever $S$ is $k^abs(X)$-coloured, there exists an $A$-invariant copy of $X^(n - 1)$, and let $T$ be a finite set such that whenever $T$ is $k^abs(S)$-coloured, there exists an isometric copy of $X$ with $A$ monochromatic. We claim that $S times T$ works for $X^n$.

    Let $c$ be a $k$-colouring of $S times T$. By definition of $T$, if we look at the $k^abs(S)$-colouring $c'(t) = (c(s_1, t), c(s_2, t), ..., c(s_abs(S), t))$, we have an isometric copy of $X$ with $A$ monochromatic. This induces a colouring of $S$ as follows: $c''(s) = (c(s, a), c(s, x_1), ..., c(s, x_(abs(X) - abs(A))))$ for any $a in A$ (this is well-defined as $A$ is monochromatic). This is a $k^(abs(X) - abs(A) + 1)$-colouring. So by the choice of $S$, there exists an isometric copy of $X^(n - 1)$ that is $A$-invariant. Thus we are done, since the Cartesian product of this copy with the copy of $X$ in $T$ is $A$-invariant.
]
#theorem("Křiž")[
    Every regular $m$-gon is Ramsey.
]
#proof[
    // TODO: see Maria's email for more complete version
    Let $X = {v_1, ..., v_m}$ be a regular $m$-gon. We will find an isometric copy of $sqrt(m) X$ of the form $(v_1, ..., v_m)$, $(v_2, ..., v_m, v_1)$, $(v_3, ..., v_m, v_1, v_2)$, ..., $(v_m, v_1, ..., v_(m - 1))$. We will show by induction on $r$ and all $k in NN$ at once that we can find an isometric copy of $X$ with ${v_1, ..., v_r}$ monochromatic.

    Fix a $k$-colouring. $r = 1$ is trivial, as just a point. $r = 2$ is true as it is two points at a fixed distance which we showed is Ramsey. Assume true for $r$ and all $k$. ${v_1, ..., v_r}$ is Ramsey, so for all $k$, exists $S$ such that whenever $S$ is $k$-coloured, there is a monochromatic isometric copy of ${v_1, ..., v_r}$. Fix a $k$-colouring $c$. By our product argument, there exists $S$ and $N$ such that we have an isometric copy of $X^N$ (we will choose $N$ to be as big as we want) on which the colouring ${v_1, ..., v_r}$-invariant.

    The clever part: view $X$ as an alphabet with symbols ${v_1, ..., v_m}$. We will colour $(m - 1)$-sets, ${a_1 < dots.c < a_(m - 1)}$, in $[N]$ as follows: $
        w_1: 1...1 limits(2)_(a_1) 1...1 limits(3)_(a_2) 1...1 ... 1...1 limits(m)_(a_(m - 1)) \
        w_2: 1...1 limits(3)_(a_1) 1...1 limits(4)_(a_2) 1...1 ... 1...1 limits(1)_(a_(m - 1)) \
        dots.v \
        w_r: 1...1 med limits(r + 1)_(a_1) med 1...1 med limits(r + 2)_(a_2) med 1...1 ... 1...1 med limits(r - 1)_(a_(m - 1))
    $ Colour by $c'({a_1, ..., a_(m - 1)}) = (c(w_1), ..., c(w_(r - 1)))$, this is a $k^r$-colouring of $[N]^((m - 1))$. As $N$ can be taken to be as big as needed, by Ramsey, there exists a monochromatic size $m$ set. By relabelling, we may assume that this set is ${v_1, ..., v_m}$. $
        limits(med)_1 limits(med)_2 ... limits(med)_m 11...1
    $ Now look at the following: $
        x_1: v_1 v_2 ... v_m 1 1 ... 1 \
        y_2: v_1 v_2 v_3 ... v_m v_1 1 1 ... 1 \
        x_2: v_1 v_3 ... v_m v_1 v_2 1 1 ... 1 \
        y_2: v_3 v_4 ... v_m v_2 v_1 1 1 ... 1 \
        dots.v \
        x_r: v_1 v_(r + 1) v_(r + 2) ... v_m v_1 ... v_(r - 1) \
        y_r: v_(r + 1) v_(r + 2) ... v_(r - 1) v_1
    $ With this construction, we note that the colour of $y_i$ is the same as the colouring of $x_(i + 1)$, since under $c(w_i)$, they must be the same. Now look at $(v_1, ..., v_m)$, $(v_2, ..., v_m, v_1)$, ..., $(v_(r + 1), ..., v_r, v_(r - 1))$. They all have the same colour (ignoring the 1's). They thus form a monochromatic copy of ${v_1, ..., v_(r + 1)}$.
]
#remark[
    - Same proof works for any cyclic set, i.e. a set $X = {v_1, ..., v_n}$ such that $x |-> x_(i + 1 mod n)$ is a symmetry of the set, or equivalently, there exists a cyclic transitive symmetry group on $X$.
]
#example[
    Triangular prism is cyclic set, as symmetry group is given by the group generated by the rotatino by $120^o$ and reflection. So triangular prism is Ramsey.
]