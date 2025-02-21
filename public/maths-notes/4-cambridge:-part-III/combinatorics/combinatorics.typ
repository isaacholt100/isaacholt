#import "@preview/fletcher:0.5.2" as fletcher: diagram, node, edge
#import "@preview/cetz:0.3.1" as cetz: canvas, draw
#import "../../diagram-style.typ": *
#import "@preview/cetz-plot:0.1.0": plot
#import "@preview/cetz-venn:0.1.2"
#import "@preview/suiji:0.3.0": *
#import "../../template.typ": *

#show: doc => template(doc, hidden: (), slides: false)
#set document(
    title: "Combinatorics Notes",
    author: "Isaac Holt",
    keywords: ("combinatorics", "graphs", "discrete")
)

#let line-style(color) = (fill: color, stroke: color, mark: (end: ">"))
#let diamond(width, height) = {
    import cetz.draw: *

    line((width / 2, 0), (0, height / 2))
    line((width / 2, 0), (width, height / 2))
    line((width / 2, height), (0, height / 2))
    line((width / 2, height), (width, height / 2))
}

= Set systems

== Chains and antichains

#note[
    The ideas in combinatorics often occur in the proofs, so it is advisable to learn the techniques used in proofs, rather than just learning the results and not their proofs.
]
#definition[
    Let $X$ be a set. A *set system* on $X$ (also called a *family of subsets of $X$*) is a collection $cal(F) subset.eq powset(X)$.
]<def:family>
#notation[
    $X^((r)) := {A subset.eq X: |A| = r}$ denotes the family of subsets of $X$ of size $r$.
]
#remark[
    Usually, we take $X = [n] = {1, ..., n}$, so $|X^((r))| = binom(n, r)$.
]
#notation[
    For brevity, we write e.g. $[4]^((2)) = {12, 13, 14, 23, 24, 34}$.
]
#definition[
    We can visualise $powset(X)$ as a graph by joining nodes $A in powset(X)$ and $B in powset(X)$ if $|A Delta B| = 1$, i.e. if $A = B union {i}$ for some $i in.not B$, or vice versa.

    This graph is the *discrete cube* $Q_n$.
]<def:discrete-cube>
#fig-example[
    #figure(
        grid(
            columns: 3,
            column-gutter: 2em,
            diagram(
                node-defocus: 0,
                spacing: (3em, 2em),
                mark-scale: 70%,
                node-outset: 0pt,
                node-inset: 4pt,
                $
                    & 123 edge("dl") edge("d") edge("dr") & \
                    12 edge("d") edge("dr") & 13 edge("dl") edge("d") edge("dr") & 23 edge("dl") edge("d") \
                    1 edge("dr") & 2 edge("d") & 3 edge("dl") \
                    & emptyset &
                $
            ),
            canvas({
                import cetz.draw: *

                draw.rect((1, 4.5), (2, 5.5), radius: 50%, name: "l3")
                draw.rect((0, 3), (3, 4), radius: 50%, name: "l2")
                draw.rect((0, 1.5), (3, 2.5), radius: 50%, name: "l1")
                draw.rect((1, 0), (2, 1), radius: 50%, name: "l0")
                content("l3", box[$X^((3))$])
                content("l2", box[$X^((2))$])
                content("l1", box[$X^((1))$])
                content("l0", box[$X^((0))$])
            }),
            canvas({
                import cetz.draw: *

                draw.rect((2, 6), (3, 7), radius: 50%, name: "l4")
                draw.rect((1, 4.5), (4, 5.5), radius: 50%, name: "l3")
                draw.rect((0, 3), (5, 4), radius: 50%, name: "l2")
                draw.rect((1, 1.5), (4, 2.5), radius: 50%, name: "l1")
                draw.rect((2, 0), (3, 1), radius: 50%, name: "l0")
                content("l4", box[$X^((4))$])
                content("l3", box[$X^((3))$])
                content("l2", box[$X^((2))$])
                content("l1", box[$X^((1))$])
                content("l0", box[$X^((0))$])
            })
        ),
        caption: [$Q_3$, $Q_3$, and $Q_4$.]
    )
]
#remark[
    Alternatively, we can view $Q_n$ as an $n$-dimensional unit cube ${0, 1}^n$ by identifying e.g. ${1, 3} subset.eq [5]$ with $10100$ (i.e. identify $A$ with $bb(1)_A$, the characteristic/indicator function of $A$).
]
#fig-example[
    #figure(
        canvas({
            import cetz.draw: *

            let shift-x = 1.25
            let shift-y = 1.25
            let height = 2.5
            let (A, B, C, D, E, F, G, H) = ((0, 0), (height, 0), (0, height), (height, height), (shift-x, shift-y), (height + shift-x, shift-y), (shift-x, height + shift-y), (height + shift-x, height + shift-y))
            let sets = ($emptyset$, $1$, $3$, $13$, $2$, $12$, $23$, $123$)

            draw.rect(A, D, name: "front")
            draw.rect(E, H, name: "back")
            line(A, E)
            line(B, F)
            line(C, G)
            line(D, H)

            for (i, point) in (A, B, C, D, E, F, G, H).enumerate() {
                circle(point, ..point-style, name: "point-" + str(i))
                content("point-" + str(i), box(inset: 0.2em)[#sets.at(i)], anchor: "south-east")
            }

            line((6, 0), (7, 0), mark: (end: ">"), fill: black, name: "ax-1")
            content((), $1$, anchor: "west")
            line((6, 0), (6 + shift-x / height, shift-y / height), mark: (end: ">"), fill: black, name: "ax-3")
            content((), $2$, anchor: "south-west")
            line((6, 0), (6, 1), mark: (end: ">"), fill: black, name: "ax-3")
            content((), $3$, anchor: "south")
        }),
        caption: [The cube $Q_3$ as the unit cube in $RR^3$]
    )
]
#definition[
    $cal(F) subset.eq powset(X)$ is a *chain* if $forall A, B in cal(F)$, $A subset.eq B$ or $B subset.eq A$.
]<def:chain>
#example[
    - $cal(F) = {23, 1235, 123567}$ is a chain.
    - $cal(F) = {emptyset, 1, 12, ..., [n]} subset.eq powset([n])$ is a chain.
]
#definition[
    $cal(F) subset.eq powset(X)$ is an *antichain* if $forall A != B in cal(F)$, $A subset.eq.not B$.
]<def:antichain>
#fig-example[
    #figure(
        grid(
            columns: (1fr, 1fr),
            column-gutter: 2em,
            canvas({
                import cetz.draw: *

                diamond(3, 4)
                hobby((1.4, 0.3), (1.45, 1), (1.4, 2), (1.55, 3), (1.5, 3.5), stroke: diagram-colors.red)
            }),
            canvas({
                import cetz.draw: *

                diamond(3, 4)
                for point in ((0.4, 2), (1.4, 1), (2, 1.8), (1.2, 3)) {
                    circle(point, ..point-style)
                }
            }),
        ),
        caption: [A chain and antichain.]
    )
]
#example[
    - $cal(F) = {23, 137}$ is an antichain.
    - $cal(F) = {1, ..., n} subset.eq powset([n])$ is an antichain.
    - More generally, $cal(F) = X^((r))$ is an antichain for any $r$.
]
#proposition[
    A chain and an antichain can meet at most once.
]
#proofhints[
    Trivial.
]
#proof[
    By definition.
]
#proposition[
    A chain $cal(F) subset.eq powset([n])$ can have at most $n + 1$ elements.
]
#proofhints[
    Trivial.
]
#proof[
    For each $0 <= r <= n$, $cal(F)$ can contain at most $1$ $r$-set (set of size $r$).
]
#theorem("Sperner's Lemma")[
    Let $cal(F) subset.eq powset(X)$ be an antichain. Then $|cal(F)| <= binom(n, floor(n\/2))$, i.e. the maximum size of an antichain is achieved by the set of $X^((floor(n\/2)))$.
]<thm:sperners-lemma>
#proofhints[
    - Let $r < n/2$.
    - Let $G$ be bipartite subgraph of $Q_n$ spanned by $X^((r)) union X^((r + 1))$.
    - By considering an expression and upper bound for number of $S$-$Gamma(S)$ edges in $G$ for each $S subset.eq X^((r))$, show that there is a matching from $X^((r))$ to $X^((r + 1))$.
    - Reason that this induces a matching from $X^((r))$ to $X^((r - 1))$ for each $r > n/2$.
    - Reason that joining these matchings together, together with length $1$ chains of subsets of $X^((floor(n\/2)))$ not included in a matching, result in a partition of $powset(X)$ into $binom(n, floor(n\/2))$ chains, and conclude result from here.
]
#proof[
    We use the idea: from "a chain meets each layer in $<=1$ points, because a layer is an antichain", we try to decompose the cube into chains.
    #fig-example[
        #figure(
            canvas({
                import cetz.draw: *

                diamond(3, 4)
                hobby((1.4, 0.3), (1.45, 1), (1.4, 2), (1.55, 3), (1.5, 3.5), stroke: diagram-colors.red)
                hobby((1, 1.1), (0.95, 1.7), (1.05, 2.4), stroke: diagram-colors.red)
                hobby((2, 0.8), (2.1, 1.2), (2.2, 2.7), stroke: diagram-colors.red)
                hobby((1.7, 0.6), (1.65, 1.2), (1.75, 2), stroke: diagram-colors.red)
                hobby((1.8, 2.2), (1.9, 2.5), (1.8, 3.4), stroke: diagram-colors.red)
                hobby((1, 0.8), (0.8, 1.2), (0.6, 2), (0.7, 2.4), (0.8, 2.7), (1.1, 3.2), stroke: diagram-colors.red)
            }),
            caption: [Decomposition of $powset(X)$ into chains.]
        )
    ]
    In particular, we partition $powset(X)$ into $binom(n, floor(n\/2))$ chains, so each subset of $X$ appears exactly once in one chain. Then we are done (since to form an antichain, we can pick at most one element from each chain). To achieve this, it is sufficient to find:
    - For each $r < n/2$, a matching from $X^((r))$ to $X^((r + 1))$ (a matching is a set of disjoint edges, one for each point in $X^((r))$).
    - For each $r > n/2$, a matching from $X^((r))$ to $X^((r - 1))$.
    Then put these matchings together to form a set of chains, each passing through $X^((floor(n\/2)))$.
    #fig-example[
        #figure(
            canvas({
                import cetz.draw: *

                // draw.rect((2, 6), (3, 7), radius: 50%, name: "l4")
                // draw.rect((-1, 4.5), (6, 5.5), radius: 50%, name: "l3")
                // draw.rect((0, 3), (5, 4), radius: 50%, name: "l2")
                // draw.rect((1, 1.5), (4, 2.5), radius: 50%, name: "l1")
                // draw.rect((2, 0), (3, 1), radius: 50%, name: "l0")
                circle((0, 0), radius: (4, 0.8))
                circle((0, 2), radius: (3, 0.6))
                circle((0, 4), radius: (2, 0.4))
                circle((0, -2), radius: (3, 0.6))
                circle((0, -4), radius: (2, 0.4))

                content((6, -4), $X^((n \/ 2 - 2))$)
                content((6, -2), $X^((n \/ 2 - 1))$)
                content((6, 0), $X^((n \/ 2))$)
                content((6, 2), $X^((n \/ 2 + 1))$)
                content((6, 4), $X^((n \/ 2 + 2))$)
                // content("l3", box[$X^((3))$])
                // content("l2", box[$X^((2))$])
                // content("l1", box[$X^((1))$])
                // content("l0", box[$X^((0))$])
                let N1 = 11
                let N2 = 5
                let N3 = 3
                let points1 = range(0, N1 + 1).map(i => (-3.6 + 7.2 * i / N1, 0))
                let points2 = range(0, N2 + 1).map(i => (-2.6 + 5.2 * i / N2, 2))
                let points3 = range(0, N3 + 1).map(i => (-1.6 + 3.2 * i / N3, 4))
                for (i, point) in (..points1, ..points2, ..points3).enumerate() {
                    circle(point, ..point-style, name: "point-" + str(i))
                    circle((point.at(0), -point.at(1)), ..point-style, name: "point-n-" + str(i))
                }

                set-style(
                    stroke: (
                        paint: diagram-colors.red,
                        // thickness: 1pt,
                    )
                )
                line("point-12", "point-0")
                line("point-13", "point-1")
                line("point-14", "point-4")
                line("point-15", "point-5")
                line("point-16", "point-8")

                line("point-17", "point-10")
                line("point-12", "point-18")
                line("point-13", "point-19")
                line("point-15", "point-20")
                line("point-17", "point-21")

                line("point-n-12", "point-0")
                line("point-n-13", "point-2")
                line("point-n-14", "point-3")
                line("point-n-15", "point-6")
                line("point-n-16", "point-8")
                line("point-n-17", "point-9")

                line("point-n-18", "point-n-13")
                line("point-n-19", "point-n-14")
                line("point-n-20", "point-n-16")
                line("point-n-21", "point-n-17")
            }),
            caption: [Example of joining matchings in the 5 middle layers, for $n$ even.]
        )
    ]
    If a subset $X^((floor(n\/2)))$ has a chain passing through it, then this chain is unique. The subsets with no chain passing through form their own one-element chain. By taking complements, it is enough to construct the matchings just for $r < n/2$ (since a matching from $X^((r))$ to $X^((r + 1))$ induces a matching from $X^((n - r - 1))$ to $X^((n - r))$: there is a correspondence between $X^((r))$ and $X^((n - r))$ by taking complements, and taking complements reverse inclusion, so edges in the induced matching are guaranteed to exist).
    
    Let $G$ be the (bipartite) subgraph of $Q_n$ spanned by $X^((r)) union X^((r + 1))$. For any $S subset.eq X^((r))$, the number of $S$-$Gamma(S)$ edges in $G$ is $|S|(n - r)$ (counting from below) since there are $n - r$ ways to add an element. This number is $<= |Gamma(S)| (r + 1)$ (counting from above), since $r + 1$ ways to remove an element.
    #fig-example[
        #figure(
            canvas({
                import cetz.draw: *

                // draw.rect((2, 6), (3, 7), radius: 50%, name: "l4")
                // draw.rect((-1, 4.5), (6, 5.5), radius: 50%, name: "l3")
                // draw.rect((0, 3), (5, 4), radius: 50%, name: "l2")
                // draw.rect((1, 1.5), (4, 2.5), radius: 50%, name: "l1")
                // draw.rect((2, 0), (3, 1), radius: 50%, name: "l0")
                circle((0, 3), radius: (4, 0.8))
                circle((0, 0), radius: (3, 0.6))
                set-style(
                    stroke: diagram-colors.red,
                    fill: diagram-colors.light-red
                )
                circle((0, 3), radius: (1.5, 0.5), name: "neighbourhood")
                circle((0, 0), radius: (1.05, 0.35), name: "set")
                line((-1.5, 3), (-1.05, 0))
                line((1.5, 3), (1.05, 0))

                set-style(
                    stroke: (dash: "dashed", paint: diagram-colors.red)
                )

                line((-1.5, 3), (-1.95, 0))
                line((1.5, 3), (1.95, 0))
                line((-1.5, 3), (-1.5, 0))
                line((1.5, 3), (1.5, 0))

                content((6, 0), $X^((r))$)
                content((6, 3), $X^((r + 1))$)    
                content("set", $S$)
                content("neighbourhood", $Gamma(S)$)
            })
        )
    ]
    Hence $|Gamma(S)| >= (|S| (n - r))/(r + 1) >= |S|$ as $r < n/2$. So by Hall's theorem, since there is a matching from $S$ to $Gamma(S)$, there is a matching from $X^((r))$ to $X^((r + 1))$.
]
#remark[
    The proof above doesn't tell us when we have equality in Sperner's Lemma.
]
#definition[
    For $cal(F) subset.eq X^((r))$ ($1 <= r <= n$), the *shadow* of $cal(F)$ is the set of subsets which can be obtained by removing one element from a subset in $cal(F)$: $
        partial cal(F) = partial^- cal(F) := {B in X^((r - 1)): B subset.eq cal(F) "for some" A in cal(F)}.
    $
]<def:shadow>
#fig-example[
    #figure(
        canvas({
            import cetz.draw: *

            // draw.rect((2, 6), (3, 7), radius: 50%, name: "l4")
            // draw.rect((-1, 4.5), (6, 5.5), radius: 50%, name: "l3")
            // draw.rect((0, 3), (5, 4), radius: 50%, name: "l2")
            // draw.rect((1, 1.5), (4, 2.5), radius: 50%, name: "l1")
            // draw.rect((2, 0), (3, 1), radius: 50%, name: "l0")
            circle((0, 0), radius: (4, 0.8))
            circle((0, 3), radius: (3, 0.6))
            set-style(
                stroke: diagram-colors.red,
                fill: diagram-colors.light-red
            )
            circle((0, 0), radius: (1.5, 0.5), name: "neighbourhood")
            circle((0, 3), radius: (1.05, 0.35), name: "set")

            set-style(
                stroke: (dash: "dashed", paint: diagram-colors.red)
            )

            line((-1.5, 0), (-1.05, 3))
            line((1.5, 0), (1.05, 3))

            content((6, 0), $X^((r - 1))$)
            content((6, 3), $X^((r))$)    
            content("set", $cal(F)$)
            content("neighbourhood", $partial cal(F)$)
        }),
        caption: [A family $cal(F) subset.eq X^((r))$ and its shadow.]
    )
]
#example[
    Let $cal(F) = {123, 124, 134, 137} in [7]^((3))$. Then $partial cal(F) = {12, 13, 23, 14, 24, 34, 17, 37}$.
]
#proposition("Local LYM")[
    Let $cal(F) subset.eq X^((r))$, $1 <= r <= n$. Then $
        (|cal(F)|)/binom(n, r) <= (|partial cal(F)|)/binom(n, r - 1).
    $ i.e. the proportion of the level occupied by $partial cal(F)$ is at least the proportion of the level occupied by $cal(F)$.
]<prop:local-lym>
#proofhints[
    Find equation and upper bound for number of $cal(F)$-$partial cal(F)$ edges in $Q_n$.
]
#proof[
    The number of $cal(F)$-$partial cal(F)$ edges in $Q_n$ is $abs(cal(F)) r$ (counting from above, since we can remove any of $r$ elements from $abs(cal(F))$ sets) and is $<= |partial cal(F)| (n - r + 1)$ (since adding one of the $n - r + 1$ elements not in $A in partial cal(F)$ to $A$ may not result in a subset of $cal(F)$). Hence, $
        abs(cal(F)) / abs(partial cal(F)) <= (n - r + 1)/r = binom(n, r)\/binom(n, r - 1). #qedhere
    $
]
#remark[
    For equality in Local LYM, we must have that $forall A in cal(F)$, $forall i in A$, $forall j in.not A$, we must have $(A - {i}) union {j} in cal(F)$, i.e. $cal(F) = emptyset$ or $X^((r))$ for some $r$.
]
#notation[
    Write $cal(F)_r$ for $cal(F) sect X^((r))$.
]
#theorem("LYM Inequality")[
    Let $cal(F) subset.eq powset(X)$ be an antichain. Then $
        sum_(r = 0)^n (|cal(F) sect X^((r))|)/binom(n, r) <= 1,
    $ i.e. the proportions of each layer occupied add to $<= 1$.
]<thm:lym-inequality>
#fig-example[
    #figure(
        canvas({
            import cetz.draw: *

            diamond(3, 4)
            line((0.75, 3), (1, 3), stroke: diagram-colors.red)
            line((1.2, 2), (2.2, 2), stroke: diagram-colors.red)
            line((2.2, 2.5), (2.5, 2.5), stroke: diagram-colors.red)
            line((1, 0.8), (1.15, 0.8), stroke: diagram-colors.red)
        })
    )
]
#proofhints[
    - Method 1: show the result for the sum $sum_(r = k)^n$ by induction, starting with $k = n$. Use local LYM, and that $partial cal(F)_n$ and $cal(F)_(n - 1)$ are disjoint (and analogous results for lower levels).
    - Method 2: let $cal(C)$ be uniformly random maximal chain, find an expression for $Pr(cal(C) "meets" cal(F))$.
    - Method 3: determine number of maximal chains in $X$, determine number of maximal chains passing through a fixed $r$-set, deduce maximal number of chains passing through $cal(F)$.
]
#proof[
    *Method 1*: "bubble down with local LYM". We trivially have that $cal(F)_n \/ binom(n, n) <= 1$. $partial cal(F)_n$ and $cal(F)_(n - 1)$ are disjoint, as $cal(F)$ is an antichain, so $
        (|partial cal(F)_n|)/binom(n, n - 1) + (|cal(F)_(n - 1)|)/binom(n, n - 1) = (|partial cal(F)_n union cal(F)_(n - 1)|)/binom(n, n - 1) <= 1.
    $ So by local LYM, $ (|cal(F)_n|)/binom(n, n) + (|cal(F)_(n - 1)|)/binom(n, n - 1) <= 1. $ Now, $partial (partial cal(F)_n union cal(F)_(n - 1))$ and $cal(F)_(n - 2)$ are disjoint, as $cal(F)$ is an antichain, so $
        (|partial(partial cal(F)_n union cal(F)_(n - 1))|)/binom(n, n - 2) + (|cal(F)_(n - 2)|)/binom(n, n - 2) <= 1.
    $ So by local LYM, $
        (|partial cal(F)_n union cal(F)_(n - 1)|)/binom(n, n - 1) + (|cal(F)_(n - 2)|)/binom(n, n - 2) <= 1.
    $ So $ (|cal(F)_n|)/binom(n, n) + (|cal(F)_(n - 1)|)/binom(n, n - 1) + (|cal(F)_(n - 2)|)/binom(n, n - 2) <= 1. $ Continuing inductively, we obtain the result.

    *Method 2*: Choose uniformly at random a maximal chain $cal(C)$ (i.e. $C_0 subset.neq C_1 subset.eq dots.c subset.neq C_n$ with $abs(C_r) = r$ for all $r$). For any $r$-set $A$, $Pr(A in cal(C)) = 1\/binom(n, r)$, since all $r$-sets are equally likely. So $Pr(cal(C) "meets" cal(F)_r) = abs(cal(F)_r)\/binom(n, r)$, since the events are disjoint. Thus, $Pr(cal(C) "meets" cal(F)) = sum_(r = 0)^n abs(cal(F)_r)\/binom(n, r) <= 1$ since the events are disjoint (since $cal(F)$ is an antichain).
    #fig-example[
        #figure(
            canvas({
                import cetz.draw: *

                diamond(3, 4)
                line((0.75, 3), (1, 3), stroke: diagram-colors.red)
                line((1.2, 2), (2.2, 2), stroke: diagram-colors.red)
                line((2.2, 2.5), (2.5, 2.5), stroke: diagram-colors.red)
                line((1, 0.8), (1.15, 0.8), stroke: diagram-colors.red)
                hobby((1.5, 0), (1.4, 1), (1.5, 1.5), (1.5, 4), stroke: diagram-colors.blue)
                content((1.7, 1.3), $cal(C)$)
                content((2.9, 0.9), $Q_n$)
            }),
            caption: [A random maximal chain $cal(C)$.]
        )
    ]
    
    *Method 3* (same as method 2 but counting instead of using probability): The number of maximal chains is $n!$, and the number through any fixed $r$-set is $r! (n - r)!$, so $sum_r abs(cal(F)_r) r! (n - r)! <= n!$.
]
#remark[
    To have equality in LYM, we must have equality in each use of local LYM in proof method 1. In this case, the maximum $r$ with $cal(F)_r != emptyset$ has $cal(F)_r = X^((r))$. So equality holds iff $cal(F) = X^((r))$ for some $r$. Hence equality in Sperner's Lemma holds iff $cal(F) = X^((floor(n\/2)))$ or $cal(F) = X^((ceil(n\/2)))$.
]

== Two total orders on $X^((r))$

#definition[
    Let $A != B$ be $r$-sets, $A = a_1 ... a_r$, $B = b_1 ... b_r$ (where $a_1 < dots.c < a_n$, $b_1 < dots.c < b_n$). $A < B$ in the *lexicographic (lex)* ordering if for some $j$, we have $a_i = b_i$ for all $i < j$, and $a_j < b_j$. "use small elements".
]<def:lex-order>
#example[
    The elements of $[4]^((2))$ in lexicographic order are $12, 13, 14, 23, 24, 34$. The elements of $[6]^((3))$ in lexicographic order are $123, 124, 125, 126, 134, 135, 136, 145, 146, 156, 234, 235, 236, 245, 246, 256, 345, 346, 356, 456$.
]
#definition[
    Let $A != B$ be $r$-sets, $A = a_1 ... a_r$, $B = b_1 ... b_r$ (where $a_1 < dots.c < a_n$, $b_1 < dots.c < b_n$). $A < B$ in the *colexicographic (colex)* order if for some $j$, we have $a_i = b_i$ for all $i > j$, and $a_j < b_j$. "avoid large elements".
]<def:colex-order>
#example[
    The elements of $[4]^((2))$ in colex order are $12, 13, 23, 14, 24, 34$. The elements of $[6]^((3))$ are $123, 124, 134, 234, 125, 135, 235, 145, 245, 345, 126, 136, 236, 146, 246, 346, 156, 256, 356, 456$.
]
#remark[
    Lex and colex are both total orders. Note that in colex, $[n - 1]^((r))$ is an initial segment of $[n]^((r))$ (this does not hold for lex). So we can view colex as an enumeration of $NN^((r))$.
]
#remark[
    $A < B$ in colex iff $A^c < B^c$ in lex with ground set order reversed.
]
#remark[
    By Local LYM, we know that $abs(partial cal(F)) >= abs(cal(F)) r\/(n - r + 1)$. Equality is rare (only for $cal(F) = X^((r))$ for $0 <= r <= n$). What happens in between, i.e., given $abs(cal(F))$, how should we choose $cal(F)$ to minimise $abs(partial cal(F))$?

    You should be able to convince yourself that if $abs(cal(F)) = binom(k, r)$, then we should take $cal(F) = [k]^((r))$. If $binom(k, r) < abs(cal(F)) < binom(k + 1, r)$, then convince yourself that we should take some $[k]^((r))$ plus some $r$-sets in $[k + 1]^((r))$.

    E.g. for $cal(F) subset.eq X^((r))$ with $abs(cal(F)) = binom(8, 3) + binom(4, 2)$, take $cal(F) = [8]^((3)) union \{9 union B: B in [4]^((2))\}$.
]
#remark[
    We want to show that if $cal(F) subset.eq X^((r))$ and $cal(C) subset.eq X^((r))$ is the initial segment of colex with $abs(cal(C)) = abs(cal(F))$, then $abs(partial cal(C)) <= abs(partial cal(F))$. In particular, if $abs(cal(F)) = binom(k, r)$ (so $cal(C) = [k]^((r))$), then $abs(partial cal(F)) >= binom(k, r - 1)$.
]

== Compressions

#remark[
    We want to transform $cal(F) subset.eq X^((r))$ into some $cal(F)' subset.eq X^((r))$ such that:
    - $abs(cal(F)') = abs(cal(F))$,
    - $abs(partial cal(F)') <= abs(partial cal(F))$.
    Ideally, we want a family of such "compressions" $cal(F) -> cal(F)' -> ... -> cal(B)$ such that either $cal(B) = cal(C)$, or $cal(B)$ is similar enough to $cal(C)$ that we can directly check that $abs(partial cal(C)) <= abs(partial cal(B))$.
]
#definition[
    Let $1 <= i < j <= n$. The *$i j$-compression* $C_(i j)$ is defined as:
    - For $A in X^((r))$, $
        C_(i j) (A) = cases(
            (A union i) - j & "if" j in A\, i in.not A,
            A & "otherwise"
        ).
    $
    - For $cal(F) subset.eq X^((r))$, $C_(i j)(cal(F)) = {C_(i j) (A): A in cal(F)} union {A in cal(F): C_(i j) (A) in cal(F)}$.
    "replace $j$ by $i$ where possible". This definition is inspired by "colex prefers $i < j$ to $j$".
    Note that $C_(i j) (cal(F)) subset.eq X^((r))$ and $abs(C_(i j)(cal(F))) = abs(cal(F))$.
]<def:compression>
#fig-example[
    #figure(
        canvas({
            import cetz.draw: *

            let h = 2.
            rect((-h, -h), (h, h), name: "r")
            content((-h, -h), box(inset: 0.2em)[$A$], anchor: "north-east")
            content((-h, h), box(inset: 0.2em)[$A union j$], anchor: "south-east")
            content((h, -h), box(inset: 0.2em)[$A union i$], anchor: "north-west")
            content((h, h), box(inset: 0.2em)[$A union i j$], anchor: "south-west")
            let delta = 0.3
            line((-h + delta, h - delta), (h - delta, -h + delta), ..line-style(diagram-colors.red))
            let x-axis-sep = 1
            let y-axis-sep = 1.7
            line((-h + delta, -h - x-axis-sep), (h - delta, -h - x-axis-sep), ..line-style(black), name: "i-axis")
            line((-h - y-axis-sep, -h + delta), (-h - y-axis-sep, h - delta), ..line-style(black), name: "j-axis")
            content("i-axis.mid", box(inset: (top: 0.5em))[$i$], anchor: "north")
            content("j-axis.mid", box(inset: (right: 0.5em))[$j$], anchor: "east")
        }),
        caption: [Applying an $i j$-compression to $A in X^((r))$.]
    )
]
#definition[
    $cal(F)$ is *$i j$-compressed* if $C_(i j) (cal(F)) = cal(F)$.
]<def:compressed>
#example[
    Let $cal(F) = {123, 134, 234, 235, 146, 567}$, then $C_(1 2) (cal(F)) = {123, 134, 234, 135, 146, 567}$.
]
#lemma[
    Let $cal(F) subset.eq X^((r))$, $1 <= i < j <= n$. Then $abs(partial C_(i j) (cal(F))) <= abs(partial cal(F))$.
]
#proofhints[
    - Let $cal(F)' = C_(i j)(cal(F))$, $B in partial cal(F)' - partial cal(F)$.
    - Show that $i in B$ and $j in.not B$.
    - Reason that $B union j - i in partial cal(F)'$.
    - Show that $B union j - i in.not partial cal(F)'$ by contradiction.
    - Conclude the result.
]
#proof[
    Let $cal(F)' = C_(i j)(cal(F))$. Let $B in partial cal(F)' - partial cal(F)$. We'll show that $i in B$, $j in.not B$, $(B union j) - i in partial cal(F) - partial cal(F)'$.
    #fig-example[
        #figure(
            canvas({
                import cetz.draw: *

                let h = 2
                rect((-h, -h), (h, h), name: "r")
                content((-h, -h), box(inset: 0.2em)[$B - i$], anchor: "north-east")
                content((-h, h), box(inset: 0.2em)[$(B union j) - i$], anchor: "south-east")
                content((h, -h), box(inset: 0.2em)[$B$], anchor: "north-west")
                content((h, h), box(inset: 0.2em)[$B union j$], anchor: "south-west")
                let delta = 0.3
                line((h - delta, -h + delta), (-h + delta, h - delta), ..line-style(diagram-colors.red), stroke: (dash: "dashed", paint: diagram-colors.red))
                let x-axis-sep = 1
                let y-axis-sep = 2.5
                line((-h + delta, -h - x-axis-sep), (h - delta, -h - x-axis-sep), ..line-style(black), name: "i-axis")
                line((-h - y-axis-sep, -h + delta), (-h - y-axis-sep, h - delta), ..line-style(black), name: "j-axis")
                content("i-axis.mid", box(inset: (top: 0.5em))[$i$], anchor: "north")
                content("j-axis.mid", box(inset: (right: 0.5em))[$j$], anchor: "east")
            }),
        )
    ]
    Note that $B union x in cal(F)'$ and $B union x in.not cal(F)$ (since $B in.not partial cal(F)$) for some $x$. So $i in B union x$, $j in.not B union x$, $(B union x union j) - i in cal(F)$. We can't have $x = i$, since otherwise $(B union x union j) - i = B union j$, which gives $B in partial cal(F)$, a contradiction. So $i in B$ and $j in.not B$. Also, $B union j - i in partial cal(F)$, since $B union x union j - i in cal(F)$.
    
    Suppose $B union j - i in partial cal(F)'$: so $(B union j - i) union y in cal(F)'$ for some $y$. We cannot have $y = i$, since otherwise $B union j in cal(F)'$, so $B union j in cal(F)$ (as $j in B union j$), contradicting $B in.not partial cal(F)$. Hence $j in (B union j - i) union y$ and $i in.not (B union j - i) union y$. Thus, both $(B union j - i) union y$ and $B union y = C_(i j) ((B union j - i) union y)$ belong to $cal(F)$ (by definition of $cal(F)'$), contradicting $B in.not partial cal(F)$.
]
#remark[
    In the above proof, we actually showed that $partial C_(i j) (cal(F)) subset.eq C_(i j) (partial cal(F))$.
]
#definition[
    $cal(F) subset.eq X^((r))$ is *left-compressed* if $C_(i j) (cal(F)) = cal(F)$ for all $i < j$.
]<def:left-compressed>
#corollary[
    Let $cal(F) subset.eq X^((r))$. Then there exists a left-compressed $cal(B) subset.eq X^((r))$ with $abs(cal(B)) = abs(cal(F))$ and $abs(partial cal(B)) <= abs(partial cal(F))$.
]
#proofhints[
    Define a sequence $cal(F)_0, cal(F)_1, ...$ of subsets of $X^((r))$ with $sum_(A in cal(F)_k) sum_(i in A) i$ strictly decreasing.
]
#proof[
    Define a sequence $cal(F)_0, cal(F)_1, ...$ as follows: set $cal(F)_0 = cal(F)$. Having defined $cal(F)_0, ..., cal(F)_k$, if $cal(F)_k$ is left-compressed the end the sequence with $cal(F)_k$; if not, choose $i < j$ such that $cal(F)_k$ is not $i j$-compressed, and set $cal(F)_(k + 1) = C_(i j)(cal(F)_k)$.
    
    This must terminate after a finite number of steps, e.g. since $sum_(A in cal(F)_k) sum_(i in A) i$ is strictly decreasing with $k$. The final term $cal(B) = cal(F)_k$ satisfies $abs(cal(B)) = abs(cal(F))$, and $abs(partial cal(B)) <= abs(partial cal(F))$ by the above lemma.
]
#remark[
    - Another way of proving this is: among all $cal(B) subset.eq X^((r))$ with $abs(cal(F)) = abs(cal(F))$ and $abs(partial cal(B)) <= abs(partial cal(F))$, choose one with minimal $sum_(A in cal(B)) sum_(i in A) i$.
    - We can choose an order of the $C_(i j)$ so that no $C_(i j)$ is applied twice.
    - Any initial segment of colex is left-compressed, but the converse is false, e.g. ${123, 124, 125, 126}$ is left-compressed.
]
#definition[
    Let $U, V subset.eq X$, $abs(U) = abs(V)$, $U sect V = emptyset$ and $max U < max V$. Define the *$U V$-compression* $C_(U V)$ as:
    - For $A subset.eq X$, $
        C_(U V)(A) = cases(
            (A - V) union U & "if" V subset.eq A\, U sect A = emptyset,
            A & "otherwise"
        ).
    $
    - For $cal(F) subset.eq X^((r))$, $
        C_(U V) (cal(F)) = {C_(U V) (A): A in cal(F)} union {A in cal(F): C_(U V)(A) in cal(F)}.
    $
    We have $C_(U V)(cal(F)) subset.eq X^((r))$ and $abs(C_(U V)(cal(F))) = abs(cal(F))$.
    This definition is inspired by "colex prefers $23$ to $14$".
]
#definition[
    $cal(F)$ is *$U V$-compressed* if $C_(U V)(cal(F)) = cal(F)$.
]
#example[
    Let $cal(F) = {123, 124, 147, 237, 238, 149}$, then $C_(23, 14) (cal(F)) = {123, 124, 147, 237, 238, 239}$.
]
#example[
    We can have $abs(partial C_(U V)(cal(F))) > abs(partial cal(F))$.
    E.g. $cal(F) = {147, 157}$ has $abs(partial cal(F)) = 5$, but $C_(23, 14)(cal(F)) = {237, 157}$ has $abs(partial C_(23, 14)(cal(F))) = 6$.
]
#lemma[
    Let $cal(F) subset.eq X^((r))$ be $U V$-compressed for all $U, V subset.eq X$ with $abs(U) = abs(V)$, $U sect V = emptyset$ and $max U < max V$. Then $cal(F)$ is an initial segment of colex.
]
#proofhints[
    Suppose not, consider a compression for appropriate $U$ and $V$.
]
#proof[
    Suppose not, then there exists $A, B in X^((r))$ with $B < A$ in colex but $A in cal(F)$, $B in.not cal(F)$. Let $V = A \\ B$, $U = B \\ A$. Then $abs(V) = abs(U)$, $U sect V = emptyset$, and $max V > max U$ (since $max(A Delta B) in A$, by definition of colex). Since $cal(F)$ is $U V$-compressed, we have $C_(U V)(A) = B in C_(U V)(cal(F)) = cal(F)$, contradiction.
]
#lemma[
    Let $U, V subset.eq X$, $abs(U) = abs(V)$, $U sect V = emptyset$, $max U < max V$. For $cal(F) subset.eq X^((r))$, suppose that $
        forall u in U, exists v in V: quad cal(F) "is" #[$(U - u, V - v)$-compressed].
    $ Then $abs(partial C_(U V)(cal(F))) <= abs(partial cal(F))$.
]
#proofhints[
    - Let $cal(F)' = C_(U V)(cal(F))$, $B in partial cal(F)' - partial cal(F)$.
    - Show that $U subset.eq B$ and $V sect B = emptyset$.
    - Reason that $(B - U) union V in partial cal(F)$.
    - Show that $(B - U) union V in.not partial cal(F)'$ by contradiction.
]
#proof[
    Let $cal(F)' = C_(U V)(cal(F))$. For $B in partial cal(F)' - partial cal(F)$, we will show that $U subset.eq B$, $V sect B = emptyset$ and $B union V - U in partial cal(F) - partial cal(F)'$, then we will be done.
    
    #fig-example[
        #figure(
            canvas({
                import cetz.draw: *

                let h = 2
                rect((-h, -h), (h, h), name: "r")
                content((-h, -h), box(inset: 0.2em)[$B - U$], anchor: "north-east")
                content((-h, h), box(inset: 0.2em)[$(B union V) - U$], anchor: "south-east")
                content((h, -h), box(inset: 0.2em)[$B$], anchor: "north-west")
                content((h, h), box(inset: 0.2em)[$B union V$], anchor: "south-west")
                let delta = 0.3
                line((h - delta, -h + delta), (-h + delta, h - delta), ..line-style(diagram-colors.red), stroke: (dash: "dashed", paint: diagram-colors.red))
                let x-axis-sep = 1
                let y-axis-sep = 1
                line((-h + delta, -h - x-axis-sep), (h - delta, -h - x-axis-sep), ..line-style(black), name: "i-axis")
                line((-h - y-axis-sep, -h + delta), (-h - y-axis-sep, h - delta), ..line-style(black), name: "j-axis")
                content("i-axis.mid", box(inset: (top: 0.5em))[$union U$], anchor: "north")
                content("j-axis.mid", box(inset: (right: 0.5em))[$union V$], anchor: "east")
            }),
        )
    ]
    We have $B union x in cal(F)'$ for some $x in X$, and $B union x in.not cal(F)$. So $U subset.eq B union x$, $V sect (B union x) = emptyset$, and $(B union x union V) - U in cal(F)$, by definition of $C_(U V)$. If $x in U$, then $exists y in V$ such that $cal(F)$ is $(U - x, V - y)$-compressed, so from $(B union x union V) - U in cal(F)$, we have $B union y in cal(F)$, contradicting $B in.not partial cal(F)$. Thus $x in.not U$, so $U subset.eq B$ and $V sect B = emptyset$. Certainly $B union V - U in partial cal(F)$ (since $(B union x union V) - U in cal(F)$), so we just need to show that $B union V - U in.not partial cal(F)'$.
    
    Assume the opposite, i.e. $(B - U) union V in partial cal(F)'$, so $(B - U) union V union w in cal(F)'$ for some $w in X$. (This also belongs to $cal(F)$, since it contains $V$). If $w in U$, then since $cal(F)$ is $(U - w, V - z)$-compressed for some $z in V$, we have $B union z = C_(U - w, V - z)((B - U) union V union w) in cal(F)$, contradicting $B in.not partial cal(F)$. So $w in.not U$, and since $V subset.eq (B - U) union V union w$ and $U sect ((B - U) union V union w) = emptyset$, by definition of $C_(U V)$, we must have that both $(B - U) union V union w$ and $B union w = C_(U V)((B - U) union V union w) in cal(F)$, contradicting $B in.not partial cal(F)$.
]
#theorem("Kruskal-Katona")[
    Let $cal(F) subset.eq X^((r))$, $1 <= r <= n$, let $cal(C)$ be the initial segment of colex on $X^((r))$ with $abs(cal(C)) = abs(cal(F))$. Then $abs(partial cal(C)) <= abs(partial cal(F))$.

    In particular, if $abs(cal(F)) = binom(k, r)$, then $abs(partial cal(F)) >= binom(k, r - 1)$.
]<thm:kruskal-katona>
#proofhints[
    - Let $Gamma = {(U, V) in powset(X) times powset(X): abs(U) = abs(V) > 0, U sect V = emptyset, max U < max V} union {(emptyset, emptyset)}$.
    - Define a sequence $cal(F)_0, cal(F)_1, ...$ of $U V$-compressions where $(U, V) in Gamma$, choosing $abs(U) = abs(V) > 0$ minimal each time. Show that this $(U, V)$ satisfies condition of above lemma.
    - Reason that sequence terminates by considering $sum_(A in cal(F)_k) sum_(i in A) 2^i$.
]
#proof[
    Let $Gamma = {(U, V) in powset(X) times powset(X): abs(U) = abs(V) > 0, U sect V = emptyset, max U < max V} union {(emptyset, emptyset)}$. Define a sequence $cal(F)_0, cal(F)_1, ...$ of set systems in $X^((r))$ as follows: set $cal(F)_0 = cal(F)$. Having chosen $cal(F)_0, ..., cal(F)_k$, if $cal(F)_k$ is $(U V)$-compressed for all $(U, V) in Gamma$ then stop. Otherwise, choose $(U, V) in Gamma$ with $abs(U) = abs(V) > 0$ minimal, such that $cal(F)_k$ is not $(U V)$-compressed.
    
    Note that $forall u in U$, $exists v in V$ such that $(U - u, V - v) in Gamma$ (namely $v = min(V)$). So by the above lemma, $abs(partial C_(U V) (cal(F)_k)) <= abs(partial cal(F)_k)$. Set $cal(F)_(k + 1) = C_(U V) (cal(F)_k)$, and continue. The sequence must terminate, as $sum_(A in cal(F)_k) sum_(i in A) 2^i$ is strictly decreasing with $k$. The final term $cal(B) = cal(F)_k$ satisfies $abs(cal(B)) = abs(cal(F))$, $abs(partial cal(B)) <= abs(partial cal(F))$, and is $(U V)$-compressed for all $(U, V) in Gamma$. So $cal(B) = cal(C)$ by lemma before previous lemma.
]
#remark[
    - Equivalently, if $abs(cal(F)) = binom(k_r, r) + binom(k_(r - 1), r - 1) + dots.c + binom(k_s, s)$ where each $k_i > k_(i - 1)$ and $s >= 1$, then $
        abs(partial cal(F)) >= binom(k_r, r - 1) + binom(k_(r - 1), r - 2) + dots.c + binom(k_s, s - 1).
    $
    - Equality in Kruskal-Katona: if $abs(cal(F)) = binom(k, r)$ and $abs(partial cal(F)) = binom(k, r - 1)$, then $cal(F) = Y^((r))$ for some $Y subset.eq X$ with $abs(Y) = k$. However, it is not true in general that if $abs(partial cal(F)) = abs(partial C)$, then $cal(F)$ is isomorphic to $cal(C)$ (i.e. there is a permutation of the ground set $X$ sending $cal(F)$ to $cal(C)$).
]
#definition[
    For $cal(F) subset.eq X^((r))$, $0 <= r <= n - 1$, the *upper shadow* of $cal(F)$ is $
        partial^+ cal(F) := {A union x: A in cal(F), x in.not A} subset.eq X^((r + 1)).
    $
]<def:upper-shadow>
#corollary[
    Let $cal(F) subset.eq X^((r))$, $0 <= r <= n - 1$, let $cal(C)$ be the initial segment of lex on $X^((r))$ with $abs(cal(C)) = abs(cal(F))$. Then $abs(partial^+ cal(C)) <= abs(partial^+ cal(F))$.
]
#proofhints[
    By Kruskal-Katona.
]
#proof[
    By Kruskal-Katona, since $A < B$ in colex iff $A^c < B^c$ in lex with ground-set ($X$) order reversed, and if $cal(F)' = {A^c: A in cal(F)}$, then $abs(partial^+ cal(F)') = abs(partial cal(F))$.
]
#remark[
    The fact that the shadow of an initial segment of colex on $X^((r))$ is an initial segment of colex on $X^((r - 1))$ (since if $cal(C) = {A in X^((r)): A <= a_1 ... a_r "in colex"}$, then $partial cal(C) = {B in X^((r - 1)): B <= a_2 ... a_r "in colex"}$) gives:
]
#corollary[
    Let $cal(F) subset.eq X^((r))$, $1 <= r <= n$, $cal(C)$ be the initial segment of colex on $X^((r))$ with $abs(cal(C)) = abs(cal(F))$. Then $abs(partial^t cal(C)) <= abs(partial^t cal(F))$ for all $1 <= t <= r$ (where $partial^t$ is shadow applied $t$ times).
]
#proofhints[
    Straightforward.
]
#proof[
    If $abs(partial^t cal(C)) <= abs(partial^t cal(F))$, then $abs(partial^(t + 1) cal(C)) <= abs(partial^(t + 1) cal(F))$, since $partial^t cal(C)$ is an initial segment of colex. So we are done by induction (base case is Kruskal-Katona).
]
#remark[
    So if $abs(cal(F)) = binom(k, r)$, then $abs(partial^t cal(F)) >= binom(k, r - t)$.
]

== Intersecting families

#definition[
    A family $cal(F) in powset(X)$ is *intersecting* if for all $A, B in cal(F)$, $A sect B != emptyset$.

    We are interested in finding intersecting families of maximum size.
]<def:family.intersecting>
#proposition[
    For all intersecting families $cal(F) subset.eq powset(X)$, $abs(cal(F)) <= 2^(n - 1) = 1/2 abs(powset(X))$.
]<prop:size-of-intersecting-family-is-at-most-half-of-size-of-powerset>
#proofhints[
    Straightforward.
]
#proof[
    Given any $A subset.eq X$, at most one of $A$ and $A^c$ can belong to $cal(F)$.
]
#example[
    - $cal(F) = {A subset.eq X: 1 in A}$ is intersecting, and $abs(cal(F)) = 2^(k - 1)$.
    - $cal(F) = {A subset.eq X: abs(A) > n/2}$ for $n$ odd.
]
#example[
    Let $cal(F) subset.eq X^((r))$:
    - If $r > n/2$, then $cal(F) = X^((r))$ is intersecting.
    - If $r = n/2$, then choose one of $A$ and $A^c$ for all $A in X^((r))$. This gives $abs(cal(F)) = 1/2 binom(n, r)$.
    - If $r < n/2$, then $cal(F) = {A in X^((r)): 1 in A}$ has size $binom(n - 1, r - 1) = r/n binom(n, r)$ (since the probability of a random $r$-set containing $1$ is $r/n$). If $(n, r) = (8, 3)$, then $abs(cal(F)) = binom(7, 2) = 21$.
    - Let $cal(F) = {A in X^((r)): abs(A sect {1, 2, 3}) >= 2}$. If $(n, r) = (8, 3)$, then $abs(cal(F)) = 1 + binom(3, 2) binom(5, 1) = 16 < 21$ (since $1$ set $A$ has $abs(B sect [3]) = 3$, $15$ sets $A$ have $abs(A sect [3]) = 2$).
]
#theorem("Erdos-Ko-Rado")[
    Let $cal(F) subset.eq X^((r))$ be an intersecting family, where $r < n/2$. Then $abs(cal(F)) <= binom(n - 1, r - 1)$.
]<thm:erdos-ko-rado>
#proofhints[
    - Method 1:
        - Let $overline(cal(F)) = {A^c: A in cal(F)}$. Show that $partial^(n - 2r) overline(cal(F))$ and $cal(F)$ are disjoint families of $r$-sets.
        - Assume the opposite, show that the size of the union of these two sets is greater than the size of $X^((r))$.
    - Method 2:
        - Let $c: [n] -> ZZ\/n$ be bijection, i.e. cyclic ordering of $[n]$. Show there at most $r$ sets in $cal(F)$ that are intervals (sets with $r$ consecutive elements) under this ordering.
        - Find expression for number of times an $r$-set in $cal(F)$ is an interval all possible orderings, and find an upper bound for this using the above.
]
#proof[
    Proof 1 ("bubble down with Kruskal-Katona"): note that $A sect B != emptyset$ iff $A subset.eq.not B^c$.
    #fig-example[
        #figure(
            canvas({
                import cetz.draw: *

                circle((0, 0), radius: (4, 0.8))
                circle((0, 3), radius: (4, 0.8))
                set-style(
                    stroke: diagram-colors.red,
                    fill: diagram-colors.light-red
                )
                circle((1.8, 0), radius: (1.2, 0.5), name: "neighbourhood")
                circle((-1.8, 3), radius: (1.2, 0.5), name: "set")

                set-style(
                    stroke: (dash: "dashed", paint: diagram-colors.red)
                )

                line((-3, 0), (-3, 3))
                line((-0.6, 0), (-0.6, 3))

                circle((1.3, 0), ..point-style, name: "A")
                circle((2.2, 0), ..point-style, name: "B")
                circle((-1.4, 3), ..point-style, name: "B^c")
                content("A", box(inset: (right: 0.3em))[$A$], anchor: "east")
                content("B", box(inset: (left: 0.3em))[$B$], anchor: "west")
                content("B^c", box(inset: (left: 0.3em))[$B^c$], anchor: "west")

                content((6, 0), $X^((r))$)
                content((6, 3), $X^((n - r))$)    
                content((0.3, 0), $cal(F)$)
                content((-0.2, 3), $overline(cal(F))$)
            }),
        )
    ]
    Let $overline(cal(F)) = {A^c: A in cal(F)} subset.eq X^((n - r))$. We have $partial^(n - 2r) overline(cal(F))$ and $cal(F)$ are disjoint families of $r$-sets (if not, then there is some $A in cal(F)$ such that $A subset.eq B^c$ for some $B in cal(F)$, but then $A sect B = emptyset$). Suppose $abs(cal(F)) > binom(n - 1, r - 1)$. Then $abs(overline(cal(F))) = abs(cal(F)) > binom(n - 1, r - 1) = binom(n - 1, n - r)$. So by Kruskal-Katona, we have $abs(partial^(n - 2r) overline(cal(F))) >= binom(n - 1, r)$. So $abs(cal(F)) + abs(partial^(n - 2r) overline(cal(F))) > binom(n - 1, r - 1) + binom(n - 1, r) = binom(n, r) = abs(X^((r)))$, a contradiction, since $cal(F), partial^(n - 2r) overline(cal(F)) subset.eq X^((r))$.

    Proof 2: pick a cyclic ordering of $[n]$, i.e. a bijection $c: [n] -> ZZ\/n$. There are at most $r$ sets in $cal(F)$ that are intervals ($r$ consecutive elements) under this ordering: for $c_1 ... c_r in cal(F)$, for each $2 <= i <= r$, at most one of the two intervals $c_i ... c_(i + r - 1)$ and $c_(i - r) ... c_(i - 1)$ can belong to $cal(F)$, since they are disjoint and $cal(F)$ is intersecting (the indices of $c$ are taken $mod n$).
    #fig-example[
        #figure(
            canvas({
                import cetz.draw: *

                let r = 2
                circle((0, 0), radius: r)
                content((4, 0), $ZZ_n$)
                // arc((r - 0.2, 0), radius: r - 0.2, start: 0deg, stop: -120deg, stroke: diagram-colors.red)
                // arc((r - 0.2, 0), radius: r - 0.2, start: 0deg, stop: 120deg, stroke: diagram-colors.blue)
                c-arc((0, 0), r - 0.2, -15deg, -135deg, stroke: diagram-colors.red)
                c-arc((0, 0), r - 0.2, 0deg, 120deg, stroke: diagram-colors.blue)

                circle((r, 0), radius: 0.1, fill: black, stroke: none, name: "i - 1")
                circle((r * calc.cos(15deg), r * calc.sin(15deg)), radius: 0.1, fill: black, stroke: none, name: "i - 2")
                circle((r * calc.cos(105deg), r * calc.sin(105deg)), radius: 0.1, fill: black, stroke: none, name: "i - r + 1")
                circle((r * calc.cos(120deg), r * calc.sin(120deg)), radius: 0.1, fill: black, stroke: none, name: "i - r")
                circle((r * calc.cos(-15deg), r * calc.sin(-15deg)), radius: 0.1, fill: black, stroke: none, name: "i")
                circle((r * calc.cos(-30deg), r * calc.sin(-30deg)), radius: 0.1, fill: black, stroke: none, name: "i + 1")
                circle((r * calc.cos(-120deg), r * calc.sin(-120deg)), radius: 0.1, fill: black, stroke: none, name: "i + r - 2")
                circle((r * calc.cos(-135deg), r * calc.sin(-135deg)), radius: 0.1, fill: black, stroke: none, name: "i + r - 1")
                content("i", box(inset: 0.4em)[$c_i$], anchor: "west")
                content("i + 1", box(inset: 0.2em)[$c_(i + 1)$], anchor: "north-west")
                content("i + r - 2", box(inset: 0.2em)[$c_(i + r - 2)$], anchor: "north")
                content("i + r - 1", box(inset: 0.4em)[$c_(i + r - 1)$], anchor: "east")
                content("i - 1", box(inset: 0.4em)[$c_(i - 1)$], anchor: "west")
                content("i - 2", box(inset: 0.2em)[$c_(i - 2)$], anchor: "south-west")
                content("i - r + 1", box(inset: 0.4em)[$c_(i - r + 1)$], anchor: "south")
                content("i - r", box(inset: 0.2em)[$c_(i - r)$], anchor: "south-east")
            })
        )
    ]
    For each $r$-set $A$, out of the $n!$ cyclic orderings, there are $n dot r! (n - r)!$ which map $A$ to an interval ($r!$ orderings inside $A$, $(n - r)!$ orderings outside $A$, $n$ choices for the start of the interval). Hence, by counting the number of times an $r$-set in $cal(F)$ is an interval under a given ordering (over all $r$-sets in $cal(F)$ and all cyclic orderings), we obtain $abs(cal(F)) n r! (n - r)! <= n! r$, i.e. $abs(cal(F)) <= binom(n - 1, r - 1)$.
]
#remark[
    - The calculation at the end of proof method 1 had to give the correct answer, as the shadow calculations would all be exact if $cal(F) = {A in X^((r)): 1 in A}$ (in this case, $cal(F)$ and $partial^(n - 2r) overline(cal(F))$ partition $X^((r))$).
    - The calculations at the end of proof method 2 had to work out, given equality for the family $cal(F) = {A in X^((r)): 1 in A}$.
    - In method 2, equivalently, we are double-counting the edges in the bipartite graph, where the vertex classes (partition sets) are $cal(F)$ and all cyclic orderings, with $A$ joined to $c$ if $A$ is an interval under $c$. This method is called *averaging* or *Katona's method*.
    - Equality in Erdos-Ko-Rado holds iff $cal(F) = {A in X^((r)): i in A}$, for some $1 <= i <= n$. This can be obtained from proof 1 and equality in Kruskal-Katona, or from proof 2.
]


= Isoperimetric inequalities

We seek to answer questions of the form "how do we minimise the boundary of a set of given size?"

#example[
    In the continuous setting:
    - Among all subsets of $RR^2$ of a given fixed area, the disc minimises the perimeter.
    - Among all subsets of $RR^3$ of a given fixed volume, the solid sphere minimises the surface area.
    - Among all subsets of $S^2$ of given fixed surface area, the circular cap minimises the perimeter.
]
#definition[
    For a $A$ of vertices of a graph $G$, the *boundary* of $A$ is $
        b(A) = {x in G: x in.not A, x y in E "for some" y in A}.
    $
]<def:vertex-set-boundary>
#fig-example[
    #figure(
        canvas({
            import cetz.draw: *

            let h = 2
            rect((0, 0), (h, h))
            line((h, h), (2 * h, h))
            line((2 * h - h * calc.cos(60deg), 0), (2 * h, h))
            line((2 * h + h * calc.cos(60deg), 0), (2 * h, h))
            line((2 * h - h * calc.cos(60deg), 0), (2 * h + h * calc.cos(60deg), 0))
            circle((0, h), ..point-style, name: "1")
            circle((h, h), ..point-style, name: "2")
            circle((0, 0), ..point-style, fill: diagram-colors.blue, name: "3")
            circle((h, 0), ..point-style, name: "4")
            circle((2 * h, h), ..point-style, fill: diagram-colors.blue, name: "5")
            circle((2 * h - h * calc.cos(60deg), 0), ..point-style, fill: black, name: "6")
            circle((2 * h + h * calc.cos(60deg), 0), ..point-style, fill: black, name: "7")
            let anchors = ("south", "south", "north", "north", "south", "north", "north")
            for (i, anchor) in anchors.enumerate() {
                let j = i + 1
                content(str(j), box(inset: 0.4em, radius: 50%)[$#j$], anchor: anchor)
            }
        }),
        caption: [$A = {1, 2, 4}$ (in red) has boundary ${3, 5}$ (in blue).]
    )
]
#definition[
    An *isoperimetric inequality* on a graph $G$ is an inequality of the form $
        forall A subset.eq G, quad abs(b(A)) >= f(abs(A))
    $ for some function $f: NN -> RR$.
]<def:isoperimetric-inequality>
#definition[
    The *neighbourhood* of $A subset.eq V(G)$ is $N(A) := A union b(A)$, i.e. $
        N(A) = {x in G: d(x, A) <= 1}.
    $
]<def:vertex-set-neighbourhood>
#fig-example[
    Let $A subset.eq powset(X) = V(Q_3)$, $abs(A) = 4$.
    #align(center)[#grid(
        columns: 2,
        column-gutter: 4em,
        align: center + horizon,
        figure(
            canvas({
                import cetz.draw: *

                let shift-x = 1.25
                let shift-y = 1.25
                let height = 2.5
                let (A, B, C, D, E, F, G, H) = ((0, 0), (height, 0), (0, height), (height, height), (shift-x, shift-y), (height + shift-x, shift-y), (shift-x, height + shift-y), (height + shift-x, height + shift-y))
                let sets = ($emptyset$, $1$, $3$, $13$, $2$, $12$, $23$, $123$)

                draw.rect(A, D, name: "front")
                draw.rect(E, H, name: "back")
                line(A, E)
                line(B, F)
                line(C, G)
                line(D, H)

                for (i, point) in (A, B, E, C).enumerate() {
                    circle(point, ..point-style, name: "point-" + str(i))
                }
                for (i, point) in (F, D, G).enumerate() {
                    circle(point, ..point-style, fill: diagram-colors.blue, name: "point-" + str(i))
                }
            }),
            caption: [$abs(b(A)) = 3$]
        ),
        figure(
            canvas({
                import cetz.draw: *

                let shift-x = 1.25
                let shift-y = 1.25
                let height = 2.5
                let (A, B, C, D, E, F, G, H) = ((0, 0), (height, 0), (0, height), (height, height), (shift-x, shift-y), (height + shift-x, shift-y), (shift-x, height + shift-y), (height + shift-x, height + shift-y))
                let sets = ($emptyset$, $1$, $3$, $13$, $2$, $12$, $23$, $123$)

                draw.rect(A, D, name: "front")
                draw.rect(E, H, name: "back")
                line(A, E)
                line(B, F)
                line(C, G)
                line(D, H)

                for (i, point) in (A, B, E, F).enumerate() {
                    circle(point, ..point-style, name: "point-" + str(i))
                }
                for (i, point) in (C, D, G, H).enumerate() {
                    circle(point, ..point-style, fill: diagram-colors.blue, name: "point-" + str(i))
                }
            }),
            caption: [$abs(b(A)) = 4$]
        )
    )]
]
#example[
    A good (and natural) example for $A$ that minimises $abs(b(A))$ in the discrete cube $Q_n$ might be a ball $B(x, r) = {y in G: d(x, y) <= r}$.

    A good guess is that balls are best, i.e. sets of the form $B(emptyset, r) = X^((<= r)) = X^((0)) union dots.c union X^((r))$. What if $abs(X^((<= r))) <= abs(A) <= abs(X^((<= r + 1)))$? A good guess is take $A$ with $X^((<= r)) subset.neq A subset.neq X^((<= r + 1))$. If $A = X^((<= r)) union B$, where $B subset.eq X^((r + 1))$, then $b(A) = (X^((r + 1)) - B) union partial^+ B$, so we would take $B$ to be an initial segment of lex by Kruskal-Katona. This motivates the following definition.
]
#definition[
    The *simplicial ordering* on $powset(X)$ defines $x < y$ if either $abs(x) < abs(y)$, or both $abs(x) = abs(y)$ and $x < y$ in lex.
]<def:simplicial-ordering>
We want to show the initial segments of the simplicial ordering minimise the boundary.
#definition[
    For $A subset.eq powset(X)$ and $1 <= i <= n$, the *$i$-sections* of $A$ are the families $A_-^((i)), A_+^((i)) subset.eq powset(X \\ i)$, given by $
        A_-^((i)) = A_- & := {x in A: i in.not x}, \
        A_+^((i)) = A_+ & := {x - i: x in A, i in x}
    $ Note that $A = A_-^((i)) union \{x union i: x in A_+^((i))\}$, so we can define a family by its $i$-sections.
]<def:i-sections>
#fig-example[
    #figure(
        canvas({
            import cetz.draw: *

            let shift-x = 1.25
            let shift-y = 1.25
            let height = 2.5
            let (A, B, C, D, E, F, G, H) = ((0, 0), (height, 0), (0, height), (height, height), (shift-x, shift-y), (height + shift-x, shift-y), (shift-x, height + shift-y), (height + shift-x, height + shift-y))
            let sets = ($emptyset$, $1$, $3$, $13$, $2$, $12$, $23$, $123$)

            let shift-1 = (0, 5)
            let shift-2 = (9, 0)
            draw.rect(A, D)
            draw.rect(E, H)
            draw.rect(add-points(A, shift-1), add-points(D, shift-1))
            draw.rect(add-points(E, shift-1), add-points(H, shift-1))
            draw.rect(add-points(A, shift-2), add-points(D, shift-2))
            draw.rect(add-points(E, shift-2), add-points(H, shift-2))
            draw.rect(add-points(A, shift-1, shift-2), add-points(D, shift-1, shift-2))
            draw.rect(add-points(E, shift-1, shift-2), add-points(H, shift-1, shift-2))
            line(A, E)
            line(add-points(A, shift-1), add-points(E, shift-1))
            line(add-points(A, shift-2), add-points(E, shift-2))
            line(add-points(A, shift-1, shift-2), add-points(E, shift-1, shift-2))
            line(B, F)
            line(add-points(B, shift-1), add-points(F, shift-1))
            line(add-points(B, shift-2), add-points(F, shift-2))
            line(add-points(B, shift-1, shift-2), add-points(F, shift-1, shift-2))
            line(C, G)
            line(add-points(C, shift-1), add-points(G, shift-1))
            line(add-points(C, shift-2), add-points(G, shift-2))
            line(add-points(C, shift-1, shift-2), add-points(G, shift-1, shift-2))
            line(D, H)
            line(add-points(D, shift-1), add-points(H, shift-1))
            line(add-points(D, shift-2), add-points(H, shift-2))
            line(add-points(D, shift-1, shift-2), add-points(H, shift-1, shift-2))

            line((-1, height), add-points((-1, 0), shift-1), ..line-style(black), name: "i-axis")
            content("i-axis.mid", box(inset: (right: 0.6em))[$i$], anchor: "east")

            for (i, point) in (A, D, G, H).enumerate() {
                circle(point, ..point-style, name: "point-" + str(i))
            }
            for (i, point) in (A, B, C, D, E).enumerate() {
                circle(add-points(point, shift-1), ..point-style, name: "point-" + str(i))
            }
            for (i, point) in (A, B, E, C).enumerate() {
                circle(add-points(point, shift-2), ..point-style, name: "point-" + str(i))
            }
            for (i, point) in (A, B, E, F, C).enumerate() {
                circle(add-points(point, shift-1, shift-2), ..point-style, name: "point-" + str(i))
            }
            content((height + shift-x + 0.6, (height + shift-y) / 2), $A_-^((i))$)
            content(add-points((height + shift-x + 0.6, (height + shift-y) / 2), shift-1), $A_+^((i))$)
            content(add-points((height + shift-x + 1, (height + shift-y) / 2), shift-2), $C_i (A)_-^((i))$)
            content(add-points((height + shift-x + 1, (height + shift-y) / 2), shift-1, shift-2), $C_i (A)_+^((i))$)

            line((height + shift-x + 1, (height + shift-y + shift-1.at(1)) / 2), (height + shift-x + 4, (height + shift-y + shift-1.at(1)) / 2), ..line-style(black), name: "compression")
            content("compression.mid", box(inset: 0.4em)[$C_i$], anchor: "south")
        }),
        caption: [$i$-compression of $A$]
    )
]
#remark[
    When viewing $powset(X)$ as the $n$-dimensional cube $Q_n$, we view the $i$-sections as subgraphs of the $(n - 1)$-dimensional cube $Q_(n - 1)$ (which we view $powset(X \\ i)$ as).
]
#definition[
    A *Hamming ball* is a family $A subset.eq powset(X)$ with $X^((<= r)) subset.eq A subset.eq X^((<= r + 1))$ for some $r$.
]<def:hamming-ball>
#definition[
    The *$i$-compression* of $A subset.eq powset(X)$ is the family $C_i (A) subset.eq powset(X)$ given by its $i$-sections:
    - $(C_i (A))_-^((i))$ is the first $abs(A_-^((i)))$ elements of the simplicial order on $powset(X - i)$, and
    - $(C_i (A))_+^((i))$ is the first $abs(A_+^((i)))$ elements of the simplicial order on $powset(X - i)$.
    Note that $abs(C_i (A)) = abs(A)$, and $C_i (A)$ "looks more like" a Hamming ball than $A$ does.
]<def:i-compression>
#definition[
    $A subset.eq powset(X)$ is *$i$-compressed* if $C_i (A) = A$.
]<def:i-compressed>
#example[
    Note that a set that is $i$-compressed for all $i in [n]$ is not necessarily an initial segment of simplicial, e.g. take ${emptyset, 1, 2, 12}$ in $Q_3$.
    #unmarked-fig[
        #figure(
            canvas({
                import cetz.draw: *

                let shift-x = 1.25
                let shift-y = 1.25
                let height = 2.5
                let (A, B, C, D, E, F, G, H) = ((0, 0), (height, 0), (0, height), (height, height), (shift-x, shift-y), (height + shift-x, shift-y), (shift-x, height + shift-y), (height + shift-x, height + shift-y))

                rect(A, D)
                rect(E, H)
                line(A, E)
                line(B, F)
                line(C, G)
                line(D, H)

                for (i, point) in (A, B, E, F).enumerate() {
                    circle(point, ..point-style)
                }
            })
        )
    ]
    However...
]
#lemma[
    Let $B subset.eq Q_n$ be $i$-compressed for all $i in [n]$ but not an initial segment of the simplicial order. Then either:
    - $n$ is odd (say $n = 2k + 1$) and $
        B = X^((<= k)) \\ underbrace({k + 2, k + 3, ..., 2k + 1}, #[last $k$-set]) union underbrace({1, 2, ..., k + 1}, #[first $(k + 1)$-set]),
    $
    - or $n$ is even (say $n = 2k$), and $
        B = X^((< k)) union {x in X^((k)): 1 in x} \\ underbrace({1, k + 2, k + 3, ..., 2k}, #[last $k$-set with $1$]) union underbrace({2, 3, ..., k + 1}, #[first $k$-set without $1$]).
    $
]
#fig-example[
    #figure(
        grid(
            columns: 2,
            column-gutter: 4em,
            canvas({
                import cetz.draw: *

                content((2.5, 6.5), [$n$ odd])
                polygon(((2.5, 0), (0, 3), (5, 3)), name: "bottom-half", fill: diagram-colors.light-red, stroke: none)
                polygon(((5, 3), (4.5, 3), (4.7, 2.63)), fill: diagram-colors.red, stroke: none, name: "lose")
                polygon(((0, 3), (0.5, 3), (0.3, 3.37)), fill: diagram-colors.blue, stroke: none, name: "gain")
                content("gain.centroid", box(inset: 0.5em)[Gain], anchor: "south-east")
                content("lose.centroid", box(inset: 0.5em)[Lose], anchor: "north-west")
                content("bottom-half.centroid", $X^((<= k))$)
                diamond(5, 6)
            }),
            canvas({
                import cetz.draw: *

                content((2.5, 6.5), [$n$ even])
                polygon(((0, 3), (0.3, 3.37), (2.32, 3.37), (2.32, 3)), fill: diagram-colors.light-red, stroke: none)
                rect((2.32, 3), (2.62, 3.37), stroke: none, fill: diagram-colors.red, name: "lose")
                rect((2.62, 3), (2.92, 3.37), stroke: none, fill: diagram-colors.blue, name: "gain")
                polygon(((2.5, 0), (0, 3), (5, 3)), name: "bottom-half", fill: diagram-colors.light-red)
                content("gain", box(inset: 0.5em)[Gain], anchor: "west")
                content("lose", box(inset: 0.5em)[Lose], anchor: "south-east")
                diamond(5, 6)
            })
        )
    )
]
#proofhints[
    For $x in.not B$ and $y in B$, show by contradiction that any $i in [n]$ is in exactly one of $x$ and $y$ (it helps to visualise this), and deduce that no elements lie strictly between $x$ and $y$ in the simplicial ordering.
]
#proof[
    As $B$ is not an initial segment, there are $x < y$ in simplicial ordering with $x in.not B$ and $y in B$.
    #unmarked-fig[
        #figure(
            canvas({
                import cetz.draw: *

                line((0, 0), (12, 0), mark: (end: ">"), fill: black, name: "order")
                circle((5, 0), ..point-style, name: "x", fill: diagram-colors.blue)
                circle((9, 0), ..point-style, name: "y")
                content("x", box(inset: 0.5em)[$x$], anchor: "south")
                content("x", box(inset: 0.5em)[$in.not B$], anchor: "north")
                content("y", box(inset: 0.5em)[$y$], anchor: "south")
                content("y", box(inset: 0.5em)[$in B$], anchor: "north")
                content("order.centroid", box(inset: (top: 2em))[Simplicial order], anchor: "north")
            })
        )
    ]
    For each $i in [n]$, assume $i in x, y$. Since the $i$-section that $y$ lives in is an initial segment of simplicial on $PP(X \\ i)$ (as $B$ is $i$-compressed), and $x - i < y - i$ in simplicial on $PP(X \\ i)$, we have that $x - i$ lives in the same $i$-section, and so $x in B$: contradiction. Similarly, $i in.not x, y$ leads to a contradiction (as then $x < y$ in simplicial on $PP(X \\ i)$). So $x = y^c$.
    
    Thus for each $y in B$, there is at most one $x < y$ with $x in.not B$ (namely $x = y^c$), and for each $x in.not B$, there is at most one $y > x$ with $y in B$ (namely $y = x^c$). So no sets lie between $x$ and $y$ in the simplicial ordering. So $B = {z: z <= y} \\ {x}$, with $x$ the predecessor of $y$, and $x = y^c$.
    #unmarked-fig[
        #figure(
            canvas({
                import cetz.draw: *

                line((0, 0), (12, 0), mark: (end: ">"), fill: black, name: "order")
                circle((8, 0), ..point-style, name: "x", fill: diagram-colors.blue)
                circle((9, 0), ..point-style, name: "y")
                content("x", box(inset: 0.5em)[$x$], anchor: "south")
                content("x", box(inset: 0.5em)[$in.not B$], anchor: "north")
                content("y", box(inset: 0.5em)[$y$], anchor: "south")
                content("y", box(inset: 0.5em)[$in B$], anchor: "north")
                content("order.centroid", box(inset: (top: 2em))[Simplicial order], anchor: "north")
                rect((0.1, -0.25), (7.25, 0.25), fill: diagram-colors.red, stroke: none, name: "B")
                content("B", box(inset: (bottom: 1em))[$B$], anchor: "south")
            })
        )
    ]
    Hence if $n = 2k + 1$, then $x$ is the last $k$-set (otherwise sizes of $x$ and $y = x^c$ don't match), and if $n = 2k$, then $x$ is the last $k$-set containing $1$.
]
#theorem("Harper")[
    Let $A subset.eq V(Q_n)$ and let $C$ be the initial segment of the simplicial order on $powset(X) = V(Q_n)$, with $abs(C) = abs(A)$. Then $abs(N(A)) >= abs(N(C))$. So initial segments of the simplicial order minimise the boundary. In particular, if $abs(A) = sum_(i = 0)^r binom(n, i)$, then $abs(N(A)) >= sum_(i = 0)^(r + 1) binom(n, i)$.
]<thm:harper>
#proofhints[
    - Using induction, prove the claim that $abs(N(C_i (A))) <= abs(N(A))$:
        - Find expressions for $N(A)_-$ as union of two sets, similarly for $N(A)_+$, same for $N(B)_-$ and $N(B)_+$.
        - Explain why $N(B_-)$ and $B_+$ are nested, use this to show $abs(N(B_-) union B_+) <= abs(N(A_-) union A_+)$.
        - Do the same with the $+$ and $-$ switched.
    - Define a suitable sequence of families $A_0, A_1, ... in Q_n$.
    - Reason that the sequence terminates by considering $sum_(x in A_k) ("position of" x "in simplicial order")$.
    - Conclude by above lemma.
]
#proof[
    By induction on $n$. $n = 1$ is trivial. Given $n > 1$, $A subset.eq Q_n$ and $1 <= i <= n$, we claim that $abs(N(C_i (A))) <= abs(N(A))$.
    #proof("of claim")[
        Write $B = C_i (A)$. We have $N(A)_- = N(A_-) union A_+$, and $N(A)_+ = N(A_+) union A_-$. Similarly, $N(B)_- = N(B_-) union B_+$, and $N(B)_+ = N(B_+) union B_-$.
        
        Now $abs(B_+) = abs(A_+)$ by definition of $B$, and by the inductive hypothesis, $abs(N(B_-)) <= abs(N(A_-))$ (since $C_i (A_-) = B_-$). But $B_+$ is an initial segment of the simplicial ordering, and $N(B_-)$ is as well (since the neighbourhood of an initial segment of the simplicial ordering is also an initial segment). So $B_+$ and $N(B_-)$ are nested (one is contained in the other). Hence, $abs(N(B_-) union B_+) <= abs(N(A_-) union A_+)$.
        
        Similarly, $abs(B_-) = abs(A_-)$ by definition of $B$. Since $B_+$ and $C_i (A_+)$ are both initial segments of size $abs(B_+) = abs(A_+)$, we have $B_+ = C_i (A_+)$, hence by the inductive hypothesis, $abs(N(B_+)) <= abs(N(A_+))$. $B_-$ and $N(B_+)$ are initial segments, so are nested. Hence $abs(N(B_+) union B_-) <= abs(N(A_+) union A_-)$.
        
        This gives $abs(N(B)) = abs(N(B)_-) + abs(N(B)_+) <= abs(N(A)_-) + abs(N(A)_+) = abs(N(A))$, which proves the claim.

        Define a sequence $A_0, A_1 ,... subset.eq Q_n$ as follows:
        - Set $A_0 = A_1$.
        - having chosen $A_0, ..., A_k$, if $A_k$ is $i$-compressed for all $i in [n]$, then end the sequence with $A_k$. If not, pick $i$ with $C_i (A_k) != A_k$ and set $A_(k + 1) = C_i (A_k)$, and continue.
        The sequence must terminate, since $sum_(x in A_k) ("position of" x "in simplicial order")$ is strictly decreasing. The final family $B = A_k$ satisfies $abs(B) = abs(A)$, $abs(N(B)) <= abs(N(A))$, and is $i$-compressed for all $i in [n]$.

        So we are done by above lemma, since in each case certainly we have $abs(N(B)) >= abs(N(C))$.
    ]

]
#remark[
    - If $A$ was a Hamming ball, then we would be already done by @thm:kruskal-katona.
    - Conversely, @thm:harper implies @thm:kruskal-katona: given $B subset.eq X^((r))$, apply @thm:harper to $A = X^((<= r - 1)) union B$.
    - We could also prove @thm:harper using $U V$-compressions.
    - Conversely, we can also prove @thm:kruskal-katona using these "codimension $1$" compressions.
]
#fig-example[
    #figure(
        canvas({
            import cetz.draw: *

            polygon(((0, 0), (0, 3), (3, 0)), fill: diagram-colors.light-red, stroke: none)
            rect((0, 0), (6, 6))
            line((4, 0), (0, 4), stroke: (dash: "dotted", thickness: 1.4pt))
            content((-1, 1.5), $X^((< r))$)
            for point in ((3.5, 0.2), (3, 0.6), (2.5, 1), (2.1, 1.4), (1.7, 2)) {
                circle(point, ..point-style, fill: diagram-colors.red)
            }
            content((4, -0.5), $B subset.eq X^((r))$)
        }),
        caption: [@thm:harper implies @thm:kruskal-katona.]
    )
]
#definition[
    For $A subset.eq Q_n$ and $t in NN$, the *$t$-neighbourhood* of $A$ is $
        A_((t)) = N^t (A) := {x in Q_n: d(x, A) <= t}.
    $
]<def:t-neighbourhood>
#fig-example[
    #figure(
        canvas({
            import cetz.draw: *

            let r = 3
            rect((-r, -r), (r, r), name: "cube")
            content((r + 1, 0), $Q_n$)
            circle((0.5, -0.5), radius: 2, fill: diagram-colors.light-red, stroke: (paint: diagram-colors.red, dash: "dashed"))
            circle((0.5, -0.5), radius: 1, fill: diagram-colors.red, stroke: none)
            content((0.5, -0.5), box[
                #set text(fill: white)
                $A$
            ])
            content((0.5, 2), $N^t (A)$)
        }),
        caption: [$t$-neighbourhood of $A$.]
    )
]
#corollary[
    Let $A subset.eq Q_n$ with $abs(A) >= sum_(i = 0)^r binom(n, i)$. Then $
        forall t <= n - r, quad abs(N^t (A)) >= sum_(i = 0)^(r + t) binom(n, i).
    $
]<cor:iterated-harper>
#proofhints[
    By Harper's theorem.
]
#proof[
    By Harper's theorem and induction on $t$.
]
#remark[
    To get a feeling for the strength of the above corollary, we'll need some estimates on quantities such as $sum_(i = 0)^r binom(n, i)$. Note that $i = n\/2$ maximises $binom(n, i)$, while $i = (1\/2 - epsilon) n$ makes it small: we are going $epsilon sqrt(n)$ standard deviations away from the mean $n\/2$.
    #unmarked-fig[
        // https://math.stackexchange.com/questions/1987599/approximation-of-the-gamma-function-for-small-value
        #let gamma(x) = calc.sqrt(2.0 * calc.pi * (x + 1/6)) * (calc.pow(x, x - 1)) / calc.exp(x)
        #let factorial(x) = gamma(x + 1)
        #let choose(n, i) = factorial(n) / (factorial(i) * factorial(n - i))
        #figure(
            canvas({
                plot.plot(
                    axis-style: "school-book",
                    size: (6, 6),
                    x-tick-step: none,
                    y-tick-step: none,
                    x-grid: "minor",
                    y-grid: "minor",
                    x-label: $i$,
                    y-label: $binom(n, i)$,
                    x-min: -0.2,
                    y-min: -4,
                    {
                        let n = 10
                        plot.add(
                            samples: 500,
                            style: (stroke: diagram-colors.red + 2pt),
                            domain: (0, 10), x => choose(n, x)
                        )
                    }
                )
            })
        )
    ]
]
#proposition[
    Let $0 < epsilon < 1\/4$. Then $
        sum_(i = 0)^floor((1\/2 - epsilon)n) binom(n, i) <= 1/epsilon e^(-epsilon^2 n\/2) dot 2^n.
    $ For $epsilon$ fixed and $n -> oo$, the upper bound is an exponentially small fraction of $2^n$.
]<prop:upper-bound-on-less-than-half-first-binomial-coefficients>
#proofhints[
    - Let $L = floor((1\/2 - epsilon) n)$ and $M = floor((1\/2 - epsilon \/ 2)n)$.
    - For $1 <= i <= L$, show that $binom(n, i - 1)\/binom(n, i) <= 1 - 2 epsilon$, use this to show that $
        sum_(i = 0)^L binom(n, i) <= 1/(2 epsilon) binom(n, L).
    $
    - Use the same argument to show that $
        binom(n, L) <= binom(n, M) (1 - epsilon)^(M - L).
    $
    - Use that $1 - epsilon <= e^(-epsilon)$ to conclude the result.
]
#proof[
    Let $L = floor((1\/2 - epsilon) n)$. For $1 <= i <= L$, $
        binom(n, i - 1)\/binom(n, i) = i/(n - i + 1) <= ((1\/2 - epsilon)n)/((1\/2 + epsilon)n) = (1\/2 - epsilon)/(1\/2 + epsilon) = 1 - (2 epsilon)/(1\/2 + epsilon) <= 1 - 2 epsilon.
    $ Hence by induction, $binom(n, i) <= (1 - 2 epsilon)^(L - i) binom(n, L)$ for each $0 <= i <= L$, and so $
        sum_(i = 0)^L binom(n, i) <= 1/(2 epsilon) binom(n, L)
    $ (since this is the sum of geometric progression). Let $M = floor((1\/2 - epsilon \/ 2)n)$. It is easy to show that $M - L > epsilon n \/ 2 - 1$. By the same argument as above, $binom(n, i) <= (1 - 2 epsilon / 2)^(M - i) binom(n, M)$ for each $0 <= i <= M$. In particular, $
        binom(n, L) & <= binom(n, M) (1 - 2 epsilon/2)^(M - L) \
        binom(n, L) & <= binom(n, M) (1 - epsilon)^(epsilon n \/2 - 1) \
        & <= 2^n dot 2 (1 - epsilon)^(epsilon n \/2) \
        & <= 2^n dot 2 e^(-epsilon^2 n\/2)
    $ since $1 - epsilon <= e^(-epsilon)$. Combining with the previous upper bound, we obtain #qed-multiline($
        sum_(i = 0)^L binom(n, i) <= 1/(2 epsilon) dot 2 e^(-epsilon^2 n\/2) dot 2^n.
    $)
]
#theorem[
    Let $0 < epsilon < 1 \/ 4$, $A subset.eq Q_n$. If $abs(A) \/ 2^n >= 1 \/ 2$, then $
        abs(N^(epsilon n)(A)) / 2^n >= 1 - 2/epsilon e^(-epsilon^2 n \/ 2).
    $ So sets of at least half density have exponentially dense $epsilon n$-neighbourhoods.
]<thm:sets-of-at-least-half-density-have-exponentially-dense-neighbourhoods>
#proofhints[
    - Enough to show that if $epsilon n in NN$, then $abs(N^(epsilon n)(A))\/2^n >= 1 - 1/epsilon e^(-epsilon^2 n\/2)$.
    - Give lower bound on $abs(A)$ which is a binomial sum, deduce lower bound on $N^(epsilon n)(A)$.
    - Give an upper bound on $abs(N^(epsilon n)(A)^c)$ using the above proposition.
]
#proof[
    It is enough to show that if $epsilon n in NN$, then $abs(N^(epsilon n)(A))\/2^n >= 1 - 1/epsilon e^(-epsilon^2 n\/2)$. We have $abs(A) >= sum_(i = 0)^ceil(n\/2 - 1) binom(n, i)$, so by @cor:iterated-harper, $
        abs(N^(epsilon n)(A)) >= sum_(i = 0)^ceil(n\/2 - 1 + epsilon n) binom(n, i).
    $ So $
        abs(N^(epsilon n)(A)^c) & <= sum_(i = ceil(n\/2 + epsilon n))^n binom(n, i) \
        & = sum_(i = ceil(n\/2 + epsilon n))^n binom(n, n - i) \
        & = sum_(i = 0)^ceil(n\/2 - epsilon n) binom(n, i) \
        & <= 1/epsilon e^(-epsilon^2 n\/2) dot 2^n.
    $ by @prop:upper-bound-on-less-than-half-first-binomial-coefficients.
]
#remark[
    The same argument would give a result for "small" sets: if $abs(A) \/ 2^n >= 2/epsilon e^(-epsilon^2 n\/2)$, then $abs(N^(2epsilon n)(A))\/2^n >= 1 - 2/epsilon e^(-epsilon^2 n\/2)$.
]
#definition[
    $f: Q_n -> RR$ is *Lipschitz* if for all adjacent $x, y in Q_n$, $abs(f(x) - f(y)) <= 1$.
]<def:lipschitz>
#definition[
    For $f: Q_n -> RR$, we say $M in RR$ is a *Levy mean* (or *median*) of $f$ if $abs({x in Q_n: f(x) <= M}) >= 2^(n - 1)$ and $abs({x in Q_n: f(x) >= M}) >= 2^(n - 1)$.
]<def:levy-mean>
#example[
    Let $f: Q_n -> RR$, $f(x) = 1$ if $1 in x$ and $f(x) = 0$ otherwise. Then any $M in [0, 1]$ is a Levy mean of $f$.
]
#theorem("Concentration of Measure Phenomenon")[
    Let $f: Q_n -> RR$ be Lipschitz with Levy mean $M$. Then for all $0 < epsilon < 1/4$, $
        abs({x in Q_n: abs(f(x) - M) <= epsilon n}) / 2^n >= 1 - 4/epsilon e^(-epsilon^2 n\/ 2).
    $ So "every well-behaved function on the cube $Q_n$ is roughly constant nearly everywhere".
]<thm:concentration-of-measure-phenomenon>
#fig-example[
    #figure(
        canvas({
            import cetz.draw: *

            rect((0, 0), (4, 4))
            content((2, 4.5), $Q_n$)
            let curve-points = ((0, 2.5), (1, 2.4), (2, 1.9), (3, 2.1), (4, 2.2))
            let shifted-points = curve-points.map(point => add-points(point, (0, 1)))
            hobby(..curve-points)
            hobby(..shifted-points, stroke: (paint: diagram-colors.red, dash: "dashed"))
            let shift = 0.2
            line((4 + shift, 2.2), (4 + shift, 3.2), mark: (start: "straight", end: "straight"), name: "dist")
            content("dist.centroid", box(inset: (left: 0.5em))[$epsilon n$], anchor: "west")
            content((2, 1), $f(x) <= M$)
        })
    )
]
#proofhints[
    - Consider two subsets $A, B subset.eq Q_n$ of density at least $1\/2$, and apply @thm:sets-of-at-least-half-density-have-exponentially-dense-neighbourhoods on them.
    - Use the fact that $f$ is Lipschitz to find upper bound for the image of the $epsilon n$-neighbourhood of one of $A$ and $B$, similarly find a lower bound for the image of the $epsilon n$-neighbourhood of the other.
]
#proof[
    Let $A = {x in Q_n: f(x) <= M}$. Then by definition, $abs(A) \/ 2^n >= 1 \/ 2$, so by the above theorem, $
        abs(N^(epsilon n)(A)) / 2^n >= 1 - 2/epsilon e^(-epsilon^2 n\/2).
    $ But $f$ is Lipschitz, so $x in N^(epsilon n)(A) ==> f(x) <= M + epsilon n$, so $N^(epsilon n)(A) subset.eq {x in Q_n: f(x) <= M + epsilon n} =: L$. Thus, $
        abs(L) / 2^n >= 1 - 2/epsilon e^(-epsilon^2 n\/2).
    $ Similarly, let $U = {x in Q_n: f(x) >= M - epsilon n}$, then $abs(U) \/ 2^n >= 1 - 2/epsilon e^(-epsilon^2 n \/ 2)$. Hence, we have $
        abs(L sect U) / 2^n & = abs(L) / 2^n + abs(U) / 2^n - abs(L union U) / 2^n \
        & >= 1 - 2/epsilon e^(-epsilon^2 n \/ 2) + 1 - 2/epsilon e^(-epsilon^2 n \/ 2) - 1 \
        & = 1 - 4/epsilon e^(-epsilon^2 n \/ 2).
    $
]
#definition[
    The *diameter* of a graph $G = (V, E)$ is $max{d(x, y): x, y in V}$.
]<def:graph-diameter>
#definition[
    Let $G$ be a graph of diameter $D$. Write $
        alpha(G, epsilon) = max{1 - abs(N^(epsilon D)(A))/abs(G): A subset.eq G, abs(A) / abs(G) >= 1/2}.
    $ So if $alpha(G, epsilon)$ is small, then sets of at least half density have large $epsilon D$-neighbourhoods.
]
#definition[
    A sequence of graphs $\(G_n\)_(n in NN)$ is a *Levy family* if $
        forall epsilon > 0, quad alpha(G_n, epsilon) -> 0 "as" n -> oo.
    $ It is a *normal Levy family* if for all $epsilon > 0$, $alpha(G_n, epsilon)$ decays exponentially with $n$.
]<def:levy-family>
#example[
    By the above theorem, the sequence $(Q_n)$ is a normal Levy family (note that $Q_n$ has diameter $n + 1$). More generally, we have concentration of measure for any Levy family.
]
#example[
    Many naturally-occurring families of graphs are Levy families, e.g. $\(S_n\)_(n in NN)$, where the permutation group $S_n$ is made into a graph by including an edge between $sigma$ and $tau$ if $tau sigma^(-1)$ is a transposition.
]
#example[
    Similarly, we can define $alpha(X, epsilon)$ for any metric measure space $X$ (of finite measure and finite diameter). E.g. the sequence of spheres $\(S^n\)_(n in NN)$ is a Levy family. To prove this, we have:
    + An isoperimetric inequality on $S^n$: for $A subset.eq S^n$ and $C$ a circular cap with $abs(C) = abs(A)$, we have $abs(N^(epsilon)(A)) >= abs(N^(epsilon)(C))$.
    + An estimate: a circular cap $C$ of measure $1\/2$ is the cap of angle $pi\/2$. So $N^(epsilon)(C)$ is the circular cap of angle $pi\/2 + epsilon$. This has measure roughly equal to $integral_epsilon^(pi\/2) cos^(n - 1)(t) dif t -> 0$ as $n -> oo$.
    #unmarked-fig[
        #figure(
            canvas({
                plot.plot(
                    axis-style: "school-book",
                    size: (4, 4),
                    x-tick-step: none,
                    y-tick-step: none,
                    x-grid: "minor",
                    y-grid: "minor",
                    x-min: -0.2,
                    y-min: -0.1,
                    x-ticks: ((0.4, $epsilon$), (calc.pi / 2, $pi \/ 2$)),
                    {
                        let n = 20
                        plot.add(
                            samples: 500,
                            style: (stroke: diagram-colors.red + 2pt),
                            domain: (0, calc.pi / 2), x => calc.pow(calc.cos(x), n)
                        )
                    }
                )
            })
        )
    ]
]
#remark[
    We deduced concentration of measure from an isoperimetric inequality. Conversely, we have:
]
#proposition[
    Let $G$ be a graph such that for any Lipschitz function $f: G -> RR$ with Levy mean $M$, we have $
        abs({x in G: abs(f(x) - M) > t}) / abs(G) <= alpha
    $ for some given $t, alpha >= 0$. Then for all $A subset.eq G$ with $abs(A) \/ abs(G) >= 1\/2$, we have $
        abs(N^(t)(A)) / abs(G) >= 1 - alpha.
    $
]
#proofhints[
    Consider an appropriate Lipschitz function with Levy mean $0$.
]
#proof[
    The function $f(x) = d(x, A)$ is Lipschitz, and has $0$ as a Levy mean. So $
        abs({x in G: d(x, A) > t}) / abs(G) = abs({x in G: x in.not N^(t)(A)}) / abs(G) <= alpha.
    $
]

== Concentration of measure

== Edge-isoperimetric inequalities

#definition[
    For a graph $G$ and $A subset.eq V(G)$, the *edge-boundary* of $A$ is $
        partial_e A = partial A := {x y in E: x in A, y in.not A}.
    $
]<def:edge-boundary>
#fig-example[
    #figure(
        canvas({
            import cetz.draw: *

            let h = 2
            rect((0, 0), (h, h))
            line((0, 0), (0, h), stroke: diagram-colors.red + 2pt)
            line((0, 0), (h, 0), stroke: diagram-colors.red + 2pt)
            line((h, h), (2 * h, h), stroke: diagram-colors.red + 2pt)
            line((2 * h - h * calc.cos(60deg), 0), (2 * h, h))
            line((2 * h + h * calc.cos(60deg), 0), (2 * h, h))
            line((2 * h - h * calc.cos(60deg), 0), (2 * h + h * calc.cos(60deg), 0))
            circle((0, h), ..point-style, fill: diagram-colors.blue, name: "1")
            circle((h, h), ..point-style, fill: diagram-colors.blue, name: "2")
            circle((0, 0), ..point-style, fill: black, name: "3")
            circle((h, 0), ..point-style, fill: diagram-colors.blue, name: "4")
            circle((2 * h, h), ..point-style, fill: black, name: "5")
            circle((2 * h - h * calc.cos(60deg), 0), ..point-style, fill: black, name: "6")
            circle((2 * h + h * calc.cos(60deg), 0), ..point-style, fill: black, name: "7")
            let anchors = ("south", "south", "north", "north", "south", "north", "north")
            for (i, anchor) in anchors.enumerate() {
                let j = i + 1
                content(str(j), box(inset: 0.4em, radius: 50%)[$#j$], anchor: anchor)
            }
        }),
        caption: [$A = {1, 2, 4}$ (in blue) has edge-boundary ${13, 34, 25}$ (in red).]
    )
]
#definition[
    An *edge-isoperimetric inequality* on a graph $G$ is an inequality of the form $
        forall A subset.eq G, quad abs(partial A) >= f(abs(A)).
    $
]<def:edge-isoperimetric-inequality>
#example[
    We are interested in the case $G = Q_n$. Given $abs(A)$, which $A subset.eq Q_n$ should we take to minimise $abs(partial A)$? Let $abs(A) = 4$, $A subset.eq Q_3$.
    #unmarked-fig[
        #align(center)[#grid(
            columns: 2,
            column-gutter: 4em,
            align: center + horizon,
            figure(
                canvas({
                    import cetz.draw: *

                    let shift-x = 1.25
                    let shift-y = 1.25
                    let height = 2.5
                    let (A, B, C, D, E, F, G, H) = ((0, 0), (height, 0), (0, height), (height, height), (shift-x, shift-y), (height + shift-x, shift-y), (shift-x, height + shift-y), (height + shift-x, height + shift-y))
                    let sets = ($emptyset$, $1$, $3$, $13$, $2$, $12$, $23$, $123$)

                    draw.rect(A, D, name: "front")
                    draw.rect(E, H, name: "back")
                    line(A, E)
                    line(B, F)
                    line(C, G)
                    line(D, H)

                    let line-points = ((C, G), (C, D), (B, F), (B, D), (E, G), (E, F))
                    for (p1, p2) in line-points {
                        line(p1, p2, stroke: diagram-colors.red + 2pt)
                    }
                    for (i, point) in (A, B, E, C).enumerate() {
                        circle(point, ..point-style, fill: diagram-colors.blue, name: "point-" + str(i))
                    }
                }),
                caption: [$abs(partial A) = 6$]
            ),
            figure(
                canvas({
                    import cetz.draw: *

                    let shift-x = 1.25
                    let shift-y = 1.25
                    let height = 2.5
                    let (A, B, C, D, E, F, G, H) = ((0, 0), (height, 0), (0, height), (height, height), (shift-x, shift-y), (height + shift-x, shift-y), (shift-x, height + shift-y), (height + shift-x, height + shift-y))
                    let sets = ($emptyset$, $1$, $3$, $13$, $2$, $12$, $23$, $123$)

                    draw.rect(A, D, name: "front")
                    draw.rect(E, H, name: "back")
                    line(A, E)
                    line(B, F)
                    line(C, G)
                    line(D, H)

                    let line-points = ((A, C), (B, D), (E, G), (F, H))
                    for (p1, p2) in line-points {
                        line(p1, p2, stroke: diagram-colors.red + 2pt)
                    }

                    for (i, point) in (A, B, E, F).enumerate() {
                        circle(point, ..point-style, fill: diagram-colors.blue, name: "point-" + str(i))
                    }
                }),
                caption: [$abs(partial A) = 4$]
            )
        )]
    ]
    The diagram suggests that subcubes are best. If $2^k < abs(A) < 2^(k + 1)$, then it is natural to take $A = powset([k]) union "some sets in" powset([k + 1])$. If $A subset.eq Q_4$ has size $abs(A) > 2^3$, then it is natural to take all of the bottom layer and $abs(A) - 2^3$ elements in the top layer. Then the size of the edge boundary is the number of edges from the bottom layer to the top layer (i.e. $2^3 - (abs(A) - 2^3) = 2^4 - abs(A)$) plus the number of edges in the top layer. So now we want to minimise the number of edges in the top layer.
]
#definition[
    For $x, y in Q_n$, $x != y$, say $x < y$ in the *binary ordering* on $Q_n$ if $max (x Delta y) in y$. Equivalently, $
        x < y <==> sum_(i in x) 2^i < sum_(i in y) 2^i.
    $ "Go up in subcubes". Effectively, we are counting the naturals up to $2^(n - 1)$ (where an $n$-bit binary string corresponds to a subset of $Q_n$ in the obvious way).
]<def:binary-order>
#example[
    The elements of $Q_3$ in ascending binary order are $
        emptyset, 1, 2, 12, 3, 13, 23, 123.
    $
]
#definition[
    For $A subset.eq Q_n$, $1 <= i <= n$, the *$i$-binary-compression* $B_i (A) subset.eq Q_n$ is defined by its $i$-sections:
    - $(B_i (A))_-^((i))$ is the initial segment of binary ordering on $powset(X - i)$ of size $abs(A_-^((i)))$.
    - $(B_i (A))_+^((i))$ is the initial segment of binary ordering on $powset(X - i)$ of size $abs(A_+^((i)))$.
    So $abs(B_i (A)) = abs(A)$.
]<def:i-binary-compression>
#definition[
    $A subset.eq Q_n$ is *$i$-binary-compressed* if $B_i (A) = A$.
]<def:i-binary-compressed>
#example[
    A set $B subset.eq Q_n$ which is $i$-binary-compressed for all $1 <= i <= n$ is not necessarily an initial segment of binary, e.g. ${emptyset, 1, 2, 3} subset.eq Q_3$. However, we have:
]
#lemma[
    Let $B subset.eq Q_n$ be $i$-binary-compressed for all $1 <= i <= n$ but not an initial segment of binary. Then $
    B = underbrace(powset([n - 1]), #[downstairs]) \\ underbrace({1, 2, ..., n - 1}, #[last point in binary order in $
        powset([n - 1])$]) union underbrace({n}, #[first point in binary order not in $powset([n - 1])$])
    $
]<lem:edge-case-for-binary-compressed-but-not-initial-segment>
#unmarked-fig[
    #figure(
        canvas({
            import cetz.draw: *

            let h = 4
            rect((0, 0), (h, h), fill: diagram-colors.light-red)
            let shift = (0, h + 1)
            rect(add-points((0, 0), shift), add-points((h, h), shift))
            content((h + 0.25, h / 2), $Q_(n - 1)$, anchor: "west")
            content(add-points((h + 0.25, h / 2), shift), $Q_(n - 1)$, anchor: "west")
            content((h / 2, -0.5), $Q_n$)
            rect((h - 0.5, h - 0.5), (h, h), fill: diagram-colors.red, stroke: none, name: "lose")
            content("lose", box(inset: (left: 1em))[Lose], anchor: "west")
            rect(add-points((0, 0), shift), add-points((0.5, 0.5), shift), fill: diagram-colors.blue, stroke: none, name: "gain")
            content("gain", box(inset: (right: 1em))[Gain], anchor: "east")
        })
    )
]
#proofhints[
    For $x in.not B$ and $y in B$, show by contradiction that any $i in [n]$ is in exactly one of $x$ and $y$ (it helps to visualise this), and deduce that no elements lie strictly between $x$ and $y$ in the binary ordering.
]
#proof[
    As $B$ is not an initial segment, there are $x < y$ with $x in.not B$ and $y in B$.  For each $1 <= i <= n$, assume that $i in x, y$. Since the $i$-section that $y$ lives in is an initial segment of binary on $PP(X \\ i)$ (as $B$ is $i$-binary-compressed), and $x - i < y - i$ in binary on $PP(X \\ i)$, we have that $x - i$ lives in the same $i$-section, and so $x in B$: contradiction. Similarly, $i in.not x, y$ leads to a contradiction (as then $x < y$ in binary on $PP(X \\ i)$). So $x = y^c$.
    
    Thus, for each $y in B$, there is at most one $x < y$ with $x in.not B$ (namely $x = y^c$), and for each $x in.not B$, there is at most one $y > x$ with $y in B$ (namely $y = x^c$). So $B = {z: z <= y} \\ {x}$, where $x$ is the predecessor of $y$ and $y = x^c$. So we must have $y = {n}$ and $x = {1, 2, ..., n - 1}$.
]
#theorem([Edge-isoperimetric Inequality in $Q_n$])[
    Let $A subset.eq Q_n$ and let $C$ be the initial segment of binary on $Q_n$ with $abs(C) = abs(A)$. Then $abs(partial C) <= abs(partial A)$. In particular, if $abs(A) = 2^k$, then $abs(partial A) >= 2^k (n - k)$.
]<thm:edge-isoperimetric-inequality-in-cube>
#proofhints[
    - By induction on $n$.
    - Prove for each $1 <= i <= n$, $abs(partial B_i (A)) <= abs(partial A)$, by expressing $partial A$ as a disjoint union of three sets (it helps to visualise this), and using that $B_+$ and $B_-$ are nested (why?).
    - Define a sequence $A_0, A_1, ...$ in the obvious way, show it terminates by considering a suitable function $A_k$.
    - Use above lemma to conclude the result.
]
#proof[
    By induction on $n$. $n = 1$ is trivial. For $n > 1$ and $A subset.eq Q_n$, and $1 <= i <= n$, we claim that $abs(partial B_i (A)) <= abs(partial A)$.
    #proof("of claim")[
        Write $B = B_i (A)$. We have (remember $A_-, A_+ subset.eq Q_(n - 1)$ not $Q_n$) $
            abs(partial A) = underbrace(abs(partial A_-), "downstairs") + underbrace(abs(partial A_+), "upstairs") + underbrace(abs(A_+ Delta A_-), "across")
        $ and similarly, $abs(partial B) = abs(partial B_-) + abs(partial B_+) + abs(B_+ Delta B_-)$. Now, $abs(partial B_-) <= abs(partial A_-)$ and $abs(partial B_+) <= abs(partial A_+)$ by the induction hypothesis. Also, the sets $B_+$ and $B_-$ are nested/comparable (one is contained in the other), as each is an initial segment of binary on $powset(X - i)$. So, since $abs(B_-) = abs(A_-)$ and $abs(B_+) = abs(A_+)$ by definition, we have $
            abs(B_+ Delta B_-) = abs(B_+) - abs(B_-) = abs(A_+) - abs(A_-) <= abs(A_+ - A_-) <= abs(A_+ Delta A_-).
        $ if $B_- subset.eq B_+$, and similarly this holds if $B_+ subset.eq B_-$. So $abs(partial B) <= abs(partial A)$. This proves the claim.
    ]
    Define a sequence $A_0, A_1, ...$ as follows: set $A_0 = A$. Having defined $A_0, ..., A_k$, if $A_k$ is $i$-binary-compressed for all $1 <= i <= n$, then stop the sequence with $A_k$. Otherwise, choose $i$ with $B_i (A_k) != A_k$, and set $A_(k + 1) = A_k$. This must terminate, as the function $k |-> sum_(x in A_k) ("position of" x "in binary")$ is strictly decreasing.

    The final family in this sequence $B = A_k$ satisfies $abs(B) = abs(A)$, $abs(partial B) <= abs(partial A)$, and $B$ is $i$-binary-compressed for all $1 <= i <= n$. Then by @lem:edge-case-for-binary-compressed-but-not-initial-segment, we are done, since if $B$ is not initial segment, then clearly we have $abs(partial B) >= abs(partial C)$, since in that case $C = powset([n - 1])$.
]
#remark[
    It is vital in the proof, and of Harper's theorem, that the extremal sets, i.e. the $i$-sections of the compression (in dimension $n - 1$) were nested.
]
#definition[
    The *isoperimetric number* of a graph $G$ is $
        i(G) := min{abs(partial A) / abs(A): A subset.eq G, abs(A) / abs(G) <= 1/2}.
    $ $abs(partial A) \/ abs(A)$ can be thought as the average out-degree of $A$.
]<def:isoperimetric-number>
#corollary[
    We have $i(Q_n) = 1$.
]<crl:cube-has-isoperimetric-number-one>
#proofhints[
    Straightforward.
]
#proof[
    Taking $A = powset(n - 1)$ shows that $i(Q_n) <= 1$. To show $i(Q_n) >= 1$, by the above theorem, we just need to show that if $C$ is an initial segment of binary with $abs(C) <= 2^(n - 1)$, then $abs(partial C) >= abs(C)$. But in this case, $C subset.eq powset(n - 1)$, so certainly $abs(partial C) >= abs(C)$.
]

== Inequalities in the grid

#definition[
    For $k >= 2$ and $n in NN$, the *grid* is the graph on $[k]^n$ in which $x$ is joined to $y$ if $
        exists 1 <= i <= n: abs(x_i - y_i) = 1 "and" forall j != i, quad x_j = y_j.
    $ "The distance is the $ell_1$ distance". Note that for $k = 2$, this is precisely the definition of $Q_n$.
]<def:grid>
#fig-example[
    #figure(
        canvas({
            import cetz.draw: *

            let k = 4
            grid((0, 0), (k, k))
            for shift-x in range(k + 1) {
                for shift-y in range(k + 1) {
                    circle((shift-x, shift-y), ..point-style)
                }
            }
        }),
        caption: [The grid $[5]^2$]
    )
]
#notation[
    For a point $x$ in the grid on $[k]^n$, write $abs(x)$ for $sum_(i = 1)^n abs(x_i) = norm(x)_(ell_1)$. So $x$ is joined to $y$ in the grid on $[k]^n$ iff $norm(x - y)_(ell_1) = 1$.
]
#example[
    Which sets $A subset.eq [k]^n$ (of a given size) minimise $abs(N(A))$?
    #unmarked-fig[
        #align(center)[#grid(
            columns: 2,
            column-gutter: 4em,
            figure(
                canvas({
                    import cetz.draw: *

                    let h = 4
                    rect((0, 0), (h, h))
                    polygon(((0, 0), (h/calc.sqrt(2), 0), (0, h/calc.sqrt(2))), fill: diagram-colors.light-red, name: "A")
                    content("A.centroid", $A$)
                    let shift = (0, -0.2)
                    line(add-points((0, 0), shift), add-points((h/calc.sqrt(2), 0), shift), mark: (start: "straight", end: "straight"), name: "r")
                    content("r.centroid", $r$, anchor: "north")
                })
            ),
            figure(
                canvas({
                    import cetz.draw: *

                    let h = 4
                    rect((0, 0), (h, h))
                    rect((0, 0), (h/2, h/2), fill: diagram-colors.light-red, name: "B")
                    content("B.center", $B$)
                    let shift = (0, -0.2)
                    line(add-points((0, 0), shift), add-points((h/2, 0), shift), mark: (start: "straight", end: "straight"), name: "r")
                    content("r.centroid", $r$, anchor: "north")
                })
            )
        )]
    ]
    In the diagram for $[k]^2$, $abs(b(A)) approx r approx sqrt(2 abs(A))$ and $abs(b(B)) = 2 r = 2 sqrt(abs(B))$ suggests we "go up in levels" according to $abs(x) = sum_(i = 1)^n abs(x_i)$, so we'd take ${x in [k]^n: abs(x) <= r}$. If $
        abs({x in [k]^n: abs(x) <= r}) < abs(A) < abs({x in [k]^n: abs(x) <= r + 1}),
    $ then a reasonable guess is to take $A = {x in [k]^n: abs(x) <= r}$ together with some points with $x$ with $abs(x) = r + 1$. As suggested in the diagram below, we should take points while obeying the motto "keep $x_1$ large":
    #unmarked-fig[
        #figure(
            canvas({
                import cetz.draw: *
                import cetz.matrix
                
                set-transform(matrix.transform-rotate-dir((1.2, -1, 1.2), (0, -0.5, -.3)))
                // axes
                let r = 4
                line((0, 0, 0), (r, 0, 0), mark: (end: "straight"))
                line((0, 0, 0), (0, r, 0), mark: (end: "straight"))
                line((0, 0, 0), (0, 0, r), mark: (end: "straight"))
                polygon(((r/2, 0, 0), (0, r/2 + 1, 0), (0, 0, r/2)), fill: diagram-colors.light-red, stroke: diagram-colors.red, name: "simplex")
                polygon(((r/2, 0, 0), (r/2 - 0.5, (r/2 + 1)/(r/2)*0.5, 0), (r/2 - 0.5, 0, 0.5)), fill: diagram-colors.red, stroke: none)
                line((0.25, 0, r/2 - 0.25), (0.25, r/2 + 1 - (r/2 + 1)/(r/2)*0.25, 0), stroke: (paint: diagram-colors.red, dash: "dashed"), name: "large")
                content("large.end", box(inset: (left: 0.5em))[$x_1$ large], anchor: "west")
                content((r/2, 0, 0), box(inset: 0.2em)[$x_1$ small], anchor: "north-east")
                line((r/4 - 0.2, (r/2 + 1)/(r/2)*r/4 - 0.2, 0), (r/2, r/2, 0), name: "label-line")
                content("label-line.end", box(inset: (left: 0.5em))[$abs(x) = sum_i x_i = r + 1$], anchor: "north-west")
            })
        )
    ]
    This suggests the following definition:
]
#definition[
    The *simplicial order* on the grid $[k]^n$ defines $x < y$ if either $abs(x) < abs(y)$, or $abs(x) = abs(y)$ and $x_i > y_i$, where $i = min\{j in [n]: x_j != y_j\}$.

    Note that this definition agrees with the definition of simplicial order on the cube (i.e. when $k = 2$).
]<def:simplicial-order-on-grid>
#example[
    The elements of $[3]^2$ in ascending simplicial order are $
        (1, 1), (2, 1), (1, 2), (3, 1), (2, 2), (1, 3), (3, 2), (2, 3), (3, 3).
    $
    #unmarked-fig[
        #figure(
            canvas({
                import cetz.draw: *

                grid((0, 0), (4, 4), step: 2)
                for shift-x in range(0, 5, step: 2) {
                    for shift-y in range(0, 5, step: 2) {
                        circle((shift-x, shift-y), ..point-style)
                    }
                }
                let line-points = (((2, 0), (0, 2)), ((4, 0), (0, 4)), ((4, 2), (2, 4)))
                for (p1, p2) in line-points {
                    line(p1, p2, stroke: diagram-colors.red, mark: (end: "straight"))
                }
            })
        )
    ]
    The elements of $[4]^3$ in ascending simplicial order are $
        & (1, 1, 1), (2, 1, 1), (1, 2, 1), (1, 1, 2), (3, 1, 1), (2, 2, 1), (2, 1, 2), (1, 3, 1), (1, 2, 2), (1, 1, 3), \
        & (4, 1, 1), (3, 2, 1), ...
    $
]
#definition[
    For $A subset.eq [k]^n$, $n >= 2$, and $1 <= i <= n$, the *$i$-sections* of $A$ are the sets $
        A_j^((i)) = A_j := {x in [k]^(n - 1): (x_1, ..., x_(i - 1), j, x_(i + 1), ..., x_(n - 1)) in A} subset.eq [k]^(n - 1).
    $ for each $1 <= j <= k$.
]<def:i-sections-for-grid>
#fig-example[
    #figure(
        canvas({
            import cetz.draw: *
            import cetz.matrix
            
            set-transform(matrix.transform-rotate-dir((1.1, -0.5, 1.1), (0, -0.6, -.3)))
            // axes
            let r = 4
            let shift-1 = (0, 0, 3)
            let shift-2 = (0, 0, 6)
            rect((0, 0, 0), (r, r, 0))
            rect(add-points((0, 0, 0), shift-1), add-points((r, r, 0), shift-1))
            rect(add-points((0, 0, 0), shift-2), add-points((r, r, 0), shift-2))
            content((0, 0, 0), box(inset: (right: 0.5em))[$A_1$], anchor: "east")
            content(shift-1, box(inset: (right: 0.5em))[$A_2$], anchor: "east")
            content(shift-2, box(inset: (right: 0.5em))[$A_3$], anchor: "east")
            line((r + 0.5, r + 0.5, 0), add-points((r + 0.5, r + 0.5, 0), shift-2), mark: (end: "straight"), name: "axis")
            content("axis.centroid", box(inset: (left: 0.5em))[$3$], anchor: "west")
            let points-1 = ((0.5, 0.5), (1, 0.4), (1.2, 0.35), (1.8, 0.5), (1, 1), (0.8, 1.2))
            let points-1 = points-1.map(p => (p.at(0) * 1.5, p.at(1) * 1.5))
            hobby(..points-1, close: true, fill: diagram-colors.light-red, stroke: diagram-colors.red)
            let points-2 = ((0.5, 0.5), (1, 0.5), (1.3, 0.45), (2, 0.6), (1, 1.2), (0.7, 1.2))
            // let points-2 = points-2.map(p => add-points(p, shift-1))
            let points-2 = points-2.map(p => (p.at(1) * 2, p.at(0) * 1.7))
            translate(z: shift-1.at(2))
            hobby(..points-2, close: true, fill: diagram-colors.light-red, stroke: diagram-colors.red)
            let points-3 = ((0.5, 0.6), (0.9, 0.6), (1.2, 0.65), (1.9, 0.6), (1.2, 1.1), (0.7, 1.3))
            let points-3 = points-3.map(p => (p.at(0) * 1.6, p.at(1) * 2))
            translate(z: shift-1.at(2))
            set-style(
                fill: diagram-colors.light-red,
                stroke: diagram-colors.red
            )
            hobby(..points-3, close: true)
        }),
        caption: [The $3$-sections of $A subset.eq [k]^3$]
    )
]
#definition[
    The *$i$-compression* of $A subset.eq [k]^n$ is the set $C_i (A) subset.eq [k]^n$ which is defined by its $i$-sections: $C_i (A)_j$ is the initial segment of simplicial on $[k]^(n - 1)$ of size $abs(A_j)$, for each $1 <= j <= k$.

    We have $abs(C_i (A)) = abs(A)$.
]<def:grid-i-compression>
#definition[
    $A subset.eq [k]^n$ is *$i$-compressed* if $C_i (A) = A$.
]<def:grid-i-compressed>
#theorem("Vertex-isoperimetric Inequality in the Grid")[
    Let $A subset.eq [k]^n$ and $C$ be the initial segment of simplicial on $[k]^n$ with $abs(C) = abs(A)$. Then $abs(N(C)) <= abs(N(A))$. In particular, $
        abs(A) >= abs({x in [k]^n: abs(x) <= r}) quad ==> quad abs(N(A)) >= abs({x in [k]^n: abs(x) <= r + 1}).
    $
]<thm:vertex-isoperimetric-inequality-in-the-grid>
#proofhints[
    - Use induction on $n$.
    - Prove that $abs(N(C_i (A))) <= abs(N(A))$ by writing the $i$-section $N(A)_j^((i))$ as a union of three sets, doing the same for $N(C_i (A))_j^((i))$, and using the fact that these three sets (for $C_i (A)$) are nested (why?).
    - Let $B subset.eq [k]^n$, $abs(B) = abs(A)$ and $abs(N(B)) <= abs(N(A))$, and let $B$ be $i$-compressed for all $1 <= i <= n$ (find an expression to minimise which will imply $B$ has this property).
    - Case $n = 2$:
        - Let $r = min{abs(x): x in.not B}$, $s = max{abs(x): x in B}$.
        - Explain why $r <= s + 1$ and that we can assume $r <= s$.
        - Show that if $r = s$, then $abs(N(C)) <= abs(N(B))$.
        - Explain why ${x in [k]^n: abs(x) = s} subset.eq B$ implies ${x in [k]^n: abs(x) = r} subset.eq B$, reason that this would be a contradiction. Deduce that there exist $y in B$, $y' in.not B$ such that $abs(y) = abs(y') = s$ and $y' = y plus.minus (1, -1)$.
        - By a similar argument, show that there exist $x in.not B$, $x' in B$ with $abs(x) = abs(x') = r$ and $x' = x plus.minus (1, -1)$.
        - Consider $B'$ which is obtained from $B$ by adding an appropriate element and removing an appropriate element.
        - Reason that $abs(N(B')) <= abs(N(B))$, contradicting the minimality of $B$ (it helps to draw a diagram).
    - Case $n >= 3$:
        - For $1 <= i <= n - 1$ and $x in B$ with $x_n > 1$ and $x_i < k$ explain why $x - e_n + e_i in B$.
        - Considering the $n$-sections of $B$, explain why $N(B)_j subset.eq B_(j - 1)$ and hence that $N(B)_j = B_(j - 1)$.
        - TODO: add in a few more details maybe.
        - Use this to show that $abs(N(B)) = abs(B) - abs(B_k) + abs(N(B_1))$, and similarly for $C$.
        - Show that $abs(B_k) <= abs(C_k)$, by defining a set $D subset.eq [k]^n$ by its $n$-sections: $D_k := B_k$, and $D_(j - 1) = N(D_j)$ for all $j$, and showing that $D subset.eq C$.
        - Show that $abs(B_1) >= abs(C_1)$, by defining a set $E subset.eq [k]^n$ by its $i$-sections: $E_1 := B_1$, $E_j = {x in [k]^(n - 1): N({x}) subset.eq E_(j - 1)}$, and showing that $C subset.eq E$.
        - Conclude that $abs(N(B_1)) >= abs(N(C_1))$.
]
#proof[
    By induction on $n$. The case $n = 1$ follows since if $A subset.eq [k]^1$ and $A != emptyset, [k]^1$, then $abs(N(A)) >= abs(A) + 1 = abs(N(C))$. Now given $n > 1$, and $A subset.eq [k]^n$, fix $1 <= i <= n$, we claim that $abs(N(C_i (A))) <= abs(N(A))$.

    #proof("of claim")[
        Write $B = C_i (A)$. For any $1 <= j <= k$, we have $
            N(A)_j = underbrace(N(A_j), "from" x_i = j) union underbrace(A_(j - 1), "from" x_i = j - 1) union underbrace(A_(j + 1), "from" x_i = j + 1)
        $ where we set $A_0 = A_(k + 1) = emptyset$. Similarly, $N(B)_j = N(B_j) union B_(j - 1) union B_(j + 1)$. Now, $abs(B_(j - 1)) = abs(A_(j - 1))$ and $abs(B_(j + 1)) = abs(A_(j + 1))$ by definition, and $abs(N(B_j)) <= abs(N(A_j))$ by the induction hypothesis. But the sets $B_(j - 1), B_(j + 1)$ and $N(B_j)$ are nested, as each is an initial segment of simplicial on $[k]^(n - 1)$ (since neighbourhood of initial segment of simplicial is initial segment of simplicial). Hence $abs(N(B)_j) <= abs(N(A)_j)$ for each $1 <= j <= k$, thus $abs(N(B)) <= abs(N(A))$. This proves the claim.
    ]

    Among all $B subset.eq [k]^n$ with $abs(B) = abs(A)$ and $abs(N(B)) <= abs(N(A))$, pick one with $sum_(x in B) ("position of" x "in simplicial")$ minimal. Then $B$ is $i$-compressed for all $1 <= i <= n$. We consider the following cases:
    - Case $n = 2$: what we know is precisely that $B$ is a down-set ($A subset.eq [k]^n$ is a *down-set* if $forall x in A, forall y in [k]^n, (y_i <= x_i thick forall 1 <= i <= n) ==> y in A$.)
    #unmarked-fig[
        #figure(
            canvas({
                import cetz.draw: *

                let h = 4
                polygon(((0, 0), (0, 3), (1, 3), (1, 2), (1.2, 2), (1.8, 2), (1.8, 1.6), (2.2, 1.6), (2.2, 1), (2.7, 1), (2.7, 0.5), (3.8, 0.5), (3.8, 0)), fill: diagram-colors.light-red, stroke: diagram-colors.red, name: "B")
                content("B.centroid", $B$)
                content((h/2, h), box(inset: (bottom: 0.5em))[$[k]^2$], anchor: "south")
                rect((0, 0), (h, h))
            })
        )
    ]
    Let $r = min{abs(x): x in.not B}$ and $s = max{abs(x): x in B}$. We have that $r <= s + 1$ by definition. We may assume that $r <= s$, since if $r = s + 1$, then $B = {x: abs(x) <= r - 1}$ which is an initial segment of simplicial, hence $B = C$.
    #unmarked-fig[
        #figure(
            canvas({
                import cetz.draw: *

                let h = 4
                polygon(((0, 0), (0, 3), (1, 3), (1, 2), (1.2, 2), (1.8, 2), (1.8, 1.6), (2.2, 1.6), (2.2, 1), (2.7, 1), (2.7, 0.5), (3.8, 0.5), (3.8, 0)), fill: diagram-colors.light-red, stroke: diagram-colors.red, name: "B")
                content("B.centroid", $B$)
                content((h/2, h), box(inset: (bottom: 0.5em))[$[k]^2$], anchor: "south")
                rect((0, 0), (h, h))
                circle((1, 2), ..point-style)
                circle((3.8, 0.5), ..point-style)
                line((0, 3), (3, 0), stroke: (paint: diagram-colors.red, dash: "dashed"), name: "level-r")
                line((0.3, 4), (4, 0.3), stroke: (paint: diagram-colors.red, dash: "dashed"), name: "level-s")
                content("level-r.end", box(inset: (top: 0.5em))[level $r$], anchor: "north")
                content("level-s.end", box(inset: (left: 0.5em))[level $s$], anchor: "west")
            })
        )
    ]
    If $r = s$, then $
        {x in [k]^n: abs(x) <= r - 1} subset.eq B subset.eq {x in [k]^n: abs(x) <= r},
    $ so clearly $abs(N(C)) <= abs(N(B))$.
    #unmarked-fig[
        #figure(
            canvas({
                import cetz.draw: *

                polygon(((0, 0), (0, 3), (3, 0)), fill: diagram-colors.light-red, stroke: diagram-colors.red, name: "region")
                rect((0, 0), (6, 6))
                line((4, 0), (0, 4), stroke: (dash: "dashed", paint: diagram-colors.red, thickness: 1.4pt))
                content("region.centroid", $X^((< r))$)
                for point in ((3.5, 0.2), (3, 0.6), (2.5, 1), (2.1, 1.4), (1.7, 2)) {
                    circle(point, ..point-style, fill: diagram-colors.red)
                }
                content((4, -0.25), [some stuff on level $r$])
            }),
            caption: [Case when $r = s$]
        )
    ]
    We cannot have ${x in [k]^n: abs(x) = s} subset.eq B$ because then also ${x in [k]^n: abs(x) = r} subset.eq B$ (as $B$ is a down-set).
    #unmarked-fig[
        #figure(
            canvas({
                import cetz.draw: *

                rect((0, 0), (4, 4))
                set-style(
                    // stroke: diagram-colors.red
                )
                line((2.5, 0), (0, 2.5), name: "level-r")
                line((2, 4), (4, 2), name: "level-s")
                content("level-r.end", box(inset: (right: 0.5em))[$r$], anchor: "east")
                content("level-s.end", box(inset: (left: 0.5em))[$s$], anchor: "west")
                
                hobby((2.5, 3.5), (2.3, 3.3), (1.5, 3.1), (1.4, 2.5), (2.4, 1.8), (2.5, 1.5), (1.5, 1), mark: (end: ">"))
                for (point, name) in ((1.5, 1), (1, 1.5), (1.5, 1.5), (3, 3), (2.5, 3.5), (3, 3.5)).zip(("x", "x'", "w", "y'", "y", "z")) {
                    circle(point, ..point-style, name: name)
                }
                content("x", box(inset: (top: 0.25em))[$x$ out], anchor: "north-east")
                content("x'", box(inset: (right: 0em))[$x'$ in], anchor: "north-east")
                content("y", box(inset: (right: 0.5em))[$y$ in], anchor: "east")
                content("y'", box(inset: (right: 0.5em))[$y'$ out], anchor: "north-east")
                content("w", box(inset: (bottom: 0.5em))[$w$], anchor: "south")
                content("z", box(inset: (left: 0.5em))[$z$], anchor: "west")
            }),
            caption: [Case when $r < s$]
        )
    ]
    So there are $y, y'$ with $abs(y) = abs(y') = s$, $y in B$, $y' in.not B$, and $y' = y plus.minus (e_1 - e_2)$ (where $e_1 = (1, 0)$, $e_2 = (0, 1)$ are the standard basis vectors). Similarly, since ${x in [k]^n: abs(x) != s} subset.eq {x in [k]^n: abs(x) != r}$, we cannot have ${x in [k]^n: abs(x) = r} sect B = emptyset$, because then ${x in [k]^n: abs(x) = s} sect B = emptyset$ (since $B$ is a down-set): contradiction. So there are $x, x'$ with $abs(x) = abs(x') = r$, $x in.not B$, $x' in B$, and $x' = x plus.minus (e_1 - e_2)$. Now let $B' = B union {x} \\ {y}$. From $B$ we lost at least one point in the neighbourhood (namely the unique point $z$ which is joined to both $y$ and $y'$) and gained at most one point (the only point we might gain is the unique point $w$ which is joined to both $x$ and $x'$), so $abs(N(B')) <= abs(N(B))$, but this contradicts the minimality of $B$.
    - Case $n >= 3$: for any $1 <= i <= n - 1$ and any $x in B$ with $x_n > 1$ and $x_i < k$, we have $x - e_n + e_i in B$, since $x - e_n + e_i < x$ in simplicial and $B$ is $j$-compressed for any $j != i, n$. So, considering the $n$-sections of $B$, we have $N\(B_j\) subset.eq B_(j - 1)$ for all $j = 2, ..., k$. Recall that $N(B)_j = N\(B_j\) union B_(j + 1) union B_(j - 1)$. So in fact, $N(B)_j = B_(j - 1)$ for all $j >= 2$. Thus $
        abs(N(B)) = underbrace(abs(B_(k - 1)), "level" k) + underbrace(abs(B_(k - 2)), "level" k - 1) + dots.c + underbrace(abs(B_1), "level" 2) + underbrace(abs(N(B_1)), "level" 1) = abs(B) - abs(B_k) + abs(N(B_1)).
    $ Similarly, $abs(N(C)) = abs(C) - abs(C_k) + abs(N(C_1))$. So to show $abs(N(C)) <= abs(N(B))$, it is enough to show that $abs(B_k) <= abs(C_k)$ and $abs(B_1) >= abs(C_1)$ (since $B_1$, $C_1$ and their neighbourhoods are initial segments of simplicial). \ $abs(B_k) <= abs(C_k)$: define a set $D subset.eq [k]^n$ by its $n$-sections as follows: let $D_k := B_k$, and for $j = k - 1, k - 2, ..., 1$, set $D_j := N\(D_(j + 1)\)$. Then $D subset.eq B$, so $abs(D) <= abs(B)$. Also, $D$ is an initial segment of simplicial, since $B_k$ is an initial segment of simplicial, and so all $n$-sections of $D$ are as well. So in fact, $D subset.eq C$, whence $abs(B_k) = abs(D_k) <= abs(C_k)$. \ $abs(B_1) >= abs(C_1)$: define a set $E subset.eq [k]^n$ as follows: set $E_1 = B_1$ and for $j = 2, 3, ..., k$, set $E_j = {x in [k]^(n - 1): N({x}) subset.eq E_(j - 1)}$, so $E_j$ is the biggest set whose neighbourhood is contained in $E_(j - 1)$. Then $B subset.eq E$, so $abs(E) >= abs(B)$. Also, $E$ is an initial segment of simplicial. So $C subset.eq E$, whence $abs(B_1) = abs(E_1) >= abs(C_1)$.
]
#corollary[
    Let $A subset.eq [k]^n$ and $abs(A) >= abs({x in [k]^n: abs(x) <= r})$. Then $abs(N^j (A)) >= abs({x in [k]^n: abs(x) <= r + j})$ for all $j$.
]
#proofhints[
    Trivial by above.
]
#proof[
    By induction, using above.
]
#remark[
    We can check from the above corollary that, for $k$ fixed, the sequence of grids ${[k]^n: n in NN}$ is a Levy family.
]

== The edge-isoperimetric inequality in the grid

#example[
    Which set $A subset.eq [k]^n$ of given size should we take to minimise $abs(partial A)$?
    #unmarked-fig[
        #align(center)[#grid(
            columns: 2,
            column-gutter: 4em,
            figure(
                canvas({
                    import cetz.draw: *

                    let h = 4
                    rect((0, 0), (h, h))
                    polygon(((0, 0), (h/calc.sqrt(2), 0), (0, h/calc.sqrt(2))), fill: diagram-colors.light-red, name: "A")
                    content("A.centroid", $A$)
                    let shift = (-0.2, 0)
                    line(add-points((0, 0), shift), add-points((0, h/calc.sqrt(2)), shift), mark: (start: "straight", end: "straight"), name: "r")
                    content("r.centroid", box(inset: (right: 0.25em))[$r$], anchor: "east")
                }),
                caption: [$abs(partial A) approx 2r$]
            ),
            figure(
                canvas({
                    import cetz.draw: *

                    let h = 4
                    rect((0, 0), (h, h))
                    rect((0, 0), (h/2, h/2), fill: diagram-colors.light-red, name: "B")
                    content("B.center", $B$)
                    let shift = (0, 0.2)
                    let shift-2 = (0.2, 0)
                    line(add-points((0, h/2), shift), add-points((h/2, h/2), shift), mark: (start: "straight", end: "straight"), name: "r")
                    line(add-points((h/2, 0), shift-2), add-points((h/2, h/2), shift-2), mark: (start: "straight", end: "straight"), name: "r-2")
                    content("r.centroid", box(inset: (bottom: 0.25em))[$r$], anchor: "south")
                    content("r-2.centroid", box(inset: (left: 0.25em))[$r$], anchor: "west")
                }),
                caption: [$abs(partial A) approx 2r$]
            )
        )]
    ]
    The diagram above for $[k]^2$ suggests squares are best. However, the diagram below shows we have "phase transitions" at $abs(A) approx k^2 \/ 4$ and $abs(A) approx 3k^2 \/ 4$. So the extremal sets are not nested.
    #unmarked-fig[
        #figure(
            canvas({
                import cetz.draw: *

                let shift-1 = (5, 0)
                let shift-2 = add-points(shift-1, shift-1)
                let shift-3 = (0, -5)
                let shift-4 = add-points(shift-1, shift-3)
                let shift-5 = add-points(shift-1, shift-1, shift-3)

                set-style(fill: diagram-colors.light-red, stroke: diagram-colors.red)
                rect((0, 0), (1, 1))
                rect(add-points((0, 0), shift-1), add-points((2, 2), shift-1))
                rect(add-points((0, 0), shift-2), add-points((1, 4), shift-2))
                rect(add-points((0, 0), shift-2), add-points((1, 4), shift-2))
                rect(add-points((0, 0), shift-3), add-points((3, 4), shift-3))
                polygon(((0, 0), (0, 4), (2, 4), (2, 2), (4, 2), (4, 0)).map(p => add-points(p, shift-4)))
                polygon(((0, 0), (0, 4), (3, 4), (3, 3), (4, 3), (4, 0)).map(p => add-points(p, shift-5)))

                content((1.1, 0.5), $r$, anchor: "west")
                content((0.5, 1.1), $r$, anchor: "south")
                content(add-points((2.1, 1), shift-1), $k \/ 2$, anchor: "west")
                content(add-points((1, 2.1), shift-1), $k \/ 2$, anchor: "south")
                content(add-points((1.1, 2), shift-2), $k$, anchor: "west")
                content(add-points((0.5, 4.1), shift-2), $k \/ 4$, anchor: "south")
                content(add-points((3.1, 2), shift-3), $k$, anchor: "west")
                content(add-points((1.5, -0.1), shift-3), $3k \/ 4$, anchor: "north")
                content(add-points((2.1, 3), shift-4), $k \/ 2$, anchor: "west")
                content(add-points((3, 2.1), shift-4), $k \/ 2$, anchor: "south")
                content(add-points((2.9, 3.5), shift-5), $r$, anchor: "east")
                content(add-points((3.5, 2.9), shift-5), $r$, anchor: "north")

                set-style(fill: none, stroke: black)
                merge-path({
                    arc-through(add-points((4, 0.5), shift-2), add-points((4.5, 0), shift-2), add-points((4, -0.5), shift-2))
                    line(add-points((4, -0.5), shift-2), (0, -0.5))
                    arc-through((0, -0.5), (-0.5, -1), (0, -1.5), mark: (end: ">"))
                })
                for (i, shift) in ((0, 0), shift-1, shift-2, shift-3, shift-4, shift-5).enumerate() {
                    rect(add-points((0, 0), shift), add-points((4, 4), shift), name: "stage-" + str(i))
                }
                line("stage-0", "stage-1", mark: (end: "straight"))
                line("stage-1", "stage-2", mark: (end: "straight"))
                line("stage-3", "stage-4", mark: (end: "straight"))
                line("stage-4", "stage-5", mark: (end: "straight"))
            })
        )
    ]
    This seems to rule out all our compression methods. In $[k]^3$:
    - Start with $[a]^3$,
    - then the square columns $[a]^2 times [k]$,
    - then the "half spaces" $[a] times [k]^2$,
    - then the complements of the square columns,
    - then the complements of the cubes.
    Generalising, in $[k]^n$, up to $abs(A) = k^n \/ 2$, we get $n - 1$ of these "phase transitions".
]
#theorem("Edge-isoperimetric Inequality in the Grid")[
    Let $A subset.eq [k]^n$. If $abs(A) <= k^n \/ 2$, then $
        abs(partial A) >= min{d abs(A)^(1 - 1 \/ d) k^(n \/ d - 1): 1 <= d <= n}.
    $
]<thm:edge-isoperimetric-inequality-in-grid>
#proofhints[
    Non-examinable.
]
#proof[
    Non-examinable.
]
#remark[
    Note that if $A = [a]^d times [k]^(n - d)$, then $
        abs(partial A) = d a^(d - 1) k^(n - d) = d abs(A)^(1 - 1 \/ d) k^(n \/ d - 1).
    $ So the @thm:edge-isoperimetric-inequality-in-grid says that some set of the form $[a]^d times [k]^(n - d)$ minimises the edge boundary.
]
#remark[
    Very few isoperimetric inequalities are known (even approximately), e.g. "iso in a layer": in a graph $X^((r))$, with $x, y$ joined if $abs(x sect y) = r - 1$. This is open. A nice special case is $r = n\/2$, where it is conjectured that balls are best, i.e. sets of the form ${x in [2r]^((r)): abs(x sect [r]) >= t}$.
]


= Intersecting families

== $t$-intersecting families

#definition[
    $A subset.eq powset(X)$ is *$t$-intersecting* if $
        forall x, y in A, quad abs(x sect y) >= t.
    $
]<def:t-intersecting-family>
#example[
    How large can a $t$-intersecting family be? For $t = 2$, we could take ${x subset.eq X: 1, 2 in x}$, which has size $1/4 dot 2^n$, but better is ${x subset.eq X: abs(x) >= n \/ 2 + 1}$, which has size $approx 1/2 dot 2^n$.
    #unmarked-fig[
        #figure(
            canvas({
                import cetz.draw: *

                polygon(((0, 3), (1.8, 3 - 3/2 * 1.8), (-1.8, 3 - 3/2 * 1.8)), fill: diagram-colors.light-red, stroke: diagram-colors.red)
                polygon(((0, -3), (-2, 0), (0, 3), (2, 0)))
                content((1.8, 3 - 3/2 * 1.8), box(inset: (left: 0.5em))[$n\/2 + 1$], anchor: "west")
            })
        )
    ]
]
#theorem([Katona's $t$-intersecting Theorem])[
    Let $A subset.eq powset(X)$ be $t$-intersecting, where $n equiv t mod 2$. Then $
        abs(A) <= abs(X^((>= (n + t)\/2))).
    $
]<thm:katona-t-intersecting>
#proofhints[
    - Show that $N^(t - 1)(A)$ is disjoint from $overline(A) := {y^c: y in A}$.
    - Assuming the negation of the theorem statement, show that $
        abs(N^(t - 1)(A)) >= abs(X^((>= (n - t) \/ 2 + 1))),
    $ and derive a contradiction (find a strict lower bound for the size of $overline(A)$).
]
#proof[
    For any $x, y in A$, we have $abs(x sect y) >= t$, so $d(x, y^c) >= t$. Writing $overline(A) = {y^c: y in A}$, we have $d\(A, overline(A)\) >= t$, i.e. $N^(t - 1)(A)$ is disjoint from $overline(A)$. Suppose for a contradiction $abs(A) > abs(X^((>= (n + t) \/ 2)))$. Then by @thm:harper, we have $
        abs(N^(t - 1)(A)) >= abs(X^((>= (n + t) \/ 2 - (t - 1)))) = abs(X^((>= (n - t) \/ 2 + 1))).
    $ But $N^(t - 1)(A)$ is disjoint from $overline(A)$ which has size $abs(overline(A)) = abs(A) > abs(X^((<= (n - t) \/ 2)))$, contradicting $abs(N^(t - 1)(A)) + abs(overline(A)) <= 2^n$.
]
#example[
    What about $t$-intersecting $A$ with $A subset.eq X^((r))$? We might guess that the best is $A_0 = {x in X^((r)): [t] subset.eq x}$. We could also try $A_alpha = {x in X^((r)): abs(x sect [t + 2 alpha]) >= t + alpha}$ for $alpha = 1, ..., r - t$.
    - For $2$-intersecting families in $[7]^((4))$: $abs(A_0) = binom(5, 2) = 10$, $abs(A_1) = 1 + binom(4, 3) binom(3, 1) = 13$, $abs(A_2) = binom(6, 4) = 15$.
    - For $2$-intersecting families in $[8]^((4))$: $abs(A_0) = binom(6, 2) = 15$, $abs(A_1) = 1 + binom(4, 3) binom(4, 1) = 17$, $abs(A_2) = binom(6, 4) = 15$.
    - For $2$-intersecting families in $[9]^((4))$: $abs(A_0) = binom(7, 2) = 21$, $abs(A_1) = 1 + binom(4, 3) binom(5, 1) = 21$, $abs(A_2) = binom(6, 4) = 15$.
    Note that $A_0$ grows quadratically, $A_1$ grows linearly, $A_2$ is constant, so $A_0$ is the largest of these for large $n$.
    #unmarked-fig(
        figure(
            canvas({
                import cetz.draw: *

                line((0.8, 0), (7.2, 0))
                for i in range(1, 8) {
                    circle((i, 0), ..point-style, fill: diagram-colors.blue, name: "point-" + str(i))
                    content("point-" + str(i), box(inset: (bottom: 0.5em))[$#i$], anchor: "south")
                }
                set-style(stroke: diagram-colors.red + 2pt)
                line((2.5, 0.25), (2.5, -0.25), name: "A0")
                line((4.5, 0.25), (4.5, -0.25), name: "A1")
                line((6.5, 0.25), (6.5, -0.25), name: "A2")
                content("A0.end", box(inset: (top: 0.5em))[$A_0$], anchor: "north")
                content("A1.end", box(inset: (top: 0.5em))[$A_1$], anchor: "north")
                content("A2.end", box(inset: (top: 0.5em))[$A_2$], anchor: "north")
            })
        )
    )
]
#theorem("Second Erdos-Ko-Rado Theorem")[
    Let $X = [n]$ and let $A subset.eq X^((r))$ be $t$-intersecting. Then, for $n$ sufficiently large, we have $abs(A) <= abs(A_0) = binom(n - t, r - t)$.
]<thm:second-erdos-ko-rado>
#proofhints[
    - Show by contradiction that a maximal $t$-intersecting family $A' supset.eq A$ has $x, y in A'$ with $abs(x sect y) = t$.
    - Explain why we can assume that there exists $z in A'$ with $x sect y subset.eq.not z$, and hence each $w in A'$ meets $x union y union z$ in $>= t + 1$ points.
    - Show that $abs(A')$ is bounded above by a polynomial in $n$ of degree $r - t - 1$.
]
#proof[
    Idea: "$A_0$ has $r - t$ degrees of freedom".

    Extend $A$ to a maximal $t$-intersecting family $A'$, trivially $abs(A) <= abs(A')$. There exist $x, y in A'$ with $abs(x sect y) = t$ (if not, then by maximality, we have that $forall x in A', forall i in x, forall j in.not x$, $x \\ i union j in A'$; repeating this, we have $A' = X^((r))$: contradiction). We may assume that there exists $z in A'$ with $x sect y subset.eq.not z$; otherwise, all $z in A'$ contain the $t$-set $x sect y subset.eq z$, whence $abs(A') <= binom(n - t, r - t) = abs(A_0)$. So each $w in A'$ must meet $x union y union z$ in $>= t + 1$ points.
    #unmarked-fig(
        figure(
            canvas({
                import cetz.draw: *

                cetz-venn.venn3(name: "venn", not-abc-stroke: none, padding: 0)
                content("venn.a", $x$)
                content("venn.b", $y$)
                content("venn.c", $z$)
                line("venn.ab", (rel: (0, 1)), mark: (start: "o", fill: diagram-colors.red), name: "label")
                content("label.end", $abs(x sect y) = t$, anchor: "south")
            })
        )
    )
    Thus $
        abs(A') <= underbrace(2^(3r), #[$w$ on $x union y union z$]) dot underbrace((binom(n, r - t - 1) + binom(n, r - t - 2) + dots.c + binom(n, 0)), #[$w$ off $x union y union z$])
    $ which is a polynomial in $n$ of degree $r - t - 1$, so is eventually smaller than $abs(A_0) = binom(n - t, r - t)$, a polynomial in $n$ of degree $r - t$.
]
#remark[
    The bound we obtain for $n$ in the @thm:second-erdos-ko-rado would be $>= (16r)^r$ (crude) or $2 t r^3$ (careful).
]

== Modular intersections

#example[
    For intersecting families, we ban $abs(x sect y) = 0$. What if we banned $abs(x sect y) = 0 mod k$ for some $k in NN$?

    For example, for $k = 2$, we want $A subset.eq X^((r))$ with $abs(x sect y)$ odd for all $x != y in A$. When $r$ is odd, we can achieve $abs(A) = binom(floor((n - 1)\/2), (r - 1)\/2)$ by the diagram below.
    #unmarked-fig[
        #figure(
            canvas({
                import cetz.draw: *

                for i in range(1, 6) {
                    circle((i, 0), ..point-style, fill: diagram-colors.blue, name: "point-" + str(i))
                    content("point-" + str(i), box(inset: (bottom: 0.5em))[$#i$], anchor: "south")
                }
                line((1, -0.9), (1, -0.25), mark: (end: "straight"), name: "take")
                content("take.start", box(inset: (top: 0.5em))[Take], anchor: "north")
                for i in range(5) {
                    circle((6 + i/4, 0), radius: 0.05, stroke: none, fill: black)
                }
                circle((8, 0), ..point-style, fill: diagram-colors.blue, name: "point-n1")
                content("point-n1", box(inset: (bottom: 0.5em))[$n - 1$], anchor: "south")
                circle((9, 0), ..point-style, fill: diagram-colors.blue, name: "point-n")
                content("point-n", box(inset: (bottom: 0.5em))[$n$], anchor: "south")
                cetz.decorations.brace((2, -0.5), (9, -0.5), flip: true, name: "brace")
                content("brace.content", [Take $(r - 1)\/2$ pairs from here])
                let bracket = merge-path({
                    line((1.8, -0.1), (1.8, -0.3))
                    line((1.8, -0.3), (3.2, -0.3))
                    line((3.2, -0.3), (3.2, -0.1))
                })
                bracket
                translate(x: 2)
                bracket
                translate(x: 4)
                bracket
            })
        )
    ]
    For $r$ odd, if we want $abs(x sect y)$ even for all $x != y in A$, we can achieve $n - r + 1$ by the diagram below, but this is only linear in $n$.
    #unmarked-fig(
        figure(
            canvas({
                import cetz.draw: *

                rect((0, 0), (6, 1), name: "first", fill: diagram-colors.light-red)
                content("first.center", $[r - 1]$)
                rect((0, 0), (10, 1), name: "n")
                content("n.north", box(inset: (bottom: 0.5em))[$[n]$], anchor: "south")
                cetz.decorations.brace((0, -0.1), (6, -0.1), name: "brace1", flip: true)
                cetz.decorations.brace((6, -0.1), (10, -0.1), name: "brace2", flip: true)
                content("brace1.content", [Take all of this])
                content("brace2.content", [Take $1$ point from here])
            })
        )
    )
]
#example[
    Similarly, for $r$ even, if we want $abs(x sect y)$ even for all $x != y in A$, we can achieve $abs(A) = binom(floor(n \/ 2), r \/ 2)$ by the diagram below.
    #unmarked-fig[
        #figure(
            canvas({
                import cetz.draw: *

                for i in range(1, 5) {
                    circle((i, 0), ..point-style, fill: diagram-colors.blue, name: "point-" + str(i))
                    content("point-" + str(i), box(inset: (bottom: 0.5em))[$#i$], anchor: "south")
                }
                for i in range(5) {
                    circle((5 + i/4, 0), radius: 0.05, stroke: none, fill: black)
                }
                circle((7, 0), ..point-style, fill: diagram-colors.blue, name: "point-n1")
                content("point-n1", box(inset: (bottom: 0.5em))[$n - 1$], anchor: "south")
                circle((8, 0), ..point-style, fill: diagram-colors.blue, name: "point-n")
                content("point-n", box(inset: (bottom: 0.5em))[$n$], anchor: "south")
                cetz.decorations.brace((1, -0.5), (8, -0.5), flip: true, name: "brace")
                content("brace.content", [Take $r\/2$ pairs from here])
                let bracket = merge-path({
                    line((0.8, -0.1), (0.8, -0.3))
                    line((0.8, -0.3), (2.2, -0.3))
                    line((2.2, -0.3), (2.2, -0.1))
                })
                bracket
                translate(x: 2)
                bracket
                translate(x: 4)
                bracket
            })
        )
    ]
    If we want $abs(x sect y)$ odd for all $x != y in A$, can achieve $n - r + 1$ by the diagram below.
    #unmarked-fig(
        figure(
            canvas({
                import cetz.draw: *

                rect((0, 0), (6, 1), name: "first", fill: diagram-colors.light-red)
                content("first.center", $[r - 1]$)
                rect((0, 0), (10, 1), name: "n")
                content("n.north", box(inset: (bottom: 0.5em))[$[n]$], anchor: "south")
                cetz.decorations.brace((0, -0.1), (6, -0.1), name: "brace1", flip: true)
                cetz.decorations.brace((6, -0.1), (10, -0.1), name: "brace2", flip: true)
                content("brace1.content", [Take all of this])
                content("brace2.content", [Take $1$ point from here])
            })
        )
    )
]
It seems to be that banning $abs(x sect y) = r (mod 2)$ forces the family to be very small (polynomial in $n$; in fact, a linear polynomial). Remarkably, we cannot beat linear.
#proposition[
    Let $r$ be odd and $A subset.eq X^((r))$. If $abs(x sect y)$ is even for all $x != y in A$, then $abs(A) <= n$.
]
#proofhints[
    Identify each $x in powset(X)$ with a point $overline(x)$ in an appropriate vector space, and by considering dot products, show that ${overline(x): x in A}$ is linearly independent.
]
#proof[
    Idea: find $abs(A)$ linearly independent vectors in a vector space of dimension $n$, namely $Q_n$.

    View $powset(X)$ as $FF_2^n$, the $n$-dimensional vector space over $FF_2$, by identifying each $x in powset(X)$ with $overline(x)$, its characteristic sequence (where we count from the left, so ${1, 3, 4} <-> 1011000...0$). Then we have $overline(x) . overline(x) != 0$ for all $x in A$ (as $r$ is odd). Also, $overline(x) . overline(y) = 0$ for all $x != y in A$, as $abs(x sect y)$ is even. Hence ${overline(x): x in A}$ is linearly independent (if $sum_i lambda_i overline(x_i)$, dot with $overline(x_j)$ to get $lambda_j = 0$). So $abs(A) <= n$.
]
#corollary[
    Hence also, if $A subset.eq X^((r))$ with $r$ even with $abs(x sect y)$ odd for all $x != y in A$, then $abs(A) <= n + 1$.
]
#proofhints[
    Use the above proposition.
]
#proof[
    Just add $n + 1$ to each $x in A$ and apply above proposition.
]
This $mod 2$ behaviour generalises: namely, allowing $s$ values for $abs(x sect y) mod p$ implies that $abs(A)$ is bounded above by a polynomial of degree $s$.
#theorem("Frankl-Wilson")[
    Let $p$ be prime and $A subset.eq X^((r))$. Suppose that for all $x != y in A$, we have $abs(x sect y) equiv lambda_i thick mod p$ for some $i$, where $s <= r$ and $lambda_1, ..., lambda_s in ZZ$ with no $lambda_i equiv r thick mod p$. Then $abs(A) <= binom(n, s)$.
]<thm:frankl-wilson>
#proofhints[
    - For each $i <= j$, let $M(i, j)$ be the $binom(n, i) times binom(n, j)$ matrix with rows indexed by $X^((i))$, columns indexed by $X^((j))$, with $
        M(i, j)_(x y) = cases(
            1 quad & "if" x subset.eq y,
            0 & "otherwise"
        ), quad x in X^((i)), y in X^((j)).
    $
    - Let $V$ be the vector space over $RR$ spanned by the rows of $M(s, r)$.
    - By finding an expression for each of its entries, show that $M(i, s) M(s, r) = binom(r - i, s - i) M(i, r)$.
    - Let $M(i) = M(i, r)^T M(i, r)$. Explain why each row of each $M(i)$ is in $V$.
    - Let $M = sum_(i = 0)^s a_i M(i)$, where the $a_i$ are chosen so that $M_(x y) = (abs(x sect y) - lambda_1) med dots.c med (abs(x sect y) - lambda_s)$ (explain why each $a_i in ZZ$).
    - Consider the submatrix of $M$ spanned by the rows and columns corresponding to the elements of $A$.
]
#proof[
    Idea: try to find $abs(A)$ linearly independent points in a vector space of dimension $binom(n, s)$, by somehow "applying" the polynomial $(t - lambda_1) med dots.c med (t - lambda_s)$ to $abs(x sect y)$.

    For each $i <= j$, let $M(i, j)$ be the $binom(n, i) times binom(n, j)$ matrix with rows indexed by $X^((i))$, columns indexed by $X^((j))$, with $
        M(i, j)_(x y) = cases(
            1 quad & "if" x subset.eq y,
            0 & "otherwise"
        ), quad x in X^((i)), y in X^((j)).
    $ Let $V$ be the vector space over $RR$ spanned by the rows of $M(s, r)$, so $dim(V) <= binom(n, s)$. For $i <= s$, consider the matrix $M(i, s) M(s, r)$. Each row of this matrix belongs to $V$, as we have left-multiplied $M(s, r)$ by a matrix. For $x in X^((i))$, $y in X^((r))$, $
        (M(i, s) M(s, r))_(x y) = #[number of $s$-sets $z$ with $x subset.eq z$ and $z subset.eq y$] = cases(
            0 quad & "if" x subset.eq.not y,
            binom(r - i, s - i) & "if" x subset.eq y.
        )
    $ So $M(i, s) M(s, r) = binom(r - i, s - i) M(i, r)$. So all rows of $M(i, r)$ belong to $V$. Let $M(i) = M(i, r)^T M(i, r)$. Again, each row of this matrix is in $V$, since we have left-multiplied $M(i, r)$ by a matrix. For $x, y in X^((r))$, we have $
        M(i)_(x y) = #[number of $i$-sets $z$ with $z subset.eq x$ and $z subset.eq y$] = binom(abs(x sect y), i).
    $ Write the integer polynomial $(t - lambda_1) med dots.c med (t - lambda_s)$ as $sum_(i = 0)^s a_i binom(t, i)$ with all $a_i in ZZ$. This is possible since $t(t - 1) dots.c (t - i + 1) = i! binom(t, i)$. Let $M = sum_(i = 0)^s a_i M(i)$. Note each row of each $M(i)$ is in $V$. Then for all $x, y in X^((r))$, $
        M_(x y) = sum_(i = 0)^s a_i binom(abs(x sect y), i) = (abs(x sect y) - lambda_1) med dots.c med (abs(x sect y) - lambda_s).
    $ So the submatrix of $M$ spanned by the rows and columns corresponding to the elements of $A$ is $
        mat(
            equiv.not 0 mod p, , 0;
            , dots.down, ;
            0, , equiv.not 0 mod p;
        )
    $ Hence the rows of $M$ corresponding to $A$ are linearly independent over $FF_p$, so also over $ZZ$, so also over $QQ$, so also over $RR$. So $abs(A) <= dim(V) = binom(n, s)$.
]
#remark[
    - The bound in @thm:frankl-wilson is a _polynomial_ in $n$, even as $r$ varies!
    - The bound is essentially the best possible: we can achieve $abs(A) = binom(n, n - r + s) approx binom(n, s)$ for large $n$, as shown in the diagram below.
    #unmarked-fig(
        figure(
            canvas({
                import cetz.draw: *

                rect((0, 0), (12, 1), name: "n")
                rect((0, 0), (5, 1), name: "first", fill: diagram-colors.light-red)
                rect((5, 0), (12, 1), name: "last")
                content("first.center", $[r - s]$)
                content("n.south", box(inset: (top: 0.5em))[$[n]$], anchor: "north")
                content("last.center", [any $s$-set])
            })
        )
    )
    - The condition $lambda_i equiv.not r thick mod p$ for all $i$ is necessary: indeed, if $n = a + lambda p$, $0 <= a <= p - 1$, then can have $A subset.eq X^(a + k p)$ with $abs(A) = binom(lambda, k)$ and all $abs(x sect y) equiv a thick mod p$, but $binom(lambda, k)$ is not a polynomial in $n$ (as we can choose any $k$).
    #unmarked-fig[
        #figure(
            canvas({
                import cetz.draw: *

                for i in range(5) {
                    circle((7 + i/4, -0.2), radius: 0.05, stroke: none, fill: black)
                }
                cetz.decorations.brace((1, -0.5), (10, -0.5), flip: true, name: "brace")
                content("brace.content", [Take $k$ of these])
                merge-path({
                    line((-0.7, -0.1), (-0.7, -0.3))
                    line((-0.7, -0.3), (0.2, -0.3))
                    line((0.2, -0.3), (0.2, -0.1))
                }, name: "b1")
                content("b1.centroid", box(inset: (bottom: 0.5em))[$a$], anchor: "south")
                line((-0.25, -1), (-0.25, -0.45), mark: (end: "straight"), name: "take")
                content("take.start", box(inset: (top: 0.5em))[Take], anchor: "north")
                let bracket(name) = merge-path({
                    line((0.8, -0.1), (0.8, -0.3))
                    line((0.8, -0.3), (2.2, -0.3))
                    line((2.2, -0.3), (2.2, -0.1))
                }, name: name)
                bracket("b2")
                content("b2.centroid", box(inset: (bottom: 0.5em))[$p$], anchor: "south")
                translate(x: 2)
                bracket("b3")
                content("b3.centroid", box(inset: (bottom: 0.5em))[$p$], anchor: "south")
                translate(x: 2)
                bracket("b4")
                content("b4.centroid", box(inset: (bottom: 0.5em))[$p$], anchor: "south")
                translate(x: 4)
                bracket("b5")
                content("b5.centroid", box(inset: (bottom: 0.5em))[$p$], anchor: "south")
            })
        )
    ]
]
#remark[
    We do need $p$ prime. Grolmusz constructed, for each $n$, a value of $r equiv 0 mod 6$ and a family $A subset.eq [n]^((r))$ such that $forall x != y in A$, we have $abs(x sect y) equiv.not 0 mod 6$ and $abs(A) > n^(c log n \/ log log n)$, which is not a polynomial in $n$.
]
#corollary[
    Let $A subset.eq [n]^((r))$ with $abs(x sect y) equiv.not r mod p$ for all $x != y in A$, where $p < r$ is prime. Then $abs(A) <= binom(n, p - 1)$.
]<crl:frankl-wilson-special-case>
#proofhints[
    Trivial by @thm:frankl-wilson.
]
#proof[
    We are allowed $p - 1$ values of $abs(x sect y) mod p$, so done by @thm:frankl-wilson.
]
Two $(n \/ 2)$-sets in $[n]$ typically meet in $approx n \/ 4$ points, but having the exact equality $abs(x sect y) = n \/ 4$ is very unlikely. But remarkably:
#corollary[
    Let $p$ be prime, and $A subset.eq [4p]^((2p))$ with $abs(x sect y) != p$ for all $x != y in A$. Then $abs(A) <= 2 binom(4p, p - 1)$.
]<crl:there-are-few-2p-size-sets-with-non-half-intersection>
#proofhints[
    Remove all complements from $A$ and use @crl:frankl-wilson-special-case.
]
#proof[
    By halving $abs(A)$ if necessary, we may assume that no $x, x^c in A$ (for any $x in [4p]^((2p))$). Then for $x != y in A$, $abs(x sect y) != 0, p, 2p$, so $abs(x sect y) equiv.not 0 mod p$. So $abs(A) <= binom(4p, p - 1)$ by @crl:frankl-wilson-special-case.
]
#remark[
    $abs(x sect y) != p$ for all $x != y in A$ is a weak constraint, yet $2 binom(4p, p - 1)$ is a _tiny_ (exponentially small) fraction of $binom(4p, 2p)$. Indeed, $binom(n, n \/ 2) approx c dot 2^n \/ sqrt(n)$, for some constant $c$, whereas $binom(n, n \/ 4) <= 4 e^(-n \/ 32) 2^n$ by @prop:upper-bound-on-less-than-half-first-binomial-coefficients.
]

== Borsuk's conjecture

Let $S subset.eq RR^n$ be bounded. How few pieces can we break $S$ into, such that each piece has smaller diameter than that of $S$?
#fig-example[
    #figure(
        canvas({
            import cetz.draw: *

            scale(origin: (0, 0), x: 1.4, y: 1.4)
            blob-2d(num-points: 16, radius: 1)
            content((1.5, 0.2), $S subset.eq RR^2$)
            line((0, 0), (0, 2))
            line((0, 0), (-calc.sqrt(3), -1))
            line((0, 0), (calc.sqrt(3), -1))
            content((0, -0.5), $3$)
            content((0.4, 0.2), $2$)
            content((-0.4, 0.2), $1$)
        }),
        caption: [A partition of $S$ into three pieces]
    )
]
The example of a regular $n$-simplex in $RR^n$ ($n + 1$ points, all at distance $1$) shows that we may need $n + 1$ pieces.
#conjecture("Borsuk")[
    $n + 1$ pieces is always sufficient.
]<cnj:borsuk>
@cnj:borsuk is true when $n = 1$ (trivial), $n = 2$ (doable), $n = 3$ (hard), and also when $S$ is a smooth convex body in $RR^n$ (e.g. sphere), or a symmetric ($x in S => -x in S$) convex body in $RR^n$ (e.g. octohedron).

However, in general, @cnj:borsuk is massively false:
#theorem("Kahn, Kalai")[
    For all $n in NN$, there exists a bounded $S subset.eq RR^n$ such that to break $S$ into pieces of smaller diameter, we need at least $C^sqrt(n)$ pieces for some constant $C > 1$.
]
#remark[
    Our proof will show Borsuk is false for $n >= 2000$.
]
#proofhints[
    - Prove for all $n$ of the form, $binom(4p, 2)$ for $p$ prime.
    - For $x, y in [n]^((r))$, find an expression for $norm(x - y)^2$ in terms of $abs(x sect y)$.
    - Identify $[n]$ with the edge set of an appropriate graph, and for each $x in [4p]^((2p))$, let $G_x$ be the complete bipartite graph with vertex classes $x$ and $x^c$.
    - Show that the number of edges in $G_x sect G_y$ is $abs(G_x sect G_y) = abs(x sect y)^2 + (2p - abs(x sect y))^2$ and give the value of $abs(x sect y)$ which minimises this.
    - Let $S$ be an appropriate set of size $abs(S) = 1/2 binom(4p, 2p)$. Using @crl:there-are-few-2p-size-sets-with-non-half-intersection, show that any subset $S' subset.eq S$ of smaller diameter than $S$ has size at most $2 binom(4p, p - 1)$.
    - Use @prop:upper-bound-on-less-than-half-first-binomial-coefficients and the fact that $binom(n, n \/ 2) approx c dot 2^n \/ sqrt(n)$ to conclude the result. #qedhere
]
#proof[
    We will prove it for all $n$ of the form $binom(4p, 2)$ where $p$ is prime. Then we are done for all $n in NN$ (with a different constant $C$), e.g. because there exists prime $p$ with $n \/ 2 <= p <= n$. We'll find $S subset.eq Q_n subset.eq RR^n$. In fact, $S subset.eq [n]^((r))$ for some $r$. (These are genuine ideas). Since $S subset.eq [n]^((r))$, we have $forall x, y in S$, $
        norm(x - y)^2 & = "number of coordinates where" x, y "differ" \
        & = abs(x Delta y) = abs(x \\ y) + abs(y \\ x) = 2(r - abs(x sect y)).
    $
    #unmarked-fig[
        #figure(
            canvas({
                import cetz.draw: *

                rect((-4, -1), (4, 1), name: "n")
                circle((-1.5, 0), radius: (2, 0.6), name: "x")
                circle((1.5, 0), radius: (2, 0.6), name: "y")
                content("n.south", box(inset: (top: 0.5em))[$[n]$], anchor: "north")
                content("x.center", $x$, anchor: "east")
                content("y.center", $y$, anchor: "west")
            })
        )
    ]
    The diameter of $S$ is $max{norm(x - y): x, y in S}$, so we seek $S$ with $min{abs(x sect y): x, y in S} = k$, where every subset $S' subset.eq S$ with $min{abs(x sect y): x, y in S'} > k$ is very small (so need many pieces).

    Identify $[n]$ with the edge set of the complete graph $K_(4p)$ on $4p$ points. For each $x in [4p]^((2p))$, let $G_x$ be the complete bipartite graph with vertex classes $x, x^c$. Let $S = {G_x: x in [4p]^((2p))}$. So $S subset.eq [n]^((4p^2))$, and $abs(S) = 1/2 binom(4p, 2p)$ (since $G_x = G_(x^c)$). Now, the number of edges in $G_x sect G_y$ is $
        abs(G_x sect G_y) & = abs(x sect y) dot abs(x^c sect y^c) + abs(x^c sect y) dot abs(x sect y^c) \
        & = abs(x sect y)^2 + abs(x^c sect y)^2 \
        & = d^2 + (2p - d)^2, quad "where" d = abs(x sect y),
    $ which is minimised when $d = abs(x sect y) = p$.
    #unmarked-fig[
        #figure(
            canvas({
                import cetz.draw: *
                import cetz.decorations: *

                scale(x: 6, y: 6)
                rect((0, 0), (1, 1), name: "4p")
                content("4p.south", box(inset: (top: 0.5em))[$[4p]$], anchor: "north")
                set-style(stroke: diagram-colors.red)
                line((0.5, 0), (0.5, 1))
                flat-brace((0.01, 1.02), (0.49, 1.02), outer-curves: 0.2, amplitude: 0.05, name: "x")
                flat-brace((0.51, 1.02), (0.99, 1.02), outer-curves: 0.2, amplitude: 0.05, name: "xc")
                content("x.spike", box(inset: (bottom: 0.5em))[$x$], anchor: "south")
                content("xc.spike", box(inset: (bottom: 0.5em))[$x^c$], anchor: "south")
                set-style(stroke: diagram-colors.blue)
                line((0, 1/4), (1, 3/4))
                line((1/4, 1/8), (3/4, 3/8), mark: (start: "straight", end: "straight", width: 0.025cm, length: 0.2cm / 6), name: "y")
                line((1/4, 5/8), (3/4, 7/8), mark: (start: "straight", end: "straight", width: 0.025cm, length: 0.2cm / 6), name: "yc")
                content("y.centroid", box(inset: (left: 0.5em, top: 0.5em))[$y$], anchor: "west")
                content("yc.centroid", box(inset: (left: 0.5em, top: 0.5em))[$y^c$], anchor: "west")
            })
        )
    ]
    Now let $S' subset.eq S$ have smaller diameter than that of $S$: $S' = {G_x: x in A}$, where $A subset.neq [4p]^(2p)$. So we must have that $forall x != y in A$, $abs(x sect y) != p$ (as otherwise diameter of $S'$ is equal to diameter of $S$). Thus $abs(A) <= 2 binom(4p, p - 1)$ by @crl:there-are-few-2p-size-sets-with-non-half-intersection.

    So by @prop:upper-bound-on-less-than-half-first-binomial-coefficients, the number of pieces needed is at least #qed-multiline($
        (1/2 binom(4p, 2p))/(2 binom(4p, p - 1)) & >= (c dot 2^(4p) \/ sqrt(p))/(e^(-p \/ 8) 2^(4p)) quad & "for some" c \
        & >= (c')^p quad & "for some" c' \
        & >= (c'')^sqrt(n) quad & "for some" c''.
    $)
]