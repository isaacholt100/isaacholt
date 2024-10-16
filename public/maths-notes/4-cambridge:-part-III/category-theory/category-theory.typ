#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge
#import "../../template.typ": *
#show: doc => template(doc, hidden: (), slides: false)

#let ob = math.op("ob")
#let mor = math.op("mor")
#let cod = math.op("cod")
#let asdf = math.bold("asdf")
#let Set = math.bold("Set")
#let Gp = math.bold("Gp")
#let AbGp = math.bold("AbGp")
#let Rng = math.bold("Rng")
#let Vect(K) = $bold("Vect")_#K$
#let Top = math.bold("Top")
#let Met = math.bold("Met")
#let Mfd = math.bold("Mfd")
#let TopGp = math.bold("TopGp")
#let Htpy = math.bold("Htpy")
#let Rel = math.bold("Rel")
#let Part = math.bold("Part")
#let Mat(K) = $bold("Mat")_#K$
#let Cat = math.bold("Cat")


= Definitions and examples

== Categories

#definition[
    A *category* $cal(C)$ consists of:
    + a collection $ob(cal(C))$ of *objects* $A, B, C, ...$,
    + a collection $mor(cal(C))$ of *morphisms* $f, g, h, ...$,
    + two operations $dom$ and $cod$ from $mor(cal(C))$ to $ob(cal(C))$. We write $f: A -> B$ to mean $f$ is a morphism, with domain $A$ and codomain $B$.
    + an operation from $ob(cal(C))$ to $mor(cal(C))$ sending $A$ to $1_A: A -> A$.
    + a partial binary *composition* operation $(f, g) |-> f g$ on $mor(C)$, such that $f g$ is defined iff $dom(f) = cod(g)$, and in this case $dom(f g) = dom(g)$ and $cod(f g) = cod(f)$.
    and satisfies the following:
    + $f 1_A = f$ and $1_A g = g$ when the composites are defined.
    + $f(g h) = (f g) h$ whenever $f g$ and $g h$ are defined.
]<def:category>
#remark[
    - $ob(cal(C))$ and $mor(cal(C))$ are not necessarily sets. If they are, then $cal(C)$ is called a *small* category, otherwise it is called *large*.
    - An equivalent definition exists without using objects (since objects $A$ biject with identity morphisms $1_A$).
    - $f g$ means first apply $g$, then $f$.
]
#example[
    $Set$ = the category of all sets and functions between them. (Formally, a morphism of $Set$ is a pair $(f, B)$ where $f$ is a set-theoretic function and $B$ is its codomain).
]<exa:category-of-sets>
#example[
    Algebraic categories:
    - $Gp$ is the category of groups and group homomorphisms.
    - $Rng$ is the category of rings and ring homomorphisms.
    - $Vect(K)$ is the category of vector spaces over a field $K$ with $K$-linear maps.
]<exa:algebraic-categories>
#example[
    Topological categories:
    - $Top$ is the category of topological spaces and continuous maps.
    - $Met$ is the category of metric spaces and non-expansive maps (i.e. $d(f(x), f(y)) <= d(x, y)$).
    - $Mfd$ is the category of smooth manifolds and smooth ($C^oo$) maps.
    - $TopGp$ is the category of topological groups and continuous homomorphisms.
    - $Htpy$ is the category with same objects as #Top but morphisms are homotopy classes of continuous maps.
]<exa:topological-categories>
#definition[
    Given a category $cal(C)$ and an equivalence relation $tilde$ on $mor(cal(C))$ such that $f tilde g => (dom(f) = dom(g) and cod(f) = cod(g))$, and $f tilde g => f h tilde g h$ when the composites $f h$ and $g h$ are defined, we can form a *quotient* category $cal(C)\/tilde$, which has the same objects as $cal(C)$, but morphisms are equivalence classes of morphisms in $cal(C)$ under $tilde$. $tilde$ is called a *congruence*.
]<def:category.quotient>
#example[
    Relation categories:
    - $Rel$ is the category with the same objects as *Set* but with morphisms that are relations $R subset.eq A times B$, with composition defined by $R compose S = {(a, c) in A times C: exists b: (a, b) in S and (b, c) in R}$. If $R$ and $S$ are functions, then $compose$ is the function composition operation.
    - $Part$ is the category with sets as objects and partial functions as morphisms. $Part$ is a subcategory of $Rel$, and $Set$ is a subcategory of $Part$.
]<exa:relation-categories>
#definition[
    For every category $cal(C)$, the *opposite category* $cal(C)^"op"$ has the same objects and morphisms as $cal(C)$, but $dom$ and $cod$ are interchanged and composition is reversed. This yields a *duality principle*: if $P$ is a true statement about categories, then so is the dual statement $P^*$ (which is obtained by reversing arrows in $P$).
]<def:category.opposite>
#definition[
    A *monoid* (a group but inverses not guaranteed) is a small category with one object $*$. In particular, a group is a $1$-object where all morphisms are isomorphisms.
]<def:monoid>
#definition[
    A *groupoid* is a category where every morphism is an isomorphism.
]<def:groupoid>
#example[
    The *fundamental groupoid* of a space $X$, $pi_1 (X)$, is the category where objects are the points of $X$, and morphisms $x -> y$ are homotopy classes of paths from $x$ to $y$. (Note this depends only on $X$, whereas the fundamental group depends on $X$ and a point $x in X$).
]<exa:fundamental-groupoid>
#definition[
    A category is *discrete* if the only morphisms are identities.
]<def:category.discrete>
#definition[
    A category $cal(C)$ is a *preorder* if for every pair of objects $(A, B)$, there exists at most $1$ morphism $A -> B$, then $mor(C)$ becomes a reflexive and transitive relation on $ob(C)$ (so existence of morphism $A -> B$ corresponds to $A lt.eq.curly B$).

    In particular, a poset is a small preorder where the only isomorphisms are identity morphisms.
]<def:category.preorder>
#example[
    For a field $K$, the category $Mat(K)$ has natural numbers as objects, morphisms $n -> m$ are $m times n$ matrices with entries from $K$, and composition is matrix multiplication.
]<exa:matrix-category>

== Functors

#definition[
    Let $cal(C)$ and $cal(D)$ be categories. A *functor* $F: cal(C) -> cal(D)$ consists of mappings $F: ob(cal(C)) -> ob(cal(D))$ and $F: mor(cal(C)) -> mor(cal(D))$ such that $F(dom(f)) = dom(F f)$, $F(cod(f)) = cod(F f)$, $F(1_A) = 1_(F A)$ and $F(f g) = (F f) (F g)$ whenever $f g$ is defined.

    Write $Cat$ for the category with objects as small categories and morphisms as functors between them.
]<def:functor>
#example[
    We have *forgetful* functors $Gp -> Set$, $Rng -> Set$, $Top -> Set$, $Rng -> AbGp$, $Met -> Top$, $TopGp -> Top$, $TopGp -> Gp$. They "forget" the structure of the objects, and/or "forget" the conditions on the morphisms.
]<exa:functor.forgetful>
#example[
    The construction of free groups is a functor $F: Set -> Gp$: given a set $A$, $F A$ is the group freely generated by $A$, such that every mapping $A -> G$, where $G$ is a group, extends uniquely to a homomorphism $F A -> G$.

    Given $f: A -> B$, define $F f: F A -> F B$ to be the unique homomorphism extending $A limits(-->)^f B arrow.hook F B$. If we also have $g: B -> C$, then $F (g f)$ and $(F g)(F f)$ are both homomorphisms extending $A limits(-->)^f B limits(-->)^g C arrow.hook F C$, so are equal by uniqueness.
]<exa:free-group-construction-functor>
#example[
    Given a set $A$, $P A$ is the set of all subsets of $A$. Given $f: A -> B$, define $P f: P A -> P B$ by $P f(A') = {f(a): a in A'} subset.eq B$. So $P$ is a functor $Set -> Set$.
]<exa:powerset-functor>
#example[
    We also have a functor $P^*: Set^"op" -> Set$ (or $Set -> Set^"op"$), where $P^* A = P A$ and for $f: A -> B$, $P^*f: P B -> P A$ is given by $P^* f(B') = {a in A: f(a) in B'}$. So $P^*$ is the same construction as the power-set functor, except each subset of $B$ is mapped by $P^* f$ to its inverse image under $f$ rather than its image under $f$.

]
#definition[
    A *contravariant* functor is a functor $F: cal(C) -> cal(D)^"op"$, i.e. $F$ reverses the direction of arrows. Functors which do not reverse arrow directions are called *covariant*.
]<def:functor.contravariant-and-covariant>
#example[
    Given a vector space $V$ over $K$, write $V^*$ for the space of linear maps $V -> K$. Given $f: V -> W$, write $f^*: W^* -> V^*$ for the map $theta |-> theta f$. This defines a functor $(-)^*: Vect(K)^"op" -> Vect(K)$.
]
#example[
    The mappings $cal(C) |-> cal(C)^"op"$, $F |-> F$ define a covariant functor $Cat -> Cat$.
]
#example[
    A functor between monoids is a monoid homomorphism, a functor between groups is a group homomorphism, and a functor between posets is a monatone map.
]
#example[
    Given a group $G$, a functor $G -> Set$ is given by a set $A$ equipped with a $G$-action $(g, a) |-> g dot a$, i.e. a permutation representation of $G$.

    Similarly, a functor $G -> Vect(K)$ is a $K$-linear representation of $G$.
]
#example[
    The fundamental group construction is a functor $pi_1: Top^* -> Gp$, where $Top^*$ is the category of topological spaces with basepoints and continuous maps preserving basepoints.
]

== Natural transformations

#definition[
    Let $cal(C)$ and $cal(D)$ be categories and $F, G: cal(C) -> cal(D)$ be functors. A *natural transformation* $alpha: F -> G$ is a mapping $ob(cal(C)) -> mor(cal(D))$ which assigns to each $A in ob(cal(C))$ a morphism $alpha_A: F A -> G A$ in $cal(D)$, such that for any $f: A -> B$ in $mor(cal(C))$, the following *naturality square* commutes:
    #figure(diagram(cell-size: 10mm, $
        F A edge(F f, ->) edge("d", alpha_A, ->) & F B \
        G A edge(G f, ->) & edge("u", alpha_B, <-) G B
    $))

    If $alpha: F -> G$, $beta: G -> H$ are natural transformation, define $beta alpha: F -> H$ by $(beta alpha)_A = beta_A alpha_A$. Write $[cal(C), cal(D)]$ for the category with objects as functors $cal(C) -> cal(D)$ and morphisms as natural transformations between the functors.
]<def:natural-transformation>
#example[
    Given a vector space $V$, we have a linear map $alpha_V: V -> V^(**)$ which sends $v in V$ to the linear form $theta |-> theta(v)$ on $V^*$. These maps define a natural transformation $1_(Vect(K)) -> (-)^(**)$.
]
#example[
    Therre is a natural transformation $alpha: 1_Set -> U F$ where $F$ is the free group functor and $U$ is the forgetful functor $Gp -> Set$ whose value at $A$ is the inclusion $A arrow.hook U F A$. The naturality square is
    #figure(diagram(cell-size: 10mm, $
        A edge(f, ->) edge("d", alpha_A, ->) & B \
        U F A edge(U F f, ->) & edge("u", alpha_B, <-) U F B
    $))
]
#example[
    For any set $A$, we have a mapping $alpha_A: A -> P A$ given by $alpha_A (a) = {a}$. This is a natural transformation $1_Set -> P$ since $P f({a}) = {f(a)}$ for any $a in A$.
]
#example[
    Given order-preserving maps $f, g: P -> Q$ between posets, there exists a unique natural transformation $f -> g$ iff $f(p) <= g(p)$ for all $p in P$.
]
#example[
    Given two group homomorphisms $u, v: G -> H$, a natural transformation $u -> v$ is given by $h in H$ such that $h u(g) = v(g) h$ for all $g in G$, or equivalently, $u(g) = h^(-1) v(g) h$ for all $g in G$, i.e. $u$ and $v$ are *conjugate* homomorphisms.

    In particular, the group of natural transformations $u -> u$ is the *centraliser* of the image of $u$.
]
#example[
    If $A$ and $B$ are $G$-sets, considered as functors $G -> Set$, a natural transformation $f: A -> B$ is a *$G$-equivariant* map, i.e. $f: A -> B$ such that $g dot f(a) = f(g dot a)$ for all $a in A$, $g in G$.
]
#example[
    The *Hurewicz homomorphism* links the homotopy and homology gruops of a space $X$. Elements of $pi_n (X, x)$ are homotopy classes of basepoint-preserving maps $f: S^n -> X$. If we think of $S^n$ as $partial Delta^(n + 1)$, $f$ defines a singular $n$-cycle on $X$ and homotopic maps differ by an $n$-boundary, so we get a well-defined map $h_n: pi_n (X x) -> H_n (x)$. $h_n$ is a homomorphism and a natural transformation $pi_n -> H_n U$, where $U$ is the forgetful functor $Top^* -> Top$.
]

== Equivalence of categories

#example[
    $Rel$ is isomorphic to $Rel^"op"$ in the category $Cat$ via the functor $F: Rel -> Rel^"op"$, $F A = A$, $F R = R^o = {(b, a): (a, b) in R}$.
]
#lemma[
    Let $alpha: F -> G$ be a natural transformation between functors $F, G: cal(C) -> cal(D)$. Then $alpha$ is an isomorphism in the functor category $[cal(C), cal(D)]$ iff $alpha_A$ is an isomorphism in $cal(D)$ for each $A$.
]
#proof[
    - $=>$ is trivial as composition in $[cal(C), cal(D)]$ is pointwise.
    - $<=$: suppose each $alpha_A$ has an inverse $beta_A$. Given $f: A -> B$ in $cal(C)$, in the diagram
    #figure(diagram(cell-size: 10mm, $
        F A edge(f, ->) edge("d", alpha_A, ->) & F B \
        G A edge(G f, ->) & edge("u", alpha_B, <-) G B
    $)) TODO finish
    - We have $(F f) beta_A = beta_B alpha_B (F f) beta_A = beta_B (G f) alpha_A beta_A = beta_B (G f)$ by naturality of $alpha$. So $beta$ is natural and an inverse for $alpha$.
]
#definition[
    Let $cal(C)$ and $cal(D)$ be categories. An *equivalence* between $cal(C)$ and $cal(D)$ consists of functors $F: cal(C) -> cal(D)$ and $G: cal(D) -> cal(C)$, together with natural isomorphisms $alpha: 1_(cal(C)) -> G F$ and $beta: F G -> 1_(cal(D))$.

    Write $cal(C) tilde.eq cal(D)$ if there is an equivalence between $cal(C)$ and $cal(D)$.
]<def:category.equivalent>
#definition[
    $P$ is a *categorical property* if $cal(C)$ satisfies $P$ and $cal(C) tilde.eq cal(D)$ implies that $cal(D)$ satisfies $P$.
]<def:categorical-property>
#example[
    The category $Part$ of sets and partial functions is equivalent to $Set^*$: define $F: Set^* -> Part$ by $F(A, a) = A - {a}$, and for $f: (A, a) -> (B, b)$, $(F f)(x) = f(x)$ if $f(x) != b$ and undefined otherwise. Define $G: Part -> Set^*$ by $G(A) = (A union {a}, A)$, and for $f: A arrow.dashed B$, $G f(x) = f(x)$ if $x in A$ and $f(x)$ is defined, and $B$ otherwise.

    Note $F G = 1_Part$; $G F != 1_(Set^*)$, but there is an isomorphism $1_(Set^*) -> G F$. Note also that $Part tilde.equiv.not Set^*$.
]
#example[
    We have an equivalence $bold("fdVect")_K tilde.eq bold("fdVect")_K^op$: both functors are $(-)^*$, and both isomorphisms are $alpha: 1_(bold("fdVect")_K) -> (-)^(**)$.
]
#example[
    $bold("fdVect")_K tilde.eq Mat_K$: define $F: Mat_K -> bold("fdVect")_K$, $F(n) = k^n$, $F(A: n -> p)$ is the linear map $k^n -> k^p$ represented by $A$ (w.r.t. standard bases). To define $G$, choose a basis for each $V$, and define $G(v) = dim(V)$, $G(f: V -> W)$ is the matrix representing $f$ w.r.t. the chosen basis.

    $G F = 1_(Mat_K)$; the choice of bases yields isomorphisms $k^(dim(V)) -> V$ for each $V$.
]
#definition[
    Let $F: cal(C) -> cal(D)$ be a functor. $F$ is *faithful* if, given $f$ and $g$ in $mor(cal(C))$, if $(F f = F g)$, $dom(f) = dom(g)$ and $cod(f) = cod(g)$, then $f = g$.
]<def:functor.faithful>
#definition[
    A functor $F: cal(C) -> cal(D)$ is *full* if for every $g: F A -> F B$ in $cal(D)$, there exists $f: A -> B$ in $cal(C)$ with $F f = g$.
]<def:functor.full>
#definition[
    A functor $F: cal(C) -> cal(D)$ is *essentially surjective* if, for any $B in ob(D)$, there exists an $A in ob(cal(C))$ with $F A tilde.equiv B$.
]<def:functor.essentially-surjective>
#remark[
    If $F$ is full and faithful, then it is essentially surjective: given $g: F A -> F B$ in $cal(D)$, the unique $f: A -> B$ with $F f = g$ is an isomorphism.
]
#definition[
    A subcategory $cal(D) subset.eq cal(C)$ is a *full* subcategory if the inclusion functor $cal(D) -> cal(C)$ is a full functor.
]<def:subcategory.full>
#lemma[
    Let $F: cal(C) -> cal(D)$. Then $F$ is part of an equivalence $cal(C) tilde.eq cal(D)$ iff $F$ is full, faithful and essentially surjective.
]