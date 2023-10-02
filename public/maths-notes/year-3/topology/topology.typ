#import "../../template.typ": template
#show: template

= Metric spaces

== Metrics

- *Metric space*: $(X, d)$, $X$ is set, $d: X times X -> [0, infinity)$ is *metric* satisfying:
    - $d(x, y) = 0 <==> x = y$
    - *Symmetry*: $d(x, y) = d(y, x)$
    - *Triangle inequality*: $d(x, y) <= d(x, z) + d(z, y)$
- Examples of metrics:
    - $p$-adic metric: $ d_p (x, y) = (sum_(i = 1)^n |x_i - y_i|^p)^(1/p) $
    - Extension of the $p$-adic metric: $ d_infinity (x, y) = max{|x_i - y_i|: i in [n]} $
    - Metric of $C([a, b])$: $ d(f, g) = sup{|f(x) - g(x)|: x in [a, b]} $
    - Discrete metric: $ d(x, y) = cases(0 & "if" x = y, 1 & "if" x != y) $
- *Open ball of radius $r$ around $x$*: $ B(x; r) = {y in X: d(x, y) < r} $
- *Closed ball of radius $r$ around $x$*: $ D(x; r) = {y in X: d(x, y) <= r} $

== Open and closed sets

- $U subset.eq X$ is *open* if $ forall x in U, exists epsilon > 0: B(x; epsilon) subset U $
- $A subset.eq X$ is *closed* if $X - A$ is open.
- Sets can be neither closed nor open, or both.