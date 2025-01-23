#import "@preview/cetz:0.3.1" as cetz
#import "@preview/suiji:0.3.0": *

#let diagram-colors = (
    "red": rgb("#bf0101"),
    "light-red": rgb("f9e5e6"),
    "blue": rgb("#3333b2"),
    "green": rgb("#006001")
)
#let point-style = (radius: 0.1, stroke: none, fill: diagram-colors.red)
#let polygon(points, ..other) = cetz.draw.merge-path({
    for i in range(points.len() - 1) {
        cetz.draw.line(points.at(i), points.at(i + 1))
    }
}, close: true, ..other)
#let c-arc(centre, radius, start, stop, ..args) = {
    let start-pos = (centre.at(0) + radius * calc.cos(start), centre.at(1) + radius * calc.sin(start))
    return cetz.draw.arc(start-pos, radius: radius, start: start, stop: stop, ..args)
}
#let add-points(..points) = {
    let points = points.pos()
    let x = points.map(point => point.at(0)).sum()
    let y = points.map(point => point.at(1)).sum()
    if points.at(0).len() == 2 {
        return (x, y)
    }
    let z = points.map(point => point.at(2)).sum()
    return (x, y, z)
}
#let blob-2d(num-points: int, dev: 0.2, radius: 1, seed: 42) = {
    let n = num-points
    let rng = gen-rng(seed)
    let regular-points = range(n).map(i => (radius * calc.cos(2 * calc.pi * i/n), radius * calc.sin(2 * calc.pi * i/n)))
    let shape-points = regular-points.enumerate().map(a => add-points(a.at(1), uniform(gen-rng(a.at(0)), low: -dev / 2, high: dev / 2, size: 2).at(1)))
    cetz.draw.hobby(..shape-points, close: true, fill: diagram-colors.light-red, stroke: diagram-colors.red)
}