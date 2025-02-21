#import "@preview/polylux:0.3.1": *
#import "@preview/ctheorems:1.1.3": *

#let thmstyle = (
    titlefmt: strong,
    inset: 0em,
    separator: [#h(0.1em)#h(0.2em)],
    namefmt: x => [(#x)],
    base: "heading",
    // numbering: "1.1"
    base_level: 1,
)

#let theorem = thmplain("theorem", "Theorem", ..thmstyle)
#let lemma = thmplain("theorem", "Lemma", ..thmstyle)
#let corollary = thmplain("theorem", "Corollary", ..thmstyle)
#let definition = thmplain("theorem", "Definition", ..thmstyle)
#let remark = thmplain("theorem", "Remark", ..thmstyle)
#let proposition = thmplain("theorem", "Proposition", ..thmstyle)
#let example = thmplain("theorem", "Example", ..thmstyle)
#let fig-example = thmplain("theorem", "Diagram", ..thmstyle)
#let conjecture = thmplain("theorem", "Conjecture", ..thmstyle)
#let algorithm = thmplain("theorem", "Algorithm", ..thmstyle)
#let notation = thmplain("theorem", "Notation", ..thmstyle)
#let postulate = thmplain("theorem", "Postulate", ..thmstyle)
#let note = thmplain("theorem", "Note", ..thmstyle)
#let fact = thmplain("theorem", "Fact", ..thmstyle)
#let axiom = thmplain("theorem", "Axiom", ..thmstyle)
#let problem = thmplain("theorem", "Problem", ..thmstyle)
#let exercise = thmplain("theorem", "Exercise", ..thmstyle)
#let proof = thmproof("proof", "Proof", inset: 0em, separator: [#h(0.1em).#h(0.2em)])
#let proofhints = thmproof("proofhints", "Proof (Hints)", inset: 0em, separator: [#h(0.1em).#h(0.2em)])
#let proofsketch = thmproof("proofsketch", "Proof (Sketch)", inset: 0em, separator: [#h(0.1em).#h(0.2em)])
#let unmarked-fig(body) = figure(
    body,
    supplement: [Unmarked Figure],
    kind: "thmenv"
)

#let to-identifier(name) = {
    if name == "Proof (Hints)" {
        return "proofhints"
    }
    if name == "Proof (Sketch)" {
        return "proofsketch"
    }
    if name == "Unmarked Figure" {
        return "unmarked-fig"
    }
    return lower(name)
}

#let template(doc, hidden: ("proof", ), slides: false, name-abbrvs: (:)) = {
	set text(
        font: "New Computer Modern",
		size: if slides { 24pt } else { 12pt },
	)
    set par(justify: true)
    set page(paper: if slides {
        "presentation-16-9"
    } else {
        "a4"
    }, numbering: if slides {
        none
    } else {
        "1"
    })
	set math.mat(delim: "[")
    set math.vec(delim: "[")
	set heading(numbering: "1.")

    let hidden-supplements = hidden

    show: thmrules.with(qed-symbol: $square$)
    show figure.where(kind: "thmenv"): it => {
        if hidden-supplements.contains(to-identifier(it.supplement.text)) {
            none
        } else {
            if slides {
                polylux-slide[
                    #it
                ]
            } else {
                it
            }
        }
    }


    show heading: it => {
        if slides {
            polylux-slide[
                #set align(center + horizon)
                #it
            ]
        } else {
            it
        }
    }

    show math.equation.where(block: true): set block(breakable: true)
    // show math.equation.where(block: true): set align(center)

    show math.equation.where(block: true): e => [
        #block(width: 100%, inset: 0em, breakable: true, [
            #set align(center)
            #e
        ])
    ]
    
    // show link: set text(fill: rgb("f00000"))

    let styled-link = (color, it) => {
        highlight(stroke: 0.5pt + color, fill: none)[#it]
    }
    show link: it => {
        if type(it.dest) == str {
            return styled-link(rgb("66ffff"), it)
        }
        if (type(it.dest) == location or type(it.dest) == label) and (query(it.dest).first().at("kind", default: none) == math.equation or query(it.dest).first().at("func", default: none) == math.equation) {
            if it.body.text.contains(")") {
                return [(#[#link(it.dest, it.body.text.replace(")", "").replace("(", ""))])]
            }
        } else {
            if it.body.has("children") {
                return [#it.body.children.slice(0, -2).join("") #link(it.dest, it.body.children.at(-1))]
            }
        }
        styled-link(rgb("ff0000"), it)
    }

    show ref: it => {
        let ref-name = str(it.target)
        if it.element == none {
            return it
        }
        if it.element.func() == figure and it.element.caption != none {
            let full-name = str(it.element.caption.body.text)
            let name = if full-name in name-abbrvs {
                name-abbrvs.at(full-name)
            } else {
                full-name
            }
            link(it.target, name)
        } else {
            it
            // it.element.fields()
            // counter(it.target)
            // let num = context { // apply the heading's numbering style
            //     let count = it.element.counter.at(it.target)
            //     numbering(it.element.numbering, ..(2, 3))
            // }
            // [#it.element.supplement #it.element.numbering #link(it.target, num)]
            // counter(it.target).get()
            // it.fields()
            // [#it.element.supplement #link(it.target, it.element.numbering)]
            // it
        }
    }
    // show ref: it => box[
    //     #it
    // ]
    // show ref: set text(fill: blue)
    // show ref: underline

    set figure(numbering: none)

    if not slides {
        outline()
        pagebreak()
    }

	doc
}

#let cdots = $dot dot dot$
#let powset = math.bb("P")
#let dom = math.op("dom")
#let indicator(S) = $bb(1)_#S$
#let gen(..gens) = $angle.l #gens.pos().join(",") angle.r$
#let supp = math.op("supp")
#let vd(v) = math.bold(v)
#let span = math.op("span")

#let qed-multiline(eq) = grid(
    columns: (1fr, auto, 1fr),
    [], eq, align(right + bottom)[#thm-qed-show]
)