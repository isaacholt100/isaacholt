#import "@preview/polylux:0.3.1": *
#import "@preview/ctheorems:1.1.3": *

#let thmstyle = (
    titlefmt: strong,
    inset: 0em,
    separator: [#h(0.1em)#h(0.2em)],
    namefmt: x => [(#x)],
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
#let note = thmplain("theorem", "Note", ..thmstyle)
#let fact = thmplain("theorem", "Fact", ..thmstyle)
#let axiom = thmplain("theorem", "Axiom", ..thmstyle)
#let problem = thmplain("theorem", "Problem", ..thmstyle)
#let exercise = thmplain("theorem", "Exercise", ..thmstyle)
#let proof = thmproof("proof", "Proof", inset: 0em, separator: [#h(0.1em).#h(0.2em)])
#let proofhints = thmproof("proofhints", "Proof (Hints)", inset: 0em, separator: [#h(0.1em).#h(0.2em)])
#let unmarked-fig(body) = figure(
    body,
    supplement: [Unmarked Figure],
    kind: "thmenv"
)

#let to-identifier(name) = {
    if name == "Proof (Hints)" {
        return "proofhints"
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

    show math.equation.where(block: true): e => [
        #box(width: 100%, inset: 0em, [
            #set align(center)
            #e
        ])
    ]
    
    show link: set text(fill: rgb("ff0000"))

    show ref: it => {
        let ref-name = str(it.target)
        if it.element != none and it.element.func() == figure and it.element.caption != none {
            let full-name = str(it.element.caption.body.text)
            let name = if full-name in name-abbrvs {
                name-abbrvs.at(full-name)
            } else {
                full-name
            }
            link(it.target, name)
        } else {
            it
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