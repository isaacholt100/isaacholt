#import "@preview/lemmify:0.1.5": *

#let thm-style-proof(
    thm-type,
    name,
    number,
    body
) = block(width: 100%, breakable: true)[#{
    emph(thm-type) + "."
    if number != none {
        strong(number) + " "
    }

    if name != none {
        emph[(#name)] + " "
    }
    " " + body + h(1fr) + $square$
}]

#let thm-style-simple(
  thm-type,
  name,
  number,
  body
) = block(width: 100%, breakable: true, radius: 0.25em, /*fill: rgb("#e2e2ec"), inset: 0.25em,*/ spacing: 1em)[#{
  strong(thm-type)
  if number != none {
    // " " + strong(number)
  }

  if name != none {
    " " + [(#name)]
  }
    ". " + body
}]

#let (
    theorem, lemma, corollary, definition, remark, proposition, example, proof, rules: thm-rules
) = default-theorems("thm-group", lang: "en", proof-styling: thm-style-proof, thm-styling: thm-style-simple)

#let (algorithm, note, notation, rules) = new-theorems("thm-group", ("algorithm": [Algorithm], "note": [Note], "notation": [Notation]), thm-styling: thm-style-simple)

#let template(doc, hidden: ("proof", )) = {
	set text(
        font: "New Computer Modern",
		size: 12pt,
	)
    // set par(justify: true)
	set math.mat(delim: "[")
    set math.vec(delim: "[")
	set heading(numbering: "1.")
	set page(
		numbering: "1"
	)

    show: rules
    show: thm-rules

    let hidden = hidden.map(s => [#s])

    show thm-selector("thm-group"): it => {
        if hidden.contains(it.supplement) {
            none
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
    
    show link: underline

    outline()
    pagebreak()

	doc
}

#let hdots = $op(dot.op dot.op dot.op)$