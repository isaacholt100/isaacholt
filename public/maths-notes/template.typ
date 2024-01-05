#let template(doc) = [
	#set text(
        font: "New Computer Modern",
		size: 12pt,
	)
	#set math.mat(delim: "[")
    #set math.vec(delim: "[")
	#set heading(numbering: "1.")
	#set page(
		numbering: "1"
	)
	#doc
]

#let hdots = $dot.op dot.op dot.op$