#let template(doc) = [
	#set text(
        font: "New Computer Modern",
		size: 12pt,
	)
	#set math.mat(delim: "[")
	#set heading(numbering: "1.")
	#set page(
		numbering: "1"
	)
	#doc
]