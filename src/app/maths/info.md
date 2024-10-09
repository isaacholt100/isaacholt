These are summary notes I wrote for some of my university mathematics modules. The notes were made with [Typst](https://typst.app/docs/). The template used is available [here](https://github.com/isaacholt100/isaacholt/blob/main/public/maths-notes/template.typ). If you notice a mistake in any of these notes, feel free to create an issue or submit a pull request on this website's [GitHub repository](https://github.com/isaacholt100/isaacholt).

With the exception of the Durham: Year 2 notes, you can choose which kinds of items (theorems, lemmas, definitions, proofs, etc.) are shown in the compiled document, by adding the relevant items to the `hidden` argument of the template, e.g. to hide proofs and remarks:
```rust
#show: doc => template(doc, hidden: ("proof", "remark"))
```
This can be useful e.g. if you simply want to memorise just the definitions or just the results.