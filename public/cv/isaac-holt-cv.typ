#set text(font: "New Computer Modern")

#show link: underline
#show link: set text(fill: blue)

#set page(
  margin: (x: 0.9cm, y: 1cm),
)

#set text(
    size: 10pt,
)

#set par(justify: true)

#let hr() = {v(-8pt); line(length: 100%); v(-2pt)}

#let date(from, to) = text(rgb(128, 128, 128), [#h(1fr) #from -- #to])

#show heading: it => if it.level == 2 [
    #it.body
    #hr()
] else [
    #it
]


= Isaac Holt

#link("tel:+447393098225")[+44 7393 098225] |
#link("mailto:isaac_holt@icloud.com")[isaac_holt\@icloud.com] |
#link("https://www.linkedin.com/in/isaacholt100/")[linkedin.com/in/isaacholt100] |
#link("https://github.com/isaacholt100")[GitHub] |
#link("https://isaacholt.vercel.app")[Personal Website]

== Summary

Highly capable mathematician, with a final year average grade of 97% at undergraduate (the highest in my year), who excels at tackling difficult and technical problems. Strong skills in a variety of programming languages and owner of a popular Rust library with over 500,000 downloads. Experience in mathematical research, soon-to-be co-author of a paper on tropical geometry. Focussed and driven, with a passion for setting challenging goals and achieving them.

== Education

*Durham University*, BSc Mathematics #date("09/2021", "06/2024") \
- Classification: First Class Honours.
- Grade: 95% (joint-highest in my cohort).
- Awards: The Mathematical Sciences Best 3H Student Prize

*University of Cambridge*, MASt in Mathematics #date("10/2024", "06/2024") \

*Colchester Royal Grammar School* #date("09/2019", "06/2021") \
- A Levels: Mathematics (A\*), Further Mathematics (A\*), Physics (A\*), Latin (A\*).
- Awards: Year 13 Prize for Further Mathematics.

== Research Experience

*Research Project in Tropical Geometry* #date("06/2023", "07/2023") \
Department of Mathematical Sciences, Durham University \
- Area of research was how the tropical modification of certain polynomial systems can be used to determine the generic root count of those systems.
- The results of our work are expected to be published in a paper by the end of this year.
- Invited by supervisor to attend a #link("https://www.oscar-system.org/meetings/2023-09/")[working group] for the OSCAR computer algebra system in Germany, to write code related to the project.

== Work Experience

*Web and Communications Internship* #date("07/2023", "08/2023") \
Grey College, Durham University \
- Created a #link("https://www.greyscr.co.uk")[new website] for Grey College Senior Common Room, using React, Next.js, Bootstrap, and KV storage.
- Built an admin dashboard with an email client for sending markdown emails and templated emails.
- Developed a password-less email authentication system.

*Student Digital Leader* #h(1fr) #date("09/2022", "06/2023") \
Durham University \
- Part of a pool of students who worked on various technical projects for the university.
- For the first few weeks, I worked in online support with the university's digital services for new students.
- I then worked as a UAT (User Acceptance Testing) Analyst within this role, using Azure DevOps and Jira to pass/fail test cases and report bugs for a new event-booking website that the university is launching.

*Software Tester* #h(1fr) #date("01/2021", "03/2021") \
Blutick \
- Tested Blutick's marking software for online GCSE maths exams, reported bugs I found when using the website.
- Given the responsibility of editing the online questions and mark schemes myself using Latex.
- Developed TypeScript program to generate all solutions for questions where many combinations of answers were allowed.

== Projects

*bnum* #h(1fr) #date("05/2021", "Present") \
Mathematical #link("https://crates.io/crates/bnum")[Rust library] with over 500,000 downloads that uniquely provides fixed size signed and unsigned integer types, designed to extend functionality of Rust's primitive integer types to arbitrary bit sizes. Used by a blockchain-related package.

== Extracurriculars

Piano (ABRSM Grade 8 Distinction) |
Durham University Chess Society |
Durham University Spaceflight Society |
Durham University Mathematical Problem Solving Society |
Grey College Table Tennis A Team |
Grey College Badminton B Team |
Durham University Chess Society |
Durham University Quant Fund |
Co-leader of Physics and Maths Society at Sixth Form

== Skills

Mathematics | Rust | JavaScript | Python | Latex | Programming | Research

// #set text(font: "New Computer Modern")

#pagebreak()

#show link: underline
#show link: set text(fill: blue)

#set page(
  margin: (x: 0.9cm, y: 1cm),
)

#set text(
    size: 11pt,
)

#set par(justify: true)

#let hr() = {v(-8pt); line(length: 100%); v(-2pt)}

#let date(from, to) = text(rgb(128, 128, 128), [#h(1fr) #from -- #to])

#show heading: it => if it.level == 2 [
    #it.body
    #hr()
] else [
    #it
]

= Isaac Holt

#link("tel:+447393098225")[+447393098225] |
#link("mailto:isaac_holt@icloud.com")[isaac_holt\@icloud.com] |
#link("https://www.linkedin.com/in/isaacholt100/")[linkedin.com/in/isaacholt100]

== Summary

Highly capable third year undergraduate mathematician with current average mark of 91%. Seeking admission into the MASt in Mathematics, with wide-ranging interests in areas such as number theory, combinatorics and quantum computation. Driven and committed to expanding and deepening my mathematical knowledge and discovering new results, as the co-author of a paper on tropical geometry which has been submitted as a chapter for a forthcoming book.

== Education

*Durham University*, MMath Mathematics #date("09/2021", "Present") \
- Third year modules: _Analysis_, _Cryptography and Codes_, _Galois Theory_, _Number Theory_, _Quantum Computing_, _Topology_.
- Grade: 1st (expected). First year average: 90%, second year average: 92%.
- Notable marks (1st year): _Discrete Mathematics_: 90% | _Analysis_: 91% | _Linear Algebra_: 96%.
- Notable marks (2nd year): _Algebra_: 94% | _Complex Analysis_: 95% | _Elementary Number Theory_: 98%.

*Colchester Royal Grammar School* #date("09/2019", "06/2021") \
- A-levels: Mathematics (A\*, 99%), Further Mathematics (A\*, 97%), Physics (A\*, 91%), Latin (A\*, 90%).
- Awards: Year 13 Prize for Further Mathematics - I was selected for this prize out of the 50 or so students in my cohort taking Further Mathematics A-level.

== Research Experience

*Summer Research Project* - Department of Mathematical Sciences, Durham University #date("06/2023", "07/2023") \
- Area of research was in tropical geometry; specifically, how the modification and tropicalisation of horizontally parametrised polynomial systems can be used to determine the generic root count of those systems.
- First four weeks were mostly spent learning about the area and reading relevant books and materials.
- Last four weeks were devoted to formulating and proving a new result, where I produced a generalised proof of a theorem from a recent paper on the number of equilibria of coupled nonlinear oscillators.
- Paper has been published on #link("https://arxiv.org/abs/2311.18018")[arXiv] and submitted as a chapter for the upcoming book on the OSCAR computer algebra system.
- Invited by my supervisor to attend a #link("https://www.oscar-system.org/meetings/2023-09/")[working group] for OSCAR at Paderborn University, Germany, to write an illustrative #link("https://github.com/isaacholt100/generic_root_count")[program] in Julia for the paper.

*(Upcoming) Mitacs Globalink Research Internship* - University of British Columbia #date("06/2024", "08/2024") // TODO: make sure you're happy with this wording

== Work Experience

*Web and Communications Internship* - Grey College, Durham University #date("07/2023", "08/2023") \
- Developed the #link("https://www.greyscr.co.uk")[new website] for my college's Senior Common Room, using my programming abilities.

*Student Digital Leader* - Durham University #date("09/2022", "06/2023") \
- Worked as a User Acceptance Testing Analyst, using Azure DevOps to pass/fail test cases and report bugs for a new event-booking website that the university is launching.

*Software Tester* - Blutick #date("01/2021", "03/2021") \
- Used my capacity for mathematical rigour to test the marking software for online GCSE maths exams.
- Having excelled in this task, was given the responsibility of editing the questions using Latex.
- Developed computer program to generate all solutions for questions where many combinations of answers were allowed.

== Publications

#place(hide(bibliography("./publications.bib")))

#cite(<holt2023generic>, form: "full", style: "apa") Available at #link("https://arxiv.org/abs/2311.18018")[arXiv:2311.18018].

== Projects

*bnum* #date("05/2021", "Present") \
- Mathematical #link("https://crates.io/crates/bnum")[Rust library] for operating on arbitrarily-sized integers, with over 250,000 downloads.
- Is a dependency for two other libraries, including a popular smart contract #link("https://crates.io/crates/cosmwasm-std")[package].
- To my knowledge, it is the only library to extend functionality of Rust's primitive integer types to arbitrary, fixed size signed and unsigned integers.
- Development involved researching arithmetical algorithms, e.g. Knuth's integer division algorithm and exponentiation by squaring.

== Relevant skills

- Mathematical research experience, including helping produce a paper in 2023 on tropical geometry.
- Experience reading mathematical publications (currently reading _Mathematical Logic_ by Cori and Lascar).
- Experience in the typsetting languages Latex and Typst - typeset notes for my undergraduate modules are available on my #link("https://isaacholt.vercel.app/maths")[website].
- Programming experience in a variety of languages: Rust, Python, Julia, R, JavaScript, TypeScript.

== Extracurriculars

- Co-leader of Physics and Maths Society at Sixth Form
- Durham University Mathematical Problem Solving Society
- Simon Marais Mathematics Competition (2022, 2023)
- Imperial-Cambridge Mathematics Competition (2022, 2023)
- British Mathematical Olympiad (2020)
- Classical Piano (ABRSM Grade 8 Distinction, working towards the ARSM diploma)
- Durham University Chess Society
- Durham University Spaceflight Society
- Grey College Badminton B Team
- Grey College Table Tennis A Team
- Durham University Table Tennis Development Squad