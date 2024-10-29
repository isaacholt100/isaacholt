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

#let dates(from, to) = text(rgb(128, 128, 128), [#h(1fr) #from -- #to])

#show heading: it => if it.level == 2 [
    #it.body
    #hr()
] else [
    #it
]


// = Isaac Holt

// #link("tel:+447393098225")[+44 7393 098225] |
// #link("mailto:isaac_holt@icloud.com")[isaac_holt\@icloud.com] |
// #link("https://www.linkedin.com/in/isaacholt100/")[linkedin.com/in/isaacholt100] |
// #link("https://github.com/isaacholt100")[GitHub] |
// #link("https://isaacholt.vercel.app")[Personal Website]

// == Summary

// Highly capable mathematician, with a final year average grade of 97% at undergraduate (the highest in my year), who excels at tackling difficult and technical problems. Strong skills in a variety of programming languages and owner of a popular Rust library with over 500,000 downloads. Experience in mathematical research, soon-to-be co-author of a paper on tropical geometry. Focussed and driven, with a passion for setting challenging goals and achieving them.

// == Education

// *University of Cambridge*, MASt in Pure Mathematics #dates("10/2024", "06/2025") \

// *Durham University*, BSc Mathematics #dates("09/2021", "06/2024") \
// - Classification: First Class Honours.
// - Grade: 95% (joint-highest in my cohort).
// - Awards: The Mathematical Sciences Best 3H Student Prize

// *Colchester Royal Grammar School* #dates("09/2019", "06/2021") \
// - A Levels: Mathematics (A\*), Further Mathematics (A\*), Physics (A\*), Latin (A\*).
// - Awards: Year 13 Prize for Further Mathematics.

// == Research Experience

// *Research Project in Tropical Geometry* #dates("06/2023", "07/2023") \
// Department of Mathematical Sciences, Durham University \
// - Area of research was how the tropical modification of certain polynomial systems can be used to determine the generic root count of those systems.
// - The results of our work are expected to be published in a paper by the end of this year.
// - Invited by supervisor to attend a #link("https://www.oscar-system.org/meetings/2023-09/")[working group] for the OSCAR computer algebra system in Germany, to write code related to the project.

// == Work Experience

// *Web and Communications Internship* #dates("07/2023", "08/2023") \
// Grey College, Durham University \
// - Created a #link("https://www.greyscr.co.uk")[new website] for Grey College Senior Common Room, using React, Next.js, Bootstrap, and KV storage.
// - Built an admin dashboard with an email client for sending markdown emails and templated emails.
// - Developed a password-less email authentication system.

// *Student Digital Leader* #h(1fr) #dates("09/2022", "06/2023") \
// Durham University \
// - Part of a pool of students who worked on various technical projects for the university.
// - For the first few weeks, I worked in online support with the university's digital services for new students.
// - I then worked as a UAT (User Acceptance Testing) Analyst within this role, using Azure DevOps and Jira to pass/fail test cases and report bugs for a new event-booking website that the university is launching.

// *Software Tester* #h(1fr) #dates("01/2021", "03/2021") \
// Blutick \
// - Tested Blutick's marking software for online GCSE maths exams, reported bugs I found when using the website.
// - Given the responsibility of editing the online questions and mark schemes myself using Latex.
// - Developed TypeScript program to generate all solutions for questions where many combinations of answers were allowed.

// == Projects

// *bnum* #h(1fr) #dates("05/2021", "Present") \
// Mathematical #link("https://crates.io/crates/bnum")[Rust library] with over 500,000 downloads that uniquely provides fixed size signed and unsigned integer types, designed to extend functionality of Rust's primitive integer types to arbitrary bit sizes. Used by a blockchain-related package.

// == Extracurriculars

// Piano (ABRSM Grade 8 Distinction) |
// Durham University Chess Society |
// Durham University Spaceflight Society |
// Durham University Mathematical Problem Solving Society |
// Grey College Table Tennis A Team |
// Grey College Badminton B Team |
// Durham University Chess Society |
// Durham University Quant Fund |
// Co-leader of Physics and Maths Society at Sixth Form

// == Skills

// Mathematics | Rust | JavaScript | Python | Latex | Programming | Research

// #set text(font: "New Computer Modern")

// #pagebreak()

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

#let dates(from, to) = text(rgb(128, 128, 128), [#h(1fr) #from -- #to])
#let date(d) = text(rgb(128, 128, 128), [#h(1fr) #d])

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

- Highly capable mathematician, with the joint-highest grade in my undergraduate cohort.
- Involved in two summer research projects.
- Co-author of a chapter in a book published in Springer's _Algorithms and Computation in Mathematics_ series.
- Developer of a popular big integer library.

== Education

*University of Cambridge*, MASt in Pure Mathematics #dates("10/2024", "06/2025") \
- Current courses: Additive Combinatorics, Combinatorics, Information Theory, Logic and Computability, Quantum Computation, Ramsey Theory

*Durham University*, BSc Mathematics #dates("09/2021", "06/2024") \
- Grade: First Class Honours
- Marks: 90% (first year), 92% (second year), 97% (third year)
- Awards: The Mathematical Sciences Best 3H Student Prize

*Colchester Royal Grammar School* #dates("09/2019", "06/2021") \
- A-levels: Mathematics (A\*, 99%), Further Mathematics (A\*, 97%), Physics (A\*, 91%), Latin (A\*, 90%)
- Awards: Year 13 Prize for Further Mathematics

== Research Experience

*Summer Research Project* - Durham University #dates("06/2023", "07/2023") \
- Researched and wrote a paper on using tropical geometry to determine the generic root count of a certain class of polynomial systems.
// - Area of research was in tropical geometry; specifically, how the modification and tropicalisation of horizontally parametrised polynomial systems can be used to determine the generic root count of those systems.
- First four weeks were mostly spent learning about the area and reading relevant books and materials.
- Last four weeks were devoted to formulating and proving a new result, where I produced a generalised proof of a theorem from a recent paper on the number of equilibria of coupled nonlinear oscillators.
- Paper has been published on #link("https://arxiv.org/abs/2311.18018")[arXiv] and as a chapter in the book _The OSCAR Computer Algebra System_.
- Invited by my supervisor to attend a #link("https://www.oscar-system.org/meetings/2023-09/")[working group] for OSCAR at Paderborn University, Germany, to write a #link("https://github.com/isaacholt100/generic_root_count")[program] in Julia for the paper.

*Mitacs Globalink Research Internship* - University of British Columbia #dates("06/2024", "09/2024")
- Worked on two projects: one on improving the accuracy of reconstruction of intersecting multi-surfaces (arising from atomic potential energy surfaces) given value-sorted sample data, the other relating to the benefits and drawbacks of encoding symmetries (such as rotation invariance) of a physical system into a model of that system versus "learning" these symmetries via data augmentation.
- Expecting to be a co-author of a paper on both projects.

== Work Experience

*Web and Communications Internship* - Grey College, Durham University #dates("07/2023", "08/2023") \
- Developed the #link("https://www.greyscr.co.uk")[new website] for Grey College's Senior Common Room.

*Student Digital Leader* - Durham University #dates("09/2022", "06/2023") \
- Worked as a User Acceptance Testing Analyst, using Azure DevOps to pass/fail test cases and report bugs for a new university-funded event-booking website.

*Software Tester* - Blutick #dates("01/2021", "03/2021") \
- Tested and contributed to Blutick's (now owned by AQA) marking software for online GCSE maths exams.

== Publications

#place(hide(bibliography("./publications.bib")))

#cite(<holt2023generic>, form: "full", style: "apa") \
#cite(<hr2023chapter>, form: "full", style: "apa")

== Conferences

*Tomorrow's Mathematicians Today 2024* - IMA & University of Greenwich (Online) #date("03/2024")
- #link("https://sites.google.com/view/imatmt2024/")[Undergraduate mathematics conference] at which I presented a brief introduction to tropical geometry and an overview of my summer project on it.

== Projects

*bnum* #dates("05/2021", "Present") \
- Mathematical #link("https://crates.io/crates/bnum")[Rust library] for operating on arbitrarily-sized integers, with over 750,000 downloads.
- A dependency for four other libraries, including a popular smart contract package.
- The only library (to my knowledge) to extend functionality of Rust's primitive integer types to arbitrary, fixed size signed and unsigned integers.
- Development involved researching arithmetical algorithms, e.g. integer division, exponentiation by squaring.

== Selected Extracurriculars

- Simon Marais Mathematics Competition (2022, 2023)
- Imperial-Cambridge Mathematics Competition (2022, 2023)
- British Mathematical Olympiad Round 1 (2020)
- ABRSM Grade 8 Piano (Distinction)