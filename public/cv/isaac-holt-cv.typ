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

Highly capable mathematician, with average mark 91% at undergraduate, who excels at tackling difficult and technical problems. Strong skills in a variety of programming languages and owner of a popular Rust library with over 200,000 downloads. Experience in mathematical research, soon-to-be co-author of a paper on tropical geometry. Focussed and driven, with a passion for setting challenging goals and achieving them.

== Education

*Durham University* #date("09/2021", "06/2024") \
MMath Mathematics \
- Third year modules: Analysis, Cryptography and Codes, Galois Theory, Number Theory, Quantum Computing, Topology.
- Grade: predicted 1st (average mark 91%).

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
Mathematical #link("https://crates.io/crates/bnum")[Rust library] with over 200,000 downloads that uniquely provides fixed size signed and unsigned integer types, designed to extend functionality of Rust's primitive integer types to arbitrary bit sizes. Used by a blockchain-related package.

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
