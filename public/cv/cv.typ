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

#link("mailto:isaac_holt@icloud.com")[Email] |
#link("https://www.linkedin.com/in/isaacholt100/")[LinkedIn] |
#link("https://github.com/isaacholt100")[GitHub] |
#link("https://isaacholt.vercel.app")[Personal Website]

== Summary

Highly capable mathematician who excels at tackling difficult problems. Focussed and driven, with a passion for setting challenging goals and achieving them.

== Education

*Durham University* #date("09/2021", "Present") \
MMath Mathematics \
- Third year modules: Analysis, Cryptography and Codes, Differential Geometry, Machine Learning and Neural Networks, Quantum Computing, Topology.
- Predicted 1st (average mark 90%).

*Colchester Royal Grammar School* #date("09/2019", "06/2021") \
- A Levels: Mathematics (A\*), Further Mathematics (A\*), Physics (A\*), Latin (A\*).
- Awards: Year 13 Prize for Further Mathematics.

== Research Experience

*Research Project in Tropical Geometry* #date("06/2023", "07/2023") \
Durham University \
- Area of research was how the tropical modification of certain polynomial systems can be used to determine the generic root count.
- The results of our work are expected to be published as a paper at the end of this year.
- Attended a #link("https://www.oscar-system.org/meetings/2023-09/")[working group] in Germany relating to this research, to write code for the OSCAR computer algebra system.

== Work Experience

*Web and Communications Internship* #date("07/2023", "08/2023") \
Grey College, Durham University \
- Created a #link("https://grey-scr.vercel.app")[new website] for Grey College Senior Common Room, using React, Next.js, Bootstrap, and KV storage.
- Built an admin dashboard with an email client for sending markdown emails and template emails.
- Developed a password-less email authentication system for the dashboard.

*Student Digital Leader* #h(1fr) #date("09/2022", "06/2023") \
Durham University \
- For the first few weeks, I worked in online support with the university's digital services for the new students.
- I then worked as a UAT (User Acceptance Testing) Analyst within this role, using Azure DevOps and Jira to pass/fail test cases and report bugs for a new website that the university is launching.

*Software Tester* #h(1fr) #date("01/2021", "03/2021") \
Blutick \
- Tested Blutick's marking software for online GCSE maths exams, reported bugs I found when using the website.
- Given the responsibility of editing the online questions and mark schemes myself using Latex.
- Developed TypeScript program to generate all solutions for questions where many combinations of answers were allowed.

== Projects

*bnum* #h(1fr) #date("05/2021", "Present") \
#link("https://crates.io/crates/bnum")[Rust library] with over 150,000 downloads that provides fixed size signed and unsigned integer types, designed to extend the functionality of Rust's primitive integer types to arbitrary bit sizes. I am developing a floating point type that similarly will extend the functionality of Rust's floating point types to arbitrary bit sizes.

== Extracurriculars

Durham University Mathematical Problem Solving Society |
Piano (Grade 8 Distinction) |
Grey College Table Tennis A Team |
Grey College Badminton B Team |
Durham University Chess Society |
Durham University Quant Fund |
Co-leader of Physics and Maths Society at sixth form

== Skills

Mathematics | Rust | Python | Latex
