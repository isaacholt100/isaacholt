import Link from "next/link";
import PageTitle from "../../components/PageTitle";
import { LINKEDIN_URL } from "../socials/page";

export default function About() {
	return (
		<>
			<PageTitle title="About Me" />
			<p>
				I am currently a mathematics student at Durham University. What I love about maths is that it is used in just about everything. I find it beautiful that merely starting from a set of axioms can lead us to discover many fascinating and often useful results. Being an avid coder, one of my biggest interests in maths is areas which have a direct application in computer science. I really enjoy seeing the link between these two: mathematics allows us to formulate ideas and theories, while computing provides a means to use these ideas into real world applications.
			</p>
			<p>
				I love programming in my spare time, a hobby which started in 2017 when I took an online course in web development, which remains a key interest of mine. Having developed profiency in CSS, JavaScript and TypeScript, I then learnt Rust as I wanted to be able to use and understand a more low-level programming language. While learning these languages, I have built a number of projects - you can find my completed ones on my {" "}
				<Link href="/projects" className="link-primary">
					projects
				</Link>
				{" "} page.
			</p>
			<p>
				When {"I'm"} not battling with numbers or writing code, I am a musical person so I like playing piano and composing songs on GarageBand. I also enjoy playing tennis, table tennis and badminton, and {"I'm"} a big fan of online chess.
			</p>
			<p style={{marginBottom: 0}}>
				Feel free to take a look at my{" "}
				<Link className="link-primary" href={LINKEDIN_URL}>LinkedIn page</Link>
				{" "} for more about my experience, education, etc.
			</p>
		</>
	);
}