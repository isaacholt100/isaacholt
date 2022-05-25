import Link from "next/link";
import PageTitle from "../components/PageTitle";
import { LINKEDIN_URL } from "./contact";

export default function About() {
	return (
		<div>
			<PageTitle title="About Me" />
			<p>
				I am a first year, mathematics student at Grey College, Durham. Mathematics surrounds us. No matter where I look, I am yet to find a place where it {"doesn't"} exist. Every new discovery is a tantalising oppurtunity. The flow from the beginning of a story, an axiom discovery, is exhilerating to me; who knows what fascinating possibilities may be discovered.
				
				The direct application from mathematics into computer science is likely my most keen interest. Being an avid coder, I split my time between learning about the formulation of ideas and theories within maths, to the real world solutions and putting what I have learnt into direct practive within coding and computer science.

				Whenever I have it, I always directly invest my free time into programming. This began with a 2017 online web development course. I am proficient in CSS, JavaScript Typescript as web programming languages, and Rust as a low-level. So much of my time is spent on coding as it is an excuse for my creative side to be released and whilst challenging my mental dexterity. More details about my specific projects can be found [here]
				
				{" "}
				<Link href="/projects">
					<a className="link-primary">projects</a>
				</Link>
				{" "} page.
			</p>
			<p>
				When {"I'm"} not battling with numbers or writing code, I am a musical person so I like playing piano and composing songs on GarageBand. I also enjoy playing tennis, table tennis and badminton, and {"I'm"} a big fan of online chess.
			</p>
			<p>
				Feel free to take a look at my{" "}
				<Link href={LINKEDIN_URL}>
					<a className="link-primary">LinkedIn page</a>
				</Link>
				{" "} for more about my experience, education, etc.
			</p>
		</div>
	);
}