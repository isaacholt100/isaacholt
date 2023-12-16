import Link from "next/link";
import PageTitle from "../../components/PageTitle";
import Icon from "@mdi/react";
import { mdiCodeBracesBox, mdiOpenInNew } from "@mdi/js";

interface Project {
	name: string;
	url?: string;
	source?: string;
	description: string;
	image: string;
}

const PROJECTS: Project[] = [
	{
		name: "bnum",
		url: "https://crates.io/crates/bnum",
		source: "https://github.com/isaacholt100/bnum",
		description: "A Rust library that provides arbitrary, fixed size signed and unsigned integer types that extend the functionality of Rust's primitive integers, using const generics. It is the first library that I have published, and my biggest coding project so far.",
		image: ""
	},
	{
		name: "My Year Book",
		url: "https://myyearbook.vercel.app",
		source: "https://github.com/isaacholt100/MYB",
		description: "A progressive web app that allows students from a school to upload photos and a quote. Prizes can also be created/suggested by students which are then voted for. The results are used to create a downloadable yearbook in PDF format.",
		image: ""
	},
	{
		name: "Latin Grammar Test",
		url: "https://latingrammartest.vercel.app",
		source: "https://github.com/isaacholt100/latin-grammar-test",
		description: "A simple single page application which tests knowledge of Latin grammar. I created this while I was studying Latin A Level to help with my revision.",
		image: ""
	},
	// {
	// 	name: "AoC 2022",
	// 	url: "https://replit.com/@isaacholt1/aoc2022",
	// 	source: "https://github.com/isaacholt100/aoc2022",
	// 	description: "Solutions written in Python for Advent of Code 2022.",
	// 	image: ""
	// },
	{
		name: "My Personal Website",
		url: "/",
		source: "https://github.com/isaacholt100/isaacholt",
		description: "The website you're on right now! Built with TypeScript, React.js, Next.js and Sass.",
		image: ""
	}
];

export default function Projects() {
	return (
		<>
			<PageTitle title="Projects" />
			<div className="row g-2 g-md-3">
				{PROJECTS.map(project => (
					<div className="col col-12 col-sm-6 col-lg-4 col-xl-3" key={project.name}>
						<div className="card border-light h-100 bg-transparent">
							{/*<img src="..." className="card-img-top" alt="" />*/}
							<div className="card-body d-flex flex-column">
								<h3 className="card-title text-primary">
									{project.name}
								</h3>
								<div className="card-text">
									{project.description}
								</div>
								<div className="row g-2 mt-auto">
									{project.url && (
										<div className="col">
											<Link href={project.url} role="button" target="_blank" className="btn btn-light w-100">
                                                <span className="d-flex align-items-center justify-content-center">
                                                    <Icon path={mdiOpenInNew} size="24px" className="me-1" />
                                                    Visit
                                                </span>
											</Link>
										</div>
									)}
									{project.source && (
										<div className="col">
											<a role="button" href={project.source} className="btn btn-outline-light w-100" target="_blank">
                                                <span className="d-flex align-items-center justify-content-center">
                                                    <Icon path={mdiCodeBracesBox} size="24px" className="me-1" />
                                                    Source
                                                </span>
											</a>
										</div>
									)}
								</div>
							</div>
						</div>
					</div>
				))}
			</div>
		</>
	);
}