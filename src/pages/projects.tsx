import Image from "next/image";
import Link from "next/link";
import PageTitle from "../components/PageTitle";

interface Project {
	name: string;
	url?: string;
	source?: string;
	description: string;
	image: string;
}

const PROJECTS: Project[] = [
	{
		name: "My Year Book",
		url: "https://myyearbook.vercel.app",
		source: "https://github.com/isaacholt100/MYB",
		description: "A progressive web app that allows students from a school to upload photos and a quote. Prizes can also be created/suggested by students which are then voted for. The results are used to create a downloabable yearbook in PDF format.",
		image: ""
	},
	{
		name: "Latin Grammar Test",
		url: "https://latingrammartest.vercel.app",
		source: "https://github.com/isaacholt100/latin-grammar-test",
		description: "A simple single page application which tests knowledge of Latin grammar. It features a \"Live\" mode where users from the same school can challenge each other to a timed test. I created this while I was taking Latin A Level to help with my revision.",
		image: ""
	},
	{
		name: "Test",
		url: "https://example.com",
		description: "some description of my project",
		image: ""
	}
];

export default function Projects() {
	return (
		<div>
			<PageTitle title="Projects" />
			<div className="row g-2 g-md-3">
				{PROJECTS.map(project => (
					<div className="col-12 col-sm-6 col-sm-4 col-xl-3" key={project.name}>
						<div className="card h-100 border-light bg-transparent">
							{/*<img src="..." className="card-img-top" alt="" />*/}
							<div className="card-body d-flex flex-column">
								<h5 className="card-title">{project.name}</h5>
								<div className="flex-1">
									<p className="card-text">{project.description}</p>
								</div>
								<div className="row g-2 mt-auto">
									{project.url && (
										<div className="col">
											<Link href={project.url}>
												<a className="btn btn-info w-100 col">Visit</a>
											</Link>
										</div>
									)}
									{project.source && (
										<div className="col">
											<Link href={project.source}>
												<a className="btn btn-outline-info w-100">Source</a>
											</Link>
										</div>
									)}
								</div>
							</div>
						</div>
					</div>
				))}
			</div>
		</div>
	);
}