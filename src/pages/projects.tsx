import Link from "next/link";
import Row from "react-bootstrap/Row";
import Card from "react-bootstrap/Card";
import Col from "react-bootstrap/Col";
import PageTitle from "../components/PageTitle";
import Button from "react-bootstrap/Button";
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
		url: "https://docs.rs/bnum/latest/bnum",
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
		description: "A simple single page application which tests knowledge of Latin grammar. It features a \"Live\" mode where users from the same school can challenge each other to a timed test. I created this while I was studying Latin A Level to help with my revision.",
		image: ""
	},
	{
		name: "AoC 2022",
		url: "https://replit.com/@isaacholt1/aoc2022",
		source: "https://github.com/isaacholt100/aoc2022",
		description: "Solutions written in Python for Advent of Code 2022.",
		image: ""
	},
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
			<Row className="g-2 g-md-3">
				{PROJECTS.map(project => (
					<Col xs={12} sm={6} lg={4} xl={3} key={project.name}>
						<Card border="light" bg="transparent" className="h-100">
							{/*<img src="..." className="card-img-top" alt="" />*/}
							<Card.Body className="d-flex flex-column">
								<Card.Title as="h3" className="text-primary">
									{project.name}
								</Card.Title>
								<Card.Text>
									{project.description}
								</Card.Text>
								<Row className="g-2 mt-auto">
									{project.url && (
										<Col>
											<Link href={project.url} passHref legacyBehavior>
												<Button
													as="a"
													href={project.url} variant="light"
													className="w-100"
													target="_blank"
												>
													<span className="d-flex align-items-center justify-content-center">
														<Icon path={mdiOpenInNew} size="24px" className="me-1" />
														Visit
													</span>
												</Button>
											</Link>
										</Col>
									)}
									{project.source && (
										<Col>
											<Button variant="outline-light" href={project.source} className="w-100">
													<span className="d-flex align-items-center justify-content-center">
														<Icon path={mdiCodeBracesBox} size="24px" className="me-1" />
														Source
													</span>
											</Button>
										</Col>
									)}
								</Row>
							</Card.Body>
						</Card>
					</Col>
				))}
			</Row>
		</>
	);
}