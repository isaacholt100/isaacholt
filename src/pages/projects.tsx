import Image from "next/image";
import Link from "next/link";
import Row from "react-bootstrap/Row";
import Card from "react-bootstrap/Card";
import Col from "react-bootstrap/Col";
import PageTitle from "../components/PageTitle";
import Button from "react-bootstrap/Button";

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
											<Button variant="primary" href={project.url} className="w-100">
												Visit
											</Button>
										</Col>
									)}
									{project.source && (
										<Col>
											<Button variant="outline-primary" href={project.source} className="w-100">
												Source
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