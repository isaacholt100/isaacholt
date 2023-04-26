import { mdiCodeBracesBox, mdiFile } from "@mdi/js";
import Icon from "@mdi/react";
import { GetStaticProps } from "next";
import Link from "next/link";
import { Button, ButtonProps, Card, Col, Row } from "react-bootstrap";
import PageTitle from "../../components/PageTitle";
import { getMathsNotes, MathsNoteFile } from "../../lib/mathsNotes";
import { Fragment } from "react";

function downloadLinkProps(github: boolean, name: string, extension: string): Partial<ButtonProps> {
	return {
		href: (github ? GITHUB_REPO_URL + "/blob/main/public" : "") + "/maths-notes/" + name + "/" + name + "." + extension,
		target: "_blank",
		as: "a",
	}
}

const GITHUB_REPO_URL = "https://github.com/isaacholt100/isaacholt";

const DATE_FORMAT_OPTIONS: Intl.DateTimeFormatOptions = {
	day: "2-digit",
	month: "2-digit",
	year: "numeric",
}

export default function Maths(props: { mathsNotes: { year: string, notes: MathsNoteFile[] }[] }) {
	return (
		<>
			<PageTitle title="Maths Notes" />
			<p>These are summary notes I wrote for my undergraduate maths modules at Durham. The notes were made with <Link className="link-primary" href={"https://typst.app/docs/"}>Typst</Link>. If you notice a mistake in any of these notes, feel free to create an issue or submit a pull request on this website{"'"}s <Link className="link-primary" href={GITHUB_REPO_URL}>GitHub repository</Link>.</p>
			{props.mathsNotes.map(y => (
				<Row className="g-2 g-md-3" key={y.year}>
					<h2>{y.year}</h2>
					{y.notes.map(note => (
						<Col xs={12} sm={6} lg={4} xl={3} key={note.name}>
							<Card border="light" bg="transparent" className="h-100">
								{/*<img src="..." className="card-img-top" alt="" />*/}
								<Card.Body className="d-flex flex-column">
									<Card.Title as="h3" className="text-primary">
										{note.displayName}
									</Card.Title>
									<Card.Text className="mt-auto">
										{note.dateCreated !== null && "Created: " + new Date(note.dateCreated).toLocaleDateString("en-GB", DATE_FORMAT_OPTIONS) + " | "}

										Edited: {new Date(note.dateModified).toLocaleDateString("en-GB", DATE_FORMAT_OPTIONS)}
									</Card.Text>
									<Row className="g-2">
										{/*<Col>
											<Link href={router.asPath + "/" + note.name} legacyBehavior passHref>
												<Button
													as="a"
													variant="light"
													className="w-100">
														<span className="d-flex align-items-center justify-content-center">
															<Icon path={mdiFile} size="24px" className="me-1" />
															View
														</span>
												</Button>
											</Link>
										</Col>*/}
										<Col>
											<Button variant="light" className="w-100" {...downloadLinkProps(false, note.name, "pdf")}>
												<span className="d-flex align-items-center justify-content-center">
													<Icon path={mdiFile} size="24px" className="me-1" />
													PDF
												</span>
											</Button>
										</Col>
										<Col>
											<Button variant="outline-light" className="w-100" {...downloadLinkProps(true, note.name, "typ")}>
												<span className="d-flex align-items-center justify-content-center">
													<Icon path={mdiCodeBracesBox} size="24px" className="me-1" />
													Source
												</span>
											</Button>
										</Col>
									</Row>
								</Card.Body>
							</Card>
						</Col>
					))}
				</Row>
			))}
		</>
	);
}

export const getStaticProps: GetStaticProps = async () => {
	const mathsNotes = await getMathsNotes();
	return {
		props: {
			mathsNotes,
		}
	}
}