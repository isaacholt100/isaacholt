import { mdiDownload, mdiDownloadCircle } from "@mdi/js";
import Icon from "@mdi/react";
import { GetStaticProps } from "next";
import Link from "next/link";
import { useRouter } from "next/router";
import { Button, ButtonProps, Card, Col, Row } from "react-bootstrap";
import PageTitle from "../../components/PageTitle";
import { getMathsNotes, MathsNoteFile } from "../../lib/mathsNotes";

function downloadLinkProps(name: string, extension: string): Partial<ButtonProps> {
	return {
		href: "/maths-notes/" + name + "/" + name + "." + extension,
		target: "_blank",
		as: "a",
	}
}

export default function Maths(props: { mathsNotes: MathsNoteFile[] }) {
	const router = useRouter();
	return (
		<>
			<PageTitle title="Maths Notes" />
			<Row className="g-2 g-md-3">
				{props.mathsNotes.map(note => (
					<Col xs={12} xl={6} key={note.name}>
						<Card border="light" bg="transparent" className="h-100">
							{/*<img src="..." className="card-img-top" alt="" />*/}
							<Card.Body className="d-flex flex-column">
								<Card.Title as="h3" className="text-primary">
									{note.displayName}
								</Card.Title>
								<Card.Text>
									{note.dateCreated !== null && "Created: " + new Date(note.dateCreated).toLocaleDateString() + " | "}
									
									Edited: {new Date(note.dateModified).toLocaleDateString()}
								</Card.Text>
								<Row className="g-2 mt-auto">
									<Col>
										<Link href={router.asPath + "/" + note.name} legacyBehavior passHref>
											<Button
												as="a"
												variant="light"
												className="w-100">
												View
											</Button>
										</Link>
									</Col>
									<Col>
										<Button variant="outline-light" className="w-100" {...downloadLinkProps(note.name, "pdf")}>
											<span className="d-flex align-items-center justify-content-center">
												<Icon path={mdiDownloadCircle} size="24px" className="me-1" />
												PDF
											</span>
										</Button>
									</Col>
									<Col>
										<Button variant="outline-light" className="w-100" {...downloadLinkProps(note.name, "tex")}>
											<span className="d-flex align-items-center justify-content-center">
												<Icon path={mdiDownloadCircle} size="24px" className="me-1" />
												TeX
											</span>
										</Button>
									</Col>
								</Row>
							</Card.Body>
						</Card>
					</Col>
				))}
			</Row>
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