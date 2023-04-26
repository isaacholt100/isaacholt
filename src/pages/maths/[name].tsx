/*import { mdiChevronLeftCircle } from "@mdi/js";
import Icon from "@mdi/react";
import { GetStaticPaths, GetStaticProps } from "next"
import Link from "next/link";
import { Button } from "react-bootstrap";
import { capitalizeName, getMathsNotesPaths } from "../../lib/mathsNotes";
import PDFViewer from "../../components/PDFViewer";
import { useEffect, useState } from "react";
import Head from "next/head";
import pageTitle from "../../lib/title";
import styles from "../../styles/mathsnotes.module.scss";

export default function MathsNotesViewer(props: { name: string, displayName: string; }) {
	const [file, setFile] = useState<Blob | null>(null);
	const [error, setError] = useState(false);

	useEffect(() => {
		(async () => {
			try {
				const res = await fetch("/maths-notes/" + props.name + "/" + props.name + ".pdf").catch(err => {
					throw err;
				});
				const blob = await res.blob();
				setFile(blob);
			} catch (err) {
				setError(true);
			}
		})();
	}, [props.name]);
	return (
		<>
			<Head>
				<title>{pageTitle(props.displayName + " Notes")}</title>
			</Head>
			<div className="d-flex align-items-center mb-2 mb-md-3">
				<Link href="/maths" passHref legacyBehavior>
					<Button
						as="a"
						variant="outline-primary"
						className="me-2"
					>
						<span className="d-flex align-items-center">
							<Icon size={"24px"} className="me-1" path={mdiChevronLeftCircle} />
							All Notes
						</span>
					</Button>
				</Link>
				<h5 className="m-0 ms-auto">{props.displayName}</h5>
			</div>
			<div className={styles.viewer_container}>
				{error ? "There was an error loading this file" : <PDFViewer file={file} />}
			</div>
		</>
	);
}

export const getStaticPaths: GetStaticPaths = async () => {
	const paths = await getMathsNotesPaths();
	return {
		paths: paths.map(p => ({
			params: {
				name: p,
			},
		})),
		fallback: false,
	}
}

export const getStaticProps: GetStaticProps = async ({ params }) => {
	return {
		props: {
			name: params?.name,
			displayName: capitalizeName(params?.name as string),
		},
	}
}*/