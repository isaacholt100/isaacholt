import { mdiCodeBracesBox, mdiFile } from "@mdi/js";
import Icon from "@mdi/react";
import Link from "next/link";
import PageTitle from "../../components/PageTitle";
import { getMathsNotes } from "../../lib/mathsNotes";
import { capitalizeName } from "../../lib/capitalizeName";
import { AnchorHTMLAttributes } from "react";

function downloadLinkProps(github: boolean, year: string, name: string, extension: string): Partial<AnchorHTMLAttributes<HTMLAnchorElement>> {
	return {
		href: (github ? GITHUB_REPO_URL + "/blob/main/public" : "") + "/maths-notes/" + year + "/" + name + "/" + name + "." + extension,
		target: "_blank",
	}
}

const GITHUB_REPO_URL = "https://github.com/isaacholt100/isaacholt";

const DATE_FORMAT_OPTIONS: Intl.DateTimeFormatOptions = {
	day: "2-digit",
	month: "2-digit",
	year: "numeric",
}

export default async function Maths() {
    const mathsNotes = await getMathsNotes();
	return (
		<>
			<PageTitle title="Maths Notes" />
			<p>These are summary notes I wrote for my undergraduate maths modules at Durham. The notes were made with <Link className="link-primary" href={"https://typst.app/docs/"}>Typst</Link>. If you notice a mistake in any of these notes, feel free to create an issue or submit a pull request on this website{"'"}s <Link className="link-primary" href={GITHUB_REPO_URL}>GitHub repository</Link>.</p>
			{mathsNotes.map(y => (
				<div className="row g-2 g-md-3" key={y.year}>
					<h2>{capitalizeName(y.year)}</h2>
					{y.notes.map(note => (
						<div className="col col-xs-12 col-sm-6 col-lg-4 col-xl-3" key={note.name}>
							<div className="card border-light bg-transparent h-100">
								<div className="card-body d-flex flex-column">
									<h3 className="card-title text-primary">
										{note.displayName}
									</h3>
									<p className="card-text mt-auto">
										{note.dateCreated !== null && "Created: " + new Date(note.dateCreated).toLocaleDateString("en-GB", DATE_FORMAT_OPTIONS) + " | "}

										Edited: {new Date(note.dateModified).toLocaleDateString("en-GB", DATE_FORMAT_OPTIONS)}
									</p>
									<div className="row g-2">
										<div className="col">
											<a role="button" className="btn btn-light w-100" {...downloadLinkProps(false, y.year, note.name, "pdf")}>
												<span className="d-flex align-items-center justify-content-center">
													<Icon path={mdiFile} size="24px" className="me-1" />
													PDF
												</span>
											</a>
										</div>
										<div className="col">
											<a role="button" className="btn btn-outline-light w-100" {...downloadLinkProps(true, y.year, note.name, "typ")}>
												<span className="d-flex align-items-center justify-content-center">
													<Icon path={mdiCodeBracesBox} size="24px" className="me-1" />
													Source
												</span>
											</a>
										</div>
									</div>
								</div>
							</div>
						</div>
					))}
				</div>
			))}
		</>
	);
}