import { mdiCodeBracesBox, mdiFile } from "@mdi/js";
import Icon from "@mdi/react";
import Link from "next/link";
import PageTitle from "../../components/PageTitle";
import { generateMetadataFile } from "../../lib/mathsNotes";
import { capitalizeName } from "../../lib/capitalizeName";
import { AnchorHTMLAttributes } from "react";
import InfoText from "./info.md";
import "highlight.js/styles/github-dark.css";
import notesMetadata from "./notes-metadata.json"; // this is so we can access local metadata like date created, date edited

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

function splitAfterFirst(str: string, substr: string): string {
    let idx = str.indexOf(substr);
    if (idx == -1) {
        return str;
    }
    return str.slice(idx + 1);
}

export default async function Maths() {
    process.env.NODE_ENV === "development" && await generateMetadataFile();
	return (
		<>
			<PageTitle title="Maths Notes" />
            <InfoText />
            <div className="mt-n4" />
			{notesMetadata.sort((y1, y2) => y1.year.localeCompare(y2.year)).reverse().map((y, i) => (
				<div className="row g-2 g-md-3 pt-3" key={y.year}>
					<h2>{capitalizeName(splitAfterFirst(y.year, "-"))}</h2>
					{y.notes.map(note => (
						<div className="col col-12 col-sm-6 col-lg-4 col-xl-3" key={note.name}>
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