import Link from "next/link";
import PageTitle from "../components/PageTitle";
import { Metadata } from "next";

export const metadata: Metadata = {
    title: "Page Not Found"
}

export default function PageNotFound() {
	return (
		<div>
			<PageTitle title="Page Not Found" />
			<div className="mb-2 mb-md-3">Error 404: page not found.</div>
			<div className="d-flex">
				<Link href="/" role="button" className="btn btn-outline-primary">
					Go Home
				</Link>
			</div>
		</div>
	);
}