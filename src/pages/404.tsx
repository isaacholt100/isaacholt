import Link from "next/link";
import { useRouter } from "next/router";
import { Button } from "react-bootstrap";
import PageTitle from "../components/PageTitle";

export default function PageNotFound() {
	const router = useRouter();
	return (
		<div>
			<PageTitle title="Page Not Found" />
			<div className="mb-2 mb-md-3">Error 404: page not found.</div>
			<div className="d-flex">
				<Link href="/" passHref legacyBehavior>
					<Button as="a" variant="outline-primary">Go Home</Button>
				</Link>
				{typeof(history) !== "undefined" && history.length > 2 && (
					<Button onClick={() => router.back()} as="a" variant="outline-primary ms-2">Go Back</Button>
				)}
			</div>
		</div>
	);
}