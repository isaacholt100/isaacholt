import Head from "next/head";
import pageTitle from "../lib/title";

export default function About() {
	return (
		<div>
			<Head>
				<title>{pageTitle("About")}</title>
			</Head>
		</div>
	);
}