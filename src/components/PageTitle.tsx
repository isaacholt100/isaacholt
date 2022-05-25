import Head from "next/head";
import pageTitle from "../lib/title";

export default function PageTitle(props: { title: string }) {
	return (
		<>
			<Head>
				<title>{pageTitle(props.title)}</title>
			</Head>
			<h1>{props.title}</h1>
			<hr className="border-3 border-light opacity-100" />
		</>
	);
}