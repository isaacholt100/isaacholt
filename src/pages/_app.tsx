import type { AppProps } from "next/app"
import Head from "next/head";
import MenuBar from "../components/MenuBar";
//import "bootstrap/scss/bootstrap.scss";
import "../styles/globals.scss";

export default function MyApp({ Component, pageProps }: AppProps) {
	return (
		<div>
			<Head>
				<link rel="apple-touch-icon" sizes="180x180" href="/favicons/apple-touch-icon.png" />
				<link rel="icon" type="image/png" sizes="32x32" href="/favicons/favicon-32x32.png" />
				<link rel="icon" type="image/png" sizes="16x16" href="/favicons/favicon-16x16.png" />
				<link rel="mask-icon" href="/favicons/safari-pinned-tab.svg" color="#2E79FF" />
				<meta name="msapplication-TileColor" content="#2E79FF" />
				<link rel="manifest" href="/favicons/site.webmanifest" />
			</Head>
			<MenuBar />
			<div className="mx-auto p-2 p-md-3 container-xxl">
				<Component {...pageProps} />
			</div>
		</div>
	);
}