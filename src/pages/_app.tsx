import type { AppProps } from "next/app"
import Head from "next/head";
import MenuBar from "../components/MenuBar";
//import "bootstrap/scss/bootstrap.scss";
import "../styles/globals.scss";

export default function MyApp({ Component, pageProps }: AppProps) {
	return (
		<div>
			<Head>
				<link rel="icon" href="/favicon.ico" />
			</Head>
			<MenuBar />
			<div className="mx-auto p-2 p-md-3 container-xxl" style={{marginTop: "66px"}}>
				<Component {...pageProps} />
			</div>
		</div>
	);
}