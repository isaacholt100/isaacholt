import type { AppProps } from "next/app"
import Head from "next/head";
import MenuBar from "../components/MenuBar";
import "../styles/globals.scss";

export default function MyApp({ Component, pageProps }: AppProps) {
	return (
		<div>
			<Head>
				<link rel="icon" href="/favicon.ico" />
			</Head>
			<MenuBar />
			<div style={{maxWidth: 1280, margin: "0 auto", padding: 12}}>
				<Component {...pageProps} />
			</div>
		</div>
	);
}