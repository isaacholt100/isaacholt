import '../styles/globals.css'
import type { AppProps } from 'next/app'
import MenuBar from '../components/MenuBar';
import "bootstrap/dist/css/bootstrap.css";

function MyApp({ Component, pageProps }: AppProps) {
	return (
		<div>
			<MenuBar />
			<Component {...pageProps} />
		</div>
	);
}

export default MyApp
