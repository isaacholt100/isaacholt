import { useEffect, useState } from "react";

export default function useWindowWidth() {
	const [windowWidth, setWindowWidth] = useState<number | null>(null);

	useEffect(() => {
		function onResize() {
			setWindowWidth(window.innerWidth);
		}

		window.addEventListener("resize", onResize);

		onResize();

		return () => window.removeEventListener("resize", onResize);
	}, []);

	return windowWidth;
}