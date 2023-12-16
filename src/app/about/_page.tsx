import Link from "next/link";
import PageTitle from "../../components/PageTitle";
import { LINKEDIN_URL } from "../socials/page";
import AboutContent from "./about.md";

export default function About() {
	return (
		<>
			<PageTitle title="About Me" />
			<AboutContent />
		</>
	);
}