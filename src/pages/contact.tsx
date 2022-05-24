import Head from "next/head";
import pageTitle from "../lib/title";
import Icon from "@mdi/react";
import { mdiGithub, mdiGitlab, mdiLinkedin } from "@mdi/js";

const SOCIALS = [{
	name: "LinkedIn",
	url: "https://www.linkedin.com/in/isaacholt100/",
	icon: mdiLinkedin,
}, {
	name: "GitHub",
	url: "https://www.github.com/isaacholt100/",
	icon: mdiGithub,
}, {
	name: "GitLab",
	url: "https://www.gitlab.com/isaacholt100/",
	icon: mdiGitlab,
}]

export default function Contact() {
	return (
		<div>
			<Head>
				<title>{pageTitle("Contact")}</title>
			</Head>
			<h1>Contact Me</h1>
			<p>Email me at {"isaac_holt@icloud.com"} or connect with me on the following social networks:</p>
			<div className="row gy-2 g-lg-3">
				{SOCIALS.map(social => (
					<div className="col-12 col-lg-6 col-xl-4" key={social.name}>
						<a href={social.url} className="btn btn-outline-light btn-lg d-flex flex-row alight-items-center justify-content-center w-100">
							<Icon path={social.icon} color={undefined} className="icon-primary" size="64px" />
							<span className="ms-3 d-flex align-items-center">{social.name}</span>
						</a>
					</div>
				))}
			</div>
		</div>
	);
}