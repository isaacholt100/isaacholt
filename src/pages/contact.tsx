import Head from "next/head";
import pageTitle from "../lib/title";
import Icon from "@mdi/react";
import { mdiFacebook, mdiGithub, mdiGitlab, mdiInstagram, mdiLinkedin, mdiTwitter } from "@mdi/js";
import PageTitle from "../components/PageTitle";

const SOCIALS = [{
	name: "LinkedIn",
	url: "https://www.linkedin.com/in/isaacholt100/",
	icon: mdiLinkedin,
	color: "rgb(42, 103, 169)",
}, {
	name: "GitHub",
	url: "https://www.github.com/isaacholt100/",
	icon: mdiGithub,
	color: undefined,
}, {
	name: "GitLab",
	url: "https://www.gitlab.com/isaacholt100/",
	icon: mdiGitlab,
	color: "rgb(224, 103, 42)",
}, {
	name: "Instagram",
	url: "https://www.instagram.com/isaacholt100/",
	icon: mdiInstagram,
	color: "rgb(199, 47, 63)",
}, {
	name: "Facebook",
	url: "https://www.facebook.com/profile.php?id=100073407960215/",
	icon: mdiFacebook,
	color: "rgb(48, 94, 222)",
}, {
	name: "Twitter",
	url: "https://twitter.com/isaacholt100/",
	icon: mdiTwitter,
	color: "rgb(61, 127, 223)",
}];

const EMAIL = "isaacholt100@icloud.com";

export default function Contact() {
	return (
		<div>
			<PageTitle title="Contact" />
			<p>Email me at <a className="btn-link" href={"mailto:" + EMAIL}>{EMAIL}</a> or connect with me on these platforms:</p>
			<div className="row gy-2 g-md-3">
				{SOCIALS.map(social => (
					<div className="col-12 col-md-6 col-xl-4" key={social.name}>
						<a href={social.url} className="btn btn-outline-light btn-lg d-flex flex-row alight-items-center justify-content-center w-100" style={{position: "relative", height: 88 }}>
							<Icon path={social.icon} color={social.color} size="60px" style={{position: "absolute", left: 12, bottom: 12}} />
							<span className="ms-3 d-flex align-items-center">{social.name}</span>
						</a>
					</div>
				))}
			</div>
		</div>
	);
}