import Head from "next/head";
import pageTitle from "../lib/title";
import Icon from "@mdi/react";
import { mdiFacebook, mdiGithub, mdiGitlab, mdiInstagram, mdiLinkedin, mdiTwitter } from "@mdi/js";
import PageTitle from "../components/PageTitle";
import Link from "next/link";
import Row from "react-bootstrap/Row";
import Col from "react-bootstrap/Col";
import Button from "react-bootstrap/Button";

interface Social {
	name: string;
	url: string;
	icon: string;
	color: string | undefined;
}

export const LINKEDIN_URL = "https://www.linkedin.com/in/isaacholt100/";

const SOCIALS: Social[] = [
		{
		name: "LinkedIn",
		url: LINKEDIN_URL,
		icon: mdiLinkedin,
		color: "rgb(42, 103, 169)",
	},
	{
		name: "GitHub",
		url: "https://www.github.com/isaacholt100/",
		icon: mdiGithub,
		color: undefined,
	},
	{
		name: "GitLab",
		url: "https://www.gitlab.com/isaacholt100/",
		icon: mdiGitlab,
		color: "rgb(224, 103, 42)",
	},
	{
		name: "Instagram",
		url: "https://www.instagram.com/isaacholt100/",
		icon: mdiInstagram,
		color: "rgb(199, 47, 63)",
	},
	{
		name: "Facebook",
		url: "https://www.facebook.com/profile.php?id=100073407960215/",
		icon: mdiFacebook,
		color: "rgb(48, 94, 222)",
	},
	{
		name: "Twitter",
		url: "https://twitter.com/isaacholt100/",
		icon: mdiTwitter,
		color: "rgb(61, 127, 223)",
	}
];

const EMAIL = "isaacholt100@icloud.com";

export default function Contact() {
	return (
		<>
			<PageTitle title="Contact" />
			<p>To get in touch, email me at <a href={"mailto:" + EMAIL}>{EMAIL}</a> or connect with me on these platforms:</p>
			<Row className="g-2 g-md-3">
				{SOCIALS.map(social => (
					<Col xs={12} md={6} xl={4} key={social.name}>
						<Button
							href={social.url}
							as="a"
							size="lg"
							variant="outline-light"
							className="w-100 position-relative d-flex justify-content-center align-items-center" style={{height: 72 }}
						>
							<Icon
								path={social.icon}
								color={social.color}
								size="48px" className="position-absolute"
								style={{left: 12, bottom: 9}}
							/>
							{social.name}
						</Button>
					</Col>
				))}
			</Row>
		</>
	);
}