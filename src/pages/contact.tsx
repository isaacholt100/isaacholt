import Head from "next/head";
import pageTitle from "../lib/title";
import Icon from "@mdi/react";
import { mdiEmail, mdiFacebook, mdiGithub, mdiGitlab, mdiInstagram, mdiLinkedin, mdiTwitter } from "@mdi/js";
import PageTitle from "../components/PageTitle";
import Link from "next/link";
import Row from "react-bootstrap/Row";
import Col from "react-bootstrap/Col";
import Button from "react-bootstrap/Button";
import styles from "../styles/contact.module.scss";

interface Social {
	name: string;
	url: string;
	icon: string;
	color: string | undefined;
}

export const LINKEDIN_URL = "https://www.linkedin.com/in/isaacholt100/";

const EMAIL = "isaacholt100@icloud.com";

const SOCIALS: Social[] = [
	{
		name: "Email",
		url: "mailto:" + EMAIL,
		icon: mdiEmail,
		color: "rgb(188, 74, 56)",
	},
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
	}
];

export default function Contact() {
	return (
		<>
			<PageTitle title="Contact" />
			<Row className="g-2 g-md-3">
				{SOCIALS.map(social => (
					<Col xs={12} sm={6} xl={4} key={social.name}>
						<Button
							href={social.url}
							as="a"
							size="lg"
							variant="outline-light"
							className={"w-100 position-relative d-flex justify-content-center align-items-center " + styles["social-button"]}
						>
							<Icon
								path={social.icon}
								//color={social.color}
								size="48px" className="position-absolute"
								style={{left: 12, bottom: 9}}
							/>
							<span>
								{social.name}
							</span>
						</Button>
					</Col>
				))}
			</Row>
		</>
	);
}