import Icon from "@mdi/react";
import { mdiChessPawn, mdiDisc as mdiDiscord, mdiEmail, mdiGithub, mdiGitlab, mdiInstagram, mdiLinkedin, mdiReddit, mdiStackExchange, mdiStackOverflow } from "@mdi/js";
//import styles from "@/styles/contact.module.scss";
import PageTitle from "../../components/PageTitle";

interface Social {
	name: string;
	url: string;
	icon: string;
	size?: number;
}

export const LINKEDIN_URL = "https://www.linkedin.com/in/isaacholt100/";

const EMAIL = "isaacholt100@icloud.com";

const SOCIALS: Social[] = [
	{
		name: "Email",
		url: "mailto:" + EMAIL,
		icon: mdiEmail,
	},
	{
		name: "LinkedIn",
		url: LINKEDIN_URL,
		icon: mdiLinkedin,
	},
	{
		name: "Discord",
		url: "https://discordapp.com/users/652929649747296266",
		icon: mdiDiscord,
	},
	{
		name: "Instagram",
		url: "https://www.instagram.com/isaacholt100/",
		icon: mdiInstagram,
	},
	{
		name: "Reddit",
		url: "https://www.reddit.com/user/isaacholt100",
		icon: mdiReddit,
	},
	{
		name: "GitHub",
		url: "https://www.github.com/isaacholt100/",
		icon: mdiGithub,
	},
	{
		name: "GitLab",
		url: "https://www.gitlab.com/isaacholt100/",
		icon: mdiGitlab,
	},
	{
		name: "Stack Overflow",
		url: "https://stackoverflow.com/users/14087924/isaacholt100",
		icon: mdiStackOverflow,
	},
	{
		name: "Math SE",
		url: "https://math.stackexchange.com/users/815840/isaacholt100",
		icon: mdiStackExchange,
	},
	{
		name: "Chess.com",
		url: "https://www.chess.com/member/isaacholt100",
		icon: mdiChessPawn,
	}
];

export default function Socials() {
	return (
		<>
			<PageTitle title="Socials" />
			<div className="row g-2 g-md-3">
				{SOCIALS.map(social => (
					<div className="col col-xs-12 col-sm-6 col-xl-4" key={social.name}>
						<a
							href={social.url}
							className={"btn btn-outline-light btn-lg w-100 position-relative d-flex justify-content-center align-items-center"}
                            style={{height: 72,fontSize: 20}}
							target="_blank"
						>
							<Icon
								path={social.icon}
								//color={social.color}
								size={social.size ? social.size.toString() + "px" : "40px"}className="position-absolute"
								style={{left: 12, bottom: 13}}
							/>
							<span>
								{social.name}
							</span>
						</a>
					</div>
				))}
			</div>
		</>
	);
}