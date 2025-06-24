import Icon from "@mdi/react";
// import discord from "./discord.svg";
import { mdiChessPawn, mdiEmail, mdiGithub, mdiLinkedin, mdiReddit, mdiStackOverflow } from "@mdi/js";
//import styles from "@/styles/contact.module.scss";
import PageTitle from "../../components/PageTitle";

interface Profile {
	name: string;
	url: string;
	icon: string;
	size?: number;
}

const discordSvgPath = "M20.317 4.3698a19.7913 19.7913 0 00-4.8851-1.5152.0741.0741 0 00-.0785.0371c-.211.3753-.4447.8648-.6083 1.2495-1.8447-.2762-3.68-.2762-5.4868 0-.1636-.3933-.4058-.8742-.6177-1.2495a.077.077 0 00-.0785-.037 19.7363 19.7363 0 00-4.8852 1.515.0699.0699 0 00-.0321.0277C.5334 9.0458-.319 13.5799.0992 18.0578a.0824.0824 0 00.0312.0561c2.0528 1.5076 4.0413 2.4228 5.9929 3.0294a.0777.0777 0 00.0842-.0276c.4616-.6304.8731-1.2952 1.226-1.9942a.076.076 0 00-.0416-.1057c-.6528-.2476-1.2743-.5495-1.8722-.8923a.077.077 0 01-.0076-.1277c.1258-.0943.2517-.1923.3718-.2914a.0743.0743 0 01.0776-.0105c3.9278 1.7933 8.18 1.7933 12.0614 0a.0739.0739 0 01.0785.0095c.1202.099.246.1981.3728.2924a.077.077 0 01-.0066.1276 12.2986 12.2986 0 01-1.873.8914.0766.0766 0 00-.0407.1067c.3604.698.7719 1.3628 1.225 1.9932a.076.076 0 00.0842.0286c1.961-.6067 3.9495-1.5219 6.0023-3.0294a.077.077 0 00.0313-.0552c.5004-5.177-.8382-9.6739-3.5485-13.6604a.061.061 0 00-.0312-.0286zM8.02 15.3312c-1.1825 0-2.1569-1.0857-2.1569-2.419 0-1.3332.9555-2.4189 2.157-2.4189 1.2108 0 2.1757 1.0952 2.1568 2.419 0 1.3332-.9555 2.4189-2.1569 2.4189zm7.9748 0c-1.1825 0-2.1569-1.0857-2.1569-2.419 0-1.3332.9554-2.4189 2.1569-2.4189 1.2108 0 2.1757 1.0952 2.1568 2.419 0 1.3332-.946 2.4189-2.1568 2.4189Z";

const LINKEDIN_URL = "https://www.linkedin.com/in/isaacholt100/";

const PROFILES: Profile[] = [
	{
		name: "LinkedIn",
		url: LINKEDIN_URL,
		icon: mdiLinkedin,
	},
	{
		name: "Discord",
		url: "https://discordapp.com/users/652929649747296266",
		icon: discordSvgPath,
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
		name: "Stack Overflow",
		url: "https://stackoverflow.com/users/14087924/isaacholt100",
		icon: mdiStackOverflow,
	},
	{
		name: "Chess.com",
		url: "https://www.chess.com/member/isaacholt100",
		icon: mdiChessPawn,
	}
];

export default function Profiles() {
	return (
		<>
			<PageTitle title="Profiles" />
			<div className="row g-2 g-md-3">
				{PROFILES.map(social => (
					<div className="col col-12 col-sm-6 col-xl-4" key={social.name}>
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