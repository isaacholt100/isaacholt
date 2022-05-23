import Image from "next/image";
import Link from "next/link";
import { useRouter } from "next/router";
import styles from "../styles/menubar.module.css";

const LINKS = ["Home", "About", "Projects"];

export default function MenuBar() {
	const router = useRouter();
	console.log(router)
	return (
		<div>
			<nav className={styles.nav}>
				<Link href="/">
					<div className={styles.image_container}>
						<Image src="/images/personal_icon.jpg" alt="" width={64} height={64} layout="fixed" className={styles.personal_icon} />
					</div>
				</Link>
				<div style={{marginLeft: "auto", overflow: "auto", whiteSpace: "nowrap", paddingRight: "12px", height: "100%", display: "flex", alignItems: "center"}}>
					{LINKS.map(link => (
						<Link href={"/" + link.toLowerCase()} key={link}>
							<button className={"btn " + (router.asPath === ("/" + link.toLowerCase()) ? "btn-info" : "btn-outline-light")} style={{marginLeft: 12}}>
								{link}
							</button>
						</Link>
					))}
				</div>
			</nav>
			<div className={styles.nav_divider} />
		</div>
	);
}