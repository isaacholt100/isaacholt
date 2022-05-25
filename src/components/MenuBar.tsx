import Image from "next/image";
import Link from "next/link";
import { useRouter } from "next/router";
import styles from "../styles/menubar.module.scss";

const LINKS = [{
	name: "Home",
	path: "/",
}, {
	name: "About",
	path: "/about",
}, {
	name: "Projects",
	path: "/projects",
}, {
	name: "Contact",
	path: "/contact",
}];

export default function MenuBar() {
	const router = useRouter();
	return (
		<div>
			<nav className={styles.nav + " px-0 px-md-2 container-xxl"} >
				<Link href="/">
					<div className={styles.image_container}>
						<Image
							src="/images/personal_icon.jpg"
							alt=""
							width={64}
							height={64}
							layout="fixed"
							className={styles.personal_icon}
						/>
					</div>
				</Link>
				<div className="ms-auto d-flex align-center-items me-1" style={{marginLeft: "auto", overflow: "auto", whiteSpace: "nowrap", height: "100%", display: "flex", alignItems: "center", marginRight: 6, }}>
					{LINKS.map(link => (
						<Link href={link.path} key={link.path}>
							<a className={"btn mx-1 " + (router.asPath === (link.path) ? "btn-primary" : "btn-outline-light")}>
								{link.name}
							</a>
						</Link>
					))}
				</div>
			</nav>
			<div className={styles.nav_divider} />
		</div>
	);
}