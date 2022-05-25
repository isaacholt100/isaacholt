import Image from "next/image";
import Link from "next/link";
import { useRouter } from "next/router";
import styles from "../styles/menubar.module.scss";
import personalIcon from "../../public/images/personal_icon.jpg";

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
		<div className={styles.nav_container + " position-fixed top-0 bg-black w-100"}>
			<nav className={styles.nav + " px-md-3 px-2"} >
				<div className={styles.image_container + " me-2"}>
					<Image
						src={personalIcon}
						alt=""
						width={60}
						height={60}
						layout="fixed"
						className={styles.personal_icon + " rounded-circle "}
					/>
				</div>
				<div className="ms-auto d-flex align-items-center ml-auto h-100">
					{LINKS.map((link, i) => (
						<Link href={link.path} key={link.path}>
							<a className={"btn " + (router.asPath === (link.path) ? "btn-primary" : "btn-outline-light") + " ms-2"}>
								{link.name}
							</a>
						</Link>
					))}
				</div>
			</nav>
			<hr className="mt-0 mb-2 mb-md-3 opacity-100" />
		</div>
	);
}