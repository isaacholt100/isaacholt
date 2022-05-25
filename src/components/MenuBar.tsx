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
		<div className={styles.nav_container + " position-fixed top-0 bg-black w-100"}>
			<nav className={styles.nav + " ps-md-3 ps-2 pe-md-2 pe-0 container-xxl"} >
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
				<div className="ms-auto d-flex align-items-center ml-auto h-100 overflow-auto me-1">
					{LINKS.map(link => (
						<Link href={link.path} key={link.path}>
							<a className={"btn mx-1 " + (router.asPath === (link.path) ? "btn-primary" : "btn-outline-light")} style={{zIndex: 10000}}>
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