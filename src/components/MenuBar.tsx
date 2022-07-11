import Image from "next/image";
import Link from "next/link";
import { useRouter } from "next/router";
import styles from "../styles/menubar.module.scss";
import personalIcon from "../../public/images/personal_icon.jpg";
import Button from "react-bootstrap/Button";
import Navbar from "react-bootstrap/Navbar";
import Nav from "react-bootstrap/Nav";
import { useEffect, useState } from "react";
import Icon from "@mdi/react";
import { mdiDotsVertical, mdiDotsVerticalCircle, mdiMenu } from "@mdi/js";

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
	const [expanded, setExpanded] = useState(false);
	useEffect(() => {
		setExpanded(false);
	}, [router.asPath]);
	return (
		<>
			<Navbar bg="black" expand="sm" variant="dark" className="py-0" fixed="top" collapseOnSelect expanded={expanded}>
				<div className="mx-auto px-2 px-md-3 container-xxl">
					<div className={styles.image_container + " me-2"}>
						<Link href="/">
							<a className="d-block h-100">
								<Image
									src={personalIcon}
									alt=""
									width={"100%"}
									height={"100%"}
									layout="intrinsic"
									className={styles.personal_icon + " rounded-circle "}
								/>
							</a>
						</Link>
					</div>
					<div className="ms-auto my-2 my-md-3 d-flex align-items-center">
						<Button variant="outline-light" aria-controls="basic-navbar-nav active" className={"p-0 d-sm-none " + styles.nav_toggle} onClick={() => setExpanded(!expanded)}>
							<Icon path={mdiDotsVertical} size={"36px"} />
						</Button>
					</div>
					<Navbar.Collapse id="basic-navbar-nav">
						<Nav className="ms-auto my-sm-2 my-md-3 mt-0 mb-2">
							{LINKS.map((link, i) => (
								<Link href={link.path} key={link.path}>
									<Button
										as="a"
										href={link.path}
										variant={(router.asPath === (link.path) ? "primary" : "outline-light")}
										className="ms-md-3 ms-sm-2 ms-0 mt-2 mt-sm-0"
									>
										{link.name}
									</Button>
								</Link>
							))}
						</Nav>
					</Navbar.Collapse>
				</div>
			</Navbar>
			<hr className="my-0 opacity-100" />
		</>
	);
}