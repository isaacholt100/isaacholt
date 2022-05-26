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
			<Navbar bg="black" expand="sm" variant="dark" className="px-md-3 px-2 py-0" fixed="top" collapseOnSelect expanded={expanded}>
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
				<Navbar.Toggle className="border-primary text-white p-0"  style={{height: 40, width: 40,}} onClick={() => setExpanded(!expanded)}>
					<Icon path={mdiDotsVertical} size={"36px"} />
				</Navbar.Toggle>
				<Navbar.Collapse id="basic-navbar-nav">
					<Nav className="ms-auto my-sm-2 my-md-3 mt-0 mb-2">
						{LINKS.map((link, i) => (
							<Link href={link.path} key={link.path}>
								<Button
									as="a"
									variant={(router.asPath === (link.path) ? "primary" : "outline-light")}
									className="ms-md-3 ms-sm-2 ms-0 mt-2 mt-sm-0"
								>
									{link.name}
								</Button>
							</Link>
						))}
					</Nav>
				</Navbar.Collapse>
			</Navbar>
			<hr className="my-0 opacity-100" />
		</>
	);
}