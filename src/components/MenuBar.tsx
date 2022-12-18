import Image from "next/image";
import { useRouter } from "next/router";
import Link from "next/link";
import styles from "../styles/menubar.module.scss";
import personalIcon from "../../public/images/personal_icon.jpg";
import Button from "react-bootstrap/Button";
import Navbar from "react-bootstrap/Navbar";
import Nav from "react-bootstrap/Nav";
import { useEffect, useState } from "react";
import Icon from "@mdi/react";
import { mdiClose, mdiDotsVertical, mdiDotsVerticalCircle, mdiMenu } from "@mdi/js";
import { Offcanvas } from "react-bootstrap";

const LINKS = [
	{
		name: "Home",
		path: "/",
	},
	{
		name: "About",
		path: "/about",
	},
	{
		name: "Projects",
		path: "/projects",
	},
	{
		name: "Maths",
		path: "/maths",
	},
	{
		name: "Socials",
		path: "/socials",
	},
];

function ImageHomeLink(props: { className?: string }) {
	return (
		<div className={styles.image_container + " me-2" + (props.className ? " " + props.className : "")}>
			<Link href="/" className="d-block h-100 btn btn-primary rounded-circle border-0 position-relative p-0" style={{ backgroundColor: "transparent" }}>
				<Image
					src={personalIcon}
					alt=""
					className={"rounded-circle"}
					priority
					fill
					sizes="52px"
				/>
			</Link>
		</div>
	);
}

export default function MenuBar() {
	const router = useRouter();
	const [expanded, setExpanded] = useState(false);
	useEffect(() => {
		setExpanded(false);
	}, [router.asPath]);
	return (
		<>
			<Navbar bg="black" expand="sm" variant="dark" className="py-0" fixed="top" expanded={expanded} onSelect={() => setExpanded(false)} onToggle={e => setExpanded(e)}>
				<div className="mx-auto px-2 px-md-3 container-xxl">
					<ImageHomeLink />
					<div className="ms-auto my-2 my-md-3 d-flex align-items-center">
						<Button variant="outline-light" aria-controls="basic-navbar-nav active" className={"p-0 d-sm-none " + styles.nav_toggle} onClick={() => setExpanded(true)}>
							<Icon path={mdiDotsVertical} size={"36px"} />
						</Button>
					</div>
					<Navbar.Offcanvas id="basic-navbar-nav" placement="start">
						<div className="d-flex align-items-center px-2">
							<ImageHomeLink className="d-sm-none" />
							<Button variant="outline-light" aria-controls="basic-navbar-nav active" className={"p-0 d-sm-none ms-auto my-2 " + styles.nav_toggle} onClick={() => setExpanded(false)}>
								<Icon path={mdiClose} size={"36px"} />
							</Button>
						</div>
						<hr className="m-0 mb-0 opacity-100 d-sm-none" />
						<Offcanvas.Body className="p-2 p-sm-0">
							<Nav className="ms-auto my-sm-2 my-md-3 mt-0 mb-2">
								{LINKS.map((link, i) => (
									<Link href={link.path} key={link.path} legacyBehavior passHref>
										<Button
											as="a"
											variant={(router.asPath === (link.path) ? "primary" : "outline-light")}
											className={"ms-md-3 ms-sm-2 ms-0 mt-sm-0" + (i !== 0 ? " mt-2" : "")}
										>
											{link.name}
										</Button>
									</Link>
								))}
							</Nav>
						</Offcanvas.Body>
					</Navbar.Offcanvas>
				</div>
			</Navbar>
			<hr className="my-0 opacity-100" />
		</>
	);
}