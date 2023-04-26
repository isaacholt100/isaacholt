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
import { mdiClose, mdiDotsVertical } from "@mdi/js";
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

const IMAGE_SIZE = 52;

let colour = [0, 255, 94];

function hue(c_max: number, delta: number, r: number, g: number, b: number) {
	if (delta == 0) {
		return 0;
	} else if (c_max == r) {
		return 60 * (((g - b) / delta) % 6);
	} else if (c_max == g) {
		return 60 * (((b - r) / delta) + 2);
	} else {
		return 60 * (((r - g) / delta) + 4);
	}
}



function hsv(r: number, g: number, b: number) {
	r = r / 255;
	g = g / 255;
	b = b / 255;
	const c_max = Math.max(...colour);
	const c_min = Math.min(...colour);
	const delta = c_max - c_min;
	return hue(c_max, delta, r, g, b);
}

function ImageHomeLink(props: { className?: string }) {
	return (
		<div className={" me-2" + (props.className ? " " + props.className : "")} style={{marginLeft: -4, height: IMAGE_SIZE, width: IMAGE_SIZE}}>
			<Link href="/" className="d-block h-100 btn btn-primary rounded-circle border-0 position-relative p-0" style={{ backgroundColor: "transparent" }}>
				<Image
					src={personalIcon}
					alt=""
					className={"rounded-circle"}
					priority
					fill
					sizes={IMAGE_SIZE + "px"}
					//style={{filter: "hue-rotate(" + hsv(0, 255, 94) + "deg)"}}
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