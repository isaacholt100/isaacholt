import Link from "next/link";
import styles from "../styles/Home.module.scss";

interface MainLink {
    name: string;
    path: string;
}

const MAIN_LINKS: MainLink[] = [{
    name: "About Me",
    path: "/about"
}, {
    name: "My Projects",
    path: "/projects",
}, {
    name: "Contact Me",
    path: "/socials"
}];

export default function Home() {
    return (
        <div className={styles.container}>
            <h1>{"Hi, I'm Isaac"}</h1>
            <h4>Mathematics student at Durham University</h4>
            <div className="row g-2 g-md-3 mt-auto">
                {MAIN_LINKS.map(link => (
                    <div key={link.path} className="col col-12 col-sm-4">
                        <Link href={link.path} role="button" className="btn btn-lg btn-outline-primary w-100">
                            {link.name}
                        </Link>
                    </div>
                ))}
            </div>
        </div>
    );
}