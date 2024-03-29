import MenuBar from "../components/MenuBar";
import "../styles/globals.scss";
import { Metadata, Viewport } from "next";

export const metadata: Metadata = {
    title: {
        default: "Isaac Holt",
        template: "%s | Holt",
    },
    generator: "Isaac Holt",
    applicationName: "Isaac Holt",
    keywords: ["Isaac Holt", "personal website", "portfolio"],
    description: "Isaac Holt's personal website",
};

export const viewport: Viewport = {
    colorScheme: "dark",
    themeColor: "#000",
};

export default function RootLayout({ children }: { children: React.ReactNode }) {
    return (
        <html lang="en">
            <body>
                <MenuBar />
                <div className="mx-auto p-2 p-md-3 container-xxl">
                    {children}
                </div>
            </body>
        </html>
    );
}