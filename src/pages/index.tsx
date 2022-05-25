import type { NextPage } from "next"
import Head from "next/head"
import Image from "next/image"
import pageTitle from "../lib/title";

export default function Home() {
	return (
		<div>
			<Head>
				<title>{pageTitle("Home")}</title>
				<meta name="description" content="Generated by create next app" />
			</Head>
			<h1>{"Hi, I'm Isaac"}</h1>
		</div>
	)
}