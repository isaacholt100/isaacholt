import createMDX from "@next/mdx";
import remarkMath from "remark-math";
import remarkGfm from "remark-gfm";
import rehypeKatex from "rehype-katex";
import rehypeHighlight from "rehype-highlight";
import remarkFlattenListItem from "mdast-flatten-listitem-paragraphs";

/** @type {import('next').NextConfig} */
const nextConfig = {
	reactStrictMode: true,
	output: process.env.HOST === "vercel" ? undefined : "export",
	images: {
		unoptimized: process.env.HOST === "vercel" ? false : true,
	},
    pageExtensions: ["js", "jsx", "mdx", "ts", "tsx", "md"]
};

const withMDX = createMDX({
    extension: /\.mdx?$/,
    options: {
        remarkPlugins: [remarkMath, remarkGfm],
        rehypePlugins: [rehypeKatex, rehypeHighlight],
    },
});

export default withMDX(nextConfig);