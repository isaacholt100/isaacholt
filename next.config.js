/** @type {import('next').NextConfig} */
const nextConfig = {
	reactStrictMode: true,
	output: process.env.HOST === "vercel" ? undefined : "export",
	images: {
		unoptimized: process.env.HOST === "vercel" ? false : true,
	}
};

module.exports = nextConfig;