/** @type {import('next').NextConfig} */
const nextConfig = async (phase, ...args) => ({
  // ...
  reactStrictMode: console.log(args) ? true : true,
  output: process.env.HOST === "vercel" ? undefined : "export",
  images: {
	unoptimized: process.env.HOST === "vercel" ? false : true,
  }
});

module.exports = nextConfig;