/** @type {import('next').NextConfig} */
const nextConfig = async (phase, ...args) => ({
  // ...
  reactStrictMode: console.log(args) ? true : true,
  output: process.env.HOST === "vercel" ? undefined : "export",
  images: {
	unoptimized: true,
  }
});

module.exports = nextConfig;