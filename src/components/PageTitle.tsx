export default function PageTitle(props: { title: string }) {
	return (
		<>
			<h1 className="my-0">{props.title}</h1>
			<hr className="border-3 border-light opacity-50 my-2 my-md-3" />
		</>
	);
}