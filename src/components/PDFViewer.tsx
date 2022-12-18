import { useState } from "react";
// import default react-pdf entry
import { Document, Page, pdfjs } from "react-pdf";
// import pdf worker as a url, see `next.config.js` and `pdf-worker.js`

pdfjs.GlobalWorkerOptions.workerSrc = `//cdnjs.cloudflare.com/ajax/libs/pdf.js/${pdfjs.version}/pdf.worker.min.js`;

export default function PDFViewer(props: { file: any }) {
	const [numPages, setNumPages] = useState<number | null>(null);

	function onDocumentLoadSuccess({ numPages: nextNumPages }: { numPages: number }) {
		setNumPages(nextNumPages);
	}

	return (
		<div className="d-flex justify-content-center h-100">
			<Document file={props.file} onLoadSuccess={onDocumentLoadSuccess} className={"overflow-auto h-100"}>
				{Array.from({ length: numPages as number }, (_, index) => (
					<Page
						key={`page_${index + 1}`}
						pageNumber={index + 1}
						renderAnnotationLayer={false}
						renderTextLayer={false}
						width={800}
						className="mt-2 mt-md-3 rounded"
					/>
				))}
			</Document>
		</div>
	);
}
