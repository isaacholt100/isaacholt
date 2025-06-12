import { generateMetadataFile } from "./mathsNotes";

generateMetadataFile()
  .then(() => {
    console.log("Metadata file generated successfully.");
  })
  .catch((err: any) => {
    console.error("Error generating metadata file:", err);
    process.exit(1);
  });