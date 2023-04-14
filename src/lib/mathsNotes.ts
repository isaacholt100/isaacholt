import { promises as fs } from "fs";
import path from "path";

const notesDirectory = path.join(process.cwd(), "public/maths-notes");

export interface MathsNoteFile {
	name: string;
	displayName: string;
	dateModified: string;
	dateCreated: string | null; // birthtime property of fs.stat not available on all operating systems
}

const FULL_NAMES: {[key: string]: string} = {
	"amv": "Analysis in Many Variables",
	"dssc": "Data Science and Statistical Computing",
	"ent": "Elementary Number Theory",
	"math-phys": "Mathematical Physics"
}

export function capitalizeName(name: string): string {
	if (FULL_NAMES[name] !== undefined) {
		return FULL_NAMES[name];
	}
	return name.split("-").map(s => s.charAt(0).toLocaleUpperCase() + s.slice(1)).join(" ")
}

async function getMathsNotesFolders() {
	const contents = await fs.readdir(notesDirectory, { withFileTypes: true });
	return contents.filter(c => c.isDirectory());
}

export async function getMathsNotes(): Promise<MathsNoteFile[]> {
	const folders = await getMathsNotesFolders();
	return await Promise.all(
		folders
			.filter(f => !f.name.startsWith("."))
			.map(async f => {
				const stats = await fs.stat(path.join(notesDirectory, f.name, f.name + ".typ"));
				return {
					name: f.name,
					displayName: capitalizeName(f.name),
					dateModified: stats.ctime.toJSON(),
					dateCreated: stats.birthtime ? stats.birthtime.toJSON() : null,
				}
			})
	);
}

export async function getMathsNotesPaths() {
	const folders = await getMathsNotesFolders();
	return folders.map(f => f.name);
}

export async function getMathsNotePDF(name: string): Promise<string> {
	const file = await fs.readFile(path.join(notesDirectory, name, name + ".pdf"));
	return file.toString("base64");
}