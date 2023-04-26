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