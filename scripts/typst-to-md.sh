# mkdir src/app/maths/notes/$1
pandoc -i public/maths-notes/year-$2/$1/$1.typ -o src/app/maths/notes/$1/page.md