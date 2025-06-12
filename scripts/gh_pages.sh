npm run build
message=$(git log -1 --pretty=%B)
cp .gitignore out/
cd out
touch .nojekyll
git init
git add *
git add --force .nojekyll
echo "message:"
echo $message
git commit -m "$message"
git branch -M master
git remote add origin https://github.com/isaacholt100/isaacholt100.github.io.git
git push --force origin master