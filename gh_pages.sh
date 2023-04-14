npm run build
# npm run export
cd out
touch .nojekyll
git init
git add *
git add --force .nojekyll
git commit -m "$1"
git branch -M master
git remote add origin https://github.com/isaacholt100/isaacholt100.github.io.git
git push -u --force origin master