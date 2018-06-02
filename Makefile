build:
	cabal build
	./dist/build/site/site rebuild

run:
	./dist/build/site/site watch

clean:
	./dist/build/site/site clean

push: 
	cd _site && git init && git remote add origin https://github.com/ssomayyajula/ssomayyajula.github.io.git && git add --all && git commit -m "new post" && git push origin master --force
