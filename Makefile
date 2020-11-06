# Makefile to create docs

.PHONY: default deploy emptyDocsFolder

# Make contents locally
default :
	make -C notes

# Main goal:
# - make contents
# - copy contents to docs folder

docs : deploy emptyDocsFolder README.md Makefile
	cp -p notes/*.pdf docs/notes/
	pandoc -s -o docs/index.html README.md
# -f gfm --metadata title="Agda Scoping"
#	tree -H '.' docs -o docs/index.html



# Make contents on travis

deploy :
	make -C notes deploy

# Provide empty docs folder
emptyDocsFolder :
	mkdir -p docs/notes
	rm -f docs/notes/*.pdf
#	rm -rf docs/html


# EOF
