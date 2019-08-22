# Makefile to create docs

.PHONY: default deploy emptyDocsFolder

# Make contents locally
default :
	make -C notes

# Main goal:
# - make contents
# - copy contents to docs folder

docs : deploy emptyDocsFolder
	cp notes/*.pdf docs/notes/
#	cp -r src-cbpv/html docs/html-cbpv


# Make contents on travis

deploy :
	make -C notes deploy

# Provide empty docs folder
emptyDocsFolder :
	mkdir -p docs/notes
	rm -f docs/notes/*.pdf
#	rm -rf docs/html


# EOF
