
# lagdafiles = $(wildcard *.lagda)
# latexfiles = $(wildcard *.tex)
latexfiles=

# lagdaFilesConvertedToTex= $(lagdafiles:%.lagda=latex-before-sed/%.tex)
# lagdaFilesConvertedToTexAfterSed= $(lagdafiles:%.lagda=latex/%.tex)

# generatedLatexFiles = modcal.blg modcal.bbl modcal.ptb modcal.out \
# 	modcal.pdf modcal.log

# agdaifiles = $(wildcard *.agdai)

#gentexfiles= $(lagdafiles:.lagda=.tex)

destdir=$(HOME)/public_html/notes

#pdflatex=pdflatex -shell-escape -halt-on-error
pdflatex=pdflatex -halt-on-error

bibtool=bibtool -- 'preserve.key.case = ON' \
	  -- 'check.double = ON' \
	  -- 'check.double.delete = ON' \
	  -- 'delete.field = { abstract }' \
	  -- 'delete.field = { dvi }' \
	  -- 'delete.field = { postscript }' \
	  -- 'delete.field = { pdf }' \
	  -- 'delete.field = { available }' \
	  -- 'delete.field = { isbn }'
#	  -- 'delete.field = { note }'
#	  -- 'delete.field = { editor }'
#	  -- 'delete.field = { doi }'

bibliography=medium.bib
sedfile=postprocess.sed
stylefile=agda.sty

agda=time agda -v profile:10

mainlatexfiles=$(wildcard *.tex)

# files=postprocessAuxFile.sed \
# 	latex/agda.sty $(mainlatexfiles) \
# 	$(lagdaFilesConvertedToTexAfterSed) \
# 	Makefile
# allfiles=modcal.tex $(files) postprocess.sed $(lagdaFilesConvertedToTex)
files=

.PRECIOUS : $(lagdaFilesConvertedToTex) $(lagdaFilesConvertedToTexAfterSed)

default : agdaShadowing.pdf

all : agdaShadowing.pdf modcal.pdf

deploy : agdaShadowing.pdf

ship : $(destdir)/modcal.pdf

$(destdir)/% : %
	cp -pr $< $@

pack : modcal.zip

# modcal
##################################################################

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
# note: -shell-escape essential for minted syntax highlighting
modcal_aux : modcal.tex $(files) $(latexfiles)
	$(pdflatex) modcal.tex
	touch $@
	$(pdflatex) modcal.tex
	touch $@

#	$(pdflatex) modcal.tex;
#	sed -e s/refsObjectOrientationInAgda//g < modcal.aux > $@

softclean :
	rm -f $(lagdaFilesConvertedToTex)
	rm -f $(lagdaFilesConvertedToTexAfterSed)
	rm -f $(generatedLatexFiles)
	rm -f $(agdaifiles)
#	rm -f $(lagdafiles:%.lagda=%.tex)

#	rm -f $(gentexfiles)
#	rm -f $(genlatexfiles)
#	rm -f $(agdaifiles)

clean : softclean
	rm -rf $(furtherGeneratedFiles)

#	rm -rf $(furthergenfiles)


# then, run bibtex
modcal.bbl : modcal_aux auto-modcal.bib $(latexfiles)
	bibtex modcal;
	$(pdflatex) modcal.tex


# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
modcal.pdf : modcal.bbl $(latexfiles)
	$(pdflatex) modcal.tex
	cp modcal.pdf modcalx.pdf


# auto-modcal.bib is only defined if bibtool is present
# and $(bibliography) exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-modcal.aux : modcal_aux $(bibliography)
#	echo '\\bibstyle{jfp}' > $@
#	echo '\\bibdata{medium}' > $@
	grep -o '\\citation{.*}' modcal.aux > $@

auto-modcal.bib : auto-modcal.aux
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x auto-modcal.aux -i $(bibliography) >> $@;
endif
endif


# Templates
##################################################################

%.pdf : %.tex
	xelatex -halt-on-error $<

PANDOC_OPTS=-s -V monofont='DejaVu Sans Mono'
#  -V mainfont='DejaVu Sans Mono'

%.tex : %.md Makefile %.yaml
	cat $*.yaml $< | pandoc $(PANDOC_OPTS) -o $@

latex-before-sed/%.tex : %.lagda
	$(agda) --latex --latex-dir=latex-before-sed $<

latex/%.tex : latex-before-sed/%.tex $(sedfile)
	sed --file=$(sedfile) < $< > $@

# latex/%.tex : %.lagda $(sedfile)
# #	agda -i. -i$(agda_iolibnew) -i$(agda_stdlib) --latex --latex-dir=latex $<
# 	agda --latex --latex-dir=latex $<
# 	sed -i.bak --file=$(sedfile) $@

# #	agda -i. -i$(agda_iolibnew) -i$(agda_stdlib) --latex $<

#%.tex : latex/%.tex
#	sed --file=$(sedfile) < $< > $@


# EOF
