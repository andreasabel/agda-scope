
# lagdafiles = $(wildcard *.lagda)
# latexfiles = $(wildcard *.tex)
latexfiles=

# lagdaFilesConvertedToTex= $(lagdafiles:%.lagda=latex-before-sed/%.tex)
# lagdaFilesConvertedToTexAfterSed= $(lagdafiles:%.lagda=latex/%.tex)

# generatedLatexFiles = lifting-linear-laws.blg lifting-linear-laws.bbl lifting-linear-laws.ptb lifting-linear-laws.out \
# 	lifting-linear-laws.pdf lifting-linear-laws.log

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
# allfiles=lifting-linear-laws.tex $(files) postprocess.sed $(lagdaFilesConvertedToTex)
files=

.PRECIOUS : $(lagdaFilesConvertedToTex) $(lagdaFilesConvertedToTexAfterSed)

default : lifting-linear-laws.pdf

ship : $(destdir)/lifting-linear-laws.pdf

$(destdir)/% : %
	cp -pr $< $@

pack : lifting-linear-laws.zip

# lifting-linear-laws
##################################################################

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
# note: -shell-escape essential for minted syntax highlighting
lifting-linear-laws_aux : lifting-linear-laws.tex $(files) $(latexfiles)
	$(pdflatex) lifting-linear-laws.tex
	touch $@
	$(pdflatex) lifting-linear-laws.tex
	touch $@

#	$(pdflatex) lifting-linear-laws.tex;
#	sed -e s/refsObjectOrientationInAgda//g < lifting-linear-laws.aux > $@

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
lifting-linear-laws.bbl : lifting-linear-laws_aux auto-lifting-linear-laws.bib $(latexfiles)
	bibtex lifting-linear-laws;
	$(pdflatex) lifting-linear-laws.tex


# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
lifting-linear-laws.pdf : lifting-linear-laws.bbl $(latexfiles)
	$(pdflatex) lifting-linear-laws.tex
	cp lifting-linear-laws.pdf lifting-linear-lawsx.pdf


# auto-lifting-linear-laws.bib is only defined if bibtool is present
# and $(bibliography) exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-lifting-linear-laws.aux : lifting-linear-laws_aux $(bibliography)
#	echo '\\bibstyle{jfp}' > $@
#	echo '\\bibdata{medium}' > $@
	grep -o '\\citation{.*}' lifting-linear-laws.aux > $@

auto-lifting-linear-laws.bib : auto-lifting-linear-laws.aux
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x auto-lifting-linear-laws.aux -i $(bibliography) >> $@;
endif
endif


# Templates
##################################################################

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
