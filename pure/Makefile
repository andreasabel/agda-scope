# Makefile for microscopic module calculus

## Variables
###########################################################################

grammar         = src/HierMod

genhsfiles      = $(grammar)/Print.hs
gengenhsfiles   = $(grammar)/Lex.hs $(grammar)/Par.hs
genfiles        = $(genhsfiles) $(gengenhsfiles)

ghcflags        = --ghc-flag=-i../haskell --ghc-flag=-Wwarn

###########################################################################

# List of goals not corresponding to file names.
.PHONY : sdist clean distclean test parser

main=Main

test : $(main)
	@echo "---------------------------------------------------------------------------"
	./$(main) test/Example.agda
	@echo "---------------------------------------------------------------------------"
	! ./$(main) test/NotInScope.agda
	@echo "---------------------------------------------------------------------------"
	! ./$(main) test/ScopeErr.agda
	@echo "---------------------------------------------------------------------------"
	! ./$(main) test/ShadowedByAmbiguous.agda
	@echo "---------------------------------------------------------------------------"
	! ./$(main) test/Shadowed.agda
	@echo "---------------------------------------------------------------------------"
	! ./$(main) test/ShadowPrivate.agda


Main : Main.hs src/ScopeChecker.hs $(genfiles)
	ghc -i. -isrc $<

# Just the parser

test-parser : $(grammar)/Test
	$(grammar)/Test test/Example.agda

# Rules to build the parser:

$(grammar)/Test.hs $(grammar)/Lex.x $(grammar)/Par.y $(genhsfiles) : $(grammar).cf
	bnfc --haskell -o src -d $<

%.hs : %.y
	happy -gcai $<
#	happy --ghc --coerce --array --info $<

%.hs : %.x
	alex --ghc $<

$(grammar)/Test : $(grammar)/Test.hs $(grammar)/Par.hs $(grammar)/Lex.hs
	ghc --make $< -o $@

# Rules for shipping.

sdist : pure.tar.gz

tmpdir := $(shell mktemp -d)
pure.tar.gz : $(files)
	mkdir $(tmpdir)/pure
	cp $^ $(tmpdir)/pure/
	tar -C $(tmpdir) -czhf $@ pure

# Rules for cleaning generated files:

clean :
	-rm -f $(grammar)/*.log $(grammar)/*.aux $(grammar)/*.hi $(grammar)/*.o $(grammar)/*.dvi *.hi *.o

distclean : clean
	-rm -f $(grammar)/Doc.* $(grammar)/Lex.* $(grammar)/Par.* $(grammar)/Layout.* $(grammar)/Skel.* $(grammar)/Print.* $(grammar)/Test.* $(grammar)/Abs.* $(grammar)/Test $(grammar)/ErrM.* $(grammar)/SharedString.* $(grammar)/ComposOp.* $(grammar)/$(grammar).dtd $(grammar)/XML.* $(grammar)/*.bak $(grammar)/AST.*
	-rmdir -p $(grammar)/
	-rm -f pure.tar.gz pure

# EOF
