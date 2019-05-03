# Makefile for ModuleCalculus

## Variables
###########################################################################

grammar=ModuleCalculus

# Files of solution.  Add more files as needed.
files=core.hs $(grammar).cf Makefile

agda=agda
agdafiles=Library.agda $(grammar)/AST.agda $(grammar)/Parser.agda Concrete.agda WellScoped.agda ScopeChecker.agda
genhsfiles=$(grammar)/Print.hs $(grammar)/ErrM.hs
gengenhsfiles=$(grammar)/Lex.hs $(grammar)/Par.hs
ghcflags=--ghc-flag=-i../haskell --ghc-flag=-Wwarn

###########################################################################

# List of goals not corresponding to file names.
.PHONY : sdist clean distclean test

test : mocal
	! ./mocal test/Example.agda
	! ./mocal test/ScopeErr.agda
	./mocal test/Tiny.agda

# The extra dependency $(grammar)/Test ensures that the parser is built from $(grammar).cf

mocal : mocal.agda $(agdafiles) $(genhsfiles) $(gengenhsfiles)
	$(agda) --compile $(ghcflags) $<

test-core : core
	./core test/Example.agda

core : $(files) $(grammar)/Test
	ghc --make core.hs -o core

# Rules to build the parser:

$(grammar)/Test.hs $(grammar)/Lex.x $(grammar)/Par.y $(genhsfiles) $(grammar)/AST.agda $(grammar)/Parser.agda : $(grammar).cf Makefile
	bnfc --haskell --agda -d $<

%.hs : %.y
	happy -gcai $<
#	happy --ghc --coerce --array --info $<

%.hs : %.x
	alex --ghc $<

$(grammar)/Test : $(grammar)/Test.hs $(grammar)/Par.hs $(grammar)/Lex.hs
	ghc --make $< -o $@

# Rules for shipping.

sdist : core.tar.gz

tmpdir := $(shell mktemp -d)
core.tar.gz : $(files)
	mkdir $(tmpdir)/core
	cp $^ $(tmpdir)/core/
	tar -C $(tmpdir) -czhf $@ core

# Rules for cleaning generated files:

clean :
	-rm -f $(grammar)/*.log $(grammar)/*.aux $(grammar)/*.hi $(grammar)/*.o $(grammar)/*.dvi *.hi *.o

distclean : clean
	-rm -f $(grammar)/Doc.* $(grammar)/Lex.* $(grammar)/Par.* $(grammar)/Layout.* $(grammar)/Skel.* $(grammar)/Print.* $(grammar)/Test.* $(grammar)/Abs.* $(grammar)/Test $(grammar)/ErrM.* $(grammar)/SharedString.* $(grammar)/ComposOp.* $(grammar)/$(grammar).dtd $(grammar)/XML.* $(grammar)/*.bak $(grammar)/AST.*
	-rmdir -p $(grammar)/
	-rm -f core.tar.gz core

# EOF
