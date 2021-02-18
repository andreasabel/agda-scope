# Makefile for microscopic module calculus

## Variables
###########################################################################

grammar		=HierMod

genagdafiles	=$(grammar)/AST.agda $(grammar)/Parser.agda
genhsfiles	=$(grammar)/Print.hs $(grammar)/ErrM.hs
gengenhsfiles	=$(grammar)/Lex.hs $(grammar)/Par.hs
genfiles        =$(genhsfiles) $(gengenhsfiles) $(genagdafiles)

agdafiles	=Library.agda Concrete.agda WellScoped.agda ScopeChecker.agda

agda		=agda
ghcflags	=--ghc-flag=-i../haskell --ghc-flag=-Wwarn

###########################################################################

# List of goals not corresponding to file names.
.PHONY : sdist clean distclean test parser

test : micmod
	./micmod test/Example.agda
	! ./micmod test/NotInScope.agda
	! ./micmod test/ScopeErr.agda
	./micmod test/PrivateInSelf.agda
	./micmod test/PrivateInParent.agda
	! ./micmod test/PrivateInSibling.agda
	./micmod test/Import.agda
	! ./micmod test/ImportUnexported.agda
	! ./micmod test/ImportUnexportedOpenPrivate.agda
	! ./micmod test/Shadowed.agda

# Just the parser

test-parser : $(grammar)/Test
	$(grammar)/Test test/Example.agda

parser : Main
	./Main test/Example.agda

Main : $(grammar)/Main.agda $(genfiles)
	$(agda) --compile $(ghcflags) $<

# The extra dependency $(grammar)/Test ensures that the parser is built from $(grammar).cf

micmod : micmod.agda $(genfiles) $(agdafiles)
	$(agda) --compile $(ghcflags) $<

# Rules to build the parser:

$(grammar)/Test.hs $(grammar)/Lex.x $(grammar)/Par.y $(genhsfiles) $(genagdafiles) $(grammar)/Main.agda : $(grammar).cf
	bnfc --agda -d $<

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
