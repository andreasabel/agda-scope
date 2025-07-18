# Makefile for microscopic module calculus

## Configuration
###########################################################################

# You may with to overwrite these, e.g.
# make BIN=./micmod-ghc-8.4.4 test

BIN  = ./micmod
AGDA = agda

###########################################################################

## Variables
###########################################################################

grammar		=HierMod

genagdafiles	=$(grammar)/AST.agda $(grammar)/Parser.agda
genhsfiles	=$(grammar)/Print.hs $(grammar)/ErrM.hs
gengenhsfiles	=$(grammar)/Lex.hs $(grammar)/Par.hs
genfiles        =$(genhsfiles) $(gengenhsfiles) $(genagdafiles)

agdafiles	=Library.agda Concrete.agda WellScoped.agda ScopeChecker.agda

ghcflags	=--ghc-flag=-i../haskell --ghc-flag=-Wwarn

###########################################################################

# List of goals not corresponding to file names.
.PHONY : sdist clean distclean parser

.PHONY: default
default: micmod test

.PHONY: test
test : micmod
	$(BIN) test/Example.agda
	! $(BIN) test/NotInScope.agda
	! $(BIN) test/ScopeErr.agda
	$(BIN) test/PrivateInSelf.agda
	$(BIN) test/PrivateInParent.agda
	! $(BIN) test/PrivateInSibling.agda
	$(BIN) test/Import.agda
	! $(BIN) test/ImportUnexported.agda
	! $(BIN) test/ImportUnexportedOpenPrivate.agda
	! $(BIN) test/AmbiguousViaOpenPublic.agda
	! $(BIN) test/Shadowed.agda

# Build using cabal

.PHONY: build
build : $(genfiles)
	$(AGDA) --compile --ghc-dont-call-ghc micmod.agda
	hpack && cabal build

# Just the parser

test-parser : $(grammar)/Test
	$(grammar)/Test test/Example.agda

parser : Main
	./Main test/Example.agda

Main : $(grammar)/Main.agda $(genfiles)
	$(AGDA) --compile $(ghcflags) $<

# The extra dependency $(grammar)/Test ensures that the parser is built from $(grammar).cf

micmod : micmod.agda $(genfiles) $(agdafiles)
	$(AGDA) --compile $(ghcflags) $<

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

# Rules for cleaning generated files:

clean :
	-rm -f $(grammar)/*.log $(grammar)/*.aux $(grammar)/*.hi $(grammar)/*.o $(grammar)/*.dvi *.hi *.o

distclean : clean
	-rm -f $(grammar)/Doc.* $(grammar)/Lex.* $(grammar)/Par.* $(grammar)/Layout.* $(grammar)/Skel.* $(grammar)/Print.* $(grammar)/Test.* $(grammar)/Abs.* $(grammar)/Test $(grammar)/ErrM.* $(grammar)/SharedString.* $(grammar)/ComposOp.* $(grammar)/$(grammar).dtd $(grammar)/XML.* $(grammar)/*.bak $(grammar)/AST.*
	-rmdir -p $(grammar)/
	rm -rf MAlonzo

# EOF
