target:
	cp ASTMakerUtil/* $(PATHTOAGDASOURCES)
	cd $(PATHTOAGDASOURCES); stack install; stack runhaskell ASTMaker.hs > zzztmp1
	cat $(PATHTOAGDASOURCES)/zzztmp1  | grep "split-here" | perl -pe "s|.*module\s([^\s]*)♙.*\s.*|AST/\1\n|pg" | perl -pe "s|♙|/|pg" | perl -pe "s|♖||pg" | sort | uniq | xargs mkdir -p
	cat $(PATHTOAGDASOURCES)/zzztmp1 | perl -pe "s|'|♕|pg" | perl -pe "s|\n|♔|pg"  | perl -pe "s|-- split-here :|\n|pg"  | awk '{print $$0 > "AST/"$$1".agda"}'
	find AST -iname "*.agda" | xargs perl -p -i'.bak1' -e 's|(import .*)\+(.*)|\1\.\2|pg'
	find AST -iname "*.agda" | xargs perl -p -i'.bak2' -e 's|♖|AST.|pg'
	find AST -iname "*.agda" | xargs perl -p -i'.bak3' -e 's|\t|  |pg'
	find AST -iname "*.agda" | xargs perl -p -i'.bak4' -e 's|.*(module.*)|\1|pg'
	find AST -iname "*.agda" | xargs perl -p -i'.bak5' -e 's|♙|.|pg'
	find AST -iname "*.agda" | xargs perl -p -i'.bak6' -e 's|♝|.|pg'
	find AST -iname "*.agda" | xargs perl -p -i'.bak7' -e 's|♔|\n|pg'
	find AST -iname "*.agda" | xargs perl -p -i'.bak8' -e "s|♕|'|pg"
	find AST -iname "*.bak*" | xargs rm
	perl -i -pe 's|open import AST.Agda.Syntax.Concrete.Name|import AST.Agda.Syntax.Concrete.Name|pg' AST/Agda/Syntax/Abstract/Name.agda
# cd "AST"; ls | grep "♖" | perl -pe "s|♖||pg" | awk '{system("mv ♖"$$0" "$$0)}'



