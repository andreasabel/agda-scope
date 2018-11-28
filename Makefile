target:
	cp ASTMakerUtil/* $(PATHTOAGDASOURCES)
	cd $(PATHTOAGDASOURCES); stack install; stack runhaskell ASTMaker.hs > zzztmp1
	cat $(PATHTOAGDASOURCES)/zzztmp1 | perl -pe "s|'|♕|pg" | perl -pe "s|\n|♔|pg"  | perl -pe "s|-- split-here :|\n|pg"  | awk '{print $$0 > "AST/"$$2".agda"}'
	perl -p -i'.bak1' -e 's|♕|P|pg' AST/*.agda
	perl -p -i'.bak2' -e 's|♔|\n|pg' AST/*.agda
	perl -p -i'.bak3' -e 's|(import .*)\+(.*)|\1\.\2|pg' AST/*.agda
	perl -p -i'.bak4' -e 's|♖|AST.|pg' AST/*.agda
	perl -p -i'.bak6' -e 's|\t|  |pg' AST/*.agda
	rm AST/*.bak*
	cd "AST"; ls | grep "♖" | perl -pe "s|♖||pg" | awk '{system("mv ♖"$$0" "$$0)}'

# perl -i.bak -pe 's|open import AgdaSyntaxConcreteName|import AgdaSyntaxConcreteName|pg' ZTHOUT2/AgdaSyntaxAbstractName.agda
