all: calc

calc: calculator.hs
	ghc calculator.hs -o calc
