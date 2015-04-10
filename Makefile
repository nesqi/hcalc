all: calc

calc: calculator.hs
	ghc calculator.hs -o calc

test:
	quickCheck calculator.hs
