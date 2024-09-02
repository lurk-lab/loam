.PHONY : always

test : always
	bin/cl -Q -sp loam -x "(asdf:test-system \"loam\")"
