main:
	sml -m src/main.cm

tests:
	sml -m test/test.cm

clean:
	rm -f sequent.x86-darwin
	rm -f test.x86-darwin
	rm -rf test/.cm
	rm -rf src/.cm
	rm src/prop.grm.desc
	rm src/prop.grm.sig
	rm src/prop.grm.sml
	rm src/prop.lex.sml
