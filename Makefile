main:
	sml -m src/main.cm

tests:
	sml -m test/test.cm

clean:
	rm sequent.x86-darwin
	rm -r src/.cm
	rm src/prop.grm.desc
	rm src/prop.grm.sig
	rm src/prop.grm.sml
	rm src/prop.lex.sml
