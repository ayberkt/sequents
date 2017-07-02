main:
	echo "OS.Process.exit(OS.Process.failure)" | sml -m src/main.cm | grep "^[^'['.*]"

tests:
	echo "OS.Process.exit(OS.Process.failure)" | sml -m test/test.cm | grep "^[^'['.*]"

clean:
	rm -f sequent.x86-darwin
	rm -f test.x86-darwin
	rm -rf test/.cm
	rm -rf src/.cm
	rm src/prop.grm.desc
	rm src/prop.grm.sig
	rm src/prop.grm.sml
	rm src/prop.lex.sml
