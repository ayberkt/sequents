all:
	sml -m main.cm | grep ^[^'[']

clean:
	rm sequent.x86-darwin
	rm -rf src/.cm
