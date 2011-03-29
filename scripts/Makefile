ML=infermli unused
BYTE=$(patsubst %,%.byte,$(ML))

byte:
	ocamlbuild -cflag -g -lflag -g $(BYTE)

clean:
	ocamlbuild -clean
