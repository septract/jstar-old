ML=infermli unused
BYTE=$(patsubst %,%.byte,$(ML))

byte:
	ocamlbuild -cflag -g $(BYTE)

clean:
	ocamlbuild -clean
