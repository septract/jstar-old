ML=infermli unused
BYTE=$(patsubst %,%.byte,$(ML))

byte:
	ocamlbuild -cflag -g -lflag -g $(BYTE)

native:
	ocamlbuild -cflags -g,-p -lflags -g,-p $(patsubst %,%.native,$(ML))

clean:
	ocamlbuild -clean
