ifndef LIB
	LIB := ../../lib
endif
export LIB

SOURCES = registry.ml plugin_callback.mli plugin_callback.ml plugin_manager.mli plugin_manager.ml
INCLUDES = prover_syntax
RESULT = "$(LIB)/plugin_interface"
OCAMLLDFLAGS="-a"

include ../Makefile.jstar
