ifndef LIB
	LIB := ../../lib
endif
export LIB

SOURCES = plugin.ml plugin_callback.mli registry.ml plugin_callback.ml plugin_manager.mli plugin_manager.ml
INCLUDES = prover_syntax utils
RESULT = "$(LIB)/plugin_interface"
OCAMLLDFLAGS="-a"

include ../Makefile.jstar
