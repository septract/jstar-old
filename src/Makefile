default: build

build:
	$(MAKE) -C plugin_interface
	$(MAKE) -C jimplefront
	$(MAKE) -C proverfront
	$(MAKE) -C symbfront

debug:
	$(MAKE) -C jimplefront debug
	$(MAKE) -C proverfront debug
	$(MAKE) -C symbfront debug

clean:
	$(MAKE) -C jimple_syntax clean
	$(MAKE) -C jimplefront clean
	$(MAKE) -C parsing clean
	$(MAKE) -C plugin_interface clean
	$(MAKE) -C prover clean
	$(MAKE) -C prover_syntax clean
	$(MAKE) -C proverfront clean
	$(MAKE) -C symbexe clean
	$(MAKE) -C symbexe_syntax clean
	$(MAKE) -C symbfront clean
	$(MAKE) -C utils clean

# vim:noet:
