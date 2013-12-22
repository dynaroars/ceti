OCAML_OPTIONS = \
-I /usr/local/lib/ocaml/3.11.2/cil/

OCAMLC =        ocamlc   $(OCAML_OPTIONS)
OCAMLOPT =      ocamlopt $(OCAML_OPTIONS)
OCAMLDEP =      ocamldep $(OCAML_OPTIONS)
OCAMLLEX =      ocamllex 

all: fault_localization testcase_generation

%.cmo: %.ml 
	@if [ -f $*.mli -a ! -f $*.cmi ] ; then $(OCAMLC) -c -g $*.mli ; fi 
	$(OCAMLC) -c -g $*.ml
	@$(OCAMLDEP) $*.ml > $*.d 

%.cmx: %.ml 
	@if [ -f $*.mli -a ! -f $*.cmi ] ; then $(OCAMLC) -c -g $*.mli ; fi 
	$(OCAMLOPT) -c $*.ml
	@$(OCAMLDEP) $*.ml > $*.d 

%.cmi: %.mli
	$(OCAMLC) -c -g $*.mli

%.ml: %.mll
	$(OCAMLLEX) $*.mll

# NOTE: Module order is important!  OCaml module dependencies cannot
# be cyclic, and the order presented must respect the dependency order.

FAULT_LOCALIZATION_MODULES = \
	cil_common.cmo \
	fault_localization.cmo \

fault_localization: $(FAULT_LOCALIZATION_MODULES:.cmo=.cmx) 
	$(OCAMLOPT) -o $@ unix.cmxa str.cmxa nums.cmxa cil.cmxa $^


TESTCASE_GENERATION_MODULES = \
	cil_common.cmo \
	testcase_generation.cmo \

testcase_generation: $(TESTCASE_GENERATION_MODULES:.cmo=.cmx) 
	$(OCAMLOPT) -o $@ unix.cmxa str.cmxa nums.cmxa cil.cmxa $^


# dependencies
ALL_MODULES = \
  $(MAIN_MODULES) 

-include $(ALL_MODULES:.cmo=.d)

clean:
	rm -f *.cmo *.cmi *.d *.cmx *.dx *.o vu
