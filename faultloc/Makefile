OCAML_OPTIONS = \
-I /home/tnguyen/Dropbox/git/common_code/\
-I /home/tnguyen/Src/Devel/CIL/cil-1.7.3/_build/src/\
-I /home/tnguyen/Src/Devel/CIL/cil-1.7.3/_build/src/ext/\
-I /home/tnguyen/Src/Devel/CIL/cil-1.7.3/_build/src/frontc/\
-I /home/tnguyen/Src/Devel/CIL/cil-1.7.3/_build/ocamlutil/\

OCAMLC =    ocamlfind ocamlc   $(OCAML_OPTIONS)
OCAMLOPT =  ocamlfind ocamlopt $(OCAML_OPTIONS)
OCAMLDEP =  ocamldep $(OCAML_OPTIONS)
OCAMLLEX =  ocamllex 

all: fl

%.cmx: %.ml 
	@if [ -f $*.mli -a ! -f $*.cmi ] ; then $(OCAMLC) -c -g $*.mli ; fi 
	$(OCAMLOPT) -c $*.ml
	@$(OCAMLDEP) $*.ml > $*.d 

%.cmi: %.mli
	$(OCAMLC) -c -g $*.mli


# NOTE: Module order is important!  OCaml module dependencies cannot
# be cyclic, and the order presented must respect the dependency order.

FL_MODULES = \
	fl.cmo \

fl: $(FL_MODULES:.cmo=.cmx) 
	$(OCAMLOPT) -o $@ unix.cmxa str.cmxa nums.cmxa cil.cmxa cil_common.cmx vu_common.cmx $^

# FL_TEST_MODULES = \
# 	ceti_common.cmo\
# 	fl.cmo \
# 	fl_test.cmo

# fl_test: $(FL_TEST_MODULES:.cmo=.cmx) 
# 	$(OCAMLOPT) -o $@ unix.cmxa str.cmxa nums.cmxa cil.cmxa vu_common.cmx $^


# dependencies
ALL_MODULES =  $(MAIN_MODULES) 

-include $(ALL_MODULES:.cmo=.d)

clean:
	rm -f *.cmo *.cmi *.d *.cmx *.dx *.o fl
