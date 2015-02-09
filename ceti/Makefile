OCAML_OPTIONS = \
-I /usr/local/lib/ocaml/3.12.1/cil/\
-I /home/tnguyen/Dropbox/git/common_python/



OCAMLC =    ocamlfind  ocamlc   $(OCAML_OPTIONS)
OCAMLOPT =  ocamlfind ocamlopt $(OCAML_OPTIONS)
OCAMLDEP =  ocamldep $(OCAML_OPTIONS)
OCAMLLEX =  ocamllex 

all: ceti_common fl fl_test tf

# %.cmo: %.ml 
# 	@if [ -f $*.mli -a ! -f $*.cmi ] ; then $(OCAMLC) -c -g $*.mli ; fi 
# 	$(OCAMLC) -c -g $*.ml
# 	@$(OCAMLDEP) $*.ml > $*.d 

%.cmx: %.ml 
	@if [ -f $*.mli -a ! -f $*.cmi ] ; then $(OCAMLC) -c -g $*.mli ; fi 
	$(OCAMLOPT) -c $*.ml
	@$(OCAMLDEP) $*.ml > $*.d 

%.cmi: %.mli
	$(OCAMLC) -c -g $*.mli

# %.ml: %.mll
# 	$(OCAMLLEX) $*.mll

# NOTE: Module order is important!  OCaml module dependencies cannot
# be cyclic, and the order presented must respect the dependency order.

CETI_COMMON_MODULES = \
	ceti_common.cmo \

ceti_common: $(CETI_COMMON_MODULES:.cmo=.cmx) 
	$(OCAMLOPT) -o $@ unix.cmxa str.cmxa nums.cmxa cil.cmxa vu_common.cmx $^


FL_MODULES = \
	ceti_common.cmo\
	fl.cmo \

fl: $(FL_MODULES:.cmo=.cmx) 
	$(OCAMLOPT) -o $@ unix.cmxa str.cmxa nums.cmxa cil.cmxa vu_common.cmx $^

FL_TEST_MODULES = \
	ceti_common.cmo\
	fl.cmo \
	fl_test.cmo

fl_test: $(FL_TEST_MODULES:.cmo=.cmx) 
	$(OCAMLOPT) -o $@ unix.cmxa str.cmxa nums.cmxa cil.cmxa vu_common.cmx $^


TF_MODULES = \
	ceti_common.cmo\
	fl.cmo \
	tf.cmo \

tf: $(TF_MODULES:.cmo=.cmx) 
	$(OCAMLOPT) -o $@ unix.cmxa str.cmxa nums.cmxa cil.cmxa vu_common.cmx $^


# dependencies
ALL_MODULES =  $(MAIN_MODULES) 

-include $(ALL_MODULES:.cmo=.d)

clean:
	rm -f *.cmo *.cmi *.d *.cmx *.dx *.o ceti_common fl tf 
