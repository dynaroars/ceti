OCAML_OPTIONS = \
-I ../faultloc/\
-I /home/tnguyen/Dropbox/git/common_code/\
-I /home/tnguyen/Src/Devel/CIL/cil-1.7.3/_build/src/\
-I /home/tnguyen/Src/Devel/CIL/cil-1.7.3/_build/src/ext/\
-I /home/tnguyen/Src/Devel/CIL/cil-1.7.3/_build/src/frontc/\
-I /home/tnguyen/Src/Devel/CIL/cil-1.7.3/_build/ocamlutil/\

#-I /usr/local/lib/ocaml/3.12.1/cil/\

OCAMLC =    ocamlfind  ocamlc   $(OCAML_OPTIONS)
OCAMLOPT =  ocamlfind ocamlopt $(OCAML_OPTIONS)
OCAMLDEP =  ocamldep $(OCAML_OPTIONS)
OCAMLLEX =  ocamllex 

all: ceti
#fl fl_test

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

CETI_MODULES = \
	ceti.cmo \

ceti: $(CETI_MODULES:.cmo=.cmx) 
	$(OCAMLOPT) -o $@ unix.cmxa str.cmxa nums.cmxa cil.cmxa cil_common.cmx vu_common.cmx fl.cmx $^


# dependencies
ALL_MODULES =  $(MAIN_MODULES) 

-include $(ALL_MODULES:.cmo=.d)

clean:
	rm -f *.cmo *.cmi *.d *.cmx *.dx *.o ceti
