YICES_DIR=/home/tnguyen/Src/Devel/YICES/yices1

CC=$(CXX)
CFLAGS = -I. -I$(YICES_DIR)/include -Wall -O2 -std=c++11
CXXFLAGS = $(CFLAGS)
LDFLAGS = -L$(YICES_DIR)/lib
LOADLIBES = -lyices

BASE_LIBS = run_crest/basic_types.o run_crest/sym.o run_crest/yices_solver.o

# base/basic_types.o base/symbolic_execution.o \
#             base/symbolic_interpreter.o base/symbolic_path.o \
#             base/symbolic_predicate.o base/symbolic_expression.o \
#             base/yices_solver.o


all: run_crest/run_crest_vn

#libcrest/libcrest.a: libcrest/crest.o $(BASE_LIBS)
#	$(AR) rsv $@ $^

run_crest/run_crest_vn: run_crest/concolic_search.o $(BASE_LIBS)

#tools/print_execution: $(BASE_LIBS)

clean:
	rm -f libcrest/libcrest.a run_crest/run_crest_vn
	rm -f process_cfg/process_cfg tools/print_execution
	rm -f */*.o */*~ *~
