Z3_DIR=/home/tnguyen/Src/Devel/Z3/z3_stable

CC=gcc
CXX=g++
CFLAGS = -I. -I$(Z3_DIR)/include -Wall -O2 -std=c++11
CXXFLAGS = $(CFLAGS)
LDFLAGS = -L$(Z3_DIR)/lib
LOADLIBES = -lz3

BASE_LIBS = 	run_crest/basic_types.o \
		run_crest/sym.o \
		run_crest/smt_solver.o \
		run_crest/sym_interpreter.o


all: 	libcrest/libcrest.a \
	run_crest/concolic_search \
	install

libcrest/libcrest.a: libcrest/crest.o $(BASE_LIBS)
	$(AR) rsv $@ $^

run_crest/concolic_search: $(BASE_LIBS)


#tools/print_execution: $(BASE_LIBS)

install:
	cp libcrest/libcrest.a ../lib
	cp run_crest/concolic_search ../bin/run_crest_vn
        #cp process_cfg/process_cfg ../bin
        #cp tools/print_execution ../bin
	cp libcrest/crest.h ../include

clean:
	rm -f libcrest/libcrest.a run_crest/run_crest_vn
	rm -f process_cfg/process_cfg tools/print_execution
	rm -f */*.o */*~ *~
