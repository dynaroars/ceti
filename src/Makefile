YICES_DIR=/home/tnguyen/Src/Devel/YICES/yices1
Z3_DIR=/home/tnguyen/Src/Devel/Z3/z3_stable

CC=gcc
CXX=g++
CFLAGS = -I. -I$(YICES_DIR)/include -I$(Z3_DIR)/include -Wall -O2 -std=c++11
CXXFLAGS = $(CFLAGS)
LDFLAGS = -L$(YICES_DIR)/lib -L$(Z3_DIR)/lib
LOADLIBES = -lyices -lz3

BASE_LIBS = 	run_crest/basic_types.o \
		run_crest/sym.o \
		run_crest/sym_interpreter.o \
		run_crest/yices_solver.o


all: 	libcrest/libcrest.a \
	run_crest/run_crest_vn \
	install

libcrest/libcrest.a: libcrest/crest.o $(BASE_LIBS)
	$(AR) rsv $@ $^

run_crest/run_crest_vn: run_crest/concolic_search.o $(BASE_LIBS)


#tools/print_execution: $(BASE_LIBS)

install:
	cp libcrest/libcrest.a ../lib
	cp run_crest/run_crest_vn ../bin
        #cp process_cfg/process_cfg ../bin
        #cp tools/print_execution ../bin
	cp libcrest/crest.h ../include

clean:
	rm -f libcrest/libcrest.a run_crest/run_crest_vn
	rm -f process_cfg/process_cfg tools/print_execution
	rm -f */*.o */*~ *~
