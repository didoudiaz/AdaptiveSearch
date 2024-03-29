PKG_NAME=adaptive-$(shell cat ../VERSION)

ifndef DEBUG
DEBUG = 0
endif

CC=gcc
AR=ar

#CFLAGS=-g -Wall -DDEBUG -DLOG_FILE
CFLAGS=-g -Wall -DDEBUG
#CFLAGS=-fomit-frame-pointer -O3 -DLOG_FILE -Wall
#CFLAGS=-fomit-frame-pointer -O3 -W -Wall -Wno-unused-parameter \
#	-DDEBUG=$(DEBUG) $(COMM)

CFLAGS:=$(CFLAGS) -fcommon


# for profiling

#CFLAGS=-g -Wall -DDEBUG -DLOG_FILE -pg
#CFLAGS=-O3 -pg -Wall

RANLIB=ranlib


OBJLIB = ad_solver.o tools.o main.o \
	 no_init_config.o no_cost_var.o no_exec_swap.o no_cost_swap.o \
	 no_next_i.o no_next_j.o no_displ_sol.o no_reset.o

LIBNAME=libad_solver.a

EXECS=magic-square queens alpha all-interval partit langford langford3 skolem skolem3 perfect-square costas qap smti smti-gener

%: %.c $(LIBNAME)
	$(CC) -o $@ $(CFLAGS) $< $(LIBNAME) -lm



all: $(EXECS)

cell: $(patsubst %,%-cell,$(EXECS))

$(LIBNAME): $(OBJLIB)
	rm -f $(LIBNAME) 
	$(AR) rc $(LIBNAME) $(OBJLIB)
	$(RANLIB) $(LIBNAME)


ad_solver.o: ad_solver.h

tools.o: tools.h

langford3: langford.c
skolem: langford.c
skolem3: langford.c

smti: smti-utils.c

smti-gener: smti-utils.c
	$(CC) -o $@ $(CFLAGS) smti-utils.c $(LIBNAME) -lm

qap: qap-utils.c

# distribution

ROOT_DIR=$(shell cd ..;pwd)

distdir=/tmp
distpath=$(distdir)/$(PKG_NAME)

dist: check_doc $(PKG_NAME).tar.gz

check_doc:
	(cd ../doc; make all)

$(PKG_NAME).tar.gz: copy_dist_tree
	(cd $(distdir); tar cf $(ROOT_DIR)/src/$(PKG_NAME).tar $(PKG_NAME))
	gzip -f $(PKG_NAME).tar
	-rm -rf $(distpath)
	@banner="$(PKG_NAME).tar.gz is ready for distribution"; \
	dashes=`echo "$$banner" | sed s/./=/g`; \
	echo "$$dashes"; \
	echo "$$banner"; \
	echo "$$dashes"


# below we use 2 cd in case distpath is not an absolute path like '.'
copy_dist_tree:
	-rm -rf $(distpath)
	mkdir -p $(distpath)
	while read f;do files="$$files $$f"; done <DISTRIB_FILES; \
	(cd ..;tar cf - $$files | (cd $(ROOT_DIR)/src;cd $(distpath); tar xf -))



BENCH=$(patsubst %,BENCH-RESULT-%.txt,$(EXECS))

# create SQL files from txt
%.sql: %.txt Makefile
	sed -e 's/[ 	][ 	]*/,/g' < $< > $@

BENCH.sql: $(BENCH:.txt=.sql)
	cat $+ > $@

# cleaning

clean:
	rm -f *.o *.a *.d *~ $(EXECS)
