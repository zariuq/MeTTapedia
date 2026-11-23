CC ?= gcc
CFLAGS ?= -O3 -march=native -fno-tree-vectorize -fno-tree-loop-distribute-patterns -flto -Wall -Wextra -Werror
MICROMATH ?= ref
CESTA ?= ../cesta/build/cesta

BINS = test_tcalc mm0_tcalc mmb_tcalc hol_tcalc mg_tcalc dk_tcalc tcalc_compile diff_micromath

.PHONY: all check cesta-check clean

all: $(BINS)

test_tcalc: tcalc.c tcalc.h test_tcalc.c
	$(CC) $(CFLAGS) tcalc.c test_tcalc.c -o $@

mm0_tcalc: tcalc.c tcalc.h mm0_spec.h mm0_tcalc.c
	$(CC) $(CFLAGS) tcalc.c mm0_tcalc.c -o $@

mmb_tcalc: tcalc.c tcalc.h mm0_spec.h mmb_tcalc.c
	$(CC) $(CFLAGS) tcalc.c mmb_tcalc.c -o $@

hol_tcalc: tcalc.c tcalc.h hol_tcalc.c
	$(CC) $(CFLAGS) tcalc.c hol_tcalc.c -o $@

mg_tcalc: tcalc.c tcalc.h mg_tcalc.c
	$(CC) $(CFLAGS) tcalc.c mg_tcalc.c -o $@

dk_tcalc: tcalc.c tcalc.h dk_tcalc.c
	$(CC) $(CFLAGS) tcalc.c dk_tcalc.c -o $@

tcalc_compile: tcalc_compile.c tcalc.h
	$(CC) -O3 -march=native -Wall -Wextra -Werror tcalc_compile.c -o $@

micromath_tcalc_gen.h: tcalc_compile
	./tcalc_compile

diff_micromath: diff_micromath.c tcalc.c micromath_tcalc.c micromath_tcalc_gen.h
	$(CC) -O3 -march=native -flto -D_GNU_SOURCE -c $(MICROMATH)/kernel.c -I$(MICROMATH) -o micromath_kernel.o
	$(CC) $(CFLAGS) -D_GNU_SOURCE -DTC_HAVE_GEN -I$(MICROMATH) diff_micromath.c tcalc.c micromath_tcalc.c micromath_kernel.o -o $@
	rm -f micromath_kernel.o

check:
	./run.sh

cesta-check:
	$(CESTA) cc --cc $(CC) -I. -Icompiled -fsyntax-only compiled/micromath_leaf.cesta
	$(CESTA) cc --cc $(CC) -I. -Icompiled -fsyntax-only compiled/micromath_compiled.cesta

clean:
	rm -f $(BINS) micromath_tcalc_gen.h micromath_kernel.o
