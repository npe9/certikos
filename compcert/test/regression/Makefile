include ../../Makefile.config

CCOMP=../../ccomp
CCOMPFLAGS=-stdlib ../../runtime -dparse -dc -dclight -dasm -fall

LIBS=$(LIBMATH)

# Can run, both in compiled mode and in interpreter mode,
# and have reference output in Results

TESTS=int32 int64 floats floats-basics \
  expr1 expr6 funptr2 initializers initializers2 initializers3 \
  volatile1 volatile2 volatile3 \
  funct3 expr5 struct7 struct8 struct11 casts1 casts2 char1 \
  sizeof1 sizeof2 binops bool for1

# Can run, but only in compiled mode, and have reference output in Results

TESTS_COMP=attribs1 bitfields1 bitfields2 bitfields3 bitfields4 \
  bitfields5 bitfields6 bitfields7 bitfields8 \
  builtins-$(ARCH) packedstruct1 packedstruct2 alignas \
  varargs1 varargs2

# Can run, both in compiled mode and in interpreter mode,
# but produce processor-dependent results, so no reference output in Results

TESTS_DIFF=NaNs

# Other tests: should compile to .s without errors (but expect warnings)

EXTRAS=annot1 commaprec expr2 expr3 expr4 extern1 funct2 funptr1 \
  pragmas ptrs1 ptrs2 struct1 struct2 struct3 \
  struct4 struct5 struct6 struct9 struct10 types1 seqops \
  singlefloats

# Test known to fail
FAILURES=funct1

all: $(TESTS:%=%.compcert) $(TESTS_COMP:%=%.compcert) $(TESTS_DIFF:%=%.compcert) $(EXTRAS:%=%.s)

all_s: $(TESTS:%=%.s) $(TESTS_COMP:%=%.s) $(TESTS_DIFF:%=%.s) $(EXTRAS:%=%.s)

%.compcert: %.c $(CCOMP)
	$(CCOMP) $(CCOMPFLAGS) -o $*.compcert $*.c $(LIBS)

%.s: %.c $(CCOMP)
	$(CCOMP) $(CCOMPFLAGS) -S $*.c

clean:
	rm -f *.compcert
	rm -f *.parsed.c *.compcert.c *.light.c *.s *.o *~ 

test:
	@for i in $(TESTS) $(TESTS_COMP); do \
	   if ./$$i.compcert | cmp -s - Results/$$i; \
           then echo "$$i: passed"; \
           else echo "$$i: FAILED"; \
	   fi; \
         done
	@for i in $(TESTS); do \
           if $(CCOMP) -fall -interp -quiet $$i.c > _cinterp.log; then \
             if cmp -s _cinterp.log Results/$$i; \
             then echo "$$i: interpreter passed"; \
             else echo "$$i: interpreter FAILED"; \
             fi; \
           else \
             echo "$$i: interpreter undefined behavior"; \
           fi; \
           rm -f _cinterp.log; \
         done
	@for i in $(TESTS_DIFF); do \
           if $(CCOMP) -fall -interp -quiet $$i.c > _cinterp.log; then \
             if ./$$i.compcert | cmp -s _cinterp.log -; \
             then echo "$$i: compiler and interpreter agree"; \
             else echo "$$i: compiler and interpreter DISAGREE"; \
             fi; \
           else \
             echo "$$i: interpreter undefined behavior"; \
           fi; \
           rm -f _cinterp.log; \
         done

bench:
