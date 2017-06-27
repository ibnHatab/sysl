



SRCS = hello.tla Data.tla
OBJS = ${SRCS:.tla=.tlaps/fingerprints}

#.PHONY: ${OBJS}

.SUFFIXES:
.SUFFIXES: .tlo .tlaps/fingerprints

all: ${OBJS}

%.tlaps/fingerprints : %.tla
	tlapm -C $<

print-%:
	@echo '$*=$($*)'

clean:
	rm ${OBJS}
