

SRCS = hello.tla Data.tla StateM.tla Fact.tla Stack.tla InternalStack.tla


OBJS = ${SRCS:.tla=.tlaps/fingerprints}

.SUFFIXES:
.SUFFIXES: .tlo .tlaps/fingerprints

all: ${OBJS}

%.tlaps/fingerprints : %.tla
	tlapm -C $<

print-%:
	@echo '$*=$($*)'

clean:
	rm ${OBJS}
