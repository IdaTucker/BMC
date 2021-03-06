# $Id: Makefile 4119 2016-11-15 21:40:45Z sutre $

# Configuration
BUILD_FLAGS = -use-ocamlfind -use-menhir
DOC_FLAGS   = -charset UTF-8, -stars, -colorize-code, -sort,
DOC_FLAGS  += -hide Pervasives, -hide-warnings
REPORT = report.tex
SRC = src/
TEST = test/
EX = examples/

# Default target
all: bmc.d.byte

%.native %.byte %.d.byte %.cmo %.d.cmo: FORCE
	ocamlbuild $(BUILD_FLAGS) $@

doc: FORCE
	ocamlbuild $(BUILD_FLAGS) -docflags '$(DOC_FLAGS)' doc.docdir/index.html
	mv doc.docdir doc

report: 
	@pdflatex $(REPORT)

test: FORCE runtests.d.byte
	CAMLRUNPARAM="b" ./runtests.d.byte

clean: FORCE
	ocamlbuild -quiet -clean
	rm -rf report.aux report.log report.out	report.pyg *~ $(SRC)*~ $(TEST)*~ $(EX)*~


FORCE:

# Check for ocamlbuild
ifneq ($(shell ocamlbuild -version 2>/dev/null | sed -e 's/ .*//'), ocamlbuild)
  $(error Check for ocamlbuild failed.  Is OCaml installed?)
endif

# Check for menhir
ifneq ($(shell menhir --version 2>/dev/null | sed -e 's/,.*//'), menhir)
  $(error Check for menhir failed.  Is Menhir installed?)
endif

# Check for OCaml compiler >= 4.01.0 (required for Format.asprintf)
ifneq ($(shell expr $$(ocamlc -version) \>= 4.01.0), 1)
  $(error Check for ocamlc version >= 4.01.0 failed.)
endif
