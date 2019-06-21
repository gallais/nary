PAPER=tyde19

AGDA_FILES:=\
  StateOfTheArt.lagda \
  Examples.lagda \
  Unifier.lagda \
  N-ary.lagda \
  Printf.lagda \
  Appendix.lagda

AGDA_OUTPUT:=$(patsubst %.lagda,latex/%.tex,$(AGDA_FILES))

PAPER_DEPENDENCIES:= \
  common \
  latex/acmart.cls \
  latex/$(PAPER).tex \
  latex/nary.tex \
  latex/nary.bib \
  latex/ACM-Reference-Format.bst \
  latex/agda.sty \
  latex/unicode.tex \
  latex/commands.tex \

.SECONDARY: $(AGDA_OUTPUT)

all: latex/$(PAPER).pdf

common:
	$(MAKE) -C ../common

latex/agda.sty: $(AGDA_OUTPUT)
	mkdir -p latex/
	cp ../common/latex/agda.sty latex/

latex/$(PAPER).pdf: $(PAPER_DEPENDENCIES)
	cd latex && latexmk -pdf -bibtex ${PAPER}.tex

latex/%.cls: %.cls
	mkdir -p $(dir $@)
	cp $< $@

latex/%.bst: %.bst
	mkdir -p $(dir $@)
	cp $< $@

latex/%.bib: %.bib
	mkdir -p $(dir $@)
	cp $< $@

latex/unicode.tex: ../common/unicode.tex
	@mkdir -p $(dir $@)
	cp $< $@

latex/commands.tex: ../common/commands.tex
	@mkdir -p $(dir $@)
	cp $< $@

latex/nary.tex: nary.tex
	mkdir -p $(dir $@)
	cp $< $@

latex/$(PAPER).tex: $(PAPER).tex
	@mkdir -p $(dir $@)
	cp $< $@

latex/%.tex: ../common/latex/%.tex common
	mkdir -p $(dir $@)
	cp $< $@

clean:
	make clean -C ../common
	rm -rf latex/
