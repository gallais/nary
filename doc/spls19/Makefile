PAPER=slides

AGDA_FILES:=\
  StateOfTheArt.lagda \
  Examples.lagda \
  Unifier.lagda \
  N-ary.lagda \
  Printf.lagda \
  Applications.lagda \

AGDA_OUTPUT:=$(patsubst %.lagda,latex/%.tex,$(AGDA_FILES))

PAPER_DEPENDENCIES:= \
  common \
  latex/$(PAPER).tex \
  latex/strathclyde.sty \
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

latex/unicode.tex: ../common/unicode.tex
	@mkdir -p $(dir $@)
	cp $< $@

latex/commands.tex: ../common/commands.tex
	@mkdir -p $(dir $@)
	cp $< $@

latex/strathclyde.sty: strathclyde.sty
	@mkdir -p $(dir $@)
	cp $< $@

latex/$(PAPER).tex: $(PAPER).tex
	@mkdir -p $(dir $@)
	cp $< $@
	cp -R strathclyde/ $(dir $@)

latex/%.tex: ../common/latex/%.tex common
	mkdir -p $(dir $@)
	cp $< $@

clean:
	make clean -C ../common
	rm -rf latex/
