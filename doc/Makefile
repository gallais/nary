AGDA=agda-2.6.0 +RTS -M2G -H2G -A128M -RTS
PAPER=tyde19

AGDA_FILES:=\
  lagda/StateOfTheArt.lagda
  
AGDA_OUTPUT:=$(patsubst lagda/%.lagda,output/%.tex,$(AGDA_FILES))
AGDA_TEX:=$(patsubst lagda/%.lagda,latex/%.tex,$(AGDA_FILES))

PAPER_DEPENDENCIES:= \
  latex/acmart.cls \
  latex/tyde19.tex \
  latex/nary.tex \
  latex/agda.sty \
  latex/unicode.tex \
  $(AGDA_TEX)

all: latex/$(PAPER).pdf

latex/%.cls: %.cls
	mkdir -p $(dir $@)
	cp $< $@

latex/agda.sty: $(AGDA_OUTPUT)
	mkdir -p latex/
	cp output/agda.sty latex/

output/%.tex: lagda/%.lagda
	${AGDA} -i lagda/ --latex --latex-dir=output/ $<

latex/%.tex: output/%.tex
	mkdir -p $(dir $@)
	cp $< $@


latex/%.tex: %.tex
	mkdir -p $(dir $@)
	cp $< $@

latex/$(PAPER).pdf: $(PAPER_DEPENDENCIES)
	cd latex && latexmk -pdf -bibtex ${PAPER}.tex

clean:
	find . -name "*.agdai" | xargs rm
	rm latex/$(PAPER).pdf
