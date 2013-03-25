all: icfp13.pdf

SOURCES = icfp13.tex intro.tex \
          effdsl.tex effimpl.tex \
          appdesign.tex conclusions.tex library.bib macros.ltx library.ltx

icfp13.pdf: ${SOURCES}
#	dvipdf icfp10.dvi
	pdflatex icfp13
	-bibtex icfp13
	-pdflatex icfp13
	-pdflatex icfp13

icfp13.ps: icfp13.dvi
	dvips -o icfp10.ps icfp10

icfp13.dvi: $(SOURCES)
	-latex icfp13
	-bibtex icfp13
	-latex icfp13
	-latex icfp13

.PHONY:
