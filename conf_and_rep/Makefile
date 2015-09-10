default: conf rep

conf: conf.tex bib.bib
	pdflatex conf
	bibtex conf || true
	pdflatex conf
	pdflatex conf

rep: rep.tex bib.bib
	pdflatex rep
	bibtex rep || true
	pdflatex rep
	pdflatex rep

all: conf rep
