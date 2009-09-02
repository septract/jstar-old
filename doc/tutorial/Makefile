default : jstartut.pdf

jstartut.pdf : jstartut.tex objects.bbl logo.pdf architecture2.pdf
	pdflatex jstartut.tex
	pdflatex jstartut.tex

objects.bbl : objects.bib jstartut.aux
	bibtex jstartut

jstartut.aux : jstartut.tex 
	pdflatex jstartut.tex