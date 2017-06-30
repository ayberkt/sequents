rm -rf resources/out.tex
make && echo $1 | ./sequent --latex > resources/out.tex && cd resources && xelatex out.tex && open -a Preview out.pdf
