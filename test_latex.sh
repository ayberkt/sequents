rm -rf resources/out.tex
make && echo "A /\ B => B /\ A" | ./sequent --latex > resources/out.tex && cd resources && xelatex out.tex && open -a Preview out.pdf
