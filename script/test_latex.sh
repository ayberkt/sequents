rm -rf resources/out.tex
bash script/build.sh && echo "((A /\\ B) => (B /\\ A)) /\\ ((B /\\ A) => (A /\\ B))" | ./sequent --latex > resources/out.tex && cd resources && xelatex -halt-on-error out.tex && open -a Preview out.pdf
