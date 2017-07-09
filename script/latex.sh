rm -rf resources/out.tex
if [ $# -eq 0 ]; then
  echo "Please provide exactly one proposition.";
  exit 1
else
  ./script/build.sh && echo $1 | ./sequent --latex > resources/out.tex && cd resources && pdflatex out.tex && open -a Preview out.pdf

fi
