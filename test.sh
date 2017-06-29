export IFS=$'\n'
echo "Proofs should be found for these."
for i in `cat test/valid.txt`;
  do echo $i | ./sequent;
done
echo "Proofs should not be found for these"
for i in `cat test/invalid.txt`;
  do !(echo $i | ./sequent);
done
