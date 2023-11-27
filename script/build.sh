echo "OS.Process.exit OS.Process.failure" | sml -m src/main.cm
if [ $? -eq 0 ]; then
  printf 'sml @SMLload=sequent.amd64-darwin $@\n' > sequent
  chmod u+x sequent
else
  printf "Could not compile.\n"
  exit 1
fi
