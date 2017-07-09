echo "OS.Process.exit OS.Process.failure" | sml -m src/main.cm
if [ $? -eq 0 ]; then
  printf 'sml @SMLload=sequent.x86-darwin $@ || sml @SMLload=sequent.x86-linux $@\n' > sequent
  chmod u+x sequent
else
  printf "Could not compile.\n"
  exit 1
fi
