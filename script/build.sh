echo "OS.Process.exit(OS.Process.failure)" | sml -m src/main.cm && printf 'sml @SMLload=sequent.x86-darwin $@\n' > sequent
chmod u+x sequent
