echo "OS.Process.exit(OS.Process.failure)" | sml -m src/test/test.cm

if [ -f test.x86-linux ]; then
  sml @SMLload=test.x86-linux
else
  sml @SMLload=test.x86-darwin
fi
