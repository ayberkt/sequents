echo "OS.Process.exit(OS.Process.failure)" | sml -m src/test/test.cm
sml @SMLload=test.x86-linux || sml @SMLload=test.x86-darwin
