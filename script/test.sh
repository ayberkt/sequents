echo "OS.Process.exit(OS.Process.failure)" | sml -m src/test/test.cm > /dev/null

if [ $? -eq 0 ]; then
  if [ -f test.x86-linux ]; then
    sml @SMLload=test.x86-linux
  else
    sml @SMLload=test.x86-darwin
  fi
else
  echo "Could not compile."
  exit 1
fi
