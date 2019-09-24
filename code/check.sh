agda Main.agda
if [ $? -eq 0 ]; then
  echo " OK.";
else
  echo " FAILURE."
  exit 1
fi
