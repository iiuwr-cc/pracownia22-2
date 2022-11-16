FAILED=0

check() {
  ocamlformat --check $1
  STATUS=$?
  if [ ! $STATUS -eq 0 ]
  then
    echo "$1 is not formatted"
    FAILED=1
  fi
}

for f in $(find source -name *.ml)
do
  check $f
done

exit $FAILED