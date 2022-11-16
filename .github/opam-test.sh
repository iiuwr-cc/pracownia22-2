export OPAMROOT=/home/opam/.opam

su opam -c "opam exec -- python3 tools/tester.py --testdir $1 --plugin mods/mod_student.cma"
