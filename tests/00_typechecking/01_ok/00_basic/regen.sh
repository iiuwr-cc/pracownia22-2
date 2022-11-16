
gen() {
    ../../../../tools/gen/basic_gen.py --srctype "$1" --dsttype "$2" $3 $4 $5
}

gen int int --no-bool
gen intA intA --no-bool --no-cmp --no-arith
gen bool bool --no-cmp --no-arith
gen boolA boolA --no-bool --no-cmp --no-arith
gen record record --no-bool --no-cmp --no-arith

