#!/bin/bash
gen() {
    ../../../../tools/gen/basic_gen.py --srctype "$1" --dsttype "$2" --should-not-typecheck
    ../../../../tools/gen/basic_gen.py --srctype "$1" --dsttype "$2" --should-not-typecheck --reverse
}

gen int bool
gen int boolA
gen int intA
gen bool boolA
gen bool intA
gen intA boolA
gen record int
gen record bool
gen record intA
