
gen() {
    ../../../../tools/gen/basic_gen.py --srctype "$1" --dsttype "$2" -p comp_lt -p comp_le -p comp_gt -p comp_ge  --should-not-typecheck   --reverse
    ../../../../tools/gen/basic_gen.py --srctype "$1" --dsttype "$2" -p comp_lt -p comp_le -p comp_gt -p comp_ge  --should-not-typecheck  
}


gen bool bool
gen intA intA
gen boolA boolA
gen record record

rename -e 's/bool_bool\./bool\./' *xi
rename -e 's/boolA_boolA\./boolA\./' *xi
rename -e 's/intA_intA\./boolA\./' *xi

