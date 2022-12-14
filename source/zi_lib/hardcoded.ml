open Ir

let word_size = Int32.of_int 4
let i32_0 = Int32.of_int 0
let i32_1 = Int32.of_int 1
let expr_0 = E_Int i32_0

let preamble =
  String.concat "\n"
    [
      ".data";
      "endline: .asciiz \"\\n\"";
      "endmessage: .asciiz \"Exit code: \"";
      "";
      ".text";
      ".set noat";
      "";
      "main:";
      "   add $sp, $sp, -4";
      "   sw $ra, 4($sp)";
      "   jal _main";
      "   move $a1, $v0";
      "   la $a0, endmessage";
      "   li $v0, 4";
      "   syscall";
      "   li $v0, 1";
      "   move $a0, $a1";
      "   syscall";
      "   la $a0, endline";
      "   li $v0, 4";
      "   syscall";
      "   lw $ra, 4($sp)";
      "   add $sp, $sp, 4";
      "   jr $ra";
      "";
      "_zi_concat:";
      "   # t0 = lhs";
      "   # t1 = rhs";
      "   move $t0, $a0";
      "   move $t1, $a1";
      "   # t2 = len(lhs)";
      "   # t3 = len(rhs)";
      "   lw $t2, -4($t0)";
      "   lw $t3, -4($t1)";
      "   # t4 = len(lhs) + len(rhs)";
      "   addu $t4, $t2, $t3";
      "   # v0 = malloc(4*t4+4) ";
      "   li $t5, 4";
      "   mul $a0, $t4, $t5";
      "   addiu $a0, $a0, 4";
      "   li $v0, 9";
      "   syscall";
      "   addiu $v0, $v0, 4";
      "   sw $t4, -4($v0)";
      "   move $v1, $v0";
      "   XL0:";
      "   beq $zero, $t2, XL1";
      "   lw $t4, 0($t0)";
      "   sw $t4, 0($v1)";
      "   addiu $t2, $t2, -1";
      "   addiu $t0, $t0, 4";
      "   addiu $v1, $v1, 4";
      "   j XL0";
      "   XL1:";
      "   beq $zero, $t3, XL2";
      "   lw $t4, 0($t1)";
      "   sw $t4, 0($v1)";
      "   addiu $t3, $t3, -1";
      "   addiu $t1, $t1, 4";
      "   addiu $v1, $v1, 4";
      "   j XL1";
      "   XL2:";
      "   jr $ra";
      "";
      "_zi_alloc:";
      "   li $v0, 9";
      "   syscall";
      "   jr $ra";
      "";
      "_printString:";
      "   # t0 = len a0";
      "   move $t1, $a0";
      "   lw $t0, -4($t1)";
      "   mul $a0, $t0, 4";
      "   addiu $a0, $a0, 2";
      "   li $v0, 9";
      "   syscall";
      "   move $a0, $v0";
      "   move $v1, $v0";
      "   XL10:";
      "   beq $zero, $t0, XL11";
      "   lw $t2, 0($t1)";
      "   sb $t2, 0($v1)";
      "   addiu $t0, $t0, -1";
      "   addu $t1, $t1, 4";
      "   addu $v1, $v1, 1";
      "   j XL10";
      "   XL11:";
      "   li $t0, 10";
      "   sb $t0, 0($v1)";
      "   sb $zero, 1($v1)";
      "   li $v0, 4";
      "   syscall";
      "   jr $ra";
      "";
      "";
      "_printInt:";
      "   li $v0, 1";
      "   syscall";
      "   li $v0, 4";
      "   la $a0, endline";
      "   syscall";
      "   jr $ra";
      "";
      "";
    ]
