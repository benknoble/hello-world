# 0x20090064
# addi $t1,$0,100
# 0x03e00008
# jr $ra

.data

.text

inst:

# prep inst
lui $t1, 0x2009
ori $t1, 0x0064
sw $t1, inst($0)

lui $t1, 0x03e0
ori $t1, 0x0008
sw $t1, inst+1

# attempt to jump into data section

jal inst

# print $t1
li $v0, 1
move $a0, $t1
syscall

# exit
li $v0, 10
syscall