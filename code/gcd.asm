.text 0x3000
.globl main
main:
	# $t0 and $t1 should contain x and y
	# example
	li	$t0, 26
	li	$t1, 8
	while:
		beq $t0, $t1, end_while		# x != y
		if:
			bge $t1, $t0, else	# x > y
			sub $t0, $t0, $t1	# x = x - y
			j end_if
		else:
			sub $t1, $t1, $t0	# y = y - x
		end_if:
		j while
	end_while:
	move	$a0, $t0	# print gcd
	li	$v0, 1
	syscall
