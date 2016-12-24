# motions
## (aka) how to move in Vim

On motions:

Most motions can be prefixed with a count to indicate how many times to move.
For example, typing "5l" will move the cursor 5 characters right.

### Single Character Movements

_h_: Left.

_l_: Right.

_k_: Up.

_j_: Down.

### Left/Right Motions

_0_: First character in line.

_^_: First non-blank character in line.

_$_: Last character in line. With count **N**, down **N-1** lines.

_g0_: First character in screen line.

_g^_: First non-blank character in screen line.

_g$_: Last character in screen line.

_gm_: To middle of screen line.

_|_ (read "bar"): To first column. With count **N**, to **Nth** column.

_f_**{char}**: Find **{char}** on the right. Case-sensitive.

_F_**{char}**: Find **{char}** on the left. Case-sensitive.

_t_**{char}**: To before **{char}** on the right. Case-sensitive.

_T_**{char}**: To before **{char}** on the left. Case-sensitive.

_;_: Repeat last _f_,_F_,_t_,_T_.

_'_: Repeat last _f_,_F_,_t_,_T_ in opposite direction.

### Up/Down Motions

_-_: Up, on the first non-blank character.

_+_: Down, on the first non-blank character.

_G_: Last line, on the first non-blank character. With count **N**, go to line **N**.

_gg_: First line, on the first non-blank character. With count **N**, go to the line **N**.

**N**_%_: Go to line **Nth** percention down in file. Different from _%_ command.

_gk_: Up screen line.

_gj_: Down screen line.

### Tags (like links)

_CTRL-]_: Jump to tag.

_CTRL-T_ or _CTRL-O_: Jump back.
