# Motions
## (aka) How to Move in Vim

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

_%_: Go to matching brace, bracket, comment, or directive in this line.

### Up/Down Motions

_-_: Up, on the first non-blank character.

_+_: Down, on the first non-blank character.

_G_: Last line, on the first non-blank character. With count **N**, go to line **N**.

_gg_: First line, on the first non-blank character. With count **N**, go to the line **N**.

**N**_%_: Go to line **Nth** percention down in file. Different from _%_ command.

_gk_: Up screen line.

_gj_: Down screen line.

_H_: First line in window, on the first non-blank character.

_M_: Middle line in window, on the first non-blank character.

_L_: Last line in window, on the first non-blank character.

### Text Object Motions

_w_: Forward to the beginning of one word.

_W_: Forward to the beginning of one blank-separated "word."

_e_: Forward to the end of one word.

_E_: Forward to the end of one blank-separated "word."

_b_: Backward to the beginning of one word.

_B_: Backward to the beginning of one blank-separated "word."

_ge_: Backward to the end of one word.

_gE_: Backward to the end of one blank-separated "word."

_(_: One sentence backward.

_)_: One sentence forward.

_{_: One paragraph backward.

_}_: One paragraph forward.

_]]_: One section forward, at start of section.

_[[_: One section backward, at start of section.

_][_: One section forward, at end of section.

_[]_: One section backward, at end of section.

_[(_: Back once to unclosed '('.

_[{_: Back once to unclosed '{'.

_[m_: Back once to start of method.

_[M_: Back once to end of method.

_])_: Forward once to unclosed ')'.

_]}_: Forward once to unclosed '}'.

_]m_: Forward once to start of method.

_]M_: Forward once to end of method.

_[#_: Back once to unclosed "#if" or "#else."

_]#_: Forward once to unclosed "#else" or "#endif."

_[*_: Back once to start of comment multiline comment.

_]*_: Forward once to end of multiline comment.

### Tags (like links)

_CTRL-]_: Jump to tag.

_CTRL-T_ or _CTRL-O_: Jump back.
