# Motions
## (aka) How to Move in Vim

On motions:

Most motions can be prefixed with a count to indicate how many times to move.
For example, typing `5l` will move the cursor 5 characters right.

### Single Character Movements

`h`: Left.

`l`: Right.

`k`: Up.

`j`: Down.

### Left/Right Motions

`0`: First character in line.

`^`: First non-blank character in line.

`$`: Last character in line. With count **N**, down **N-1** lines.

`g0`: First character in screen line.

`g^`: First non-blank character in screen line.

`g$`: Last character in screen line.

`gm`: To middle of screen line.

`|` (read "bar"): To first column. With count **N**, to **Nth** column.

`f`**{char}**: Find **{char}** on the right. Case-sensitive.

`F`**{char}**: Find **{char}** on the left. Case-sensitive.

`t`**{char}**: To before **{char}** on the right. Case-sensitive.

`T`**{char}**: To before **{char}** on the left. Case-sensitive.

`;`: Repeat last `f`,`F`,`t`,`T`.

`'`: Repeat last `f`,`F`,`t`,`T` in opposite direction.

`%`: Go to matching brace, bracket, comment, or directive in this line.

### Up/Down Motions

`-`: Up, on the first non-blank character.

`+`: Down, on the first non-blank character.

`G`: Last line, on the first non-blank character. With count **N**, go to line **N**.

`gg`: First line, on the first non-blank character. With count **N**, go to the line **N**.

**N**`%`: Go to line **Nth** percention down in file. Different from `%` command.

`gk`: Up screen line.

`gj`: Down screen line.

`H`: First line in window, on the first non-blank character.

`M`: Middle line in window, on the first non-blank character.

`L`: Last line in window, on the first non-blank character.

### Text Object Motions

`w`: Forward to the beginning of one word.

`W`: Forward to the beginning of one blank-separated "word."

`e`: Forward to the end of one word.

`E`: Forward to the end of one blank-separated "word."

`b`: Backward to the beginning of one word.

`B`: Backward to the beginning of one blank-separated "word."

`ge`: Backward to the end of one word.

`gE`: Backward to the end of one blank-separated "word."

`(`: One sentence backward.

`)`: One sentence forward.

`{`: One paragraph backward.

`}`: One paragraph forward.

`]]`: One section forward, at start of section.

`[[`: One section backward, at start of section.

`][`: One section forward, at end of section.

`[]`: One section backward, at end of section.

`[(`: Back once to unclosed '('.

`[{`: Back once to unclosed '{'.

`[m`: Back once to start of method.

`[M`: Back once to end of method.

`])`: Forward once to unclosed ')'.

`]}`: Forward once to unclosed '}'.

`]m`: Forward once to start of method.

`]M`: Forward once to end of method.

`[#`: Back once to unclosed "#if" or "#else."

`]#`: Forward once to unclosed "#else" or "#endif."

`[*`: Back once to start of comment multiline comment.

`]*`: Forward once to end of multiline comment.

### Tags (like links)

`CTRL-]`: Jump to tag.

`CTRL-T` or `CTRL-O`: Jump back.
