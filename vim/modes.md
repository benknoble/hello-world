# Modes
## (aka) How to Work in Vim

There are four primary modes in Vim:

* Normal
* Insert
* Visual
* Replace

### Normal

In Normal mode, typed characters are commands (like a motion or delete).
It is also used primarily for moving around.

The default mode is Normal.

### Insert

In Insert mode, typed characters are inserted directly into the text
where the cursor is. You can temporarily suspend an insert by typing `<Ctrl-O>`,
during which you can enter _one_ Normal mode command.

To enter Insert mode, type the character `i` while in Normal mode.
To exit insert mode, pres `<Esc>`.

You can also enter Insert mode using `a` to append (start inserting _after_
the cursor) or `A` to append to the end of a line.

### Visual

### Replace

In Replace mode, characters typed replace those already there.

To enter Replace mode, type `R` while in Normal mode.
To exit, press `<Esc>`.

While technically not Replace mode, you can replace a single character
under the cursor with another single character by typing `r`**{new char}**.
