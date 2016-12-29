# Commands
## (aka) How to Do Things in Vim

There are two types of commands in Vim: Colon-commands (also called
command-line commands) and "Normal" commands.

Colon-commands are entered by first typing a colon (`:`) and then typing the
command. Press `<Enter>` to execute the command.

Normal commands are entered during Normal mode, where each character might
be a command. Simply type the command.

### Exiting Commands

`ZZ`: Write and quit.

`ZQ`: Quit without checking for changes (like `:q!`).

`:q`: Quit (will not quit if changes have not been overwritten).

`:wq`: Variation on `:q`. Write-Quit.

`:q!`: Quit and discard changes (forces quit).

`:confirm quit`: Confirm quit operation.

`:x`: Exit. Write if changes made, then quit.

### Help Commands

`:help`: Open help window.

`:help`**{subject}**: Find help on **{subject}**. Subject can be a key command,
like x, or a topic, like deleting.

`:helpgrep`**{subject}**: Search help pages for **{subject}**.

`CTRL-G`: Find where you are in a file (displays message in status line).

### Deletion Commands

`x`: Delete a single character under the cursor.

`X`: Delete a single character left of cursor.

`dd`: Delete the line the cursor is on.

`d`**{motion}**: Delete the text from cursor up to the result of
**{motion}**.

`D`: Delete to end of line.

`cc`: Change a whole line.

`c`**{motion}**: Like `d`, but leaves you in Insert mode.

`C`: Change to end of line.

`s`: Change one character.

`S`: Change a whole line.

`J`: Delete a line break (joins the cursor-line with that below it).

### Scrolling Commands

`CTRL-U`: Scroll up a half screen.

`CTRL-D`: Scroll down a half screen.

`CTRL-F`: Scroll a screen forward.

`CTRL-B`: Scroll a screen backward.

`zz`: Puts line with cursor in middle of screen.

`zt`: Puts line with curson at top of screen.

`zb`: Puts line with cursor at bottom of screen.

### Undo/Redo Commands

`u`: Undoes the last edit. Can be used in succession to undo multiple edits.

`U`: Undoes all changes on the last line edited (can be undone with `u`).

`CTRL-R`: Redoes the last Undo command.

`.`: Repeats the last change made.

### Searching Commands

`/`**{search string}**`<Enter>`: Search forward for **{search string}**.

`?`**{search string}**`<Enter>`: Search backward for **{search string}**.

`*`: Search forward for word under cursor.

`#`: Search backward for word under cursor.

`g*`: Like `*`, but match partial words.

`g#`: Like `#`, but match partial words.

`n`: Repeat last search.

`N`: Repeat last search in opposite direction.

### Jumping Commands

`(backtick)(backtick)` (\`\`): Jump to last position.

`''`: Jump to line of last position.

`CTRL-O`: Jump to older position.

`CTRL-I`: Jump to newer position.

`:jumps`: Gives a list of positions.

### Marking Commands

`m`**{char}**: Marks the cursor's position as mark **{char}**, which
can be any of the the letters a-z.

`(backtick)`**{char}** (\`**{char}**): Move to position marked by **{char}**.

`'`**{char}**: Move to line with position marked by **{char}**.

`:marks`: List marks.

### Various Commands

`o`: Open a new line (in Insert mode) on the line below the cursor.

`O`: Open a new line (in Insert mode) on the line above the cursor.
