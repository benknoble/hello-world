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

`dd`: Delete the line the cursor is on.

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

### Various Commands

`o`: Open a new line (in Insert mode) on the line below the cursor.

`O`: Open a new line (in Insert mode) on the line above the cursor.
