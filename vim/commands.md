# Commands
## (aka) How to Do Things in Vim

There are two types of commands in Vim: Colon-commands (also called
command-line commands) and "Normal" commands.

Colon-commands are entered by first typing a colon (`:`) and then typing the
command. Press `<Enter>` to execute the command.

Normal commands are entered during Normal mode, where each character might
be a command. Simply type the command.

### Exiting Commands

_ZZ_: Write and quit.

_ZQ_: Quit without checking for changes (like `:q!`).

_:q_: Quit (will not quit if changes have not been overwritten).

_:q!_: Quit and discard changes (forces quit).

_:confirm quit_: Confirm quit operation.

_:x_: Exit. Write if changes made, then quit.

### Help Commands

_:help_: Open help window.

_:help {subject}_: Find help on {subject}. Subject can be a key command,
like x, or a topic, like deleting.

_:helpgrep {subject}_: Search help pages for {subject}.

_CTRL-G_: Find where you are in a file (displays message in status line).

### Deletion Commands

_x_: Delete a single character under the cursor.

_dd_: Delete the line the cursor is on.

_J_: Delete a line break (joins the cursor-line with that below it).

### Scrolling Commands

_CTRL-U_: Scroll up a half screen.

_CTRL-D_: Scroll down a half screen.

_CTRL-F_: Scroll a screen forward.

_CTRL-B_: Scroll a screen backward.

_zz_: Puts line with cursor in middle of screen.

_zt_: Puts line with curson at top of screen.

_zb_: Puts line with cursor at bottom of screen.

### Undo/Redo Commands

_u_: Undoes the last edit. Can be used in succession to undo multiple edits.

_U_: Undoes all changes on the last line edited (can be undone with `u`).

_CTRL-R_: Redoes the last Undo command.

### Various Commands

_o_: Open a new line (in Insert mode) on the line below the cursor.

_O_: Open a new line (in Insert mode) on the line above the cursor.
