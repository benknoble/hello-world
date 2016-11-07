#Bash Tips and Tricks

###Fun stuff
```bash
[user]$ echo $'\a' #make the terminal beep
[user]$ say "something" #tested on mac only, but the computer will read text to you
```
_Changing the Command Prompt_
```bash
export PS1="prompt"
```
You can use the following items within "prompt" to display variables:
* \d – Current date
* \t – Current time
* \h – Host name
* \\# – Command number
* \u – User name
* \W – Current working directory (ie: Desktop/)
* \w – Current working directory with full path (ie: /Users/Admin/Desktop/)

You can also access environment variables like $PATH or even execute commands like $(pwd). In this example, the pwd is useful because it always outputs the full path name, unlike \W and \w which use the ~ home shortcut.

###I/O Redirection
```bash
[user]$ command > destination #redirected output
[user]$ destination < command #redirected input
[user]$ command1 | command2   #redirect command1 output into command2 input
```

###Useful commands
man or help theses commands for more info:
```bash
[user]$ man      #display manual pages
[user]$ help     #display help message
[user]$ which    #find where a command is located
[user]$ type     #describe the command type (alias, function, builtin, etc.)
[user]$ hostname #display the hostname
[user]$ sort     #sort input and output it
[user]$ uniq     #remove duplicates from sorted input and output it
[user]$ grep     #search for lines matching patterns
[user]$ fmt      #format input and output it
[user]$ pr       #ready input for printing
[user]$ head     #read first few lines of input
[user]$ tail     #read last few lines of input
[user]$ sed      #stream editor
[user]$ awk      #powerful programming language for filtering files
[user]$ echo     #print things out
[user]$ cd       #change directory
[user]$ mkdir    #make directory
[user]$ ls       #output directory contents
[user]$ touch    #access file if it exists; otherwise, create it
[user]$ cat      #ouptut the input
[user]$ cal      #display a calendar
[user]$ printenv #print env variables
[user]$ file     #display info about a file
[user]$ mkfile -n <size> junkfile
                 #make a file of size size
```
