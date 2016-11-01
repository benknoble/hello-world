#Bash Tips and Tricks

###Fun stuff
```bash
[user]$ echo $'\a' #make the terminal beep
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
```bash
[user]$ hostname #display the hostname
```
