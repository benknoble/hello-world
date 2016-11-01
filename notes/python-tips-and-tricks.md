#Python Tips and Tricks
######Disclaimer: I am just starting to learn Python, so some of this could be horrible wrong.

##Python scripts

You can create a python script by starting a .py file with the line
```python
#!/usr/bin/env python3.5
```
Then, follow that with your python script.

---

To execute it, you have a number of options. The simplest is to have python interpret the file:

`$python3.5 my_python_script.py`

Alternatively, you might create a bash script that does that work for you (perhaps naming it the same as your python script so it's easy to use).
Store it in a .sh file or a file with no extension.
```bash
#!/bin/bash
python3.5 my_python_script.py
```
To make it executable, run
`$chmod +x my_python_bash_sript`

It can be executed like (assuming you're in the directory containing the script):
`$./my_python_bash_script`

Finally, to enable the script globally, follow the above steps to create an executable bash script, and then edit your path (/etc/paths or PATH=$PATH:~/path-to-file)
to contain the path to the bash script. Then you can do:
`$my_python_bash_script`
and voilà! Python script executed.

###Using "main" in a Python script

Sometimes, you want to write a Python script/class definition with an executable function, but you later realize that class definition would be useful to import in later functions. How do we solve this? In Python, we have a special construct:

```python
#Class def

if __name__=="__main__":
  #Executable function def
```

Ignoring the details, this allows us to import the Python file and use it's class definitions _or_ call it directly from the command line, executing anything within the if block at the end of the file.
