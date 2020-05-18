Hello, thanks for your interest in my code!

This goal of this project was to create an automated way of finding a
satisfying assignment for the constraint satisfaction problem. This is
done quickly by using the most contrained variable heuristic, breaking
ties with the most constraining variable heuristic, and breaking any
remaining ties using an alphabetical ordering. Values are selected using
the least constraining value heuristic and ties are broken using a
numerical ordering.

To run the program, I use python in the command line. A valid example is:
	py csp.py
	py csp.py variableFile.var constraintFile.con
	py csp.py ex3.var ex3.con
The input files are variable (.var) and constraint (.con) text files. The
variable file states the variables and their relevant domains for the
problem. The constraint file states the constraints that must be satisfied.

When the program is run, it will output a line for each assignment it makes
and at the end of the line, states if the assignment satisfied all
constraints. When a satisfying assignment is found, the corresponding value
for each variable is outputted in a final line.