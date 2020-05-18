"""
Main CSP solver
"""

import sys

def readCommand(argv):
	"""
	Reads arguments from the command line
	"""

	from optparse import OptionParser
    
    # define usage string
	usageStr = """
    USAGE:      python csp.py <options>
    EXAMPLES:   (1) python csp.py -v ex1.var -c ex1.con
                    - solves example 1 with no forward checking
                (2) python csp.py -v ex2.var -c ex2.con -p fc
                    - solves example 2 using forward checking
	"""
	parser = OptionParser(usageStr)

	# define argument options
	parser.add_option('-v', '--variables', dest='varsFile',
		help='The input file (.var) for CSP variables', default='ex1.var')
	parser.add_option('-c', '--constraints', dest='consFile',
		help='The input file (.con) for CSP constraints', default='ex1.con')
	parser.add_option('-p', '--procedure', dest='proc',
		help='The consistency-enforcing procedure', default='none')

	# retrieves arguments and detects unknown arguments
	options, directCommands = parser.parse_args(argv)
	if len(directCommands) > 0:
		options.varsFile = directCommands[0]
		options.consFile = directCommands[1]
		if len(directCommands) > 2:
			options.proc = directCommands[2]

	# validates inputted arguments
	varSep = options.varsFile.split('.')
	if varSep[len(varSep)-1] != 'var':
		raise Exception('Variable file is an invalid file type (must be .var). Inputted:', options.varsFile)
	conSep = options.consFile.split('.')
	if conSep[len(conSep)-1] != 'con':
		raise Exception('Constraint file is an invalid file type (must be .con). Inputted:', options.consFile)
	if options.proc != 'none' and options.proc != 'fc':
		raise Exception('Procedure type is an invalid type (must be fc or none). Inputted:', options.proc)

    # assign variables, constraints, and procedure
	args = dict()
	args['varsFile'] = options.varsFile
	args['consFile'] = options.consFile
	args['proc'] = options.proc

	return args

def remVariables(asmt, varbs):
	"""
	Finds the number of unassigned variables without forward checking
	"""

	# put unassigned variables in a list with their domains
	remVars = dict()
	for v in varbs:
		if v not in asmt.keys():
			remVars[v] = varbs.get(v).copy()
	return remVars

def legalValList(var, vals, asmt, cons):
	"""
	Returns the legal domain of a single value
	"""

	# reduce constraint list to only relevant constraints
	remCons = []
	for c in cons:
		for a in asmt:
			if var in c and a in c:
				remCons.append(c)

	# for each assignment, remove illegal values from the list
	for a in asmt:
		for c in remCons:
			if a in c:
				valsCopy = vals.copy()
				for v in valsCopy:
					if not constraintSatisfied(a, asmt.get(a), var, int(v), c):
						vals.remove(v)
	return vals

def remVariablesFC(asmt, varbs, cons):
	"""
	Adjusts the domains of unassigned variables
	"""

	# put unassigned variables in a list with their original domains
	remVars = remVariables(asmt, varbs)

	# adjust domain of each variable
	for v in remVars:
		remVars[v] = legalValList(v, remVars.get(v), asmt, cons)
	return remVars


def remConstraints(cons, varbs, remVars):
	"""
	Finds the number of unassigned constraints
	"""

	remCons = []
	for c in cons:
		addCons = True
		for v in varbs:
			if v in c and v not in remVars:
				addCons = False
		if addCons:
			remCons.append(c)
	return remCons


def selectvar(asmt, varbs, cons, proc):
	"""
	Uses most constrained variable to select variable assignment. Since
	forward checking is not implemented, this should have no effect if
	vars all have the same domain. If ties exist, uses most constraining
	variable. If ties still exist, chooses a variable alphabetically.
	"""

	# determine unassigned variables
	remVars = dict()
	if proc == 'none':
		remVars = remVariables(asmt, varbs)
	elif proc == 'fc':
		remVars = remVariablesFC(asmt, varbs, cons)
	else:
		raise Exception('Unrecognized procedure', proc)

	# check if domain is empty
	for v in remVars:
		if len(remVars.get(v)) == 0:
			return 'failure'

	# determine remaining constraints
	remCons = remConstraints(cons, varbs, remVars)

	# select variable with fewest values/smallest domain
	minVar = ''
	minLength = 999
	for v in remVars:
		if len(remVars.get(v)) < minLength:
			minLength = len(remVars.get(v))
			minVar = v

	# check for ties
	tiedList = [minVar]
	for v in remVars:
		if len(remVars.get(v)) == len(remVars.get(minVar)) and v is not minVar:
			tiedList.append(v)
	if len(tiedList) == 1:
		return tiedList[0]

	# count how many constraints each var is in
	varCount = {v : 0 for v in tiedList}
	for v in tiedList:
		for c in remCons:
			if v in c:
				varCount[v] = varCount[v] + 1

	# check for ties with max variable
	maxVar = max(varCount, key=varCount.get)
	maxVal = varCount.get(maxVar)
	tiedList2 = [maxVar]
	for v in varCount:
		if varCount.get(v) == maxVal and v is not maxVar:
			tiedList2.append(v)

	# return the variable involved in the most constraints
	return sorted(tiedList2)[0]

def constraintSatisfied(var1, val1, var2, val2, c):
	"""
	Determines if a pair of variables and their respective values
	will satisfy a constraint
	"""

	# parse constraint
	v1, op, v2 = c.split(' ')

	# check if variables need to be switched
	if v1 == var2 and v2 == var1:
		temp = val1
		val1 = val2
		val2 = temp

	# return respective truth value
	if op == '=':
		return val1 == val2
	elif op == '>':
		return val1 > val2
	elif op == '<':
		return val1 < val2
	elif op == '!':
		return val1 != val2
	else:
		raise Exception('Unknown operator in constraint file:', op)

def remValues(var1, val1, var2, val2, cons):
	"""
	Finds the number of remaining legal values for a variable (var2)
	when a different variable (var1) is given an assignment
	"""

	# select constraints the variable is involved in
	remCons = []
	for c in cons:
		if var1 in c and var2 in c:
			remCons.append(c)

	# if variables not involved in constraint, return 1 (satisfied)
	if len(remCons) == 0:
		return 1

	# count legal values of variable when other variable is assigned
	sum = 0
	for c in remCons:
		if constraintSatisfied(var1, val1, var2, val2, c):
			sum += 1

	return sum

def ordervalues(asmt, varbs, cons, var, proc):
	"""
	Uses least constraining value to determine an ordering for value
	assignment. 
	"""

	# determine unassigned variables
	remVars = dict()
	if proc == 'none':
		remVars = remVariables(asmt, varbs)
	elif proc == 'fc':
		remVars = remVariablesFC(asmt, varbs, cons)
	else:
		raise Exception('Unrecognized procedure', proc)

	# determine remaining constraints
	remCons = remConstraints(cons, varbs, remVars)

	# for each val in var's domain, find sum of remaining values for remaining variables
	varLegalVals = remVars.get(var).copy()
	valCount = {int(i) : 0 for i in remVars.get(var)}
	del remVars[var]
	for val in varLegalVals:
		for var2 in remVars:
			for val2 in remVars.get(var2):
				valCount[int(val)] = valCount[int(val)] + remValues(var, int(val), var2, int(val2), remCons)

	# sort values primarily based on their count, secondarily based on increasing order
	sortedVals = sorted(valCount.items(), key=lambda tup: (-tup[1], tup[0]))
	sortedValList = []
	for v, v1 in sortedVals:
		sortedValList.append(v)
	return sortedValList

def satisfiesAllConstraints(asmt, var, val, cons):
	"""
	Given all assigned values and all constraints, check to see if
	variable var is legal when assigned value val
	"""

	# pick out relevant constraints
	remCons = []
	for c in cons:
		if var in c:
			remCons.append(c)

	# if a single constraint violated, return false
	for var1 in asmt:
		for c in remCons:
			if var1 in c:
				if not constraintSatisfied(var1, int(asmt.get(var1)), var, val, c):
					return False
	return True

def display(asmt, failString, success, i):
	"""
	Displays each branch in std out
	"""

	# append assignments to output string
	output = str(i) + '. '
	for a in asmt:
		output = output + a + '=' + str(asmt.get(a)) + ', '
	if len(failString) > 0:
		output = output + failString + ', '
	if success:
		output = output.rstrip(', ')
		output = output + ' solution'
	else:
		output = output.rstrip(', ')
		output = output + ' failure'

	return output

def backtracking(asmt, varbs, cons, proc, i):
	"""
	Recursive backtracking algorithm
	"""

	# if assignment is complete then return assignment
	complete = True
	for v in varbs:
		if v not in asmt.keys():
			complete = False
			break
	if complete:
		i += 1
		print(display(asmt, '', True, i))
		return True, i, asmt

	# order variables based on most constrained, most constraining, then alpha
	var = selectvar(asmt, varbs, cons, proc)

	# if domain is empty, var with return with 'failure'
	if var == 'failure':
		i += 1
		print(display(asmt, '', False, i))
		return False, i, ''

	# for each value in order-domain-values(var, assignment, csp) do
	vals = ordervalues(asmt, varbs, cons, var, proc)
	for v in vals:
		if satisfiesAllConstraints(asmt, var, v, cons):
			asmt[var] = v
			success, i, finalAsmt = backtracking(asmt, varbs, cons, proc, i)
			if success:
				return success, i, finalAsmt
			del asmt[var]
		else:
			i += 1
			print(display(asmt, str(var+'='+str(v)), False, i))

	# no values led to successful assignment
	return False, i, ''

def solve(varsFile, consFile, proc):
	"""
	Helper function to solve the inputted problem, uses recursive
	function backtracking()
	"""

	# read variables from .var file
	varbs = dict()
	varFile = open(varsFile, 'r')
	for v in varFile:
		line = v.rstrip('\n')
		var, dom = line.split(': ')
		varbs[var] = dom.strip().split(' ')
	varFile.close()

	# read constraints from .con file
	cons = []
	conFile = open(consFile, 'r')
	for c in conFile:
		cons.append(c.rstrip('\n'))
	conFile.close()

	# execute backtracking algorithm
	asmt = dict()
	backtracking(asmt, varbs, cons, proc, 0)

	# print solution ??
	return

if __name__ == '__main__':
	"""
	Main function called when 'csp.py' is called
	from the command line.
	Usage string activated by executing
	'csp.py --help' from the command line.
	"""

	args = readCommand(sys.argv[1:])
	solve(**args)

	pass
