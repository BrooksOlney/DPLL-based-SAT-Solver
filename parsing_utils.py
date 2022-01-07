""" Author: Brooks Olney

spec 1.0:
	Implements support for parsing basic boolean expressions in S-expression format.
	Outputs T if expression is tautology, U if unsatisficable, E if not well-formed, 
	or 'i' which is the number of rows that make the expression satisfiable.

spec 2.0:
	Implements the ability to convert an s-expression to CNF format (or DNF, really).
	CNF format is of the type: list(set())

"""

import re
import types
from copy import deepcopy
import itertools as it

# using dictionaries to specify the supported operators, the number of symbols required by each operator, and its truth table
# obviously hard-coded for the constraints of this assignment, operator and symbol support will be extended through future assignments as needed
supportedOperators = ["IF", "IFF", "AND", "OR", "NOT"]
symbolCount = dict({"IF" : 2, "IFF" : 2, "AND" : 2, "OR" : 2, "NOT" : 1})
operatorTT = dict({"IF" : "1101", "IFF" : "1001", "AND" : "0001", "OR": "0111", "NOT": "10"})

def readFormula(F):
	""" Reads the given formula and uses helper functions to build a tree representation of the formula for further processing

	Arguments:
		F {str} -- string of the input formula

	Returns:
		formulaTree {irregular list} -- nested list structure containing the boolean expression
		"E" -- if the formula is not well-formed
	"""	

	# splits the input into array like this: ['(', 'AND', '(', 'NOT', 'a', ')', 'b', ')']
	_F = re.findall(r"\(|\)|\w+", F) 

	symbols = getSymbols(_F)

	if len(_F) == 1:
		return symbols, F
		
	expression = evalFormula(_F)
	
	# print("_F: " + str(_F))
	# print("symbols: "  + str(symbols))
	# print("expression: " + str(expression))

	return symbols, expression

def evalFormula(F):

	""" Reads through the formula and builds a tree. Makes call to recursive function when encountering parens

	Arguments:
		F {list} -- list containing all split chars/words from the original formula

	Returns:
		formulaTree {irregular list} -- nested list structure containing the boolean expression
		"E" -- if the formula is not well-formed
	"""	
	

	if F[0] != '(':
		raise Exception("Called parseTokens on a non-rooted node!")
	
	curItem = F[1]
	del F[:2]
	formulaTree = [curItem]
	try:

		# get appropriate number of symbols
		while 1:
		
			if len(F) == 0:
				raise Exception("reached end of tokens while parsing for arguments!")
			
			# separate function call for evaluating parens
			if F[0] == "(":
				formulaTree.append(evalFormula(F))
				
			elif F[0] == ")":
				del F[0]
				return formulaTree

			# add verified symbol
			else:
				formulaTree.append(F.pop(0))

	except:
		return "E"

	return formulaTree

def getSymbols(F):
	""" Reads through the formula and extracts symbol names 

	Arguments:
		F {list} -- list containing all split chars/words from the original formula

	Returns:
		symbols {list(str)} -- list of all symbols in the formula
	"""	

	# pretty straight forward, just get all the symbols from the split formula
	symbols = []
	for item in F:
		if item not in supportedOperators and item not in symbols and item != "(" and item != ")":
			symbols.append(item)
	
	symbols = set(symbols)

	return list(symbols)

def convertToCNF(F):
	"""converts a propositional calculus formula into a cnf formula

	Args:
		F (string): string in s-expression format

	Returns:
		list(set()): list of clauses (sets) that represents a cnf formula
	"""	
	symbols, expression = readFormula(F)
	expression = makeBinary(expression)

	# remove implications
	noImps = removeImps(expression)
	
	# distribute negations (i.e. NOT a => -a, NOT (AND a b) => (OR -a -b))
	distNegs = distNegations(noImps)
	tree = C(distNegs)
	sets = getSets(tree)

	return sets, symbols

def C(F):
	if isinstance(F, str):
		# print("F is a literal: {}".format(F))
		return [F]

	if checkCNFDNF(F):
		# print("F is CNF: {}".format(F))
		return F

	# conversion from DNF to CNF doesn't work, submitting what I have because distribution handles it
	# it still works because of distribution, but I should ensure I can make the DNF conversion work for the future
	# if checkCNFDNF(F, True):
	# 	# print("F is DNF: {}".format(F))
	# 	return convertDNFtoCNF(F)

	if F[0] == "OR":
		p1 = C(F[1])
		p2 = C(F[2])
		return distribution(p1, p2)

	elif F[0] == "AND":
		return ["AND"] + [C(arg) for arg in F[1:]]		

def distribution(p1, p2):
	if isinstance(p1, list) and p1[0] == "AND":
		return ["AND", distribution(p1[1],p2), distribution(p1[2],p2)]
	elif isinstance(p2, list) and p2[0] == "AND":
		return ["AND", distribution(p1,p2[1]), distribution(p1,p2[2])]
	else:
		return ["OR", p1, p2]

def makeBinary(prop):
	if isinstance(prop, str):
		return prop
	elif len(prop) == 3:
		return [prop[0], makeBinary(prop[1]), makeBinary(prop[2])]
	elif len(prop) == 2:
		return [prop[0], makeBinary(prop[1])]
	else:
		# print("prop = {}".format(prop))
		return [prop[0], makeBinary(prop[1]), makeBinary([prop[0]] + prop[2:])]

def removeImps(expression):
	"""remove implications from expression

	Args:
		expression (irregular list): irregular list of expression

	Returns:
		irregular list: resulting expression after replacing implications.
	"""	
	reformExp = []

	if isinstance(expression, str):
		return expression

	token = expression[0]

	if token == "IF":
		orOp = "OR"
		reformExp.extend((orOp, ["NOT", removeImps(expression[1])], removeImps(expression[2])))

	elif token == "IFF":
		andOp = "AND"

		imp1 = ["OR", ["NOT", removeImps(expression[1])], removeImps(expression[2])]
		imp2 = ["OR", ["NOT", removeImps(expression[2])], removeImps(expression[1])]
	
		reformExp.extend((andOp, imp1, imp2))

	elif token == "AND" or token == "OR":
		reformExp.append(token)

		for item in expression[1:]:
			reformExp.append(removeImps(item))

	elif token == "NOT":
		reformExp.extend(("NOT", removeImps(expression[1])))

	else:
		reformExp.append(expression)

	return reformExp

def distNegations(expression, freq=0):
	"""distribute negations in boolean formula

	Args:
		expression (irregular list): irregular list of expression
		freq (int, optional): number of nested negations at that given recursive call. Defaults to 0.

	Returns:
		irregular list: resulting expression after getting rid of negatives
	"""	
	reformExp = []
	numNegs = freq % 2
	
	if isinstance(expression, str):
		return ('-' * (freq % 2)) + expression
	
	if isinstance(expression[0], list):
		return distNegations(expression[0], freq)

	token = expression[0]

	if token == "NOT":
		freq += 1
		numNegs = freq % 2
		nextToken = expression[1]

		if type(nextToken) is list:
			return distNegations(nextToken, freq=freq)			
		else:
			return ('-' * numNegs) + nextToken
			
	elif token == "AND" or token == "OR":

		if numNegs == 1:
			reformExp.append("OR" if token == "AND" else "AND")
		else:
			reformExp.append(token)

		for nextToken in expression[1:]:
			if type(nextToken) is list:
				recDist = distNegations(nextToken, freq=freq)
				reformExp.append(recDist)
				# reformExp.append(distNegations(nextToken, freq=freq))
			else:
				reformExp.append(('-' * numNegs) + nextToken)

	else:
		return ('-' * numNegs) + token
	
	return reformExp

def checkCNFDNF(expr, dnf=False, cnfPath=False):
	"""checks if the expression is a cnf or dnf

	Args:
		expr (irregular list): irregular list of the expression
		dnf (bool, optional): Indicates whether the expression is dnf. Defaults to False.
		cnfPath (bool, optional): Indicates whether the current expr is within a clausal path. Defaults to False.

	Returns:
		bool: whether or not the expression is cnf/dnf (depending on params)
	"""
	check = True
	checkVal1 = "AND" if dnf == False else "OR"
	checkVal2 = "OR" if dnf == False else "AND"
	token = expr[0]

	# if it encounters an AND after OR, return False (not CNF)
	# if it encounters an OR after an AND, return False (not DNF)
	if token == checkVal1:
		# if cnfPath == True:
		# 	check = False

		for i in range(2):
			nextToken = expr[i+1]			
			if isinstance(nextToken, list):
				check = checkCNFDNF(nextToken, dnf, True)
				if check == False:
					break
	
	elif token == checkVal2:
		for i in range(2):
			nextToken = expr[i+1]
			
			if isinstance(nextToken, list):
				if nextToken[0] == checkVal1:
					check = False
				else:
					check = checkCNFDNF(nextToken, dnf, cnfPath)

			if check == False:
				break

	return check	

def convertDNFtoCNF(expr):
	clauses = convertDNFtoCNFrec(expr)

	clauses = [clause if isinstance(clause, list) else [clause] for clause in clauses]
	clauses = [clause for clause in it.product(*clauses)]

	ret = []
	# print("convertDNFtoCNF clauses: {}".format(clauses))
	for clause in clauses:	
		# print("clause in convertDNFtoCNF: {}".format(clause))
		ret.append(["OR", *clause])
	

	# print("convertDNFtoCNF ret: {}".format(ret))
	# test = makeBinary([["AND", *ret]])
	# return makeBinary(["AND", *ret])
	return ["AND", *ret]

def convertDNFtoCNFrec(expr, branch=True):
	if not isinstance(expr, list):
		return [expr]

	token = expr[0]
	dnfClauses = []

	if token == "OR":
		clause = []
		
		for nextToken in expr[1:]:
			if isinstance(nextToken, list):
				clause.extend(convertDNFtoCNFrec(nextToken, True))
			else:
				clause.append(nextToken)

		newClause = []
		indLits = []
		indClauses = []
		for item in clause:
			if isinstance(item, list):
				indClauses.append(item)
			else:
				indLits.append(item)
		
		dnfClauses.extend(indLits)
		dnfClauses.extend(indClauses)
	elif token == "AND":
		newClause = []

		for nextToken in expr[1:]:
			if isinstance(nextToken, list):
				newClause.extend(convertDNFtoCNFrec(nextToken))
			else:
				newClause.append(nextToken)

		# newClause = [convertDNFtoCNF2(expr[1]), convertDNFtoCNF2(expr[2])]
		dnfClauses.extend(([newClause]))
	else:
		return token

	return dnfClauses

def getSets(expr, dnf=False, branch=False):
	""" returns a list of clauses (sets) for the given expression

	Args:
		expr (irregular list): irregular list of the expression
		dnf (bool, optional): Indicaties whether the expression is dnf. Defaults to False (cnf).

	Returns:
		list(set): list of clauses
	"""	

	clauses = []
	token = expr[0]
	
	# checkVal1 = "AND" if dnf == False else "OR"
	# checkVal2 = "OR" if dnf == False else "AND"

	if token == "AND":
		for nextToken in expr[1:]:
			if isinstance(nextToken, list):
				clauses.extend(getSets(nextToken, dnf, True))
			else:
				clauses.append(set([nextToken]))

	elif token == "OR":
		# build set of literals
		literals = set()
		for nextToken in expr[1:]:	
			if isinstance(nextToken, list):
				branch = True
				sets = getSets(nextToken, dnf, True)
				# print("Sets: {}".format(sets))

				for s in sets:
					# if on an OR branch, concatenate the set returned by the branch
					if branch == False:
						newSet = s | literals
						clauses.append(newSet)
						# print("newset: {}".format(newSet))
					else:
						for item in s:
							# print("item: {}".format(item))
							literals.add(item)

			else:
				# print("nextToken: {}".format(nextToken))
				literals |= set([nextToken])

		if len(literals) > 0:
			# don't append empty sets
			clauses.append(literals)

	else:
		clauses.append(set([token]))

	return clauses


"""
*** From the slides ***
Procedure C(F):
	Replace all φ1→φ2 with ¬φ1∨φ2
	Distribute all negations as far as you can
	Remove unnecessary parentheses, e.g. φ1∧(φ2∧φ3) to φ1∧φ2∧φ3
	If F is now CNF, then return it
	If F is now φ1∧φ2∧…∧φn:
		Return C(φ1)∧C(φ2)∧…∧C(φn)
	If F is now DNF, convert using algorithm on next slide
"""