""" Author: Brooks Olney

spec 1.0:
	Implements a SAT solver using the DPLL algorithm, with some enhancements.

"""
import collections
import re
import itertools as it
import time

performanceStats = {"oneLit" : 0, "affirmNeg": 0, "res": 0, "selRes" : 0, "selCont": 0, "branch1": 0, "branch2": 0, "preprocess": 0, "transform": 0}
performanceCount = {"oneLit" : 0, "affirmNeg": 0, "res": 0, "selRes" : 0, "selCont": 0, "branch1": 0, "branch2": 0, "preprocess": 0, "transform": 0}
resCount = 0
dpllCount = 0
supportedOperators = ["IF", "IFF", "AND", "OR", "NOT"]

def isSatisfiable(F):
	""" Uses Davis Putnam algorithm to compute satisfiability for F

	Args:
		F (string): s-expression format of well-formed equation

	Returns:
		bool : True => F is satisfiable, False => F is NOT satisfiable
	"""
	global performanceStats
	performanceStats = dict.fromkeys(performanceStats, 0)
	global performanceCount
	performanceCount = dict.fromkeys(performanceCount, 1)
	global resCount 
	global dpllCount
	resCount = 0
	dpllCount = 0

	# start1 = time.time()
	start = time.time()

	cnfClauses, symbols = convertToCNF(F)
	index = 1

	# print(newAssigns)
	newClauses = removeDuplicates(cnfClauses)

	newClauses = transformExp(newClauses, symbols)

	truthAssignments = {}
	# performanceStats["preprocess"] += time.time() - start

	sat = dpll(newClauses, truthAssignments)

	totTime = time.time() - start
	# print(totTime)
	if totTime == 0:
		totTime = 1
	for key, val in performanceStats.items():
		print("{}: {:.2f}%".format(key, (val/(totTime if totTime > 0 else 1)) * 100))
		if performanceCount[key] > 0:
			print("Average: {}".format(val/performanceCount[key]))
		print("")

	print("{}".format(totTime))

	print("resolution used {}% of the time".format((resCount / dpllCount) * 100))

	return "S" if sat == True else "U"

def transformExp(F, symbols):
	s = time.time()
	newSymbols = dict((symbol, val) for symbol, val in zip(symbols, range(1, len(symbols) + 1)))
	
	newF = []
	for clause in F:
		newClause = set()
		for lit in clause:
			if lit.startswith('-'):
				newClause |= {-1 * newSymbols[lit[len('-'):]]}
			else:
				newClause |= {newSymbols[lit]}
		
		newF.append(newClause)
	
	# performanceStats["transform"] += time.time() - s
	return newF

def removeDuplicates(cnfClauses):
	temp = [frozenset(clause) for clause in cnfClauses]
	temp = set(temp)
	return [set(clause) for clause in list(temp)]

def dpll(F, truthAssignments):
	""" implements dp/dpll variant sat solver using branching from dpll as well as resolution
			- resolution is tunable, meaning you can set the threshold to use it.
				- threshold of 0.01 (1%) means that we only use resolution if the expression gets less than 1% larger

	Args:
		F (list(set())): cnf formula
		truthAssignments (dict()): dictionary of truth assignments in given expression (not used in this implementation)

	Returns:
		bool: True if formula is satisfiable, else False
	"""
	global dpllCount
	dpllCount += 1

	oneLit = oneLiteralRule(F, truthAssignments)
	affirmNeg = affirmNegativeRule(F, truthAssignments)

	# contradiction
	if set() in F:
		return False
	
	# satisfiable
	if len(F) == 0:
		return True

	lit, numNew, numRemove = selectResLit(F)

	# cannot apply any rules?
	if oneLit == 0 and affirmNeg == 0 and numNew == 0:
		return False

	# threshold for using resolution, don't use if it blows up the expression by more than X%
	# for grading purposes: just increase the threshold to whatever. Make it a large number if you want it to use resolution on every iteration
	# Larger problems do well with a smaller threshold, smaller problems will use resolution much less with a small threshold, so you can increase it
	resThresh = 0.01
	if numNew / len(F) < resThresh:
		res = resolutionRule(F, truthAssignments, lit)
		return dpll(F, truthAssignments)
	else:
		lit = selectContLit(F)
		start = time.time()

		# check the left tail (set lit to true)
		truthAssignments[lit] = True 
		_F = [clause - {-lit} for clause in F if lit not in clause]
		
		performanceStats["branch1"] += time.time() - start
		performanceCount["branch1"] += 1

		check = dpll(_F, truthAssignments)
		if check:
			return check
		
		# check the right tail (set lit to false)
		start=time.time()
		truthAssignments[lit] = False        
		_F = [clause - {lit} for clause in F if -lit not in clause]

		performanceStats["branch2"] += time.time() - start
		performanceCount["branch2"] += 1

		check = dpll(_F, truthAssignments)
		if check:
			return check

	return False

def oneLiteralRule(F, truthAssignments):
	""" 
		Implements the one literal or unit propagation rule.
		If there is a unit clause ({'a'}) then evaluate it to true, remove clauses containing 'a', and remove '-a' from clauses
	"""
	start = time.time()

	# removedLits = set(next(iter(c)) for c in F if len(c) == 1)
	# negatedLits = {c * -1 for c in removedLits}
	# check = set(map(abs, removedLits))

	# if len(check) != len(removedLits):
	# 	F.append(set())
	# 	return 0
	
	# F[:] = [c - negatedLits for c in F if len(c & removedLits) == 0]
	# performanceStats["oneLit"] += time.time() - start
	# performanceCount["oneLit"] += 1
	# return len(removedLits)
	removedLits = set()

	for clause in F:
		
		# if clause contains one literal, remove the clause and assign it True
		if len(clause) == 1:
			removedLits |= clause

			lit = list(clause)[0] 

			# can reveal contradiction
			F[:] = [clause - {-lit} for clause in F]

			if isNegated(lit):
				truthAssignments[-lit] = False
			else:
				truthAssignments[lit] = True
	
	# generate set of negated literals from this rule, remove them from other clauses
	F[:] = [clause for clause in F if len(clause & removedLits) == 0]

	performanceStats["oneLit"] += time.time() - start
	performanceCount["oneLit"] += 1

	return len(removedLits)

def affirmNegativeRule(F, truthAssignments):
	""" 
		implements affirmative negative rule, or pure literal rule.
		If 'a' exists only in positive (or negative) form, set it to true and remove clauses containing it 
	"""
	start = time.time()

	removedLits = set()

	allLits = set(it.chain(*F))
	toRemove = [lit for lit in allLits if -lit not in allLits]

	removedLits = set(toRemove)

	# set truth assignment for P
	for lit in list(removedLits):
		if lit < 0:
			truthAssignments[-lit] = False
		else:
			truthAssignments[lit] = True

	# remove all clauses that contain P
	F[:] = [clause for clause in F if len(clause & removedLits) == 0]

	performanceStats["affirmNeg"] += time.time() - start
	performanceCount["affirmNeg"] += 1

	return len(removedLits)  

def resolutionRule(F, truthAssignments, lit):
	"""
		Implements resolution theorem. 
			1. Generates two lists to store clauses that contain +lit and -lit, and removes those clauses from F.
			2. Uses itertools.product to make all possible pairings between +lit and -lit clauses.
			3. If the clauses in the pair are equal, then it is a tautology - exclude it
			4. Else, union the two clauses and remove {lit, -lit} from the resolvent, add to F.
			5. Return # of resolvents
	"""
	start = time.time()
	global resCount
	resCount += 1

	# get all the clauses containing 'lit' and '-lit', remove them from the formula
	containsLit = [clause for clause in F if lit in clause]
	containsNegatedLit = [clause for clause in F if -lit in clause]
	_F = [clause for clause in F if clause not in containsLit and clause not in containsNegatedLit]

	# generate all the pairs, and the set of {lit, -lit} to remove from the resolvents
	newClauses = list(it.product(containsLit, containsNegatedLit))
	removeThis = {lit, -lit}

	# create the resolvents
	# newClauses = [set.union(clause[0], clause[1]) - removeThis for clause in newClauses]
	# this handles tautology rule and resolution
	fixedClauses = []
	for pair in newClauses:
		if pair[0] == pair[1]: # tautology!
			continue
		else:
			fixedClauses.append(set.union(pair[0], pair[1]) - removeThis)

	_F.extend(fixedClauses)

	# copy new formula
	F[:] = [clause for clause in _F]

	performanceStats["res"] += time.time() - start
	performanceCount["res"] += 1

	return len(newClauses)

def selectResLit(F):
	""" 
		Select lit to resolve on.
		Heuristic is min(#clauses(+lit) * #clauses(-lit)) i.e. total number of resolvents
	"""
	start = time.time()
	allLits = list(it.chain(*F))
	freq = collections.Counter(allLits)
	
	# generate heuristic for each literal
	heuristic = dict((lit, freq[lit] * freq[-lit]) for lit in set(map(abs, allLits)))

	if len(heuristic) == 0:
		return 0, 0, 0
	
	# heuristic is the minimum number of new clauses (i.e. => #clauses(+lit) * #clauses(-lit))
	ret = min(heuristic, key=heuristic.get)

	performanceStats["selRes"] += time.time() - start
	performanceCount["selRes"] += 1
	
	return ret, heuristic[ret], freq[ret] + freq[-ret]

def selectContLit(F):
	""" 
		Select a lit for branching.
			- uses sophisticated heuristics for selecting the literal to branch on
			- see: https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.137.3540&rep=rep1&type=pdf
				"Learning to Select Branching Rules in the DPLL Procedure for Satisfiability"
	"""
	start = time.time()
	
	allLits = list(it.chain(*F))
	ids = set(map(abs, allLits))

	# max occurrences
	freq = collections.Counter(allLits)
	MAXO = dict((lit, freq[lit] + freq[-lit]) for lit in set(allLits))
	MAXO_lit = max(set(MAXO), key=MAXO.get)

	# max occurrences in minimum size clauses (2)
	allLitsMinClause = list(it.chain(*[clause for clause in F if len(clause) <= 2]))
	freqMin = collections.Counter(allLitsMinClause)
	MOMS = dict((lit, freqMin[lit] + freqMin[-lit]) for lit in set(allLitsMinClause))

	if len(MOMS) > 0:
		MOMS_lit = max(set(MOMS), key=MOMS.get)
	else:
		MOMS_lit = 0

	# combinaton of MOMS and MAXO
	MAMS = dict((lit, freq[lit] + MOMS.get(-lit, 0)) for lit in ids)
	MAMS_lit = max(set(MAMS), key=MAMS.get)

	# JW is summation of 2 ** -n, where n is the size of the clause containing lit.
	# smaller clauses carry more weight
	JW_split = dict((lit, genJW(lit, F)) for lit in set(allLits))
	JW = dict((lit, JW_split.get(lit, 0) + JW_split.get(-lit, 0)) for lit in ids)
	JW_lit = max(set(JW), key=JW.get)


	tests = [MAXO_lit, MOMS_lit, MAMS_lit, JW_lit]
	SUP = []
	numUnits = len([c for c in F if len(c) == 1])

	for lit in tests:
		SUP.append(genUP(lit, numUnits, F))

	SUP_max = SUP.index(max(SUP))

	# SUP will check all 4 of the symbols from these metrics and see which one is the best
	# 'best' is determined by how many new unit clauses are present after branching on this variable
	if SUP_max == 0:
		ret = MAXO_lit if freq.get(MAXO_lit, 0) > freq.get(-MAXO_lit, 0) else -MAXO_lit
	elif SUP_max == 1:
		ret = MOMS_lit if freqMin.get(MOMS_lit, 0) > freqMin.get(-MOMS_lit, 0) else -MOMS_lit
	elif SUP_max == 2:
		ret = MAMS_lit
	else:
		ret = JW_lit if JW_split.get(JW_lit, 0) > JW_split.get(-JW_lit, 0) else -JW_lit

	# ret = max(set(MAMS), key=MAMS.get)
	performanceStats["selCont"] += time.time() - start
	performanceCount["selCont"] += 1

	return ret

def genUP(lit, numUnits, F):
	remove = {-lit}
	_F = [c - remove for c in F if lit not in c ]
	newNumUnits = len([c for c in _F if len(c) == 1])

	return newNumUnits - numUnits

def genJW(lit, F):
	return sum([2 ** (-1 * len(clause)) for clause in F if lit in clause])

def isNegated(lit):
	return lit < 0

def negate(lit):
	return -1 * lit
	
	
# --------------------------------------------------------- #
# code for parsing/converting s-expression to CNF is below  #
# --------------------------------------------------------- #

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

# following 2 functions were adapted from answers found in this stackoverflow:
# https://stackoverflow.com/questions/29189355/python-apply-distributive-law-to-elements-in-list

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

