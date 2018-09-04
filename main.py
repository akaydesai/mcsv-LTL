#!/usr/bin/python

import sys
from z3 import *

from ply_parser import parser
from ply_lexer import lexer

from formulas import *
from checks import *

#-------------- Input --------------
from input import *

#---------- Parsing and sanity checks ----------

#----- Initial states

lexer.input(initial_string)
var_names_init = list(set([tok.value for tok in lexer if tok.type == 'PROP']))
if not checkPrimed(var_names_init): #make sure no primed vars occur in init.
  sys.exit("Primed variables in initial states formula. Quitting...")
init_formula_z = boolToSAT(parser.parse(initial_string))
# print "INIT: ", init_formula_z

#------ Transition Relation

lexer.input(trans_rel_string)
tokens = [tok for tok in lexer]
var_names_unprimed = list(set([tok.value for tok in tokens if tok.type == 'PROP' and tok.value[-1] != "'"]))
# var_names_primed = list(set([tok.value for tok in tokens if tok.type == 'PROP' and tok.value[-1] == "'"]))
var_names_primed = [name + "'" for name in var_names_unprimed] #since var names should be in the same order.
# print "TRANS AST: ",parser.parse(trans_rel_string)
trans_formula_z = boolToSAT(parser.parse(trans_rel_string))
# print "TRANS: ", trans_formula_z

#------ Property (imported from input instead of replacing here.)
# print "NEG PROPERTY AST: ", property_formula
property_formula = nnf(property_formula)
print "NEGATED PROPERTY AST in NNF: ", property_formula

#-----------------------------------------------

#I(x), T(x,x') : Use these as templates; substitute when needed.
#x from var_names_unprimed, x' from var_names_primed

#---------- BMC Translations ----------

def unroll(initial, transition, k):  #Rewritten iteratively due to recursion depth limit ~1000.
  '''
  Takes initial states and Transition Relation as Z3 formulas and unrolls it up to k.
  '''

  # if k == 0:
  #   return substitute(initial, zip(Bools(var_names_init), newBools(0,var_names_init)))
  # else:
  #   sublist = zip(Bools(var_names_unprimed), newBools(k-1, var_names_unprimed)) + zip(Bools(var_names_primed), newBools(k,var_names_unprimed))
  #   return And(unroll(initial, transition, k-1), substitute(transition, sublist))

  unrolled = [ substitute(initial, zip(Bools(var_names_init), newBools(0,var_names_init))) ]
  if k == 0:
    return unrolled[0]
  else:
    for i in xrange(0,k):
      sublist = zip(Bools(var_names_unprimed), newBools(i, var_names_unprimed)) + zip(Bools(var_names_primed), newBools(i+1,var_names_unprimed))
      unrolled.append(substitute(transition, sublist))
    return And(unrolled)

# print "UNROLLED TR: ",unroll(init_formula_z, trans_formula_z, threshold)
# print unroll(init_formula_z, trans_formula_z, 1000) #exceeds recursion limit.

def isLoop(initial, transition, k, l):
  '''
  Takes initial and transition as Z3 formulas.
  '''
  return substitute(transition, zip(Bools(var_names_unprimed) + Bools(var_names_primed), newBools(k,var_names_unprimed) + newBools(l, var_names_unprimed)))

# print "ISLOOP(0,0): ", isLoop(init_formula_z, trans_formula_z, 1, 0)
# print "Test: ",isLoop(init_formula_z, trans_formula_z, 2, 1).eq(substitute(trans_formula_z, zip(Bools(var_names_unprimed), newBools(2, var_names_unprimed)) + zip(Bools(var_names_primed), newBools(1,var_names_unprimed))))

def existsLoop(initial, transition, k):
  '''
  Takes initial and transition as Z3 formulas.
  '''
  if k == 0:
    return isLoop(initial, transition, k, 0)
  return Or([isLoop(initial, transition, k, l) for l in xrange(0,k+1)])

# print "EXISTSLOOP(0): ", existsLoop(init_formula_z, trans_formula_z, 1)
# print "Test: ", existsLoop(init_formula_z, trans_formula_z, 0).eq(isLoop(init_formula_z, trans_formula_z, 0, 0))

def nonLoopTranslation(node, i, k):
  '''
  node is property AST in NNF.
  '''
  if i > k:              #Base case.
    return BoolVal(False)

  if node.type == 'PROP':
    return Bool(str(i)+node.child)
  elif node.type == 'NOT': #Since in NNF, child is PROP
    return Not(Bool(str(i)+node.child.child))
  elif node.type == 'OR':
    return Or(nonLoopTranslation(node.left, i, k), nonLoopTranslation(node.right, i , k))
  elif node.type == 'AND':
    return And(nonLoopTranslation(node.left, i , k), nonLoopTranslation(node.right, i, k))
  elif node.type == 'X':
    return nonLoopTranslation(node.child, i+1, k)
  elif node.type == 'G':
    return And(nonLoopTranslation(node.child, i, k), nonLoopTranslation(node, i+1, k))
  elif node.type == 'F':
    return Or(nonLoopTranslation(node.child, i, k), nonLoopTranslation(node, i+1, k))
  elif node.type == 'U':
    return Or(nonLoopTranslation(node.right, i, k), And(nonLoopTranslation(node.left, i, k), nonLoopTranslation(node, i+1, k)))

# print "NonLoopTranslation: ", nonLoopTranslation(property_formula, 0, threshold)

def succ(i, k, l):
  if i < k:
    return i+1
  elif i == k:
    return l
  else:
    sys.exit("Erroneous arguments to succ(). Quitting...")

def loopTranslation(node, i, k, l, called):
  '''
  node is property AST in NNF.
  '''
  # print "loopTranslation(", node,",", i,",", k,",",",", l,",", called,")"

  if node.type == 'PROP':
    return Bool(str(i)+node.child)
  elif node.type == 'NOT': #Since in NNF, child is PROP
    return Not(Bool(str(i)+node.child.child))
  elif node.type == 'OR':
    return Or(loopTranslation(node.left, i, k, l, set()), loopTranslation(node.right, i, k, l, set()))
  elif node.type == 'AND':
    return And(loopTranslation(node.left, i, k, l, set()), loopTranslation(node.right, i, k, l, set()))
  elif node.type == 'X':
    return loopTranslation(node.child, succ(i, k, l), k, l, set())
  elif node.type == 'G':
    if (i, l) in called:
      return BoolVal(True)
    called.add((i, l))    #write here instead of function argument because return type of add method is None.
    return And(loopTranslation(node.child, i, k, l, set()), loopTranslation(node, succ(i, k, l), k, l, called))
  elif node.type == 'F':
    if (i, l) in called:
      return BoolVal(False)
    called.add((i, l))
    return Or(loopTranslation(node.child, i, k, l, set()), loopTranslation(node, succ(i, k , l), k, l, called))
  elif node.type == 'U':
    if (i, l) in called:
      return BoolVal(False)
    called.add((i, l))
    return Or(loopTranslation(node.right, i, k, l, set()), And(loopTranslation(node.left, i, k, l, set()), loopTranslation(node, succ(i, k, l), k, l, called)))

# print "loopTranslation: ", loopTranslation(property_formula, 0, threshold, 2, set())

# ------------------- BMC Loop -------------------

# solver = Solver(None,main_ctx())
# solver.push()
for k in xrange(0,threshold+1):
  solver = Solver()  #Dafuq!! Need to use a new solver instance everytime!? Otherwise result is always UNSAT!
  
  # print "existsLoop({}): ".format(k),existsLoop(init_formula_z, trans_formula_z, k)
  # print "nonLoopTranslation({},{}): ".format(0,k), nonLoopTranslation(property_formula, 0, k)
  nonLoopPart = And(Not(existsLoop(init_formula_z, trans_formula_z, k)), nonLoopTranslation(property_formula, 0, k))
  # print "nonLoopPart: ",nonLoopPart

  loopPart = [ False ]
  for l in xrange(0, k+1):
    # print "isLoop ({},{}): ".format(k,l), isLoop(init_formula_z, trans_formula_z, k, l)
    # print "loopTranslation({},{},{}): ".format(0,k,l), loopTranslation(property_formula, 0, k, l, set())
    loopPart.append(And(isLoop(init_formula_z, trans_formula_z, k, l), loopTranslation(property_formula, 0, k, l, set())))


  loopPart = Or(loopPart) #Or,And can take a list of arguments.
  # print "loopPart[{},{}]: ".format(0,k), loopPart

  final_formula_z = And(unroll(init_formula_z, trans_formula_z, k) , Or(nonLoopPart, loopPart))
  # print "unrolled: ", unroll(init_formula_z, trans_formula_z, k)
  # print "final: ", final_formula_z

  solver.add(final_formula_z)
  # solver.push()

  if solver.check() == sat:
    print "\nResult: Found model at k = {}. ".format(k) ,"Property not valid."
    # print solver.unsat_core()
    break
  elif k == threshold:
    print "\nResult: Property is valid."
#-------------------------------------------------