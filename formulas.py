from z3 import *

#Could simply use namedtuples from collections instead if making these classes by hand.
class Formula():     
  def __str__(self):
    return str( self.to_tuple())

class FormulaMonadic(Formula): #Note that even ('PROP','p') is of type monadic
  def __init__(self, type, child):
    self.type = type
    self.child = child

  def to_tuple(self):
    if self.type in ['PROP', 'LITERAL', 'LNAME']:
      return (self.type, self.child)
    return (self.type, self.child.to_tuple())

class FormulaDyadic(Formula):
  def __init__(self, type, left, right):
    self.type = type
    self.left = left
    self.right = right

  def to_tuple(self):
    if self.type in ['PROP', 'LITERAL', 'LNAME']:
      return (self.type, self.child)
    return (self.type, self.left.to_tuple(), self.right.to_tuple())

def newBools(i, var_names): 
  '''
  return new/ith set of vars (Si)
  '''
  return Bools([ str(i)+name for name in var_names ])

def nnf(formula):
  # print "NNF in progress: ",formula
  if formula.type in ['PROP', 'LITERAL']:
    return FormulaMonadic(formula.type, formula.child)
  elif formula.type in ['X', 'G','F']:
    return FormulaMonadic(formula.type, nnf(formula.child))
  elif formula.type in ['OR', 'AND', 'U']:
    return FormulaDyadic(formula.type, nnf(formula.left), nnf(formula.right))
  elif formula.type == 'NOT':    
    if formula.child.type in ['PROP', 'LITERAL']:
      return FormulaMonadic('NOT', formula.child)

    elif formula.child.type == 'X':
          return FormulaMonadic('X', nnf(FormulaMonadic('NOT', formula.child.child)))
    elif formula.child.type == 'F':
      return FormulaMonadic('G', nnf(FormulaMonadic('NOT', formula.child.child)))
    elif formula.child.type == 'G':
      return FormulaMonadic('F', nnf(FormulaMonadic('NOT', formula.child.child)))
    elif formula.child.type == 'NOT':
      return nnf(formula.child.child)

    else:
      if formula.child.type == 'AND':  
        return FormulaDyadic('OR', nnf(FormulaMonadic('NOT',formula.child.left)), nnf(FormulaMonadic('NOT', formula.child.right)))
      elif formula.child.type == 'OR':
        return FormulaDyadic('AND', nnf(FormulaMonadic('NOT',formula.child.left)), nnf(FormulaMonadic('NOT', formula.child.right)))
      elif formula.child.type == 'U':
        left = nnf(FormulaMonadic('NOT',formula.child.right))
        right = FormulaDyadic('AND',nnf(FormulaMonadic('NOT', formula.child.left)),nnf(FormulaMonadic('NOT',formula.child.right)))
        return FormulaDyadic('U', left, right)
  else:
    sys.exit("Error converting to NNF. Check parser code.") 

def boolToSAT(formula):
  '''
  Takes an AST of a propositional formula and converts it to Z3 SAT formula. Creates new variables.
  Use to create formulas from ASTs of Initial states and Transition relation.
  '''
  # print formula
  if formula.type == 'LITERAL':
    if formula.child == 'tru':
      return BoolVal(True)
    else:
      return BoolVal(False)
  elif formula.type == 'PROP':
    # print "Created new variable for: ", formula.child
    return Bool(formula.child)   #assuming Bool(key) with existing key returns same variable. Looks like it does.
  elif formula.type == 'NOT':
    return Not(boolToSAT(formula.child))
  elif formula.type == 'OR':
    return Or(boolToSAT(formula.left), boolToSAT(formula.right))
  elif formula.type == 'AND':
    return And(boolToSAT(formula.left), boolToSAT(formula.right))
  else:
    print "Got formula: ", formula
    sys.exit("Something is terribly wrong. Or got a non-boolean formula.")


# ----- Test -----

# print FormulaDyadic('U', FormulaMonadic('PROP', 'p'), FormulaMonadic('PROP', 'p'))
# print FormulaMonadic('PROP', 'p')

# print nnf(FormulaDyadic('U', FormulaMonadic('PROP', 'p'), FormulaMonadic('PROP', 'p')))
# print nnf(FormulaMonadic('NOT', FormulaMonadic('PROP', 'p')))