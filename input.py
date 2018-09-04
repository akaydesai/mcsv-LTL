# Documentation
#
# Enter the input as strings below. 
# Supported boolean operators: Or(+), And(.), Not(!), Xor(^), Iff(=)
# Temporal Operators: X, F, G, U
# Literals: tru, fls
# Propositional variables must conform to the regex: [a-z]([a-z0-9]|\')* (start with lowercase alpha followed by any number of alphanumeric charcters.)
# Primed variables in transition relation will be treated as usual.
# All label names must conform to the regex: _([a-z]|[A-Z])+_  (start and end with underscore, upper or lower case alpha in between.)
# The labelling predicates are provided as a string, separated by commas.
# Label names may appear only in the property string(including negated_property_string), and nowhere else.

'''
GRAMMAR
label : LNAME COLON formula

formula : PROP
        | LITERAL
        | ! formula
        | ( formula + formula )
        | ( formula . formula )
        | ( formula ^ formula )
        | ( formula = formula )
'''

orig_property_string = "G _S_" #"(_P_ U _R_)"
initial_string = "(!x1.!x0)" #initial set of states.
trans_rel_string = "((((!x1.!x0).(x1'.!x0'))+((!x1.x0).(!x1'.!x0')))+(((x1.x0).(!x1'.!x0'))+((x1.!x0).((x1'.x0')+(!x1'.x0')))))" #"((x0'=!x0).((x0^x1) = x1'))"
labelling_string = "_P_: (!x0.!x1), _Q_ : (x0+x1), _R_ : (x0.x1), _S_ : ((!x0.!x1) + (x0+x1))"
threshold = 3

#----------- Take negation for ELTL ------------
negated_property_string = "!" + orig_property_string

# negated_property_string = "XXX _P_"  #Test ELTL formula by assigning it here.

#---------------- Conversion etc. -----------------

from formulas import *

from ply_parser import parser

property_formula = parser.parse(negated_property_string)

# print property_formula

from ply_label_parser import parser as labelparser

predicate_strings = labelling_string.split(',')
# print predicate_strings

predicates = [labelparser.parse(string) for string in predicate_strings]

def labelToFormula(lname):
  return [ formula.child for formula in predicates if formula.type == lname][0]

def replaceLabels(node):
  if node.type == 'LNAME':
    return labelToFormula(node.child)
  elif node.type in ['PROP', 'LITERAL']:
    return node
  elif node.type in ['NOT', 'X', 'F', 'G']:
    return FormulaMonadic(node.type, replaceLabels(node.child))
  elif node.type in ['OR', 'AND', 'XOR', 'IFF', 'U']:
    return FormulaDyadic(node.type, replaceLabels(node.left), replaceLabels(node.right))

property_formula = replaceLabels(property_formula)

#--------------------------------------------------