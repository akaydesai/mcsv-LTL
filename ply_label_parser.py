'''
GRAMMAR
label : LNAME COLON formula

formula : PROP
        | LITERAL
        | NOT formula
        | LPAR formula OR formula RPAR
        | LPAR formula AND formula RPAR
        | LPAR formula XOR formula RPAR
        | LPAR formula IFF formula RPAR
'''

import ply.yacc as yacc 
from ply_label_lexer import tokens
from formulas import *

def p_label(p):
  ''' label : LNAME COLON formula '''
  p[0] = FormulaMonadic(p[1], p[3])

def p_formula_prop(p):
  ''' formula : PROP '''
  p[0] = FormulaMonadic('PROP', p[1])

def p_formula_literal(p):
  ''' formula : LITERAL '''
  p[0] = FormulaMonadic('LITERAL', p[1])

def p_formula_not(p):
  ''' formula : NOT formula  '''
  p[0] = FormulaMonadic('NOT', p[2])

def p_formula_or(p):
  ''' formula : LPAR formula OR formula RPAR '''
  p[0] = FormulaDyadic('OR', p[2], p[4])

def p_formula_and(p):
  ''' formula : LPAR formula AND formula RPAR '''
  p[0] = FormulaDyadic('AND', p[2], p[4])

def p_formula_xor(p):
  ''' formula : LPAR formula XOR formula RPAR '''
  p[0] = FormulaMonadic('NOT', FormulaDyadic('AND', FormulaDyadic('OR', FormulaMonadic('NOT', p[2]), p[4]), FormulaDyadic('OR', FormulaMonadic('NOT', p[4]), p[2])))

def p_formula_iff(p):
  ''' formula : LPAR formula IFF formula RPAR '''
  p[0] =  FormulaDyadic('AND', FormulaDyadic('OR', FormulaMonadic('NOT', p[2]), p[4]), FormulaDyadic('OR', FormulaMonadic('NOT', p[4]), p[2]))

def p_error(p):
  sys.exit("Syntax Error! Check your formula.")

parser = yacc.yacc()

#------ Test ------

# print parser.parse("_Label_:(x0.x1)") 