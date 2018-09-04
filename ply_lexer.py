#!/usr/bin/python

import ply.lex as lex

tokens = (
  'OR',
  'AND',
  'NOT',
  'XOR',
  'IFF',
  'LPAR',
  'RPAR',
  'X',
  'F',
  'G',
  'U',
  'LITERAL',
  'PROP',   #Propositional variable.
  'LNAME'  #Label name.
  # 'DISCARD', #do not add discarded to list because this is passed to the parser which will then complain about unused tokens in the grammar.
  ) 

t_OR = r'\+'
t_AND = r'\.'
t_NOT = r'\!'
t_XOR = r'\^'
t_IFF = r'='
t_LPAR = r'\('
t_RPAR = r'\)'
def t_LITERAL(t):  #define as function because literals have lower precedence compared to other regexes. But patterns in functions are matched first. This avoids literals being matched as PROP.
  ''' tru|fls '''   #weird syntax(no r'')
  return t
t_X = r'X'
t_F = r'F'
t_G = r'G'
t_U = r'U'
t_PROP = r'[a-z]([a-z0-9]|\')*' #proposition names must start with alphabets.
t_LNAME = r'_([a-z]|[A-Z])+_'

def t_DISCARD(t):    #ignore whitespace.
  r'\s'
  pass

def t_error(t):
  print("Illegal character '%s'" % t.value[0])
  t.lexer.skip(1)

lexer = lex.lex()

#------- Test -------

# data = "F(tru U g) + fls"

# lexer.input(data)

# for tok in lexer:
#   print tok

 
