
def checkPrimed(tokens): 
  ''''
  Checks if there are any strings ending in "'" in the given list of strings.
  '''
  for tok in tokens:
    if tok[-1] == "'":
      return False
  return True
