import itertools
def combinations(n):
  variables_total = 0
  listas = []
  for x in range(n+1):
    lista = list(itertools.combinations(range(n), x))
    variables_total += len(lista)
    listas.append(lista)
  return (listas, variables_total)

def posibleSolution(n):
  (listas, size) = combinations(3)
  for lista in listas:
    print "iteracion:"
    for tup in lista:
      if len(tup) is not 0:
        ids = list(tup)
        print "remove:", ids
      print "funciono?"
    print ". . . . . "
    print ""