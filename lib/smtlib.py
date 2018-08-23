def declareVariable(type, name):
  if type == "Array":
    return "(declare-const " + name + " (Array Int Int))\n"
  if type == "HashMap":
    return "(declare-const " + name + " (Array String Int))\n"
  return "(declare-const " + name + " " + type + ")\n"

def assignVariable(vid, name, value, index = None):
  value = str(value)
  vid = "\n" if vid is None else  " ;; var.id: " + str(vid) + "\n"
  if index or index is 0:
    return "(assert (= (store "+name+" "+str(index)+" "+value +") "+name+"))"+vid
  else:
    return "(assert (= "+name+" "+value+"))"+vid

def declareArray(type, name, size):
  output  = declareVariable(type, name)
  output += declareVariable("Int", name + "_size")
  output += assignVariable(None, name + "_size", size)
  return output

def fillArray(varid, values, array_name, getValue, isIgnored):
  output = ""
  varid = int(varid) - 1
  # getValue = lambda name, value: toscaRawValueToSMTCorrectType(name, value, MainData)
  for i in range(0, len(values)):
    varid += 1
    # if isIgnored(varid): continue
    rawvalue = values[i]
    value = getValue(array_name+"."+str(i), rawvalue)
    output += assignVariable(varid, array_name, value, i)
  return (varid, output)

def assignToArray(arrayName, index, value):
  return assignVariable(None, arrayName, value, index)

def assignToHashMap(arrayName, prop_name, value, varid = None):
  return assignVariable(varid, arrayName, value, "\""+prop_name+"\"")