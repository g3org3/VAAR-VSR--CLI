def declareVariable(type, name):
  if type == "Array":
    return "(declare-const " + name + " (Array Int Int))\n"
  if type == "HashMap":
    return "(declare-const " + name + " (Array String Int))\n"
  if type == "Matrix":
    return "(declare-const " + name + " (Array Int (Array Int Int)))\n"
  return "(declare-const " + name + " " + type + ")\n"

def assignVariable(vid, name, value, index = None):
  value = str(value)
  vid = "\n" if vid is None else  " ;; var.id: " + str(vid) + "\n"
  if index or index is 0:
    return "(assert (= (store "+name+" "+str(index)+" "+value +") "+name+"))"+vid
  else:
    return "(assert (= "+name+" "+value+"))"+vid

def comment(line, newline = ""):
  return ";; " + line + newline

def commentTitle(title, subtitle = None):
  output = ""
  output += ";;-----------------------------\n"
  output += ";;  " + title + "\n"
  if subtitle:
    output += ";;  " + subtitle + "\n"
  output += ";;-----------------------------\n"
  return output

def declareArray(name, size):
  output = ""
  output += declareVariable("Array", name)
  output += declareVariable("Int", name + "_size")
  output += assignVariable(None, name + "_size", size)
  return output

def declareMatrix(name, size):
  output = ""
  output += declareVariable("Matrix", name)
  output += declareVariable("Int", name + "_size")
  output += assignVariable(None, name + "_size", size)
  return output

def simpleFillArray(arrayname, list):
  output = ""
  for i in range(0, len(list)):
    val = list[i]
    output += assignVariable(None, arrayname, val, i)
  return output

def fillArray(toscaName, varid, values, array_name, getValue, isIgnored, saveValue):
  output = ""
  varid = int(varid) - 1
  # getValue = lambda name, value: toscaRawValueToSMTCorrectType(name, value, MainData)
  for i in range(0, len(values)):
    varid += 1
    rawvalue = values[i]
    saveValue(toscaName + "." + array_name + "_" + str(i))
    value = getValue(array_name+"_"+str(i), rawvalue)
    if isIgnored(varid):
      output += ";;"
    output += assignVariable(varid, array_name, value, i)
    
  return (varid, output)

def assignToArray(arrayName, index, value):
  return assignVariable(None, arrayName, value, index)

def assignToHashMap(arrayName, prop_name, value, varid = None):
  return assignVariable(varid, arrayName, value, "\""+prop_name+"\"")

def declareArrayOfDictionaries(arrayname):
  return "(declare-const " + arrayname + " (Array Int (Array String Int)))\n"

def declareDictionary(arrayname):
  return "(declare-const " + arrayname + " (Array String Int))\n"

def commentDonePart(title):
  return ";;------ Done " + title + " Setup ------\n\n"