# -*- coding: latin-1 -*-
import numpy as np
import re
import z3
import time
import md5
from pyfancy import *
from functools import reduce

OUTPUT_PATH = './output/ouput.smt2'

def compose(*functions):
    def compose2(f, g):
        return lambda x: f(g(x))
    return reduce(compose2, functions, lambda x: x)

def dec2Bin(num):
  sym = "B"
  total = num
  if total > 999:
    sym = "KB"
    total = total / 1000
  if total > 999:
    sym = "MB"
    total = total / 1000
  if total > 999:
    sym = "GB"
    total = total / 1000
  if total > 999:
    sym = "TB"
    total = total / 1000
  if total > 999:
    sym = "PB"
    total = total / 1000
  return str(total) + " " + sym

def bin2Dec(rawBin):
  if len(str(rawBin).split('.')) is 4:
    return IP2Int(rawBin)
  else:
    rawBin = str(rawBin)
    if "MB" in rawBin:
      return str(int(rawBin.split("MB")[0]) * (10**6))
    if "GB" in rawBin:
      return str(int(rawBin.split("GB")[0]) * (10**9))
    if "KB" in rawBin:
      return str(int(rawBin.split("KB")[0]) * (10**3))
    if "TB" in rawBin:
      return str(int(rawBin.split("TB")[0]) * (10**12))
    if "PB" in rawBin:
      return str(int(rawBin.split("PB")[0]) * (10**15))
    if "B" in rawBin:
      return str(int(rawBin.split("B")[0]))
    return rawBin

def IP2Int(ip):
  o = map(int, ip.split('.'))
  res = (16777216 * o[0]) + (65536 * o[1]) + (256 * o[2]) + o[3]
  return str(res)


def Int2IP(ipnum):
  o1 = int(ipnum / 16777216) % 256
  o2 = int(ipnum / 65536) % 256
  o3 = int(ipnum / 256) % 256
  o4 = int(ipnum) % 256
  return '%(o1)s.%(o2)s.%(o3)s.%(o4)s' % locals()

def preProcessIPs(line):
  try:
    pattern = re.compile(r"([0-9]{1,3})\.([0-9]{1,3})\.([0-9]{1,3})\.([0-9]{1,3})")
    start = pattern.search(line).start()
    end = pattern.search(line).end()
    ipRaw = line[start:end]
    ipNumber = IP2Int(ipRaw)
    return pattern.sub(ipNumber, line)
  except:
    return line

def preProcessBytes(line):
  # detect bytes
  try:
    pattern = re.compile(r"(\d)+(\ )?(KB|MB|GB|TB|PB|B)")
    start = pattern.search(line).start()
    end = pattern.search(line).end()
    bytesRaw = line[start:end]
    bytesNumber = bin2Dec(bytesRaw)
    return pattern.sub(bytesNumber, line)
  except:
    return line
def toscaRawValueToSMTCorrectType(attributeName, value, MainData):
  # if is ip
  if len(str(value).split('.')) is 4:
    MainData["valueTypes"][attributeName] = "ip"
    return IP2Int(value)
  
  # if is memory size 100 GB
  sizes = ["B", "KB", "MB", "GB", "TB", "PB"]
  for k in sizes:
    if k in str(value):
      MainData["valueTypes"][attributeName] = "size"
      return bin2Dec(value)

  # if is true or false
  if str(value) is "True" or str(value) is "False":
    MainData["valueTypes"][attributeName] = "bool"
    return str(int(value))

  # if is int/port
  try:
    MainData["valueTypes"][attributeName] = "int"
    return str(int(value))
  except:
    # if is float/version
    # if is string
    MainData["valueTypes"][attributeName] = "string"
    result = int(md5.new(value).hexdigest(), 16)
    MainData["stringsHashMap"][result] = value
    return result
def parseUserRules(rawInput, sizes):
  inside_for = False
  invalid_for = True
  empty_for = False
  for_name = ""
  for_iterator_name =""
  validArrays = sizes.keys()
  smt2  = "\n\n;;------------------------\n"
  smt2 += ";;  USER Rules\n"
  smt2 += ";;------------------------\n"
  for line in rawInput.split('\n'):
    line = preProcessBytes(line)
    line = preProcessIPs(line)
    # print line, invalid_for, empty_for, inside_for
    if ";;endfor" in line:
      # print invalid_for
      if not invalid_for:
        smt2 += "  )\n"
        smt2 += "))\n\n"
      else:
        smt2 += line + "\n\n"
      inside_for = False
      invalid_for = True
      empty_for = False
    elif inside_for:
      if invalid_for:
        smt2 += ";;    " + line + "\n"
      elif for_iterator_name in line:
        smt2 += "    " + line.replace(for_iterator_name, "(select " + for_name + " x) ") + "\n"
      else:
        smt2 += "    " + line + "\n"
    elif ";;for " in line:
      inside_for = True
      for_name = line.split("in ")[1]
      for_iterator_name = line.split("in ")[0].split(";;for ")[1]
      if for_name in validArrays:
        arraySize = sizes[for_name]
        invalid_for = arraySize < 1
        empty_for = arraySize < 1
        smt2 += line + " | size: "+str(arraySize)+"\n" if not empty_for else ""
      if not invalid_for:
        smt2 += "(assert (forall ((x Int))\n"
        smt2 += "  (=>\n"
        smt2 += "    (and (< x " + for_name + "_size) (> x -1))\n"
      else:
        if empty_for:
          smt2 += ";;Ignore rules, because no " + for_name + " descriptions where found!\n"
        else:
          smt2 += ";; invalid for, did not match array name: \"" + for_name +"\"\n"
        smt2 += line + "\n"
    else:
      smt2 += line
  smt2 += ";;------ Done USER Rules ------\n\n"
  return smt2
"""
(assert (forall ((x Int))
  (=>
  (and (< x vms_size) (> x -1))
  (and
    (< (select (select vms x) "cpus") 10)
    (< (select (select vms x) "mem_size") 700000000)
  )
  )
))
;;for vm_i in vms
(and
  (< vm_i "mem_size" 700 MB)
  (< vm_i "num_cpus" 3)
)
;;endfor
"""

"""---------------
  GET VNFS
---------------"""
def getVNFs(tosca, MainData, ToscaFullType):
  ToscaType = ToscaFullType.split(".").pop()
  arrayLabel = ToscaType.lower()
  Title = ToscaType.upper() + "S"
  arrayName = arrayLabel + "s"
  
  if not hasattr(tosca, "nodetemplates"):
    MainData["blob"] += ";; this tosca conf does not have any nodetemplates"
    MainData["sizes"][arrayLabel] = 0
    return MainData

  nodetemplates = tosca.nodetemplates
  itemsInToscaConf = filter(lambda x: x.type == ToscaFullType, nodetemplates)

  if len(itemsInToscaConf) == 0:
    smt2  = ";;------------------------\n"
    smt2 += ";;  " + Title + " Setup: 0, None detected\n"
    smt2 += ";;------------------------\n"
    smt2 += "(declare-const " + arrayName + " (Array Int (Array String Int)))\n"
    smt2 += "(declare-const " + arrayName + "_size Int)\n"
    smt2 += "(assert (= " + arrayName + "_size 0))\n"
    
    MainData["blob"] += smt2
    MainData["sizes"][arrayLabel] = 0
    return MainData


  smt2  = ";;------------------------\n"
  smt2 += ";;  " + Title + " Setup\n"
  smt2 += ";;------------------------\n"
  smt2 += "(declare-const " + arrayName + " (Array Int (Array String Int)))\n"
  for i in range(1, len(itemsInToscaConf) + 1):
    smt2 += "(declare-const props_" + arrayLabel + str(i) + " (Array String Int))\n"

  smt2 += "\n(declare-const " + arrayName + "_size Int)\n"
  smt2 += "(assert (= " + arrayName + "_size " + str(len(itemsInToscaConf)) +"))\n"
  smt2 += ";;------ Done " + Title + " Setup ------\n\n"

  smt2 += ";;------------------------\n"
  smt2 += ";;  " + Title + " Insert Values From Conf\n"
  smt2 += ";;------------------------\n"

  for i in range(1, len(itemsInToscaConf) + 1):
    # current object of type
    vm = itemsInToscaConf[i - 1]
    smt2 += ";; "+arrayLabel+"-name: " + vm.name + "\n"
    props_name = "props_" + arrayLabel + str(i)
    
    for item in vm.templates:
      if item is vm.name:
        for (propName, propValues) in vm.templates[item].items():
          if type(propValues) is type({}):
            for (key, val) in propValues.items():
              if not key in MainData['rules']['attributes'] and MainData['optimized']:
                continue
              value = toscaRawValueToSMTCorrectType(key, val, MainData)
              if MainData["variables"]["total"] not in MainData["skipIDs"]:
                smt2 += "(assert (= (store "+props_name+" \"" + key +"\" " + bin2Dec(value) +") "+props_name+"))" + ";; var.id: " + str(MainData["variables"]["total"]) +"\n"
              else:
                smt2 += ";; (assert (= (store "+props_name+" \"" + key +"\" " + bin2Dec(value) +") "+props_name+"))" + ";; var.id: " + str(MainData["variables"]["total"]) +"\n"
              MainData["variables"]["total"] += 1
              MainData["variables"]["names"].append(vm.name + "." + props_name + "." + key)
          # else: this is actually the type: tosca.nodes.nfv.VNF
            # print ".items()", propValues
        smt2 += "(assert (= (store "+arrayName+" "+str(i-1)+" "+props_name+") "+arrayName+"))\n\n"
        break
    # print "------>"
  smt2 += ";;------ Done "+Title +" Values ------\n\n"
  
  MainData["blob"] += smt2
  MainData["sizes"][arrayName] = len(itemsInToscaConf)
  return MainData

"""---------------
  GET VMS
---------------"""
def getVMs(tosca, MainData):
  if not hasattr(tosca, "nodetemplates"):
    MainData["blob"] += ";; this tosca conf does not have any nodetemplates"
    MainData["sizes"]["vms"] = 0
    return MainData

  nodetemplates = tosca.nodetemplates
  vms = filter(lambda x: x.type == "tosca.nodes.Compute", nodetemplates)

  if len(vms) == 0:
    smt2  = ";;------------------------\n"
    smt2 += ";;  VMS Setup: 0, None detected\n"
    smt2 += ";;------------------------\n"
    smt2 += "(declare-const vms (Array Int (Array String Int)))\n"
    smt2 += "(declare-const vms_size Int)\n"
    smt2 += "(assert (= vms_size 0))\n"
    MainData["blob"] += smt2
    MainData["sizes"]["vms"] = 0
    return MainData


  smt2  = ";;------------------------\n"
  smt2 += ";;  VMS Setup\n"
  smt2 += ";;------------------------\n"
  smt2 += "(declare-const vms (Array Int (Array String Int)))\n"
  for i in range(1, len(vms) + 1):
    smt2 += "(declare-const props_vm" + str(i) + " (Array String Int))\n"

  smt2 += "\n(declare-const vms_size Int)\n"
  smt2 += "(assert (= vms_size " + str(len(vms)) +"))\n"
  smt2 += ";;------ Done VMS Setup ------\n\n"

  smt2 += ";;------------------------\n"
  smt2 += ";;  VMS Insert Values From Conf\n"
  smt2 += ";;------------------------\n"

  for i in range(1, len(vms) + 1):
    vm = vms[i - 1]
    smt2 += ";; vm-name: " + vm.name + "\n"
    props = vm.get_capabilities()['host'].get_properties().items()
    props_name = "props_vm" + str(i)
    array_name = "vms"
    for (key, prop) in props:
      if not key in MainData['rules']['attributes'] and MainData['optimized']:
        continue
      if MainData["variables"]["total"] not in MainData["skipIDs"]:
        smt2 += "(assert (= (store "+props_name+" \"" + key +"\" " + bin2Dec(prop.value) +") "+props_name+"))" + ";; var.id: " + str(MainData["variables"]["total"]) +"\n"
      else:
        smt2 += ";; (assert (= (store "+props_name+" \"" + key +"\" " + bin2Dec(prop.value) +") "+props_name+"))" + ";; var.id: " + str(MainData["variables"]["total"]) +"\n"
      MainData["variables"]["total"] += 1
      MainData["variables"]["names"].append(vm.name + "." + props_name + "." + key)
    smt2 += "(assert (= (store "+array_name+" "+str(i-1)+" "+props_name+") "+array_name+"))\n\n"
  smt2 += ";;------ Done VMS Values ------\n\n"
  
  MainData["blob"] += smt2
  MainData["sizes"]["vms"] = len(vms)
  return MainData


"""---------------
  GET CPS
---------------"""
def getCPS(tosca):
  if not hasattr(tosca, 'nodetemplates'):
    return ([], {})
  nodetemplates = tosca.nodetemplates

  # Obtain the Connection points
  cps = filter(lambda x: x.type == "tosca.nodes.nfv.CP", nodetemplates)

  # Obtain the virtuallink of the connection point
  cps = map(lambda x: {
    "name": x.name,
    "requirements": x.requirements,
    "link": filter(lambda y: y.has_key('virtualLink'), x.requirements)
    }, cps)

  # Grab the actual value of the virtual link
  cps = map(lambda x: {
    "name": x['name'],
    "requirements": x['requirements'],
    "link": x['link'][0]['virtualLink'] if (len(x['link']) > 0) else ""
    }, cps)

  # Array to Object/Dictionary, where name is the key
  cpsDict = {}
  for cp in cps:
    cpsDict[cp['name']] = cp

  connectivity = []

  # Change Dictionary to fixed Array and get length
  cpsItems = sorted(cpsDict.items(), key=lambda x: x[0])
  return (cpsItems, cpsDict)

"""---------------
GET Connecttivity Graph
---------------"""
def getConnectivityGraph(cpsItems, cpsDict):
  connectivity = []
  cpsItemsLength = len(cpsItems)

  # Fill the array with arrays of zeros
  for cp in cpsItems:
    connectivity.append([0] * cpsItemsLength)

  # Fill the connectivity matrix
  for r in range(0, cpsItemsLength):
    for c in range(0, cpsItemsLength):
      if r == c:
        connectivity[r][c] = 0
      else:
        # get relationship
        cpfrom = cpsItems[r][0]
        cpto = cpsItems[c][0]
        if cpsDict[cpfrom]['link'] == cpsDict[cpto]['link']:
          # print cpfrom, '->', cpto, '(', r, ',', c,')'
          connectivity[r][c] = 1
  return connectivity

"""---------------
  Debug Matrix
---------------"""
def debugMatrix(title, flag, cpsItems, matrix):
  if (not flag): return
  print title
  print '\t--- ', ' '.join(map(lambda x: x[0], cpsItems))
  for x in range(0, len(cpsItems)):
    _matrix = matrix[x].tolist()[0] if hasattr(matrix[x], 'tolist') else matrix[x]
    print '\t', cpsItems[x][0] + "  ", " | ".join(map(lambda y: str(y), _matrix))

"""---------------
  Get Forwarding Paths
---------------"""
def getForwardingPaths(tosca):
  if not hasattr(tosca, 'nodetemplates'):
    return []
  nodetemplates = tosca.nodetemplates

  forwarding_paths = filter(lambda x: x.type == "tosca.nodes.nfv.FP", nodetemplates)
  forwarding_paths = map(lambda x: {
    "relations": map(lambda y: y["forwarder"], x.requirements),
    "name": x.name
  }, forwarding_paths)
  return forwarding_paths

"""---------------
  Func Chains
---------------"""
def func_chains(forwarding_paths, cpsItems):
  matrixList = []
  for fp in forwarding_paths:
    matrix = []
    total_cps = len(cpsItems)
    for cp in cpsItems:
      matrix.append([0] * total_cps)
    cps_in_FP = {}
    for forwarder in fp["relations"]:
      fromCP = forwarder["capability"]
      toCP = forwarder['relationship']
      cps_in_FP[fromCP] = 1
      cps_in_FP[toCP] = 1
      # print fromCP, "->", toCP
      names = map(lambda x: x[0], cpsItems)
      fromIndex = names.index(fromCP)
      toIndex = names.index(toCP)
      matrix[fromIndex][toIndex] = 1
    matrixList.append({
      "name": fp["name"],
      "matrix": matrix,
      "total_cps": len(cps_in_FP.items()),
      "cps": cps_in_FP.items()
    })
  return matrixList


"""------------------
  Has a Loop: found any 1s in the diagonal?
------------------"""
def hasLoop(matrix):
  return len(filter(lambda x: x is not 0, matrix.diagonal().tolist()[0])) > 0


"""------------------
  Get Position of Negative
------------------"""
def getPosOfNegative(cpsItems, matrix):
  _matrix = matrix.tolist()
  names = map(lambda x: x[0], cpsItems)
  message = "  |> Found connection problem"
  fromNode = ""
  toNode = ""
  for x in range(0, len(_matrix)):
    for y in range(0, len(_matrix)):
      if _matrix[x][y] == -1:
        message += "\n    • " + names[x] + " -x-> " + names[y]
        fromNode = names[x]
        toNode = names[y]
  return { "output": message, "problem": "connectivity", "from": fromNode, "to": toNode }


"""------------------
  Nodes Involved
------------------"""
def nodesInvolved(cpsItems, matrix):
  _matrix = matrix.tolist()
  _names = []
  names = map(lambda x: x[0], cpsItems)
  for x in range(0, len(_matrix)):
    if _matrix[x][x] is not 0:
      _names.append(names[x])
  return _names


"""------------------
  debugBugMatrix
------------------"""
def debugBugMatrix(matrixBugs, config, apiOutput):
  for tupl in matrixBugs:
    (name, bugs) = tupl
    if len(bugs) is not 0:
      if bool(config['apiOutput']):
        apiOutput['FPIssues'][name] = bugs
      else:
        pyfancy().underlined("⚠️  " + name).output()
        for bug in bugs:
          print bug['output']
    else:
      if bool(config['apiOutput']):
        apiOutput['FPIssues'][name] = []
      else:
        pyfancy("  ✅  " + name).output()


"""------------------
  Find Loop
------------------"""
def findLoop(connectivity, cpsItems, obj, args):
  matrix = obj['matrix']
  total_cps = obj['total_cps']
  name = obj['name']
  m = np.matrix(matrix)
  n = total_cps
  if args.verbose or args.diff:
    pyfancy("\n   -->  ").underlined(name +":").output()
    debugMatrix("", args.verbose or args.diff, cpsItems, m)
  difference = np.matrix(connectivity) - m
  bugs = []
  if args.diff:
    if difference.min() == -1:
      pyfancy().yellow("\n\tConnection problem detected").output()
    else:
      pyfancy().dim("diff->").output()
    debugMatrix("", args.diff, cpsItems, difference)
  if difference.min() == -1:
    bugs.append(getPosOfNegative(cpsItems, difference))
  for x in range(1, n + 1):
    matrixToPower = m**x
    if (hasLoop(matrixToPower)):
      cpsInvolved = ", ".join(nodesInvolved(cpsItems, matrixToPower))
      bugs.append({
        "ouput": "  |> Found loop!\n    • Length: " + str(x) + "\n    •    CPs: " + cpsInvolved,
        "problem": "loop",
        "length": x,
        "cpsInvolved": nodesInvolved(cpsItems, matrixToPower)
      })
      if args.verbose:
        pyfancy().yellow("\n\tLoop detected in the matrix below: ^("+str(x)+")").output()
        debugMatrix("", args.verbose, cpsItems, matrixToPower)
      break
  # if not args.verbose and not args.diff:
    # if len(bugs) is not 0:
    #     pyfancy().underlined("⚠️  " + name).output()
    #     for bug in bugs:
    #         print bug
    # else:
    #     pyfancy("✅  " + name).output()
  return (name, bugs)

def prettifyValue(dataType, rawValueFromSolver):
  if dataType is "ip":
    return Int2IP(int(rawValueFromSolver))
  elif dataType is "size":
    return dec2Bin(int(rawValueFromSolver))
  elif dataType is "bool":
    return "true" if int(rawValueFromSolver) is 1 else "false"
  return rawValueFromSolver

def getAttributesFromUserRules(rawRules):
  attList = []
  for line in rawRules.split('\n'):
    try:
      pattern = re.compile(r"\"(.+)\"")
      start = pattern.search(line).start()
      end = pattern.search(line).end()
      att = line[start+1:end-1]
      if not att in attList:
        attList.append(att)
    except:
      attList = attList
  return attList

"""------------------
  Prepare output for z3
------------------"""
def prepareOutputForZ3(tosca, USER_RULES_PATH, ids = []):
  output = open(OUTPUT_PATH, mode='w')
  userRawRules = open(USER_RULES_PATH).read()
  MainData = {
    "blob": "",
    "variables": {
      "names": [],
      "total": 0
    },
    "sizes": {
      "vms": 0,
      "vnfs": 0,
      "cps": 0,
      "networks": 0,
    },
    "custom_rules": USER_RULES_PATH,
    "optimized": True,
    "skipIDs": ids,
    "stringsHashMap": {},
    "valueTypes": {},
    "rules": {
      "attributes": getAttributesFromUserRules(userRawRules)
    }
  }

  getVMs(tosca, MainData)
  getVNFs(tosca, MainData, "tosca.nodes.nfv.VNF")
  getVNFs(tosca, MainData, "tosca.nodes.Network")
  getVNFs(tosca, MainData, "tosca.nodes.nfv.CP")
  
  MainData["blob"] += parseUserRules(userRawRules, MainData["sizes"])
  output.write(MainData["blob"])
  output.close()
  return MainData

"""------------------
  Solve
------------------"""
def solve():
  f = z3.parse_smt2_file(OUTPUT_PATH)
  s = z3.Solver()
  s.add(f)
  return (s, str(s.check()))

def findSolution(tosca, MainData, comb, config, apiOutput):
  _variables_total = MainData["variables"]["total"]
  _variables_names = MainData["variables"]["names"]
  user_path_custom_rules = MainData["custom_rules"]
  quit = False
  quitReason = "unkown"
  solutionsFound = 0
  maxSolutions = int(config["suggestions"])
  
  if (solutionsFound >= maxSolutions):
    quit = True
    quitReason = "Max suggestions found (" + str(maxSolutions) + ")"
    apiOutput['quitReason'] = { "output": quitReason, "reason": "MaxSolutions", "data": maxSolutions }
    return quit
  (listas, listas_size) = comb.combinations(_variables_total)
  
  for lista in listas:
    if quit:
      break
    for tup in lista:
      if quit:
        break
      if len(tup) is not 0:
        ids = list(tup)
        if (len(ids) > int(config["maxChanges"])):
          quitReason = "Maximun changes exceed! (" + str(len(ids)) + ")"
          apiOutput['quitReason'] = { "output": quitReason, "reason": "MaxChanges", "data": len(ids) }
          quit = True
          break
        if (time.time() - config["start_time"] > int(config["timeout"])):
          quitReason = "Timeout!, it took too long, more than (" + config["timeout"] + " s)"
          apiOutput['quitReason'] = { "output": quitReason, "reason": "Timeout", "data": time.time() }
          quit = True
          break
        prepareOutputForZ3(tosca, user_path_custom_rules, ids)
        (s, status) = solve()
        if status is "sat":
          # print(s.model())
          # print(ids)
          suggestion = { "output": "", "changes": 0 }
          suggestion['output'] = "\nIf you make these " + str(len(ids)) +  " changes your configuration request will pass"
          suggestion['totalChanges'] = len(ids)
          suggestion['changes'] = []
          z3ModelName = []
          z3ModelProp = []
          z3ModelFullName = []
          for idd in ids:
            z3ModelName.append(_variables_names[idd].split('.')[1])
            z3ModelProp.append(_variables_names[idd].split('.')[2])
            z3ModelFullName.append(_variables_names[idd])
          # print " | ".join(z3ModelFullName)
          for var in s.model():
            if str(var) in z3ModelName:
              # print "FOUND:", str(var)
              indices = [i for i, x in enumerate(z3ModelName) if x == str(var)]
              for index in indices:
                prop = z3ModelProp[index]
                fullname = z3ModelFullName[index]
                values = str(s.model()[var])
                if prop in values:
                  values = values[values.index(prop):]
                  try:
                    values = values[:values.index(',\n')]
                  except:
                    values = values[:values.index(', else')]
                  rawValueFromSolver = values.split('" -> ')[1]
                  prettyValue = rawValueFromSolver
                  try:
                    dataType = MainData["valueTypes"][fullname.split('.').pop()]
                    prettyValue = prettifyValue(dataType, rawValueFromSolver)
                    suggestion['output'] += "\n    - " + " > ".join(fullname.split('.')) + ' to ' + "(" + prettyValue + ")"
                    suggestion['changes'].append({
                      "toscaObjectName": fullname.split('.')[0],
                      "propertyName": fullname.split('.').pop(),
                      "fullname": fullname,
                      "prettyValue": prettyValue,
                      "rawValue": rawValueFromSolver 
                    })
                  except:
                    if str(fullname.split('.').pop()) == "mem_size":
                      prettyValue = dec2Bin(int(prettyValue))
                    suggestion['output'] += "\n    - " + " > ".join(fullname.split('.')) + ' to ' + "(" + prettyValue + ")"
                    suggestion['changes'].append({
                      "toscaObjectName": fullname.split('.')[0],
                      "propertyName": fullname.split('.').pop(),
                      "fullname": fullname,
                      "prettyValue": prettyValue,
                      "rawValue": rawValueFromSolver
                    })

                else:
                  suggestion['output'] += "\nnot found `" + prop + "` in values" + " ".join(values.split(',\n'))
            # else:
            #   if not "k" in str(var):
            #     print "NOT-FOUND:", str(var)
          solutionsFound += 1
          apiOutput['suggestions'].append(suggestion)
          if not bool(config['apiOutput']):
            print suggestion['output']
          if (solutionsFound >= maxSolutions):
            quit = True
            quitReason = "Max suggestions found (" + str(maxSolutions) + ")"
            apiOutput['quitReason'] = { "output": quitReason, "reason": "MaxSolutions", "data": solutionsFound }
          # max soluciones encontradas o el tiempo expiro
  return quit


def playground(tosca):
  if not hasattr(tosca, "nodetemplates"):
    print("no nodetemplates")
  for node in tosca.nodetemplates:
    nodeDict = node.templates.get(node.name)
    skipProps = ['type']
    props = node.get_properties_objects()
    lenstr = compose(str, len)
    print("type       : " + node.type)
    print("name       : " + node.name)
    print("parent-type: " + node.parent_type.type)
    print("props: " + lenstr(props))
    # for prop in props: print("  * " + str(prop.name) + "<" + str(prop.type) + ">=" + str(prop.value))
    
    # generic prop read
    for (key, values) in nodeDict.items():
      if key in skipProps: continue
      print(key + ":")
      if type(values) is type({}):
        for (name, value) in values.items():
          if type(value) is type({}):
            print("  "+ name + ":")
            for (k, v) in value.items(): print("    " + k + "=" + str(v))
          else:
            print("  " + name + "=" + str(value))
      elif type(values) is type([]):
        for item in values:
          if type(item) is type({}):
            for (k, v) in item.items(): print("    " + k + "=" + str(v))
          else:
            print("  " + "- " + str(item))
      else:
        print("  " + str(props))
    print("- - - - - - - - - - - - - - - - - - - - - - -")