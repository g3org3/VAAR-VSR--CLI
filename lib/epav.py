# -*- coding: latin-1 -*-
import numpy as np
import re
import z3
import time
import md5
import json
import smtlib
import extras
from pyfancy import *
from functools import reduce

OUTPUT_PATH = './output/ouput.smt2'

def getCPS(tosca):
  return extras.getCPS(tosca)
def getConnectivityGraph(cpsItems, cpsDict):
  return extras.getConnectivityGraph(cpsItems, cpsDict)
def debugMatrix(title, flag, cpsItems, matrix):
  return extras.debugMatrix(title, flag, cpsItems, matrix)
def getForwardingPaths(tosca):
  return extras.getForwardingPaths(tosca)
def debugBugMatrix(matrixBugs, config, apiOutput):
  return extras.debugBugMatrix(matrixBugs, config, apiOutput)
def func_chains(forwarding_paths, cpsItems):
  return extras.func_chains(forwarding_paths, cpsItems)
def findLoop(connectivity, cpsItems, obj, args):
  return extras.findLoop(connectivity, cpsItems, obj, args)

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
  rawBin = str(rawBin).upper()
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

def preProcessor(line, MainData):
  if preProcessBytes(line):
    return preProcessBytes(line)
  elif preProcessIPs(line):
    return preProcessIPs(line)
  elif preProcessString(line, MainData):
    return preProcessString(line, MainData)
  return line

def preProcessIPs(line):
  try:
    pattern = re.compile(r"([0-9]{1,3})\.([0-9]{1,3})\.([0-9]{1,3})\.([0-9]{1,3})")
    start = pattern.search(line).start()
    end = pattern.search(line).end()
    ipRaw = line[start:end]
    ipNumber = IP2Int(ipRaw)
    return pattern.sub(ipNumber, line)
  except:
    return False

def preProcessString(line, MainData):
  try:
    pattern = re.compile(r"\'.+\'")
    start = pattern.search(line).start()
    end = pattern.search(line).end()
    value = line[start+1:end-1]
    result = str(int(md5.new(value).hexdigest(), 16))
    MainData["stringsHashMap"][result] = value
    return pattern.sub(result, line)
  except:
    return False

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
    return False

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
    result = str(int(md5.new(value).hexdigest(), 16))
    MainData["stringsHashMap"][result] = value
    return result

def findCustomTypesInUserRules(rawInput):
  customTypes = []
  for line in rawInput.split('\n'):
    if "deftype" in line:
      line = line.split(' ')
      if len(line) is 4:
        if line[0] == ";;" and line[1] == "deftype":
          customTypes.append({ "name": line[2], "type": line[3] })
  return customTypes

def parseUserRules(rawInput, MainData):
  sizes = MainData["sizes"]
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
    line = preProcessor(line, MainData)
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
          smt2 += "\n;;Ignore rules, because no " + for_name + " descriptions where found!\n"
        else:
          smt2 += "\n;; invalid for, did not match array name: \"" + for_name +"\"\n"
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

def prettifyValue(dataType, rawValueFromSolver, MainData):
  if dataType is "ip":
    return Int2IP(int(rawValueFromSolver))
  elif dataType is "size":
    return dec2Bin(int(rawValueFromSolver))
  elif dataType is "bool":
    return "true" if int(rawValueFromSolver) is 1 else "false"
  elif MainData["stringsHashMap"].has_key(rawValueFromSolver):
    return MainData["stringsHashMap"].get(rawValueFromSolver)
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
def prepareOutputForZ3(tosca, USER_RULES_PATH, config, ids = []):
  output = open(OUTPUT_PATH, mode='w')
  userRawRules = open(USER_RULES_PATH).read()
  MainData = {
    "blob": "",
    "variables": {
      "names": [],
      "total": 0
    },
    "types": {
      "vnfs": "tosca.nodes.nfv.VNF",
      "vdus": "tosca.nodes.nfv.VDU",
      "vls": "tosca.nodes.nfv.VL",
      "cps": "tosca.nodes.nfv.CP",
      "fps": "tosca.nodes.nfv.FP",
      "vms": "tosca.nodes.Compute",
      "networks": "tosca.nodes.network.Network"
    },# TODO: agregar aqui el nuevo type y size
    "sizes": {},
    # we generate this below
    # "sizes": {
    #   "vnfs": 0,
    #   "vdus": 0,
    #   "vls": 0,
    #   "cps": 0,
    #   "fps": 0,
    #   "vms": 0,
    #   "networks": 0,
    # },
    "custom_rules": USER_RULES_PATH,
    "optimized": True,
    "skipIDs": ids,
    "stringsHashMap": {},
    "valueTypes": {},
    "rules": {
      "attributes": getAttributesFromUserRules(userRawRules)
    },
    "customTypes": findCustomTypesInUserRules(userRawRules)
  }

  # add Custom Types
  for custom in MainData["customTypes"]:
    if MainData["types"].has_key(custom["name"]):
      MainData["types"][custom["name"]] = custom["type"]
    else:
      if config.has_key("experimental") and bool(config.get("experimental")):
        MainData["types"][custom["name"]] = custom["type"]
  
  # Generate Sizes
  for key in MainData["types"].keys(): MainData["sizes"][key] = 0

  nodes = scanAllPropertiesAndGenerateStructure(tosca)
  prepareOutputForZ3Core(nodes, MainData)
  
  MainData["blob"] += parseUserRules(userRawRules, MainData)
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
  quitReason = "unreachable"
  solutionsFound = 0
  maxSolutions = int(config["suggestions"])
  apiOutput['quitReason'] = { "output": quitReason, "reason": quitReason }
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
        prepareOutputForZ3(tosca, user_path_custom_rules, config, ids)
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
                  fullnames = fullname.split('.')
                  fullnames[1] = fullnames[1][:len(fullnames[1])-1]
                  try:
                    fullnames[1] = fullnames[1].split('_')[1] + '\'s ' + fullnames[1].split('_')[0]
                  except:
                    1 + 1
                  try:
                    dataType = MainData["valueTypes"][fullname.split('.').pop()]
                    prettyValue = prettifyValue(dataType, rawValueFromSolver, MainData)
                    suggestion['output'] += "\n    - " + " > ".join(fullnames) + ' to ' + "(" + prettyValue + ")"
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
                    suggestion['output'] += "\n    - " + " > ".join(fullnames) + ' to ' + "(" + prettyValue + ")"
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

"""
 Node Methods
 - [   ] is_derived_from
 - [   ] name
 - [   ] parent_type

 - [ ∆ ] get_capabilities_objects
 - [ ∆ ] get_properties_objects
 - [ ~ ] interfaces
 - [ ç ] related_nodes

 - [ x ] relationship_tpl
 - [ ç ] relationships
 - [ ∆ ] requirements

 - [ x ] get_relationship_template
 - [ x ] sub_mapping_tosca_template
 - [ ~ ] templates

 - [ ç ] type
 - [ ç ] type_definition
 - [ x ] validate
"""

def get_attributes_objects(node):
  _node = node.templates[node.name]
  if _node.get('attributes') is not None:
    return  _node.get('attributes')
  else:
    return {}

def scanAllPropertiesAndGenerateStructure(tosca):
  if not hasattr(tosca, "nodetemplates"): print("no nodetemplates")
  nodes = {}
  for node in tosca.nodetemplates:
    _node = {}
    _node['type'] = node.type
    _node['name'] = node.name
    _node['props'] = {}

    # Capabilities
    for capa in node.get_capabilities_objects():
      for prop in capa.get_properties_objects():
        # print(prop.type, prop.name, prop.value)
        # print(node.name + "." + prop.name+" = "+str(prop.value))
        _node['props'][prop.name] = prop.value
    
    # Properties
    for prop in node.get_properties_objects():
      # print(prop.type, prop.name, prop.value)
      # print(node.name + "." + prop.name + " = " + str(prop.value))
      _node['props'][prop.name] = prop.value
    
    # Attributes
    for (name, value) in get_attributes_objects(node).items():
      # print(node.name + "." + name + " = " + str(value))
      _node['props'][prop.name] = value

    # Requirements
    for req in node.requirements:
      # should only contain 1 key
      # the loop below should only run once
      for (name, value) in req.items():
        if type(value) is type({}):
          for (k, v) in value.items():
            # print(node.name + "." + name + "." + k + " = " + v)
            if _node['props'].has_key(name + "." + k):
              # append to array if found
              _node['props'][name + "." + k].append(v)
            else:
              # there is a case where this key can repeat
              _node['props'][name + "." + k] = [v]
        else:
          # print(node.name + "." + name + " = " + str(value))
          _node['props'][name] = value
    # add to nodes {}
    nodes.setdefault(node.type, [])
    nodes[node.type].append(_node)
  return nodes

def prepareOutputForZ3Core(nodes, MainData):
  # Arrays
  # -vnfs: tosca.nodes.nfv.VNF
  # - vdu: tosca.nodes.nfv.VDU
  # - vls: tosca.nodes.nfv.VL
  # - cps: tosca.nodes.nfv.CP
  # - fps: tosca.nodes.nfv.FP
  # - vms: tosca.nodes.Compute
  # - networks: tosca.nodes.network.Network

  lists = MainData["types"]
  smt2 = ""
  vars_counter = 0
  for (arrayName, nodetype) in lists.items():
    # just to remove the "s" at the end
    arrayLabel = arrayName[:len(arrayName) - 1]
    Title = arrayName.upper()
    smt2 += "\n"
    if not nodes.has_key(nodetype):
      smt2 += ";;------------------------\n"
      smt2 += ";;  " + Title + " Setup: 0, None detected\n"
      smt2 += ";;  " + nodetype + "\n"
      smt2 += ";;------------------------\n"
      continue
    
    # number of items of type {nodetype}
    total = len(nodes.get(nodetype))
    smt2 += ";;------------------------\n"
    smt2 += ";;  " + Title + " Setup\n"
    smt2 += ";;  " + nodetype + "\n"
    smt2 += ";;------------------------\n"
    smt2 += "(declare-const " + arrayName + " (Array Int (Array String Int)))\n"
    for i in range(0, total):
      smt2 += "(declare-const props_" + arrayLabel + str(i) + " (Array String Int))\n"
    smt2 += "(declare-const " + arrayName + "_size Int)\n"
    smt2 += "(assert (= " + arrayName + "_size " + str(total) +"))\n"
    smt2 += ";;------ Done " + Title + " Setup ------\n\n"


    smt2 += ";;------------------------\n"
    smt2 += ";;  " + Title + " Insert Values From Conf\n"
    smt2 += ";;------------------------\n"
    
    items_counter = 0
    
    # for each item of type: nodetype
    for item in nodes.get(nodetype):  
      itemid = str(items_counter)
      name = item.get("name") if item.has_key("name") else "var_id_" + itemid
      smt2 += ";; "+arrayLabel+"-name: " + name + "\n"
      item_name = "props_" + arrayLabel + str(itemid)

      # for each property that the item has
      for (prop_name, prop_value) in item.get("props").items():
        # this following line improves A LOT the performance
        if not prop_name in MainData['rules']['attributes'] and MainData['optimized']: continue
        varid = str(vars_counter)
        if type(prop_value) is type([]):
          getValue = lambda name, value: toscaRawValueToSMTCorrectType(name, value, MainData)
          isIgnored = lambda x: int(x) in MainData["skipIDs"]
          smt2 += smtlib.declareArray("Array", item_name+"."+prop_name, len(prop_value))
          (varid, output) = smtlib.fillArray(varid, prop_value, item_name+"."+prop_name , getValue, isIgnored)
          smt2 += output
          vars_counter = varid + 1
          continue
        
        # find the correct type for smtlib, handles: ips, memory sizes, ints, strings, bools
        # TODO: docs write this transformation of types
        value = toscaRawValueToSMTCorrectType(prop_name, prop_value, MainData)
        
        # this will comment out the variable
        if int(varid) in MainData["skipIDs"]: smt2 += ";; "
        
        # "(assert (= (store "+item_name+" \"" + prop_name +"\" " + value +") "+item_name+"))" + ";; var.id: " + varid +"\n"
        smt2 += smtlib.assignToHashMap(item_name, prop_name, value, varid)
        MainData["variables"]["names"].append(name + "." + item_name + "." + prop_name)
        vars_counter += 1
      index_of_array = str(int(itemid) - 1)
      smt2 += smtlib.assignToArray(arrayName, index_of_array, item_name)
      smt2 += "\n"
      # smt2 += "(assert (= (store "+arrayName+" "+ index_of_array +" "+item_name+") "+arrayName+"))\n\n"
      items_counter += 1
    MainData["sizes"][arrayName] = items_counter + 1
  MainData["variables"]["total"] = vars_counter
  MainData["blob"] = smt2
  return MainData