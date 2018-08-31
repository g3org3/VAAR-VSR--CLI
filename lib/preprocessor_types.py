import md5

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
  # elif preProcessFloats(line, MainData):
    # return preProcessString(line, MainData)
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

def isTypeIP(value):
  value = value.strip()
  parts = value.split('.')
  if len(parts) is not 4:
    return False
  types = map(lambda x: type(x), parts)
  typesDict = {}
  for t in types:
    typesDict.setdefault(t, [])
    typesDict[t].append(t)
  if len(typesDict.keys()) is not 1:
    return False
  if len(typesDict[typesDict.keys()[0]]) is not 4:
    return False
  if typesDict[typesDict.keys()[0]][0] is not type(1):
    return False
  return True