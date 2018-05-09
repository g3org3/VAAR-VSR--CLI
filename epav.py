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
    Find Loop
------------------"""
def findLoop(self, connectivity, cpsItems, obj, args):
    matrix = obj['matrix']
    total_cps = obj['total_cps']
    name = obj['name']
    m = np.matrix(matrix)
    n = total_cps
    if args.verbose or args.diff:
        pyfancy("\n   -->  ").underlined(name +":").output()
        self.printMatrix(cpsItems, m)
    difference = np.matrix(connectivity) - m
    bugs = []
    if args.diff:
        if difference.min() == -1:
            pyfancy().yellow("\n\tConnexion problem detected").output()
        else:
            pyfancy().dim("diff->").output()
        self.printMatrix(cpsItems, difference)
    if difference.min() == -1:
        bugs.append(self.getPosOfNegative(cpsItems, difference))
    for x in range(1, n + 1):
        matrixToPower = m**x
        if (self.hasLoop(matrixToPower)):
            cpsInvolved = ", ".join(self.nodesInvolved(cpsItems, matrixToPower))
            bugs.append("  |> Found loop!\n    • Length: " + str(x) + "\n    •    CPs: " + cpsInvolved)
            if args.verbose:
                pyfancy().yellow("\n\tLoop detected in the matrix below: ^("+str(x)+")").output()
                self.printMatrix(cpsItems, matrixToPower)
            break
    if not args.verbose and not args.diff:
        if len(bugs) is not 0:
            pyfancy().underlined("⚠️  " + name).output()
            for bug in bugs:
                print bug
        else:
            pyfancy("✅  " + name).output()