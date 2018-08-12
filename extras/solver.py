#!/usr/bin/env python
import z3;
import sys;
import emoji;

def createSMTInput(values = []):
    """
    Our variables that we can abstract from tosca-configs
    So the user can use them to create their own validations
    """
    variables  = ";; ---------------"
    variables += ";;   VARIABLES"
    variables += ";; ---------------"
    variables += file('./variables.smt2').read()
    variables += "(declare-const vars (Array Int Int))\n"

    """
    Values found on the user tosca-conf request,
    we assign the values to the corresponding variable
    """
    configValues = ""
    for i in range(0, len(values)):
        configValues += "(assert (= (store vars " + str(i) +" "+ str(values[i]) +") vars))\n"

    initVariables = ""
    v = variables.strip().split("\n")
    v.pop()
    for i in range(0, len(v)):
        name = v[i].split(' ')[1]
        initVariables += "(assert (= " + name +" (select vars " + str(i) + ")))\n"

    """
    User-Custom-Validations: specified by the user
    """
    userRules = file('./user.smt').read()

    blob = variables + configValues + initVariables + userRules
    ouput = open('./output.smt2', mode="w")
    ouput.write(blob)
    ouput.close()

def check(values = []):
    createSMTInput(values)
    f = z3.parse_smt2_file("./output.smt2")
    s = z3.Solver()
    s.add(f)
    sat = str(s.check())
    if sat == "sat":
        return { "sat": "sat", "model": s.model() }
    else:
        return { "sat": "unsat", "model": "" }

def main():
    values = []
    if len(sys.argv) == 3:
        values = [int(sys.argv[1]), int(sys.argv[2])]
        print("Input Values\n---------------------")
         # + ", ".join(map(lambda x: str(x), values)))
        print("total_cpus: " + str(values[0]))
        print("mem_size: " + str(values[1]))
    # print(check()["sat"])
    sat = check()["sat"]
    if sat == "unsat":
        print emoji.emojize('sat: :x:', use_aliases=True)
        print("Is unsat without initializing any variable")
        exit(1)

    solver = check(values)
    if solver["sat"] == "sat":
        print emoji.emojize('sat: :white_check_mark:', use_aliases=True)
    else:
        while solver["sat"] == "unsat" and len(values) > 0:
            values.pop()
            solver = check(values)
        print emoji.emojize('sat: :x:', use_aliases=True)
        print "\n" + emoji.emojize(':rotating_light: Suggestion :rotating_light:', use_aliases=True)+"\n---------------------"
        for i in range(len(solver["model"])-2, 0, -1):
            print solver["model"][i], ": ", solver["model"][solver["model"][i]]

# main()
f = z3.parse_smt2_file("./ouput2.smt2")
s = z3.Solver()
s.add(f)
print s.check()
