# -*- coding: latin-1 -*-
import argparse
import os
import sys
import time
import json

from toscaparser.tosca_template import ToscaTemplate
from toscaparser.common.exception import TOSCAException
from toscaparser.utils.gettextutils import _
import toscaparser.utils.urlutils
from lib import epav
from lib import comb
from pyfancy import *


class ParserShell(object):

  def get_parser(self, argv):
    parser = argparse.ArgumentParser(prog="tosca-parser")
    parser.add_argument('-v', '--version',
                        action='store_true',
                        help=_('show tool version.'))
    parser.add_argument('-x', '--verbose',
                        action='store_true',
                        help=_('display each FP matrix'))
    parser.add_argument('-d', '--diff',
                        action='store_true',
                        help=_('display each matrix'))
    parser.add_argument('-c', '--template-file',
                        metavar='<filename>',
                        help=_('YAML template or CSAR file to parse.'))
    parser.add_argument('-t', '--custom-rules',
                        metavar='<filename>',
                        help=_('smt file'))
    return parser

  def main(self, argv):
    parser = self.get_parser(argv)
    (args, extra_args) = parser.parse_known_args(argv)
    path = args.template_file

    if (args.version):
      print("v1.0.0")
      exit(0)

    if (not args.template_file):
      if (os.path.isfile('./tosca-conf.yml')):
        path = './tosca-conf.yml'
      else:
        print("\nCould not found default config file: `./tosca-conf.yml`")
        print("")
        print("  to provide explicitly the path please use `-c`")
        print("  e.g. tosca-parser -c ./my-template.yaml")
        print("")
        print("  to display default help use `--help`")
        print("")
        exit(1)
    if os.path.isfile(path):
      try:
        self.parse(path, args)
      except TOSCAException as err:
        print("\nCould not parse yaml field.")
        print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        print(err)
        print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
    elif toscaparser.utils.urlutils.UrlUtils.validate_url(path):
      self.parse(path, args, False)
    else:
      raise ValueError(_('"%(path)s" is not a valid file.') % {'path': path})

  def parse(self, path, args, a_file=True):
    output = None
    tosca = None
    try:
      tosca = ToscaTemplate(path, None, a_file)
      # epav.playground(tosca)
    except:
      print("⚠️ tosca-parser: Could not parse the given file.")
      if args.verbose:
        print("Unexpected error: ")
        print(sys.exc_info())
        print("")
      exit(1)

    configFile = file('./config')
    apiOutput = {
      'FPIssues': {},
      'sat': False,
      'suggestions': []
    }
    config = {}
    # import config
    for line in configFile:
      if line[0] is ";" or line[0] is "#" or line[0] is "//":
        continue
      key = line.strip().split("=")[0]
      val = line.strip().split("=")[1]
      config[key] = val

    config["start_time"] = time.time()
    """
    :: User Connectivity ::
    """
    (cpsItems, cpsDict) = epav.getCPS(tosca)
    connectivity = epav.getConnectivityGraph(cpsItems, cpsDict)
    epav.debugMatrix("\nconnectivity\n", (args.verbose or args.diff), cpsItems, connectivity)

    """
    :: NFS ::
    """
    forwarding_paths = epav.getForwardingPaths(tosca)
    matrixList = epav.func_chains(forwarding_paths, cpsItems)
    matrixBugs = map(lambda x: epav.findLoop(connectivity, cpsItems, x, args), matrixList)
    
    if not bool(config['apiOutput']):
      pyfancy().underlined("\n\nNFS").output()
    epav.debugBugMatrix(matrixBugs, config, apiOutput)

    nfs_time = time.time() - config["start_time"]
    # print("\n[time]: "+ str(nfs_time))

    """
    :: USER Rules ::
    """
    user_path_custom_rules = "./user.smt"
    try:
      if args.custom_rules:
        user_path_custom_rules = args.custom_rules
        open(args.custom_rules).close()
      else:
        open('./user.smt').close()
    except:
      if not bool(config['apiOutput']):
        pyfancy().underlined("\nUser Rules").output()
        print("No custom rules detected")
      return

    MainData = epav.prepareOutputForZ3(tosca, user_path_custom_rules)
    (s, status) = epav.solve()
    
    apiOutput['sat'] = status

    first_solution_time = time.time() - config["start_time"]
    if not bool(config['apiOutput']):
      print("\n[time][isSat?]: "+ str(first_solution_time))

    if not bool(config['apiOutput']):
      pyfancy().underlined("\nUser Rules").output()
      print("  ✅ sat" if status is "sat" else "  ⚠️ unsat")
    
    if status is "unsat":
      if (args.verbose or args.diff):
        print "  N =", MainData["variables"]["total"]
      apiOutput['totalVariables'] = MainData["variables"]["total"]
      epav.findSolution(tosca, MainData, comb, config, apiOutput)
      if not bool(config['apiOutput']):
        print apiOutput['quitReason']['output']
    elapsed_time = time.time() - config["start_time"]
    apiOutput['time'] = elapsed_time
    if not bool(config['apiOutput']):
      print("[time]  : "+ str(elapsed_time))
    
    if bool(config['apiOutput']):
      print json.dumps(apiOutput, indent=2, separators=(',', ': '))
    with open('./output/output.json', 'w') as fp:
      json.dump(apiOutput, fp)

def main(args=None):
  if args is None:
    args = sys.argv[1:]
  ParserShell().main(args)


if __name__ == '__main__':
  main()
