# -*- coding: latin-1 -*-
import argparse
import os
import sys

from toscaparser.tosca_template import ToscaTemplate
from toscaparser.common.exception import TOSCAException
from toscaparser.utils.gettextutils import _
import toscaparser.utils.urlutils
import epav


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
    except:
      print("⚠️ tosca-parser: Could not parse the given file.")
      if args.verbose:
        print("Unexpected error: " + str(sys.exc_info()[1]) + "\n")
      exit(1)

    (cpsItems, cpsDict) = epav.getCPS(tosca)
    connectivity = epav.getConnectivityGraph(cpsItems, cpsDict)
    epav.debugMatrix("\nconnectivity\n", (args.verbose or args.diff), cpsItems, connectivity)

    if args.verbose or args.diff:
      print("\nNFS:")
    forwarding_paths = epav.getForwardingPaths(tosca)
    matrixList = epav.func_chains(forwarding_paths, cpsItems)
    map(lambda x: epav.findLoop(connectivity, cpsItems, x, args), matrixList)


def main(args=None):
  if args is None:
    args = sys.argv[1:]
  ParserShell().main(args)


if __name__ == '__main__':
  main()
