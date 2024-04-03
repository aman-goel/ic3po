# ------------------------------------------
# IC3PO: IC3 for Proving Protocol Properties
# ------------------------------------------
# Copyright (c) 2018 - Present  Aman Goel and Karem Sakallah, University of Michigan. 
# All rights reserved.
#
# Author: Aman Goel (amangoel@umich.edu), University of Michigan
# ------------------------------------------

import argparse

from utils import eprint, elapsed_time
from ic3po import backwardReach
import common
import resource

DEFAULT_MODE="ic3po"
DEFAULT_MINIMIZE=1
DEFAULT_QF=3
DEFAULT_GEN="fef"
DEFAULT_RANDOM=0
DEFAULT_OUT="output/test"
DEFAULT_NAME="test"
DEFAULT_SEED=0
DEFAULT_SUBSUME=1
DEFAULT_INITSZ=-1
DEFAULT_REUSE=1
DEFAULT_OPTIMIZE=1
DEFAULT_CONST=1
DEFAULT_WIRES=1
DEFAULT_VERBOSITY=0
DEFAULT_FINV=0
DEFAULT_SIZE="default"
DEFAULT_RANGEBOOST=1
DEFAULT_CTI=0

header="""
---
IC3PO
---
  IC3 for Parameterized prOtocols
  
  Reads a parameterized state transition system in Ivy and performs 
  symmetry-aware property checking
-------------------
"""

short_header="""IC3PO 
copyright (c) 2018 - Present  Aman Goel and Karem Sakallah, University of Michigan"""

def getopts(header):
    p = argparse.ArgumentParser(description=str(header), formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('file', help='input file name', type=str)
    p.add_argument('-m', '--mode', help='mode: ic3po, updr, frpo (default: %s)' % DEFAULT_MODE, type=str, default=DEFAULT_MODE)
    p.add_argument('--min', help='inductive invariant minimization (between 0-2) (default: %r)' % DEFAULT_MINIMIZE, type=int, default=DEFAULT_MINIMIZE)
    p.add_argument('--qf', help='use quantifier free queries (between 0-2) (default: %r)' % DEFAULT_QF, type=int, default=DEFAULT_QF)
    p.add_argument('-g', '--gen', help='generalize: fef, fe, prefer_epr, epr_loose, epr_strict, univ, auto', type=str, default=DEFAULT_GEN)
    p.add_argument('-r', '--random', help='randomization (between 0-4) (default: %r)' % DEFAULT_RANDOM, type=int, default=DEFAULT_RANDOM)
    p.add_argument('-o', '--out', help='<output-path> (default: %s)' % DEFAULT_OUT, type=str, default=DEFAULT_OUT)
    p.add_argument('-n', '--name', help='<test-name> (default: %s)' % DEFAULT_NAME, type=str, default=DEFAULT_NAME)
    p.add_argument('--seed', help='solver seed (default: %r)' % DEFAULT_SEED, type=int, default=DEFAULT_SEED)
    p.add_argument('--subsume', help='subsumption checking level (between 0-1) (default: %r)' % DEFAULT_SUBSUME, type=int, default=DEFAULT_SUBSUME)
    p.add_argument('--reuse',             help='reuse clauses in incremental runs (between 0-1) (default: %r)' % DEFAULT_REUSE, type=int, default=DEFAULT_REUSE)
    p.add_argument('--opt',             help='optimize clauses (between 0-1) (default: %r)' % DEFAULT_OPTIMIZE, type=int, default=DEFAULT_OPTIMIZE)
    p.add_argument('--const',             help='constant propagation (between 0-1) (default: %r)' % DEFAULT_CONST, type=int, default=DEFAULT_CONST)
    p.add_argument('-w', '--wires', help='use wires (between 0-1) (default: %r)' % DEFAULT_WIRES, type=int, default=DEFAULT_WIRES)
    p.add_argument('--init', help='initial size (use -1 to use vmt size) (default: %r)' % DEFAULT_INITSZ, type=int, default=DEFAULT_INITSZ)
    p.add_argument('--finv', help='use 1 to exit after printing the finite invariant for safe property (default: %r)' % DEFAULT_FINV, type=int, default=DEFAULT_FINV)
    p.add_argument('--size', help='finite size (, separated)', type=str, default=DEFAULT_SIZE)
    p.add_argument('--rb', help='use 1 to enable RangeBoost (default: %r)' % DEFAULT_RANGEBOOST, type=int, default=DEFAULT_RANGEBOOST)
    p.add_argument('--cti', help='use 1 to enable CTI printing (default: %r)' % DEFAULT_CTI, type=int, default=DEFAULT_CTI)
    p.add_argument('-v', '--verbosity', help='verbosity level (default: %r)' % DEFAULT_VERBOSITY, type=int, default=DEFAULT_VERBOSITY)
    args, leftovers = p.parse_known_args()
    return args, p.parse_args()

def main():
    common.initialize()
    
    known, common.gopts = getopts(header)
    
    statsName = "%s/%s.results" % (common.gopts.out, common.gopts.name)
    common.gopts.statsF = open(statsName, "w")
#     print(short_header)
#     eprint(short_header)
    
    print("\t(mode: %s)" % common.gopts.mode)
    eprint("\t(mode: %s)" % common.gopts.mode)

    print("\t(reuse: %s)" % common.gopts.reuse)
    eprint("\t(reuse: %s)" % common.gopts.reuse)
    
    print("\t(opt: %s)" % common.gopts.opt)
    eprint("\t(opt: %s)" % common.gopts.opt)
    
    print("\t(const: %s)" % common.gopts.const)
    eprint("\t(const: %s)" % common.gopts.const)
    
    print("\t(wires: %s)" % common.gopts.wires)
    eprint("\t(wires: %s)" % common.gopts.wires)
    
    if common.gopts.init != DEFAULT_INITSZ:
        eprint("\t(init size: %s)" % common.gopts.init)
    
    if common.gopts.mode == "frpo":
        from fr import forwardReach
        system = forwardReach(common.gopts.file)
        backwardReach(common.gopts.file, system)
    else:
        backwardReach(common.gopts.file, None)

    common.gopts.statsF.write("wall-time-sec:\t%.2f\n" % (elapsed_time()))
    
    maxMem = (resource.getrusage(resource.RUSAGE_SELF).ru_maxrss) / (1024.0)
    common.gopts.statsF.write("memory-mb:\t%.2f\n" % (maxMem))

    common.gopts.statsF.close()
    
if __name__ == "__main__":  
    main()
