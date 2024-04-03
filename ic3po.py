#!/usr/bin/env python

import os, sys
import subprocess
import argparse
import tempfile
import shutil
import ntpath
from distutils import spawn
import re
from distutils.spawn import find_executable

version=1.1.0
IVY2VMT="ic3po/ivy_to_vmt.py"
IC3PO="ic3po/top.py"

DEFAULT_NAME="test"
DEFAULT_OUT="output"
DEFAULT_TIMEOUT=3600
DEFAULT_MEMOUT=64000
DEFAULT_PRINT_WITNESS=True
DEFAULT_MODE="ic3po"
DEFAULT_MINIMIZE=1
DEFAULT_QF=3
DEFAULT_GEN="fef"
DEFAULT_RANDOM=0
DEFAULT_SEED=1
DEFAULT_INITSZ=-1
DEFAULT_SUBSUME=1
DEFAULT_REUSE=1
DEFAULT_OPTIMIZE=1
DEFAULT_CONST=1
DEFAULT_WIRES=1
DEFAULT_VERBOSITY=1
DEFAULT_FINV=0
DEFAULT_SIZE="default"
DEFAULT_RANGEBOOST=1
DEFAULT_CTI=0

def getopts(header):
	p = argparse.ArgumentParser(description=str(header), formatter_class=argparse.RawDescriptionHelpFormatter)
	p.add_argument('file', help='input file name', type=str)
	p.add_argument('-n', '--name',      help='<test-name> (default: %s)' % DEFAULT_NAME, type=str, default=DEFAULT_NAME)
	p.add_argument('-o', '--out',       help='<output-path> (default: %s)' % DEFAULT_OUT, type=str, default=DEFAULT_OUT)
	p.add_argument('-m', '--mode',	  	help='mode: ic3po, updr, frpo (default: %s)' % DEFAULT_MODE, type=str, default=DEFAULT_MODE)
	p.add_argument('--timeout',         help='timeout (CPU time) in seconds (default: %s)' % DEFAULT_TIMEOUT, type=int, default=DEFAULT_TIMEOUT)
	p.add_argument('--memout',          help='memory limit in mega bytes (default: %s)' % DEFAULT_MEMOUT, type=int, default=DEFAULT_MEMOUT)
	p.add_argument('--min', 			help='inductive invariant minimization (between 0-2) (default: %r)' % DEFAULT_MINIMIZE, type=int, default=DEFAULT_MINIMIZE)
	p.add_argument('-r', '--random', 	help='randomization (between 0-4) (default: %r)' % DEFAULT_RANDOM, type=int, default=DEFAULT_RANDOM)
	p.add_argument('--seed', 			help='solver seed (default: %r)' % DEFAULT_SEED, type=int, default=DEFAULT_SEED)
	p.add_argument('--subsume', 		help='subsumption checking level (between 0-1) (default: %r)' % DEFAULT_SUBSUME, type=int, default=DEFAULT_SUBSUME)
	p.add_argument('-g', '--gen', 		help='generalize: fef, fe, prefer_epr, epr_loose, epr_strict, univ, auto', type=str, default=DEFAULT_GEN)
	p.add_argument('--reuse', 			help='reuse clauses in incremental runs (between 0-1) (default: %r)' % DEFAULT_REUSE, type=int, default=DEFAULT_REUSE)
	p.add_argument('--opt', 			help='optimize clauses (between 0-1) (default: %r)' % DEFAULT_OPTIMIZE, type=int, default=DEFAULT_OPTIMIZE)
	p.add_argument('--const', 			help='constant propagation (between 0-1) (default: %r)' % DEFAULT_CONST, type=int, default=DEFAULT_CONST)
	p.add_argument('-w', '--wires', help='use wires (between 0-1) (default: %r)' % DEFAULT_WIRES, type=int, default=DEFAULT_WIRES)
	p.add_argument('--witness',         help='toggles printing witness (default: %r)' % DEFAULT_PRINT_WITNESS, action="count", default=DEFAULT_PRINT_WITNESS)
	p.add_argument('--qf', 				help='use quantifier free queries (between 0-2) (default: %r)' % DEFAULT_QF, type=int, default=DEFAULT_QF)
	p.add_argument('--init', 			help='initial size (use -1 to use vmt size) (default: %r)' % DEFAULT_INITSZ, type=int, default=DEFAULT_INITSZ)
	p.add_argument('--finv', help='use 1 to exit after printing the finite invariant for safe property (default: %r)' % DEFAULT_FINV, type=int, default=DEFAULT_FINV)
	p.add_argument('--rb', help='use 1 to enable RangeBoost (default: %r)' % DEFAULT_RANGEBOOST, type=int, default=DEFAULT_RANGEBOOST)
	p.add_argument('--size', help='finite size (, separated)', type=str, default=DEFAULT_SIZE)
	p.add_argument('--cti', help='use 1 to enable CTI printing (default: %r)' % DEFAULT_CTI, type=int, default=DEFAULT_CTI)
	p.add_argument('-v', '--verbosity', help='verbosity level (default: %r)' % DEFAULT_VERBOSITY, type=int, default=DEFAULT_VERBOSITY)
	args, leftovers = p.parse_known_args()
	return args, p.parse_args()

header="""
---
IC3PO
---
  IC3 for Proving Protocol Properties
  
  Reads a parameterized state transition system in Ivy (or customized VMT) 
   and performs regularity-aware property checking
-------------------
"""

short_header="""----------------------------------------------------------------------------------
IC3PO: IC3 for Proving Protocol Properties
Copyright (c) 2018 - Present  Aman Goel and Karem Sakallah, University of Michigan
----------------------------------------------------------------------------------
"""

def split_path(name):
	head, tail = ntpath.split(name)
	if not tail:
		tail = ntpath.basename(head)
	return head, tail

def main():
	known, opts = getopts(header)
	print(short_header)
	if not os.path.exists(opts.out):
		os.makedirs(opts.out)

	path, f = split_path(opts.file)
	if not os.path.isfile(opts.file):
		raise Exception("Unable to find input file: %s" % opts.file)

	en_vmt = False
	if opts.file.endswith('.vmt') or opts.file.endswith('.smt2'):
		en_vmt = True
	elif not opts.file.endswith('.ivy'):
		raise Exception("Invalid input file: expected .ivy/.vmt, got %s" % opts.file)
	
	orig_dir = os.getcwd()
	out_dir = "%s/%s" % (opts.out, opts.name)
	tool_dir = os.path.dirname(os.path.realpath(__file__))
	print("\t(output dir: %s)" % out_dir)
	if os.path.exists(out_dir):
		shutil.rmtree(out_dir)
	os.makedirs(out_dir)
	log_file = "%s/%s.log" % (out_dir, opts.name)
	
	if en_vmt:
		print("\t(frontend: vmt)")
		vmt_file = "%s/%s.vmt" % (out_dir, opts.name)
		shutil.copyfile(str(opts.file), vmt_file)
	else:
		print("\t(frontend: ivy)")
		ivy_file = "%s/%s.ivy" % (out_dir, opts.name)
		shutil.copyfile(str(opts.file), ivy_file)
		vmt_file = "%s/%s.vmt" % (out_dir, opts.name)

		command = "python2 "
		ivy2vmtFile = "%s/%s" % (tool_dir, IVY2VMT)
		if not os.path.isfile(ivy2vmtFile):
			raise Exception("Missing ivy2vmt file: %s" % ivy2vmtFile)
			
		command += ivy2vmtFile
		command += " " +  str(out_dir) + "/" + str(opts.name) + ".ivy"
		command += " " +  str(vmt_file)
		command += " >> " + log_file
		print("\t(converting: ivy -> vmt)")
		s = subprocess.call("exec " + command, shell=True)
		if (s != 0):
			raise Exception("conversion error: return code %d" % s)
	
	command = "python2 -u "
# 	command = "python2 -m cProfile "
	topFile = "%s/%s" % (tool_dir, IC3PO)
	if not os.path.isfile(topFile):
		raise Exception("Missing top file: %s" % topFile)
		
	command += topFile
	command += " -m %s" % opts.mode
	command += " --min %s" % opts.min
	command += " --qf %s" % opts.qf
	command += " -g %s" % opts.gen
	command += " -r %s" % opts.random
	command += " --seed %s" % opts.seed
	command += " --subsume %s" % opts.subsume
	command += " --reuse %s" % opts.reuse
	command += " --opt %s" % opts.opt
	command += " --const %s" % opts.const
	command += " --init %s" % opts.init
	command += " --wires %s" % opts.wires
	command += " --finv %s" % opts.finv
	command += " --size %s" % opts.size
	command += " --rb %s" % opts.rb
	command += " -v %s" % opts.verbosity
	command += " -o %s" % out_dir
	command += " -n %s" % opts.name
	command += " --cti %s" % opts.cti
	command += " " +  vmt_file
	command += " >> " + log_file
	s = subprocess.Popen("exec " + command, shell=True)
	try:
		s.wait()
	except KeyboardInterrupt:
		try:
		   s.terminate()
		except OSError:
		   pass
		s.wait()
	retcode = s.poll()
	if (retcode != 0):
		raise Exception("ic3po error: return code %d" % retcode)
		
if __name__ == '__main__':
	main()
