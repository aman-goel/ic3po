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

keys = []
table = {}

def set_keys():
	keys.append("tool:");
	keys.append("suite:");
	keys.append("benchmark:");
	keys.append("exit-status:");
	keys.append("time:");
	keys.append("memory-mb:");
	keys.append("sz-invariant:");
	keys.append("sz-invariant-forall:");
	keys.append("sz-invariant-exists:");
	keys.append("sz-invariant-atoms:");
	keys.append("scalls:");
	keys.append("status:");
	keys.append("seed:");
	keys.append("timeout:");
	keys.append("scalls-finite:");
	keys.append("scalls-infinite:");
	keys.append("scalls-finite-full:");
	keys.append("exit-reason:");
	keys.append("cti:");

def reset_values():
	for key in keys:
		table[key] = "-1"

def get_values(statF):
	with open(statF) as f:
		lis = [x.split() for x in f]
	for entry in lis:
		if len(entry) == 2:
			table[entry[0]] = entry[1]
		elif len(entry) == 1:
			table[entry[0]] = "-1"
		else:
			print("Error in file %s" % statF)
			assert(0)

def print_keys(outF):
	for key in keys:
		outF.write("%s\t" % key)
	outF.write("\n")

def print_values(outF):
	for key in keys:
		outF.write("%s\t" % table[key])
	outF.write("\n")


DEFAULT_TOOL="ic3po"
DEFAULT_SEED="1"
DEFAULT_OUT="xtras"

def getopts(header):
	p = argparse.ArgumentParser(description=str(header), formatter_class=argparse.RawDescriptionHelpFormatter)
	p.add_argument('-t', '--tool', help='tool: ic3po (default: %s)' % DEFAULT_TOOL, type=str, default=DEFAULT_TOOL)
	p.add_argument('--seed', help='solver seed (default: %r)' % DEFAULT_SEED, type=int, default=DEFAULT_SEED)
	args, leftovers = p.parse_known_args()
	return args, p.parse_args()

def main():
	known, opts = getopts("")
	top_dir = "output"
	
	if not os.path.exists(top_dir):
		raise Exception("Unable to find tool output directory: %s" % top_dir)
	
	in_dir = "%s/seed%s" % (top_dir, opts.seed)
	if not os.path.exists(in_dir):
		raise Exception("Unable to find run for seed: %s" % in_dir)
	
	outName = "%s/%s-seed%s.csv" % (DEFAULT_OUT, opts.tool, opts.seed)
	if os.path.isfile(outName):
		os.remove(outName)
	outF = open(outName, "x")
	
	set_keys()
	print_keys(outF)
	for subdir, dirs, files in os.walk(in_dir):
		for d in dirs:
			stat_file = "%s/%s/stats.txt" % (in_dir, d)
			if not os.path.isfile(stat_file):
				print("Unable to find stats file in %s" % d)
				continue
			reset_values()
			get_values(stat_file)
			print_values(outF)
		break
	
	outF.close()

if __name__ == '__main__':
	main()
