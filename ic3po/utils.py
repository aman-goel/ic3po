# ------------------------------------------
# IC3PO: IC3 for Proving Protocol Properties
# ------------------------------------------
# Copyright (c) 2018 - Present  Aman Goel and Karem Sakallah, University of Michigan. 
# All rights reserved.
#
# Author: Aman Goel (amangoel@umich.edu), University of Michigan
# ------------------------------------------

from __future__ import print_function

import sys
import time
import common
import math
import re

from pysmt.pretty_printer import pretty_serialize
from pysmt.shortcuts import *

times = []
start_time = 0
SORT_SUFFIX = ":e"

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

def print_stat(key, val):
    common.gopts.statsF.write("%s:\t%s\n" % (key, val))

def print_stat_stdout(key, val, prefix="\t"):
    print("%s%s:\t%s" % (prefix, key, val))

def push_time():
    global times
    times.append(time.time())
    
def pop_time():
    global times
    assert(len(times) != 0)
    return time.time() - times.pop()
    
def elapsed_time():
    global start_time
    elapsed_time = time.time() - start_time
    return elapsed_time

def time_str():
    return "@ %5.0fs " % elapsed_time()

def pretty_print_str(cl, mode=0, reset=True):
    subs = {}

    qvars = cl.get_quantifier_variables()
    nameset = set()
    count = 0
    nameSort = {}
    for v in qvars:
        name = str(v)
        suffix = name.rstrip('1234567890')
        name = name[len(suffix):]
        if len(name) != 0:
            vs = v.symbol_type()
#             sname = str(vs).upper().split(':')[0]
            sname = str(vs)[0].upper()
            if sname not in nameSort:
                nameSort[sname] = 0
            nameSort[sname] += 1
            n = sname + str(nameSort[sname])
            if n in nameset:
                count += 1
                n = n + "_" + str(count)
            nameset.add(n)
            subs[v] = n
        
    fvars = cl.get_free_variables()
    for v in fvars:
        name = str(v)
        name = name.lstrip('_')
        suffix = name.rstrip('1234567890')
        if len(suffix) != 0:
            tmpName = name[:len(suffix)]
            if tmpName.endswith(SORT_SUFFIX):
                name = tmpName[:-2]
        subs[v] = name
    if reset:
        mode = 0
    return pretty_serialize(cl, mode=mode, subs=subs)
#     return pretty_serialize(cl, subs=subs)
    
def pretty_print(cl, mode=0):
    print(pretty_print_str(cl, mode))

def pretty_print_inv_set(inv_set, comment=""):
    print("### %s: #%d" % (comment, len(inv_set)))
    count = 0
    for cl in inv_set:
        count += 1
        print("invariant [%d_ic3po]\t" % count, end='')
        pretty_print(cl, 1)
    print("###\n")
    sys.stdout.flush()

def formula_key(f):
    fstr = str(f)
    frels = f.get_free_variables()
    frels2 = sorted(frels, key=str)
    return (len(fstr), str(frels2), fstr)

def label_key(label):
    prefix = label.rstrip('1234567890')
    suffix = label[len(prefix):]
    if suffix.isdigit():
        return (prefix, int(suffix))
    else:
        return (label, 0)

def pretty_print_inv(inv_list, comment, suffix=""):
    print("### %s: #%d" % (comment, len(inv_list)))
    for label, cl in sorted(inv_list, key=lambda v: label_key(v[0])):
        print("invariant [ic3po_%s%s]\t" % (label, suffix), end='')
        pretty_print(cl, 1)
    print("###\n")
    sys.stdout.flush()

def pretty_print_inv_file(invF, inv_list, comment="Proof certificate"):
    print("### %s: #%d" % (comment, len(inv_list)), file=invF)
    for label, cl in inv_list:
        print("invariant [ic3po_%s]\t" % label, end='', file=invF)
        print(pretty_print_str(cl, mode=1, reset=False), file=invF)
    print("###", file=invF)

def pretty_print_finv_file(invF, inv_list, comment=""):
    print("n:\t%d" % (len(inv_list)), file=invF)
    for label, cl in inv_list:
#         print("invariant [ic3po_%s]\t" % label, end='', file=invF)
        if label.startswith("prop"):
            print("p:\t", end='', file=invF)
        else:
            print("i:\t", end='', file=invF)
        print(pretty_print_str(cl, mode=0, reset=False), file=invF)
#     print("###", file=invF)

#     def print_smt2(self, cl):
#         solver = Solver(name="z3")
#         solver.add_assertion(cl)
#         solver.solve()
#         cl_smt2 = solver.to_smt2()
#         print(cl_smt2)
# 
# #         print(cl)
#     
#     def print_smt2_set(self, inv_set):
#         print("Proof certificate (SMT-LIB): #%d" % len(inv_set))
#         print("-------------------------------------------------")
#         count = 0
#         for cl in inv_set:
#             count += 1
#             print("invariant [ic3po_%d]\t" % count, end='')
#             self.print_smt2(cl)
#         print("-------------------------------------------------")

def pretty_print_set(s, mode=1):
    res = "[ "
    for v in s:
#         res += pretty_serialize(v, mode=mode)
        res += pretty_serialize(v)
        res += ", "
    res += "]"
    return res

def substitute_sort(f, subs, suffix, f2i=False):
    if f2i:
        name = f.symbol_name()
        if name.endswith(suffix):
            name = name[:len(name) - len(suffix)]
    else:
        name = f.symbol_name() + suffix
    s_type = f.symbol_type()
    rett = s_type
    
    args = []
    if s_type.is_function_type():
        rett = s_type.return_type
        if rett in subs:
            rett = subs[rett]
            
        i = 0
        for paramt in s_type.param_types:
            i += 1
            if paramt in subs:
                args.append(subs[paramt])
            else:
                args.append(paramt)
        ft = FunctionType(rett, tuple(args))
    else:
        if rett in subs:
            rett = subs[rett]
        ft = rett
    res = Symbol(name, ft)
    return res

def flatten_and(formula):
    flat = set()
    if (formula.is_and()):
        for arg in formula.args():
            for flat_arg in flatten_and(arg):
                flat.add(flat_arg)
    elif (formula.is_not()):
        formulaNeg = formula.arg(0)
        if formulaNeg.is_or():
            for arg in formulaNeg.args():
                for flat_arg in flatten_or(arg):
                    flat.add(Not(flat_arg))
        else:
            flat.add(formula)
    else:
        flat.add(formula)
    return flat
    
def flatten_cube(cube):
    flat = set()
    cube_flat = cube
    if cube_flat.is_exists():
        cube_flat = cube_flat.args()[0]
        
    if (cube_flat.is_and()):
        for arg in cube_flat.args():
            for flat_arg in flatten_cube(arg):
                flat.add(flat_arg)
    else:
        flat.add(cube_flat)
    return flat
    
def flatten_or(cube):
    flat = set()
    cube_flat = cube
        
    if (cube_flat.is_or()):
        for arg in cube_flat.args():
            for flat_arg in flatten_or(arg):
                flat.add(flat_arg)
    else:
        flat.add(cube_flat)
    return flat
    
def assert_permanent(solver, formulae):
    solver.add_assertion(And(formulae))
    solver.push()
    
def count_quantifiers(formula, pol=True, inF=0, inE=0):
    outF = inF
    outE = inE
#     print("formula: %s %s %d %d" % (formula, pol, outF, outE))
    if formula.is_not():
        outF, outE = count_quantifiers(formula.arg(0), not pol, outF, outE)
        return (outF, outE)
    if formula.is_implies():
        outF, outE = count_quantifiers(formula.arg(0), not pol, outF, outE)
        outF, outE = count_quantifiers(formula.arg(1), pol, outF, outE)
        return (outF, outE)
    is_e = formula.is_exists()
    is_a = formula.is_forall()
    if (is_e and pol) or (is_a and not pol):
        qvars = formula.quantifier_vars()
        outE += len(qvars)
    if (is_e and not pol) or (is_a and pol):
        qvars = formula.quantifier_vars()
        outF += len(qvars)
    for arg in formula.args():
        outF, outE = count_quantifiers(arg, pol, outF, outE)
    if formula.is_ite():
        outF, outE = count_quantifiers(formula.arg(0), not pol, outF, outE)
    if formula.is_iff() or formula.is_equals():
        outF, outE = count_quantifiers(formula.arg(0), not pol, outF, outE)
        outF, outE = count_quantifiers(formula.arg(1), not pol, outF, outE)
    return (outF, outE)

def count_and(formula):
    f = And(formula)
    flat = flatten_and(f)
    return len(flat)
 
def formula_cost_rec(formula, pol=True, inC=0):
    factor = 10
    outC = inC
#     print("formula: %s %s %d %d" % (formula, pol, outF, outE))
    outC += len(formula.args())
    if formula.is_not():
        outC = formula_cost_rec(formula.arg(0), not pol, outC)
        return outC
    if formula.is_implies():
        outC = formula_cost_rec(formula.arg(0), not pol, outC)
        outC = formula_cost_rec(formula.arg(1), pol, outC)
        return outC
    is_e = formula.is_exists()
    is_a = formula.is_forall()
    if (is_e and pol) or (is_a and not pol):
        qvars = formula.quantifier_vars()
        if inC > 0:
            factor = 1000
        outC += factor*len(qvars)
    if (is_e and not pol) or (is_a and pol):
        qvars = formula.quantifier_vars()
        if inC > 1000:
            factor = 100
        outC += factor*len(qvars)
    for arg in formula.args():
        outC = formula_cost_rec(arg, pol, outC)
    if formula.is_ite():
        outC = formula_cost_rec(formula.arg(0), not pol, outC)
    if formula.is_iff() or formula.is_equals():
        outC = formula_cost_rec(formula.arg(0), not pol, outC)
        outC = formula_cost_rec(formula.arg(1), not pol, outC)
    if formula.is_function_application():
        formulaType = formula.function_name()
        factor = 10000
        if str(formulaType).startswith("member:"):
            outC += factor
    return outC   

def binom(n, k):
    return math.factorial(n) // math.factorial(k) // math.factorial(n - k)

def num_majority(n):
    return binom(n, math.ceil((n+1.0)/2.0))
    
def substituteDefinitions(formula, defMap, mode=0):
#     print("in: %s" % formula)
    args = []
    for ch in formula.args():
        chNew = substituteDefinitions(ch, defMap)
        args.append(chNew)
#     print("curr: %s" % formula)
#     print("args: %s" % args)
        
    if formula.is_exists():
        qvars = formula.quantifier_vars()
        return Exists(qvars, args[0])
    if formula.is_forall():
        qvars = formula.quantifier_vars()
        return ForAll(qvars, args[0])
    if formula.is_not():
        return Not(args[0])
    if formula.is_implies():
        return Implies(args[0], args[1])
    if formula.is_ite():
        return Ite(args[0], args[1], args[2])
    if formula.is_iff():
        return Iff(args[0], args[1])
    if formula.is_equals():
        return Equals(args[0], args[1])
    if formula.is_and():
        return And(args)
    if formula.is_or():
        return Or(args)
    if formula.is_function_application():
        formulaType = formula.function_name()
        if formulaType in defMap:
            entry = defMap[formulaType]
            assert(len(entry) == 3)
            rhs = substituteDefinitions(entry[0], defMap)
            largs = entry[-1]
            subs = {}
            for idx, v in enumerate(largs):
                subs[v] = args[idx]
#                 print("%s becomes %s" % (v, subs[v]))
#             print("rhs: %s" % rhs)
            rhs = rhs.simple_substitute(subs)
#             print("rhsNew: %s" % rhs)
            return rhs
        if len(args) != 0:
            return Function(formulaType, args)
    if (mode == 0) and formula.is_symbol():
        formulaType = formula
        if formulaType in defMap:
            entry = defMap[formulaType]
            assert(len(entry) == 3)
            rhs = entry[0]
#             print("rhsNew: %s" % rhs)
            return rhs
        return formula
    return formula

def parseSizes(s):
    sizes = {}
    tokens = re.split('=|,', s)
    i = 0
    while i < len(tokens)-1:
        k = tokens[i]
        v = tokens[i+1]
        i += 2
        if len(k) == 0 or len(v) == 0:
            break
        if not v.isdigit():
            break
        if k in sizes:
            break
        sizes[k] = v
#     print(sizes)
    return sizes
            
    
    
