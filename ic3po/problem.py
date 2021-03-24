# ------------------------------------------
# IC3PO: IC3 for Proving Protocol Properties
# ------------------------------------------
# Copyright (c) 2021  Aman Goel and Karem Sakallah, University of Michigan. 
# All rights reserved.
#
# Author: Aman Goel (amangoel@umich.edu), University of Michigan
# ------------------------------------------

from __future__ import print_function

from utils import *
import pysmt
from pysmt.shortcuts import TRUE, And, Or, Not, EqualsOrIff, Exists, ForAll, is_sat,\
    Function
import sys
import common

def read_problem(self, fname):
    print(time_str(), "Reading from file %s" % fname)
    with open(fname, 'r') as script:
        self.system.read_ts(script)

def print_problem(self):
    print(time_str(), self.system.curr)

def add_props(self, props):
    for f in props:
        self.system.curr._prop.add(f)

def add_axioms(self, axioms):
    for f in axioms:
        self.system.curr._axiom.add(f)

def set_init_formula(self, unbounded):
    initS = self.system.curr._init
    if not initS:
        res = TRUE()
    else:
        res = And(initS)
    if unbounded:
        res = self.system.replaceDefinitions(res, 1)
    self._init_formula_orig = res
    res = self.get_formula_qf(res)
    self._init_formula = res
    return res

def set_trel_formula(self, unbounded):
    res = self.system.curr._trel
    if unbounded:
        res = self.system.replaceDefinitions(res, 1)
    res = self.get_formula_qf(res)
    self._trel_formula = res
    return res
    
def set_prop_formula(self, unbounded):
    propS = self.system.curr._prop
    if not propS:
        res = TRUE()
    else:
        res = And(propS)
    if unbounded:
        res = self.system.replaceDefinitions(res, 1)
    self._prop_formula_orig = res
    res = self.get_formula_qf(res)
    self._prop_formula = res
    return res

def set_axiom_formula(self, unbounded):
    axiomS = []
    
    for cl in self._faxioms:
        if unbounded:
            cl = self.system.replaceDefinitions(cl, 1)
        axiomS.append(cl)
    for cl in self.system.curr._axiom:
        if unbounded:
            cl = self.system.replaceDefinitions(cl, 1)
        axiomS.append(cl)
    
    if True or (not unbounded):
        for k, v in self.system.curr._definitions.items():
            axiomS.append(v)
    
    if len(self.system._sort2fin) == len(self.system._sorts):
        if self.ordered == "zero":
            cl = self.system.get_ordered_zero()
            axiomS.append(cl)
        
        if self.ordered == "partial":
            cl = self.system.get_ordered_le()
            axiomS.append(cl)
#             assert(0)
        
    if self.quorums != "none":
        cl = self.system.get_quorum_axiom()
        axiomS.append(cl)
#         assert(0)
        
    if not axiomS:
        res = TRUE()
    else:
        res = And(axiomS)
    res = self.get_formula_qf(res)
    self._axiom_formula = res
    return res

def set_problem(self, unbounded=False):
    if self.qf == 3:
        if len(self.system._sort2fin) != len(self.system._sorts):
            self.qf = 0
    if self.use_wires and (len(self.system.orig._definitions) == 0):
        self.use_wires = False
    print("(use_wires: %s)" % self.use_wires)
    set_init_formula(self, unbounded)
    set_trel_formula(self, unbounded)
    set_prop_formula(self, unbounded)
    set_axiom_formula(self, unbounded)

def init_formula(self):
    return self._init_formula
    
def init_formula_orig(self):
    return self._init_formula_orig
    
def trel_formula(self):
    return self._trel_formula

def prop_formula(self):
    return self._prop_formula

def prop_formula_orig(self):
    return self._prop_formula_orig

def axiom_formula(self):
    return self._axiom_formula


def pre2nex(self, f):
    fs = f.simple_substitute(self.system.curr._pre2nex)
    return fs
#     fsi = fs.simple_substitute(self.system.curr.syntax.inp2nex)
#     return fsi

def nex2pre(self, f):
    fs = f.simple_substitute(self.system.curr._nex2pre)
    return fs
#     fsi = fs.simple_substitute(self.system.curr.syntax.nex2pre)
#     return fsi

def set_solver(self):
    self.solver = self.new_solver()

def solve_query(formula, solver_name='z3'):
    """Provides a satisfiable assignment to the state variables that are consistent with the input formula"""
    res = is_sat(formula, solver_name)
    return res

def init_query(self):
    return And(init_formula(self), Not(prop_formula(self)))

def induct_query(self):
    return And(prop_formula(self), trel_formula(self), Not(pre2nex(self, prop_formula(self))))

def is_long_clause(system, cl):
    sort2sz = {}
    cube = Not(cl)
    if cube.is_exists():
        qvars = cube.quantifier_vars()
        for qv in qvars:
            qvt = qv.symbol_type()
            if qvt not in sort2sz:
                sort2sz[qvt] = 0
            sort2sz[qvt] += 1
    fullsorts = set()
    for s_fin in system._enumsorts.keys():
        sz = len(s_fin.domain)
        if sz < 3:
            continue
        if s_fin in sort2sz:
            if sort2sz[s_fin] >= sz:
                fullsorts.add(s_fin)
    if len(fullsorts) == 0:
        return False
    atoms = cube.get_atoms()
    for enumsort in fullsorts:
        isLong = True
        enumqvars = system._enum2qvar[enumsort]
        for i in range(len(enumqvars)-1):
            for j in range(i+1, len(enumqvars)):
                eq = EqualsOrIff(enumqvars[i], enumqvars[j])
                if eq not in atoms:
                    isLong = False
                    break
            if not isLong:
                break
        if isLong:
            return True
    return False

experimentGeneralize = True

def symmetry_cube(self, cube, fIdx, reducePremise, dest=None):
#     cube_str = pretty_serialize(Not(cube), mode=0)
    cube_str = pretty_serialize(Not(cube), mode=0)
    print("(clause)")
    print("\t%s" % cube_str)
    cvars = cube.get_enum_constants()
    crels = cube.get_free_variables()
    print("(relations)")
    for r in crels:
        print("\t%s" % pretty_serialize(r))
#     assert(0)
        
    subs = dict()
#         print(cvars)

    enum2qvar = dict()
#     for v in cvars:
    for v in sorted(cvars, key=str):
        enumsort = v.constant_type()
        if self.ordered == "partial" and enumsort in self.system._ordered_sorts:
            continue
        if self.ordered == "zero" and str(enumsort).startswith("epoch"):
#             continue
            assert(enumsort in self.system._enumsorts)
            domain = self.system._enumsorts[enumsort]
            zero = self.system.zero[1]
            firste = self.system.firste[1]
            le = self.system.le
            if v == domain[0]:
                subs[v] = zero
                continue
            elif v == domain[1]:
                subs[v] = firste
                continue
            else:
                rhs = firste
                end = 2
                try:
                    end = domain.index(v)
                except ValueError:
                    assert(0)
                for idx in range(end-1, 1, -2):
                    v2 = domain[idx]
                    if v2 in cvars:
                        rhs = v2
                        break
                gt = Not(Function(le, [v, rhs]))
                print("\tadding condition: %s" % pretty_print_str(gt))
                cube = And(cube, gt)
#                 neq = And(Not(EqualsOrIff(v, zero)), Not(EqualsOrIff(v, firste)))
#                 cube = And(cube, neq)
#         if (self.quorums != "none" and 
#             (str(enumsort).startswith("node") or str(enumsort).startswith("acceptor"))):
#             continue
        if (self.quorums != "none" and 
            (str(enumsort).startswith("quorum"))):
            continue
        if enumsort in self.system._enum2qvar:
            qvar = []
            if enumsort in enum2qvar:
                qvar = enum2qvar[enumsort]
            idx = len(qvar)
            qv = self.system._enum2qvar[enumsort][idx]
            qvar.append(qv)
            enum2qvar[enumsort] = qvar
            subs[v] = qv
            
    antecedent = dict()
    qvars = set()
    fullsorts = []
#         print(enum2qvar)
#         print(self.system._enum2qvar)
    minSz = 3
    if experimentGeneralize:
        minSz = 2
    for enumsort, qvar in enum2qvar.items():
        if  (
#                  False and
#                 (str(enumsort).startswith("acceptor") 
#                  or str(enumsort).startswith("node")
#                 or str(enumsort).startswith("quorum")
#                 ) and 
#                 (str(enumsort).startswith("quorum")) and 
            (len(qvar) >= minSz) and 
            (len(qvar) == len(self.system._enum2qvar[enumsort]))):
            fullsorts.append([enumsort, qvar])
        antecedent[enumsort] = []
        for i in range(len(qvar) - 1):
            qvi = qvar[i]
            qvars.add(qvi)
            for j in range(i+1, len(qvar)):
                if i != j:
                    deq = Not(EqualsOrIff(qvi, qvar[j]))
                    antecedent[enumsort].append(deq)
#                         print("adding: %s" % deq)
        qvars.add(qvar[-1])
    
    self.print_fullsorts(fullsorts)
    
    cubeSym = cube

    isorts = dict()
    ivars = set()
    if cubeSym.is_exists():
        for v in cubeSym.quantifier_vars():
            if v not in subs:
                vs = v.symbol_type()
                if vs not in isorts:
                    isorts[vs] = list()
                idx = len(isorts[vs])
                name = str(vs) + ":i" + str(idx)
                isymbol = Symbol(name, vs)
                isorts[vs].append(isymbol)
                subs[v] = isymbol
                ivars.add(isymbol)
                qvars.add(isymbol)
        cubeSym = cubeSym.args()[0]
                
    cubeSym = cubeSym.simple_substitute(subs)
    cubeSet = flatten_cube(cubeSym)
    
#         self.reduce_antecedent(cubeSet, qvars, antecedent, fIdx)
    
    print("(cube: std)")
    for c in cubeSet:
        print("\t%s" % pretty_serialize(c, mode=0))

    if common.gopts.opt > 0 and reducePremise:
        push_time()
        antecedent, reduceSz, varSet = self.reduce_antecedent2(cubeSym, qvars, enum2qvar, fIdx)
        self.update_time_stat("time-antecedent", pop_time())
        print()
    
    if self.ordered == "partial":
        cubeSet = self.boost_ordered(cubeSet, antecedent, qvars, fIdx)

    eqMap = dict()
    if common.gopts.const > 0:
        eqMap, cubeSet, antecedent, fullsorts = self.propagate_eq(cubeSet, antecedent, ivars, qvars, fullsorts)

    if True:
        cubeSetSimple = cubeSet.copy()
        for v in antecedent.values():
            for c in v:
                cubeSetSimple.add(c)
                
        cubeSimple = And(cubeSetSimple)
        if len(qvars) != 0:
            cubeSimple = Exists(qvars, cubeSimple)
                
        cubesOut = list()
        if (self.system.gen == "univ") or (len(fullsorts) == 0) or (len(crels) <= 1) or (len(cubeSet) < minSz):
            cubesOut.append((cubeSimple, "univ"))
        else:
            uqvars = set()        
            
            cubeSet2 = cubeSet.copy()
            for fs in fullsorts:
                enumsort = fs[0]
                qvar = fs[1]
                qvarSet = set()
                for q in qvar:
                    qvarSet.add(q)
                
                qvart = fs[0]
                uSymbol = Symbol("V:"+str(qvart), qvart)
                qv2cubes = {}
                qv2ucubes = {}
                for q in qvar:
                    qv2cubes[q] = set()
                    qv2ucubes[q] = set()
                
                ucubes = set()
                for c in cubeSet:
                    cvars = c.get_free_variables()
                    cqvars = cvars.intersection(qvarSet)
#                     cqvars = c.get_filtered_nodes(qvarSet)
                    for q in cqvars:
                        tmp_subs = {}
                        tmp_subs[q] = uSymbol
                        uc = c.substitute(tmp_subs)
                        ucubes.add(uc)
                        qv2cubes[q].add(c)
                        qv2ucubes[q].add(uc)
                print("qv2cubes #%d" % len(qv2cubes))
                for k, v in qv2cubes.items():
                    print("\t%s -> %s" % (pretty_serialize(k), pretty_print_set(v, mode=0)))
                print("qv2ucubes #%d" % len(qv2ucubes))
                for k, v in qv2ucubes.items():
                    print("\t%s -> %s" % (pretty_serialize(k), pretty_print_set(v, mode=0)))
                
                ucubes2qv = {}
                for qv, ucubes in qv2ucubes.items():
                    ucubes_sorted = sorted(ucubes, key=str)
                    uc = And(ucubes_sorted)
                    if uc not in ucubes2qv:
                        ucubes2qv[uc] = set()
                    ucubes2qv[uc].add(qv)
                print("ucubes2qv #%d" % len(ucubes2qv))
                singles = []
                multiples = []
                for k, v in ucubes2qv.items():
                    if len(v) == 1:
                        singles.append(k)
                    elif len(v) >= minSz:
                        multiples.append(k)
                    print("\t%s -> %s" % (pretty_serialize(k), pretty_print_set(v, mode=0)))

                print("(partition) #%d %s -> { " % (len(ucubes2qv), enumsort), end="")
                for v in ucubes2qv.values():
                    for d in v:
                        print("%s, " % pretty_serialize(d), end="")
                    print("| ", end="")
                print("}")

                nsingles = len(singles)
                nmultiples = len(multiples)
                ncells = len(ucubes2qv)
                print("\t#%d singles, #%d multiples (out of #%d cells)" % (nsingles, nmultiples, ncells))

                if len(ucubes2qv) == 1:
                    for rhs in ucubes2qv.values():
                        if len(rhs) != len(qvar):
                            print("found single part with incomplete instances")
                            assert(0)
                    if qvar[0].is_symbol():
                        uqvars.add(qvar[0])
                    antecedent.pop(enumsort, None)
                    
                    for cubes in qv2cubes.values():
                        for cube in cubes:
                            cubeSet2.discard(cube)
                    for uc in ucubes2qv.keys():
                        tmp_subs = {}
                        tmp_subs[uSymbol] = qvar[0]
                        uc = uc.simple_substitute(tmp_subs)
                        ucList = flatten_cube(uc)
                        for v in ucList:
                            cubeSet2.add(v)                
                    for q in qvar:
                        qvars.discard(q)
                    cubeSet = cubeSet2
                elif (ncells == (nsingles + nmultiples) 
                      and nmultiples == 1
                      and nsingles == 1
                      ):
#                 elif (len(ucubes2qv) == 2 
#                       and (len(qvar) > minSz)
# #                           and (not self.system.is_epr())
#                     ):
#                     elif len(ucubes2qv) == 2 and (len(qvar) > minSz) and (not self.system.is_epr()):
                    qsingle = []
                    qmulti = None
                    for k in singles:
                        assert(k in ucubes2qv)
                        qg = ucubes2qv[k]
                        assert(len(qg) == 1)
                        for q in qg:
                            qsingle.append(q)
                    for k in multiples:
                        assert(k in ucubes2qv)
                        qg = ucubes2qv[k]
                        assert(len(qg) >= minSz)
                        if len(qg) == (len(qvar) - len(qsingle)):
                            qmulti = qg

                    if len(qsingle) != 0 and qmulti != None:
                        ucsingle = {}
                        ucmulti = set()
                        
                        for qs in qsingle:
                            ucsingle[qs] = set()
                            tmp_subs = {}
                            tmp_subs[uSymbol] = qs
                            for uc in qv2ucubes[qs]:
                                uc = uc.simple_substitute(tmp_subs)
                                ucsingle[qs].add(uc)
                        qm = sorted(qmulti, key=str)[0]
                        tmp_subs = {}
                        tmp_subs[uSymbol] = qm
                        for uc in qv2ucubes[qm]:
                            uc = uc.simple_substitute(tmp_subs)
                            ucmulti.add(uc)
                            
                        print("ucsingle:")
                        for k, rhs in ucsingle.items():
                            print("\t%s:" % pretty_serialize(k))
                            for v in rhs:
                                print("\t\t%s" % pretty_serialize(v))
                        print("ucmulti:")
                        for v in ucmulti:
                            print("\t%s" % pretty_serialize(v))
                            
                        if qm.is_symbol():
                            uqvars.add(qm)
                        if enumsort in antecedent:
                            newAnt = []
                            for v in antecedent[enumsort]:
                                vvars = v.get_free_variables()
                                vmvars = vvars.intersection(qmulti)
                                if len(vmvars) == 0:
                                    newAnt.append(v)
                            antecedent.pop(enumsort, None)
                            if len(newAnt) != 0:
                                antecedent[enumsort] = newAnt
                        
                        for q in qmulti:
                            for cube in qv2cubes[q]:
                                cubeSet2.discard(cube)
#                             for v in ucsingle:
#                                 cubeSet2.add(v)                
                        for q in qmulti:
                            qvars.discard(q)
                        eqM = []
                        for qs in qsingle:
                            eqM.append(EqualsOrIff(qs, qm))
                        sEqm = Or(eqM)
                        for v in ucmulti:
                            vNew = Or(sEqm, v)
                            cubeSet2.add(vNew)
                        cubeSet = cubeSet2
                
            eqvars2 = set()
            forwardArcs = 0
            reverseArcs = 0
            if len(uqvars) != 0:
                if (self.system.gen != "fe"):
                    for u in qvars:
                        ut = u.symbol_type()
                        for e in uqvars:
                            et = e.symbol_type()
                            if (self.system.gen == "fef"):
                                if ut != et or True:
                                    eqvars2.add(u)
                            else:
                                print("\t(epr check: forward)", end="")
                                if not self.system.allowed_arc(ut, et):
                                    forwardArcs += 1
                                    print("\t(epr check: reverse)", end="")
                                    if not self.system.allowed_arc(et, ut):
                                        reverseArcs += 1
                                    eqvars2.add(u)
                for u in eqvars2:
                    if u in qvars:
                        qvars.remove(u)

            cubeSet = cubeSet2
            for v in antecedent.values():
                for c in v:
                    cubeSet.add(c)
            
            cubesOut = list()
            if (self.system.gen == "fef") and (len(uqvars) != 0) and (len(eqvars2) != 0):
                fancy = "fef"

                cubeSym = None
                count = 0
                innerVars = list(eqvars2)
                while True or (len(innerVars) != 0):
                    count += 1
                    preCube = set()
                    postCube = set()
                    postVars = set()
                    for q in uqvars:
                        postVars.add(q)
                    for q in innerVars:
                        postVars.add(q)
                    for c in cubeSet:
                        argvars = c.get_free_variables()
                        argvars = argvars.intersection(postVars)
                        if len(argvars) == 0:
                            preCube.add(c)
                        else:
                            postCube.add(c)
                    postCube = sorted(postCube, key=str)
                    preCube = sorted(preCube, key=str)
                    cubeSym = And(postCube)
                    if len(innerVars) != 0:
                        cubeSym = Exists(innerVars, cubeSym)
                    if len(uqvars) != 0:
                        cubeSym = ForAll(uqvars, cubeSym)
                    if len(preCube) != 0:
                        cubeSym = And(And(preCube), cubeSym)
                    if len(qvars) != 0:
                        cubeSym = Exists(qvars, cubeSym)
                    print("(#%d: quantifier-reduced) " % count)
                    print("\t%s" % pretty_serialize(Not(cubeSym), mode=0))

#                     notCubeSym_formula = self.get_formula_qf(Not(cubeSym))
#                     print("\t(quantifier-free version)")
#                     notCubeSym_formulaList = flatten_and(notCubeSym_formula)
#                     for v in notCubeSym_formulaList:
#                         print("\t\t%s" % pretty_serialize(v))
                    
                    solver = self.get_framesolver(fIdx)
                    cubeSym_formula = self.get_formula_qf(cubeSym)
                    print("\t(#%d: quantifier-rearrangement) " % count, end="")
                    result = self.solve_formula(solver, cubeSym_formula)
                    if not result:
                        cubesOut.append((cubeSym, fancy))
                        break
                    if len(innerVars) != 0:
                        u = innerVars.pop(0)
                        qvars.add(u)
                    else:
                        break
                assert(len(cubesOut) != 0)
                cubesOut.reverse()
                
#                 if len(cubesOut) == 0:
#                     preCube = set()
#                     postCube = set()
#                     postVars = set()
#                     for q in uqvars:
#                         postVars.add(q)
#                     for q in innerVars:
#                         postVars.add(q)
#                     for c in cubeSet:
#                         argvars = c.get_free_variables()
#                         argvars = argvars.intersection(postVars)
#                         if False and len(argvars) == 0:
#                             preCube.add(c)
#                         else:
#                             postCube.add(c)
#                     postCube = sorted(postCube, key=str)
#                     preCube = sorted(preCube, key=str)
#                     cubeSym2 = And(postCube)
#                     if len(uqvars) != 0:
#                         cubeSym2 = ForAll(uqvars, cubeSym2)
#                     if len(innerVars) != 0:
#                         cubeSym2 = Exists(innerVars, cubeSym2)
#                     if len(preCube) != 0:
#                         cubeSym2 = And(And(preCube), cubeSym2)
#                     if len(qvars) != 0:
#                         cubeSym2 = Exists(qvars, cubeSym2)
#                     cubesOut.append((cubeSym2, fancy))
            else:
                preCube = set()
                postCube = set()
                if len(uqvars) == 0:
                    postCube = cubeSet
                else:
                    postVars = set()
                    for q in uqvars:
                        postVars.add(q)
                    for q in eqvars2:
                        postVars.add(q)
                    for c in cubeSet:
                        argvars = c.get_free_variables()
                        argvars = argvars.intersection(postVars)
                        if len(argvars) == 0:
                            preCube.add(c)
                        else:
                            postCube.add(c)
                postCube = sorted(postCube, key=str)
                preCube = sorted(preCube, key=str)
                cubeSym = And(postCube)
                if len(eqvars2) != 0:
                    cubeSym = Exists(eqvars2, cubeSym)
                if len(uqvars) != 0:
                    cubeSym = ForAll(uqvars, cubeSym)
                if len(preCube) != 0:
                    cubeSym = And(And(preCube), cubeSym)
                if len(qvars) != 0: 
                    cubeSym = Exists(qvars, cubeSym)
                
                fancy = "univ"
                if (len(uqvars) != 0):
                    fancy = "epr"
                cubesOut.append((cubeSym, fancy))
                
                if fancy:
                    if len(eqvars2) != 0:
                        cubeSym2 = And(postCube)
                        if len(uqvars) != 0:
                            cubeSym2 = ForAll(uqvars, cubeSym2)
                        if len(eqvars2) != 0:
                            cubeSym2 = Exists(eqvars2, cubeSym2)
                        if len(preCube) != 0:
                            cubeSym2 = And(And(preCube), cubeSym2)
                        if len(qvars) != 0:
                            cubeSym2 = Exists(qvars, cubeSym2)
                        print("(epr reduced)")
                        print("\t%s" % pretty_serialize(Not(cubeSym), mode=0))
                        print("(non-epr version)")
                        print("\t%s" % pretty_serialize(Not(cubeSym2), mode=0))
                        
                        result = False
                        if (reverseArcs != 0):
                            print("\tBoth verions not allowed!")
                            if (self.system.gen == "epr_strict"):
                                result = True
                            
                        if not result:
                            solver = self.get_framesolver(fIdx)
                            print("(epr-reduction) ", end="")
                            cubeSym_formula = self.get_formula_qf(cubeSym)
                            result = self.solve_formula(solver, cubeSym_formula)
                        if result:
                            print("\tEPR-reduction is not allowed!")
                            cubesOut.pop()
                            
                            if (self.system.gen == "epr_strict") or (self.system.gen == "epr_loose"):
                                print("\tLearning universal version instead.")
                                cubesOut.append((cubeSimple, "univ"))
                            else:
                                print("\tLearning non-epr version instead.")
                                cubesOut.append((cubeSym2, "non-epr"))
    #                         assert(0)

        if common.gopts.const > 0:
            for i in range(len(cubesOut)):
                cubeTop = cubesOut[i]
                cubeEq = self.propagate_eq_post(cubeTop[0])
                cubesOut[i] = (cubeEq, cubeTop[1])
    
        print("(boosted clause)")
        print("\t%s" % pretty_serialize(Not(cubesOut[0][0]), mode=0))
        
        print("---------------------------")
        print("(original clause)")
        print("\t%s" % cube_str)
        print("(learnt sym-boosted clause)")
        print("\t%s" % pretty_serialize(Not(cubesOut[0][0]), mode=0))
        print("---------------------------")
    else:
        cubesOut = get_uniform(self, fullsorts, cubeSet, qvars, antecedent)
    
    return cubesOut

def get_uniform(self, fullsorts, cubeSet, eqvars, antecedent):
#         print("fullsorts: %s" % (fullsorts))
    uqvars = []        
    eqvars2 = []
    subs = dict()

    if len(fullsorts) != 0:
        for fs in fullsorts:
#             continue
            efs = fs[0]
            qvar = fs[1]
#             qvar = fullsorts[0][1]
            qvarSet = set()
            for q in qvar:
                qvarSet.add(q)
                subs[q] = qvar[0]
                
            isUniform = True
            uniformSet = dict()
            otherPresent = False
            for c in cubeSet:
                cvars = c.get_free_variables()
                cqvars = cvars.intersection(qvarSet)
    #             print(c)
    #             print(cvars)
    #             print(qvarSet)
    #             print(cqvars)
                if len(cqvars) == 1:
                    uniformc = c.simple_substitute(subs)
                    if uniformc not in uniformSet:
                        uniformSet[uniformc] = list()
                    uniformSet[uniformc].append(c)
#                         print("uniformc %s" % uniformc)
                elif len(cqvars) > 1:
                    print("cube %s has multiple cqvars: %s" % (c, cqvars))
                    isUniform = False
                elif len(cqvars) == 0:
                    otherPresent = True
                        
            ucList = []
            if isUniform:
                for uc, clist in uniformSet.items():
                    if len(clist) != len(qvar):
                        isUniform = False
                        print("not symmetric due to:")
                        for c in clist:
                            print("\t%s" % pretty_serialize(c))
                        break
    #                     for c in clist:
    #                         print("\t%s" % c.serialize())
                    ucList.append(uc)

            if experimentGeneralize:
                if isUniform and not otherPresent:
                    isUniform = False
                    if len(qvar) > 2:
                        eprint("Warning: experimental")
                        print("Warning: experimental")

            if not isUniform:
                for q in qvar:
                    subs.pop(q)
            if (isUniform and len(ucList) != 0):
                for k, clist in uniformSet.items():
                    for c in clist:
                        cubeSet.remove(c)
                
                uqvars.append(qvar[0])
                for uc in ucList:
                    cubeSet.add(uc)
                antecedent.pop(efs)
                for q in qvar:
                    eqvars.remove(q)
                    
    if len(uqvars) != 0:
        for u in eqvars:
            ut = u.symbol_type()
            for e in uqvars:
                et = e.symbol_type()
                if not self.system.allowed_arc(ut, et):
                    eqvars2.append(u)
        for u in eqvars2:
            if u in eqvars:
                eqvars.remove(u)
                      
    for k, v in antecedent.items():
        for i in v:
            cubeSet.add(i)
    
    preCube = set()
    postCube = set()
    if len(uqvars) == 0:
        postCube = cubeSet
    else:
        postVars = set()
        for q in uqvars:
            postVars.add(q)
        for q in eqvars2:
            postVars.add(q)
        for c in cubeSet:
            argvars = c.get_free_variables()
            argvars = argvars.intersection(postVars)
            if len(argvars) == 0:
                preCube.add(c)
            else:
                postCube.add(c)
#             print("pre : %s" % preCube)
#             print("post: %s" % postCube)
    
    cubeSym = And(postCube)
    if len(eqvars2) != 0:
        cubeSym = Exists(eqvars2, cubeSym)
    if len(uqvars) != 0:
        cubeSym = ForAll(uqvars, cubeSym)
        print("uniform: %s\t%s" % (uqvars, cubeSym))
#             if len(uqvars) > 1:
#                 assert(0)
    if len(preCube) != 0:
        cubeSym = And(And(preCube), cubeSym)
    if len(eqvars) != 0:
        cubeSym = Exists(eqvars, cubeSym)
    
    cubesOut = list()
    fancy = (len(uqvars) != 0)
    cubesOut.append((cubeSym, fancy))
    
#     if complex:
#         pretty_print(cubeSym)
#         assert(0)
        
    return cubesOut

def get_uniform2(self, fullsorts, cubeSet, eqvars, antecedent, varSet, enum2qvar):
    allow_nonepr = False
    uqvars = []
    eqvars2 = []
    subs = dict()
    
    uniformed = False
    if len(fullsorts) != 0:
        cubeSetSym = set()
        for cube in cubeSet:
            cubeSetSym.add(cube)
#         for k in antecedent.keys():
#             if k in varSet:
#                 continue
#             kt = k.symbol_type()
#             assert(kt in enum2qvar)
#             for qv in enum2qvar[kt]:
#                 subs[qv] = k
#         for cube in cubeSet:
#             cubeSym = cube.simple_substitute(subs)
#             cubeSetSym.add(cubeSym)
#             if cubeSym != cube:
#                 uniformed = True
            
#         subs.clear()
        
    for k, v in antecedent.items():
        for i in v:
            cubeSet.add(i)
    cubeSym = And(cubeSet)
    if len(eqvars) != 0:
        cubeSym = Exists(eqvars, cubeSym)
    cubesOut = list()
    cubesOut.append((cubeSym, False))
    
    for fs in fullsorts:
        qvart = fs[0]
        qvar = fs[1]
        qvarSet = set()
        for q in qvar:
            qvarSet.add(q)
        
        uSymbol = Symbol("V:"+str(qvart), qvart)
        qv2cubes = {}
        qv2ucubes = {}
        for q in qvar:
            qv2cubes[q] = set()
            qv2ucubes[q] = set()
        for c in cubeSetSym:
            cvars = c.get_free_variables()
            cqvars = cvars.intersection(qvarSet)
            if len(cqvars) > 1:
                print("Found multiple fullsorts in atom %s" % c)
                print("Enabling nonepr mode")
                allow_nonepr = True
            for q in cqvars:
                tmp_subs = {}
                tmp_subs[q] = uSymbol
                uc = c.simple_substitute(tmp_subs)
                qv2cubes[q].add(c)
                qv2ucubes[q].add(uc)
#         print("qv2cubes #%d" % len(qv2cubes))
#         for k, v in qv2cubes.items():
#             print("\t%s -> %s" % (k, v))
#         print("qv2ucubes #%d" % len(qv2ucubes))
#         for k, v in qv2ucubes.items():
#             print("\t%s -> %s" % (k, v))
        
        ucubes2qv = {}
        for qv, ucubes in qv2ucubes.items():
            uc = And(ucubes)
            if uc not in ucubes2qv:
                ucubes2qv[uc] = set()
            ucubes2qv[uc].add(qv)
        print("ucubes2qv #%d" % len(ucubes2qv))
        for k, v in ucubes2qv.items():
            print("\t%s -> %s" % (k, v))
        
        nump = len(ucubes2qv)
        assert(nump != 0)
        if nump == 1:
            # just 1 uniform structure
            for rhs in ucubes2qv.values():
                if len(rhs) != len(qvar):
                    print("found single part with incomplete instances")
                    assert(0)
            uq = qvar[0]
#                 print("uq: %s" % uq)
            for qv, cubes in qv2cubes.items():
                eqvars.discard(qv)
#                     print("cubes: %s" % cubes )
                if qv != uq:
                    for cube in cubes:
                        cubeSetSym.discard(cube)
#                             print("discarding: %s" % cube)
            uqvars.append(uq)
            antecedent.pop(qvar[0])
#                 print("cubeSetSym: %s" % cubeSetSym)
        elif nump == 2 and allow_nonepr:
            pass
#             uc = None
#             for ucubes, qv in ucubes2qv.items():
#                 if len(qv) == (len(qvar)-1):
#                     uc = ucubes
#                     break
#             if uc != None:
#                 print("found 1,N-1 parts")
#                 cubeRem = set()
#                 for qv, cubes in qv2cubes.items():
#                     for cube in cubes:
#                         cubeSetSym.discard(cube)
#                         cubeRem.add(cube)
# 
#                 uqs = ucubes2qv[uc]
#                 uq = sorted(uqs, key=str)[0]
#                 qvars_new = set()
#                 tmp_subs = {}
#                 cubeL = set()
#                 for qv, cubes in qv2cubes.items():
#                     if qv not in uqs:
#                         qvars_new.add(qv)
#                         continue
#                     eqvars.discard(qv)
#                     if qv != uq:
#                         tmp_subs[qv] = uq
#                         for cube in cubes:
#                             cubeRem.discard(cube)
#                     else:
#                         for cube in cubes:
#                             cubeL.add(cube)
#                             cubeRem.discard(cube)
#                 assert(len(qvars_new) == 1)
#                 assert(len(cubeL) != 0)
#                 for qv in qvars_new:
#                     eq = EqualsOrIff(qv, uq)
#                     cubeNew = Or(eq, And(cubeL))
#                     cubeSetSym.add(cubeNew)
#                 for cube in cubeRem:
#                     cubeSetSym.add(cube)
#                 uqvars.append(uq)
#                 antecedent.pop(qvar[0])
#                 qvars_new.add(uq)
    
    if len(uqvars) == 0:
        return cubesOut
    
    for k, v in antecedent.items():
        for i in v:
            cubeSetSym.add(i)

    for u in eqvars:
        ut = u.symbol_type()
        for e in uqvars:
            et = e.symbol_type()
            if not allow_nonepr and (not self.system.allowed_arc(ut, et)):
                eqvars2.append(u)
    for u in eqvars2:
        if u in eqvars:
            eqvars.remove(u)
    
    preCube = set()
    postCube = set()
    postVars = set()
    for q in uqvars:
        postVars.add(q)
    for q in eqvars2:
        postVars.add(q)
    for c in cubeSetSym:
        argvars = c.get_free_variables()
        argvars = argvars.intersection(postVars)
        if len(argvars) == 0:
            preCube.add(c)
        else:
            postCube.add(c)
    
    cubeSym = And(postCube)
    if len(eqvars2) != 0:
        cubeSym = Exists(eqvars2, cubeSym)
    cubeSym = ForAll(uqvars, cubeSym)
    if len(preCube) != 0:
        cubeSym = And(And(preCube), cubeSym)
    if len(eqvars) != 0:
        cubeSym = Exists(eqvars, cubeSym)
        
    print("uniform: %s\n\t" % uqvars, end="")
    pretty_print(cubeSym)

    if not uniformed:
        cubesOut.pop()
    fancy = (len(uqvars) != 0)
    cubesOut.insert(0, (cubeSym, fancy))
        
    return cubesOut

def print_sizes1(self, key):
    val = ""
    for s_inf in sorted(self.system._sorts, key=str):
        sz = 0
        if s_inf in self.system._sort2fin:
            s_fin = self.system._sort2fin[s_inf]
            sz = len(self.system._enumsorts[s_fin])
        val += "|%s|=%s;" % (s_inf, ("inf" if sz == 0 else str(sz)))
    print_stat(key, val)

def print_sizes2(self, key):
    val = ""
    for s_inf in sorted(self.system._sorts, key=str):
        sz = 0
        for s_fin, s_inf2 in self.system._fin2sort.items():
            if s_inf == s_inf2:
                sz = len(self.system._enumsorts[s_fin])
                break
        val += "|%s|=%s;" % (s_inf, ("inf" if sz == 0 else str(sz)))
    print_stat(key, val)
    
