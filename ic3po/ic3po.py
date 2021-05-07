# ------------------------------------------
# IC3PO: IC3 for Proving Protocol Properties
# ------------------------------------------
# Copyright (c) 2021  Aman Goel and Karem Sakallah, University of Michigan. 
# All rights reserved.
#
# Author: Aman Goel (amangoel@umich.edu), University of Michigan
# ------------------------------------------


from __future__ import print_function

import os
import pysmt
import random
import z3

from vmt_parser import TransitionSystem

from pysmt.shortcuts import Symbol, Not, And, Or, EqualsOrIff, Implies, Function, Exists, ForAll,\
    get_free_variables, get_quantifier_variables
from pysmt.shortcuts import is_sat, is_unsat, Solver, UnsatCoreSolver, QuantifierEliminator, TRUE, FALSE, get_atoms
from pysmt.typing import BOOL, FunctionType
from pysmt.environment import get_env
import pysmt.operators as op

from pysmt.exceptions import SolverReturnedUnknownResultError

import utils
from utils import *
from problem import *
from z3.z3util import get_z3_version
from pysmt.pretty_printer import pretty_serialize
import common

import yices_api
import itertools

os.environ["PYTHONHASHSEED"] = "0"
iterationCount = 0

class PDR(object):
    def __init__(self, system):
        self.system = system
        self.stat = dict()
        self.time_stat = dict()
        self.query_stat = dict()
        self.random = common.gopts.random
        self.qf = common.gopts.qf
        self.qtype = "?"
        self.verbose = common.gopts.verbosity
        self.last_solver = None
        self.qf_fallback_timeout = 0       # in milliseconds
        self.use_z3_minimize = False
        self.seed = common.gopts.seed
        eprint("\t(using z3 %s with seed %s)" % (get_z3_version(True), "random" if (self.random > 0) else str(self.seed)))
        print("\t(using z3 %s with seed %s)" % (get_z3_version(True), "random" if (self.random > 0) else str(self.seed)))
        eprint("\t(using yices %s with seed %s)" % (yices_api.yices_version, "random" if (self.random > 0) else str(self.seed)))
        print("\t(using yices %s with seed %s)" % (yices_api.yices_version, "random" if (self.random > 0) else str(self.seed)))
        self.init_stats()
        self.reset()
        self.debug = False
        self.subsume_level = common.gopts.subsume
        self.allow_inputs_in_cube = False
        self.use_wires = (common.gopts.wires != 0)
        if False:
#         if True:
            self.ordered = "partial"
            self.quorums = "none"
            self.boosting = "any"
            self.allow_inputs_in_cube = False
        else:
            self.ordered = "none"
#             self.quorums = "symmetric"
            self.quorums = "none"
            self.boosting = "any"
    
    def init_solver(self, qf):
        if qf == 0:
            solver = UnsatCoreSolver(name="z3", logic="UF", random_seed=self.solver_seed())
        else:
            if len(self.system._sort2fin) == len(self.system._sorts):
                solver = UnsatCoreSolver(name="yices", logic="QF_UF", random_seed=self.solver_seed())
#                 solver = UnsatCoreSolver(name="z3", logic="UF", random_seed=self.solver_seed())
                if self.qf != 2:
                    solver.enable_qf()
            else:
                solver = UnsatCoreSolver(name="z3", logic="UF", random_seed=self.solver_seed())
#                 if self.use_wires() and len(self.system._fin2sort) == len(self.system._sorts):
#                     solver.enable_qf()
        return solver

    def reset(self):
        self.frames = []
        self.globals = {}
        self.prospectives = {}
        self.framesolver = []
        z3ctx = z3.main_ctx()
        del z3ctx
        if yices_api.yices_is_inited():
            yices_api.yices_reset()
        self.solver = self.init_solver(self.qf)
        self.qesolver = QuantifierEliminator(name='scalarshannon')
        self._faxioms = []
        self._init_formula = TRUE()
        self._init_formula_orig = TRUE()
        self._trel_formula = TRUE()
        self._prop_formula = TRUE()
        self._prop_formula_orig = TRUE()
        self._axiom_formula = TRUE()
        self._print = False
        get_env().fsubstituter.freset()
        self._subsume = dict()
        self.cache_qf = dict()
        self.cache_qu = dict()
        self.init_values = dict()
        self.globalEnum = set()
#         z3.set_param('smt.ematching', False)
#         print("z3.smt.ematching = %s" % z3.get_param('smt.ematching'))
#         print("z3.smt.mbqi = %s" % z3.get_param('smt.mbqi'))
#         print("z3.smt.core.minimize = %s" % z3.get_param('smt.core.minimize'))
#         print('PYTHON HASH SEED IS', os.environ['PYTHONHASHSEED'])
        self.qf = common.gopts.qf
    
    def solver_seed(self):
        return self.seed
#         if self.random > 0:
#             return random.randint(0,999999)
#         else:
#             return self.seed
        
    def init_stats(self):
        self.set_stat("scalls", 0)
        self.set_stat("scalls-finite", 0)
        self.set_stat("scalls-infinite", 0)
        self.set_stat("scalls-finite-full", 0)
        self.set_stat("cti", 0)
        self.set_stat("cubes", 0)
        self.set_stat("subsumed-calls", 0)
        self.set_stat("subsumed-subset", 0)
        self.set_stat("subsumed-varintersect-c", 0)
        self.set_stat("subsumed-varintersect-e", 0)
        self.set_stat("subsumed-query-sat", 0)
        self.set_stat("subsumed-query-unsat", 0)
        self.set_stat("subsumed-eq", 0)
        self.set_stat("unsat-core", 0)
        self.set_stat("sz-unsat-core-sum", 0)
        self.set_stat("sz-unsat-min-sum", 0)
        self.set_stat("sz-cube-sum", 0)
        self.set_stat("antecedent-reduction-sum", 0)
        self.set_stat("antecedent-total-sum", 0)
        self.set_stat("antecedent-calls", 0)
        self.set_stat("antecedent-calls-reduced", 0)
        self.set_stat("antecedent-scalls", 0)
        self.init_time_stats()

    def init_time_stats(self):
        self.set_time_stat("time-cti-bad-sat", 0)
        self.set_time_stat("time-cti-bad-unsat", 0)
        self.set_time_stat("time-cti-sat", 0)
        self.set_time_stat("time-cti-unsat", 0)
        self.set_time_stat("time-forward", 0)
        self.set_time_stat("time-antecedent", 0)
        self.set_time_stat("time-subsume", 0)
        self.set_time_stat("time-subsume-query", 0)
        self.set_time_stat("time-inv-check-finite", 0)
        self.set_time_stat("time-inv-check-infinite", 0)
        self.set_time_stat("time-inv-reuse", 0)
        self.set_time_stat("time-minimize", 0)
        self.set_time_stat("time-qf", 0)
        self.init_query_stats()
        
    def init_query_stats(self):
        self.set_query_stat("time-q-max-finite", 0)
        self.set_query_stat("time-q-max-finite-core", 0)
        self.set_query_stat("time-q-max-infinite", 0)
        self.set_query_stat("time-q-max-infinite-core", 0)

    def print_stats(self, func=print_stat_stdout):
        print_stat_stdout("random", self.random)
        self.print_stat(func, "scalls")
        self.print_stat(func, "scalls-finite")
        self.print_stat(func, "scalls-infinite")
        self.print_stat(func, "scalls-finite-full")
        self.print_stat(func, "cti")
        self.print_stat(func, "cubes")
        self.print_stat(func, "subsumed-calls")
        self.print_stat(func, "subsumed-subset")
        self.print_stat(func, "subsumed-varintersect-c")
        self.print_stat(func, "subsumed-varintersect-e")
        self.print_stat(func, "subsumed-query-sat")
        self.print_stat(func, "subsumed-query-unsat")
        self.print_stat(func, "subsumed-eq")
        self.print_stat(func, "unsat-core")
        self.print_avg_stat(func, "sz-unsat-core-sum", self.stat["unsat-core"])
        self.print_avg_stat(func, "sz-unsat-min-sum", self.stat["unsat-core"])
        self.print_avg_stat(func, "sz-cube-sum", self.stat["cubes"])
        self.print_stat(func, "antecedent-reduction-sum")
        self.print_stat(func, "antecedent-total-sum")
        self.print_avg_stat(func, "antecedent-reduction-sum", self.stat["antecedent-total-sum"])
        self.print_stat(func, "antecedent-calls")
        self.print_stat(func, "antecedent-calls-reduced")
        self.print_stat(func, "antecedent-scalls")
        self.print_time_stats(func)
        print(time_str(), "-------------------------------------------------")
        
    def print_query_stats(self, func=print_stat_stdout):
        self.print_query_stat(func, "time-q-max-finite")
        self.print_query_stat(func, "time-q-max-finite-core")
        self.print_query_stat(func, "time-q-max-infinite")
        self.print_query_stat(func, "time-q-max-infinite-core")
        
    def print_time_stats(self, func=print_stat_stdout):
        self.print_query_stats(func)
        self.print_time_stat(func, "time-cti-bad-sat")
        self.print_time_stat(func, "time-cti-bad-unsat")
        self.print_time_stat(func, "time-cti-sat")
        self.print_time_stat(func, "time-cti-unsat")
        self.print_time_stat(func, "time-forward")
        self.print_time_stat(func, "time-antecedent")
        self.print_time_stat(func, "time-subsume")
        self.print_time_stat(func, "time-subsume-query")
        self.print_time_stat(func, "time-inv-check-finite")
        self.print_time_stat(func, "time-inv-check-infinite")
        self.print_time_stat(func, "time-inv-reuse")
        self.print_time_stat(func, "time-minimize")
        self.print_time_stat(func, "time-qf")
        self.print_total_time(func)
        print(time_str(), "-------------------------------------------------")
        
    def print_stat(self, func, name):
        assert name in self.stat
        func(name, self.stat[name])

    def print_time_stat(self, func, name, prefix=""):
        assert name in self.time_stat
        func("%s%s" % (prefix, name), "%.0f" % self.time_stat[name])

    def print_query_stat(self, func, name):
        assert name in self.query_stat
        func(name+"-ms", "%.0f" % self.query_stat[name])

    def print_total_time(self, func):
        total = 0
        for k, v in self.time_stat.items():
            if k != "time-subsume-query" and k != "time-qf":
                total += v
        func("time-sum", "%.0f" % total)

    def print_avg_stat(self, func, name, denom):
        assert name in self.stat
        name_avg = name.replace("-sum", "-avg")
        if denom == 0:
            func(name_avg, -1)
        else:
            value = (1.0 * self.stat[name]) / denom
            func(name_avg, "%.2f" % value)

    def set_stat(self, name, value):
        self.stat[name] = value

    def set_time_stat(self, name, value):
        self.time_stat[name] = value

    def set_query_stat(self, name, value):
        self.query_stat[name] = value

    def update_stat(self, name, value=1):
        assert name in self.stat
        self.stat[name] += value

    def update_time_stat(self, name, value=1):
        assert name in self.time_stat
        self.time_stat[name] += value

    def update_query_stat(self, name, value=1):
        assert name in self.query_stat
        if self.query_stat[name] < value:
            self.query_stat[name] = value
            return True
        return False

    def check_query(self, solver, formulae=None, timeout=None):
        self.print_query(solver, "last", "", formulae, False)
        if timeout == None:
            timeout = self.qf_fallback_timeout
        solver.set_timeout(timeout)
        try:
            res = solver.solve() if formulae == None else solver.solve(formulae)
            self.last_solver = solver
        except SolverReturnedUnknownResultError:
            if self.qf_fallback_timeout == 0:
                self.print_query(solver, "last", "", formulae, True)
                print("Error in solver result.")
                print("Z3 reason for unknown: %s" % solver.reason_unknown())
#                 assert(0)
            bp, assertions, n = solver.export_assertions()
#             print("backtrack points #%d:\n%s" % (len(bp), bp))
#             print("assertions #%d:\n%s" % (len(assertions), assertions))
#             print("named assertions #%d:" % (len(n)))
#             for i in n:
#                 print("\t", i, " of type %s" % type(i))

            new_solver = self.init_solver(1)
            for i in assertions:
                if isinstance(i, tuple):
                    new_solver.add_assertion(i[2], i[1])
                else:
                    new_solver.add_assertion(i)
            
            if len(self.system._fin2sort) != 0:
                timeout = 0
                print("\t(trying fresh solver)")
            else:
                print("\t(trying qf)")
            new_solver.set_timeout(timeout)
            try:
                res = new_solver.solve() if formulae == None else new_solver.solve(formulae)
                self.last_solver = new_solver
                print("\t(faster)")
            except SolverReturnedUnknownResultError:
                if self.qf_fallback_timeout == 0:
                    self.print_query(new_solver, "last2", "", formulae, True)
                    print("Error in solver result (attempt #2).")
                    print("Z3 reason for unknown (attempt #2): %s" % new_solver.reason_unknown())
                    assert(0)
                print("\t(failed with timeout: %ds)" % (timeout/1000))
                timeout = 3*timeout
                return self.check_query(solver, formulae, timeout)

#                 solver.set_timeout(0)
#                 res = solver.solve() if formulae == None else solver.solve(formulae)
#                 self.last_solver = solver

#         if (len(n) > 0) and not res:
#            print("core: %s" % self.last_solver.get_unsat_core())
#            assert(0)
#         assert(0)
        return res

#     def inf2fin(self, f):
# #         if f in self.cache_inf2fin:
# #             return self.cache_inf2fin[f]
# #         else:
# #             ff = f.fsubstitute(self.system._inf2fin)
# #             self.cache_inf2fin[f] = ff
# #             return ff
# #         ff = f.fsubstitute()
#         ff = f
#         return ff

#     def cardinality_constraint(self, s):
#         s_type = s.symbol_type()
#         ret = s_type
#         if s_type.is_function_type():
#             ret = s_type.return_type
#         constraint = TRUE()
#         if ret in self.system._inf2fin:
#             args = []
#             if s_type.is_function_type():
#                 i = 0
#                 for paramt in s_type.param_types:
#                     i += 1
#                     paramt_name = str(i) + ":" + str(paramt) 
#                     args.append(Symbol(paramt_name, paramt))
#             lhs = Function(s, args)
#             vals = self.system._inf2fin[ret]
#             disjunct = []
#             for v in vals:
#                 eq = EqualsOrIff(lhs, v)
#                 disjunct.append(eq)
#             constraint = ForAll(args, Or(disjunct))
# #             print("[card. constraint] %s: %s" % (s, constraint))
#         return constraint
    
#     def cardinality_constaints(self, varset):
#         constraints = []
# #         for s in varset:
#         for s in self.system.curr._vars:
#             c = self.cardinality_constraint(s)
#             if c != TRUE():
#                 constraints.append(c)
#         for tt, vals in self.system._inf2fin.items():
#             for i in range(len(vals) - 1):
#                 for j in range(i+1, len(vals)):
#                     if i != j:
#                         deq = Not(EqualsOrIff(vals[i], vals[j]))
#                         constraints.append(deq)
# #                         print(deq)
#         return constraints
# #         res = And(constraints)
#         return res

#     def symmetry_cube_old(self, cube):
#         cvars = cube.get_free_variables()
#         subs = dict()
# 
#         inf2qvar = dict()
#         for v in cvars:
#             inf = v.symbol_type()
#             if inf in self.system._inf2qvar:
#                 qvar = []
#                 if inf in inf2qvar:
#                     qvar = inf2qvar[inf]
#                 idx = len(qvar)
#                 qv = self.system._inf2qvar[inf][idx]
#                 qvar.append(qv)
#                 inf2qvar[inf] = qvar
#                 subs[v] = qv
#                 
#         antecedent = []
#         qvars = []
#         for inf, qvar in inf2qvar.items():
#             for i in range(len(qvar) - 1):
#                 qvi = qvar[i]
#                 qvars.append(qvi)
#                 for j in range(i+1, len(qvar)):
#                     if i != j:
#                         deq = Not(EqualsOrIff(qvi, qvar[j]))
#                         antecedent.append(deq)
# #                         print("adding: %s" % deq)
#             qvars.append(qvar[-1])
#         
#         cubeSym = cube
#         if len(antecedent) != 0:
#             cubeSym = And(And(antecedent), cubeSym)
#         cubeSym = cubeSym.substitute(subs)
#         cubeSym = Exists(qvars, cubeSym)
# #         print("fclause: %s" % cube)
# #         print("clause: %s" % cubeSym)
# #         assert(0)
#         return cubeSym
    
    def print_fullsorts(self, fullsorts):
        if len(fullsorts) != 0:
            print("(fullsorts)")
            for enumsort, qvar in fullsorts:
                print("\t%s -> %s" % (str(enumsort), pretty_print_set(qvar)))
    
    def reduce_antecedent2(self, cubeSym, qvars, enum2qvar, fIdx):
        antecedent = dict()
        
#         print(cubeSet)
        formulae = [And(cubeSym)]
        
        sym2ant = {}
        ant2sym = {}
        idx = 0
        prefix = "_p$"
        assumptions = []
        for k, v in enum2qvar.items():
            ev = self.system._enumsorts[k]
            if len(v) > 1:
                for varIdx, qvar in enumerate(v):
                    idx += 1
                    name = prefix + str(idx)
                    sym = Symbol(name)
                    sym2ant[sym] = qvar
                    ant2sym[qvar] = sym
                    
                    rhs = ev[varIdx]
                    eq = EqualsOrIff(qvar, rhs)
                    s2a = Implies(sym, eq)
                    formulae.append(s2a)
                    assumptions.append(sym)
        
        origSz = len(assumptions)
#         print("# ants = %d" % origSz)
        if origSz == 0:
            return antecedent, 0, set()
        
        print("(antecedent reduction)")
        assumptions = sorted(assumptions, key=lambda v: str(v))

#         print("# assumptions: %d" % len(assumptions))
#         for f in assumptions:
#             print("assumptions: %s -> %s" % (str(f), str(sym2ant[f])))
        
        formula = And(formulae)
        
        solver = self.get_framesolver(fIdx)
        self.qtype = "ant"
        
        solver.push()
        solver.add_assertion(formula)
        
        solver.push()
        solver.reset_named_assertions()
        for i in assumptions:
            solver.add_assertion(i, "assume" + str(i))

#         print("f: %s" % formula.serialize())
#         print("# assumptions: %d" % len(assumptions))
#         for f in assumptions:
#             print("assume: %s -> %s" % (str(f), str(sym2ant[f])))
        
        result = self.solve_formula(solver, TRUE(), True)
        self.update_stat("antecedent-scalls", 1)
        assert(not result)
        
        self.update_stat("unsat-core")
        core = list(self.last_solver.get_unsat_core())
        self.update_stat("sz-unsat-core-sum", len(core))
        solver.pop()
        
        required = set()
        assumptions = core
        
#         for f in solver.assertions:
#             print("assertion: %s" % f.serialize())
        while len(assumptions) != 0:
            if self.random > 2:
                random.shuffle(assumptions)
            
            curr = assumptions.pop()
            if self.use_z3_minimize:
                required.add(curr)
                continue
                
            solver.push()
            solver.reset_named_assertions()
            for i in assumptions:
                solver.add_assertion(i, "assume" + str(i))
            res = self.check_query(solver)
            self.update_stat("antecedent-scalls", 1)
#                 print("curr: %s -> %s" % (curr, res))
#                 named = self.solver.named_assertions
#                 print("named: #%d : %s" % (len(named), named))
            if res:
                solver.pop()
                required.add(curr)
                solver.add_assertion(curr)
            else:
                tmpCore = list(self.last_solver.get_unsat_core())
                solver.pop()
                for i in assumptions:
                    if i not in tmpCore:
                        assumptions.remove(i)
                        
        solver.reset_named_assertions()
        solver.pop()
        newSz = len(required)
        
        self.update_stat("sz-unsat-min-sum", len(required))
        self.update_stat("antecedent-reduction-sum", origSz-newSz)
        self.update_stat("antecedent-total-sum", origSz)
        self.update_stat("antecedent-calls", 1)
        
        reduceSz = origSz - newSz
        if (reduceSz != 0):
            self.update_stat("antecedent-calls-reduced", 1)
            print(time_str(), "antecedent: %d -> %d (reduced)" % (origSz, newSz))
        else:
            print(time_str(), "antecedent: %d -> %d" % (origSz, newSz))
        
#         print("# required: %d" % len(required))
#         for f in required:
#             print("required: %s -> %s" % (str(f), str(sym2ant[f])))
        
        for k, v in sym2ant.items():
            if k not in required:
                print("\tremoved: %s" % pretty_serialize(v))
        
        coreSetVar = set()
        for i in required:
            coreSetVar.add(sym2ant[i])
        
        for enumsort, qvar in enum2qvar.items():
            for i in range(len(qvar) - 1):
                qvi = qvar[i]
                if qvi in coreSetVar:
                    for j in range(i+1, len(qvar)):
                        if i != j:
                            qvj = qvar[j]
                            if qvj in coreSetVar:
                                deq = Not(EqualsOrIff(qvi, qvj))
                                if enumsort not in antecedent:
                                    antecedent[enumsort] = []
                                antecedent[enumsort].append(deq)
#         print(antecedent)
        return antecedent, reduceSz, coreSetVar
    

    def find_required_conditions(self, solver, formula, assumptions):
        origSz = len(assumptions)
        self.qtype = "ant"
        
#         print("# assumptions: %d" % len(assumptions))
#         for f in assumptions:
#             print("assumptions: %s -> %s" % (str(f), str(sym2ant[f])))
        
        solver.push()
        solver.add_assertion(formula)
        
        solver.push()
        solver.reset_named_assertions()
        for i in assumptions:
            solver.add_assertion(i, "assume" + str(i))

        result = self.solve_formula(solver, TRUE(), True)
        self.update_stat("antecedent-scalls", 1)
        if result:
            solver.pop()
            solver.pop()
            return result, None
        
        assert(not result)
        self.update_stat("unsat-core")
        core = list(self.last_solver.get_unsat_core())
        self.update_stat("sz-unsat-core-sum", len(core))
        solver.pop()
        
        required = set()
        assumptions = core
        
#         for f in solver.assertions:
#             print("assertion: %s" % f.serialize())
        while len(assumptions) != 0:
            if self.random > 2:
                random.shuffle(assumptions)
            
            curr = assumptions.pop()
            if self.use_z3_minimize:
                required.add(curr)
                continue
                
            solver.push()
            solver.reset_named_assertions()
            for i in assumptions:
                solver.add_assertion(i, "assume" + str(i))
            res = self.check_query(solver)
            self.update_stat("antecedent-scalls", 1)
#                 print("curr: %s -> %s" % (curr, res))
#                 named = self.solver.named_assertions
#                 print("named: #%d : %s" % (len(named), named))
            if res:
                solver.pop()
                required.add(curr)
                solver.add_assertion(curr)
            else:
                tmpCore = list(self.last_solver.get_unsat_core())
                solver.pop()
                for i in assumptions:
                    if i not in tmpCore:
                        assumptions.remove(i)
                        
        solver.reset_named_assertions()
        solver.pop()
        newSz = len(required)
        
        self.update_stat("sz-unsat-min-sum", len(required))
        self.update_stat("antecedent-reduction-sum", origSz-newSz)
        self.update_stat("antecedent-total-sum", origSz)
        self.update_stat("antecedent-calls", 1)
        
        reduceSz = origSz - newSz
        if (reduceSz != 0):
            self.update_stat("antecedent-calls-reduced", 1)
            print(time_str(), "antecedent: %d -> %d (reduced)" % (origSz, newSz))
        else:
            print(time_str(), "antecedent: %d -> %d" % (origSz, newSz))
        
        print("# required: %d" % len(required))
        for f in required:
            print("required: %s" % pretty_serialize(f))
        return False, required

    def boost_ordered(self, cubeSet, antecedent, qvars, fIdx):
        cubeNew = And(cubeSet)
        consts = cubeNew.get_enum_constants()
        antConditions = []
        for v in antecedent.values():
            for c in v:
                antConditions.append(c)
        antCond = And(antConditions)

#         print("(boosting ordered sorts)")
        for s, le in self.system._ordered_sorts.items():
            allConsts = self.system._enumsorts[s]
            self.system._enumsorts[s]
            presentConsts = consts.intersection(allConsts)
            if len(presentConsts) == 0:
                continue
            
            print("(boosting ordered sort: %s)" % s)
            print("(ordered consts: %s)" % (pretty_print_set(presentConsts)))
            subs = {}
            vars2idx = {}
            idx2var = []
            allVars = self.system._enum2qvar[s]
            for idx, c in enumerate(allConsts):
                if c in presentConsts:
                    qv = allVars[idx]
                    subs[c] = qv
                    vars2idx[qv] = idx
                    idx2var.append(qv)
                    qvars.add(qv)
                else:
                    idx2var.append(None)
            cubeNew = cubeNew.simple_substitute(subs)
            cubeSetNew = flatten_cube(cubeNew)
            print("(cube: new)")
            for c in cubeSetNew:
                print("\t%s" % pretty_serialize(c))
                
            conditionsEq = []
            for i in range(0,len(idx2var)-1):
                qvi = idx2var[i]
                if qvi == None:
                    continue
                for j in range(i+1,len(idx2var)):
                    qvj = idx2var[j]
                    if qvj == None:
                        continue
                    assert(qvi != qvj)
                    cond = Not(EqualsOrIff(qvi, qvj))
                    conditionsEq.append(cond)
            conditionsLe = []
            for i in range(0,len(idx2var)-1):
                qvi = idx2var[i]
                if qvi == None:
                    continue
                qvj = None
                for j in range(i+1,len(idx2var)):
                    qvj = idx2var[j]
                    if qvj != None:
                        break
                if qvj == None:
                    continue
                assert(qvi != qvj)
                cond = Not(Function(le, [qvj, qvi]))
                conditionsLe.append(cond)
            conditionsEdge = []
            if s in self.system._ordered_min:
                rhs = self.system._ordered_min[s]
                for i in range(0,len(idx2var)):
                    qvi = idx2var[i]
                    if qvi == None:
                        continue
                    cond = EqualsOrIff(qvi, rhs)
                    if i != 0:
                        cond = Not(cond)
                        conditionsEdge.append(cond)
                    else:
                        conditionsEdge.append(cond)
            if s in self.system._ordered_max:
                rhs = self.system._ordered_max[s]
                for i in range(0,len(idx2var)):
                    qvi = idx2var[i]
                    if qvi == None:
                        continue
                    cond = EqualsOrIff(qvi, rhs)
                    if i != (len(idx2var)-1):
                        cond = Not(cond)
                        conditionsEdge.append(cond)
                    else:
                        conditionsEdge.append(cond)
            conditionsFull = []
            for i in range(0,len(idx2var)-1):
                qvi = allVars[i]
                qvj = allVars[i+1]
                assert(qvi != None)
                assert(qvj != None)
                assert(qvi != qvj)
                cond = Not(Function(le, [qvj, qvi]))
                conditionsFull.append(cond)
            print("(conditions: eq)")
            for c in conditionsEq:
                print("\t%s" % pretty_serialize(c))
            print("(conditions: le)")
            for c in conditionsLe:
                print("\t%s" % pretty_serialize(c))
            print("(conditions: edge)")
            for c in conditionsEdge:
                print("\t%s" % pretty_serialize(c))
            print("(conditions: full)")
            for c in conditionsFull:
                print("\t%s" % pretty_serialize(c))
                
            solver = self.get_framesolver(fIdx)
            result = True
            conditions = []
#             conditions.extend(conditionsEq)
#             conditions.extend(conditionsLe)
#             conditions.extend(conditionsEdge)
#             conditions.extend(conditionsFull)
            result, required = self.find_required_conditions(solver, And(antCond, cubeNew), conditions)
            if (not result):
                print("(conditions: none are sufficient)")
#             assert(not result)

            if result and len(conditionsEq) != 0:
#                 conditions.extend(conditionsEq)
                conditions = conditionsEq
                result, required = self.find_required_conditions(solver, And(antCond, cubeNew), conditions)
                if (not result):
                    print("(conditions: eq are sufficient)")
                    
            if result and len(conditionsLe) != 0:
#                 conditions.extend(conditionsLe)
                conditions = conditionsLe
                result, required = self.find_required_conditions(solver, And(antCond, cubeNew), conditions)
                if (not result):
                    print("(conditions: le are sufficient)")
                    
            if result and len(conditionsEdge) != 0:
#                 conditions.extend(conditionsEdge)
                conditions = conditionsEdge
                result, required = self.find_required_conditions(solver, And(antCond, cubeNew), conditions)
                if (not result):
                    print("(conditions: edge are sufficient)")
                    
            if result and len(conditionsFull) != 0:
#                 conditions.extend(conditionsFull)
                conditions = conditionsFull
                result, required = self.find_required_conditions(solver, And(antCond, cubeNew), conditions)
                if (not result):
                    print("(conditions: full are sufficient)")
                
            if result:
                print("(conditions: full are insufficient)")
                assert(0)
                
            for c in required:
                cubeSetNew.add(c)
                cvars = c.get_free_variables()
                cqvars = cvars.intersection(allVars)
                for v in cqvars:
                    if v not in qvars:
                        qvars.add(v)
                        print("\tadding qv: %s" % pretty_serialize(v))
                
            cubeNew = And(cubeSetNew)
        cubeSetNew = flatten_cube(cubeNew)
        return cubeSetNew
        
    def propagate_eq(self, cubeSet, antecedent, ivars, qvars, fullsorts):
        eqMap = dict()
        tmpSet = set()
#         incompleteSorts = set()
        for c in cubeSet:
            if c.node_type() == op.EQUALS:
                lhs = c.arg(0)
                rhs = c.arg(1)
                if not rhs.is_symbol():
                    lhs, rhs = rhs, lhs
                if rhs.is_symbol:
                    if (common.gopts.const > 1) or (not lhs.is_function_application()):
                        rhst = rhs.symbol_type()
                        if rhst.is_enum_type() and rhs not in eqMap:
                            eqMap[rhs] = lhs
                            qvars.discard(rhs)
#                             incompleteSorts.add(rhst)
                            continue
                        elif rhs in ivars and rhs not in eqMap:
                            eqMap[rhs] = lhs
                            qvars.discard(rhs)
                            continue
                        
            tmpSet.add(c)
         
        if len(eqMap) != 0:
            changed = True
            while changed:
                changed = False
                for l, r in eqMap.items():
                    rNew = r.simple_substitute(eqMap)
                    if (rNew != r):
                        changed = True
                    eqMap[l] = rNew
            
            print("(eq map)")
            for l, r in eqMap.items():
                print("\t%s -> %s" % (pretty_serialize(l), pretty_serialize(r)))
            
            cubeSetNew = set()
            for c in tmpSet:
                c_new = c.simple_substitute(eqMap)
                cubeSetNew.add(c_new)
                
            antecedentNew = dict()
            for enumsort, qvar in antecedent.items():
                vNew = []
                for i in qvar:
                    i_new = i.simple_substitute(eqMap)
#                     if (i_new != i):
#                         cubeSetNew.add(i_new)
#                     else:
#                         vNew.append(i_new)
                    vNew.append(i_new)
                antecedentNew[enumsort] = vNew
            
            fullsortsNew = []
            for fs in fullsorts:
#                 if fs[0] not in incompleteSorts:
#                     fullsortsNew.append(fs)
                rhs = []
                for v in fs[1]:
                    if v in eqMap:
                        v = eqMap[v]
                    rhs.append(v)
                fullsortsNew.append([fs[0], rhs])
                
            print("(cube eq)")
            for c in cubeSetNew:
                print("\t%s" % pretty_serialize(c))
            
            print("(qvars eq)")
            for c in qvars:
                print("\t%s" % pretty_serialize(c))
            
            print("(antecedent eq)")
            for enumsort, qvar in antecedentNew.items():
                print("\t%s" % enumsort)
                for c in qvar:
                    print("\t-> %s" % pretty_serialize(c))
            
            self.print_fullsorts(fullsortsNew)
            
            removedVars = set(eqMap.keys())
            for c in cubeSetNew:
                fv = c.get_free_variables()
                fv_removed = fv.intersection(removedVars)
                if len(fv_removed) != 0:
                    print("Error: found bound variables as free in %s" % pretty_serialize(c))
                    for c in fv_removed:
                        print("\t%s" % pretty_serialize(c))
                    assert(0)
            
            return eqMap, cubeSetNew, antecedentNew, fullsortsNew
        else:
            return eqMap, cubeSet, antecedent, fullsorts
        
    def propagate_eq_post(self, cube):
        cubeEq = cube

        qvars = set()
        qvarsNew = set()
        v = cube
        if v.is_exists():
            vq = v.quantifier_vars()
            for i in vq:
                qvars.add(i)
                qvarsNew.add(i)
            v = v.args()[0]
        cubeSet = flatten_and(v)
        
        eqMap = dict()
        tmpSet = set()
        for c in cubeSet:
            if c.node_type() == op.EQUALS:
                lhs = c.arg(0)
                rhs = c.arg(1)
                if (not rhs.is_symbol()) or (lhs in qvars):
                    lhs, rhs = rhs, lhs
                if rhs.is_symbol and rhs in qvars:
                    if rhs not in eqMap:
                        eqMap[rhs] = lhs
                        qvarsNew.discard(rhs)
                        continue
            tmpSet.add(c)
            
        if len(eqMap) != 0:
            changed = True
            while changed:
                changed = False
                for l, r in eqMap.items():
                    rNew = r.simple_substitute(eqMap)
                    if (rNew != r):
                        changed = True
                    eqMap[l] = rNew

            print("(eq map: post)")
            for l, r in eqMap.items():
                print("\t%s -> %s" % (pretty_serialize(l), pretty_serialize(r)))
            
            cubeSetNew = set()
            for c in tmpSet:
                c_new = c.simple_substitute(eqMap)
                cubeSetNew.add(c_new)
                
            print("(cube eq: post)")
            for c in cubeSetNew:
                print("\t%s" % pretty_serialize(c))
            
            print("(qvars eq: post)")
            for c in qvarsNew:
                print("\t%s" % pretty_serialize(c))
            
            removedVars = set(eqMap.keys())
            for c in cubeSetNew:
                fv = c.get_free_variables()
                fv_removed = fv.intersection(removedVars)
                if len(fv_removed) != 0:
                    print("Error: found bound variables as free in %s" % pretty_serialize(c))
                    for c in fv_removed:
                        print("\t%s" % pretty_serialize(c))
                    assert(0)
            
            cubeEq = And(cubeSetNew)
            if len(qvarsNew) != 0:
                cubeEq = Exists(qvarsNew, cubeEq)
        return cubeEq
        
    def extend_cube(self, fIdx, cubeA):
#         print("Trying extending: %s" % cubeA.serialize())
        prospectives = set()
        atomsA = cubeA.get_atoms()
        for i in range(fIdx, len(self.frames)):
            for cubeB in self.frames[i]:
                if cubeB == cubeA:
                    continue
                atomsB = cubeB.get_atoms()
                if len(atomsA) != len(atomsB):
                    continue
                atomsBnA = atomsB.difference(atomsA)
                if len(atomsBnA) != 1:
                    continue
                atomsAnB = atomsA.difference(atomsB)
                if len(atomsAnB) != 1:
                    continue
#                 print("Possibly similar:")
#                 pretty_print(cubeA)
#                 pretty_print(cubeB)
                aA = next(iter(atomsAnB))
                aB = next(iter(atomsBnA))
                subs = {}
                subs[aA] = And(aA, aB)
                newA = cubeA.simple_substitute(subs)
                assert(newA != cubeA)
                prospectives.add(newA)
        
        added = 0
        solver = self.get_framesolver(fIdx-1)
        for corepre in prospectives:
            core = pre2nex(self, corepre)
            core_formula = self.get_formula_qf(core)
            corepre_formula = self.get_formula_qf(corepre)
            isGlobal = self.check_if_global(core_formula, corepre_formula)
            print(time_str(), "is global clause? %s" % ("Yes" if isGlobal else "No"))
            if isGlobal:
                label = "global" + str(iterationCount) + "_" + str(len(self.globals)+1)
                self.globals[Not(corepre)] = label
                self.learn_cube(len(self.frames) - 1, corepre, corepre_formula)
                added += 1
            else:
                res = self.solve_formula(solver, core_formula)
                if not res:
                    self.learn_cube(fIdx, corepre, corepre_formula)
                    added += 1
        if added != 0:
            print("Found #%d extensions" % added)
        return added != 0
    
    def fin2inf(self, f):
        print("TODO")
        assert(0)
        return f

    def get_qf_form(self, f):
#         qf_f = self.qesolver.eliminate_quantifiers(f).simplify()
        qf_f = self.qesolver.eliminate_quantifiers(f)
#         print("quantified: \n%s", f.serialize())
#         print("quantifier-free: \n%s", qf.serialize())
        return qf_f
    
    def new_solver(self):
        s = self.init_solver(self.qf)
        formulae = []
        formulae.append(axiom_formula(self))
        formulae.append(trel_formula(self))
        assert_permanent(s, formulae)
        return s
    
    def add_init_frame(self):
        assert(len(self.frames) == 0)
        cubes = set()
        fs = self.new_solver()
        cubes.add(Not(init_formula(self)))
        formula = init_formula(self)
        fs.add_assertion(formula)
        self.frames.append(cubes)
        self.framesolver.append(fs)
        self.frame_summary()
    
    def add_frame(self):
        print(time_str(), "\nAdding frame %d..." % (len(self.frames)))
        fs = self.new_solver()
        fs.add_assertion(prop_formula(self))
        self.frames.append(set())
        self.framesolver.append(fs)
        if common.gopts.verbosity == 0:
            return
        print("\n", file=sys.stderr, end="")
        
    def check_invariant_full(self, inv_set):
        self.qtype = "inv"
        print(time_str(), "Finite sorts: #%d" % len(self.system._sort2fin))
        for tt, vals in self.system._sort2fin.items():
            print("\t%s -> %s -> %s" % (tt, vals, self.system._enumsorts[vals]))
        
        print("Faxioms: #%d" % len(self._faxioms))
        for cl in self._faxioms:
            print("\t%s" % cl.serialize())
            
        result = False

        inv = And(inv_set)
        
        print("Init /\ !Inv", end =' ')
        result |= self.solve_formula(self.solver, And(init_formula(self), Not(And(inv))))
        if result:
            for cl in inv_set:
                res = self.solve_formula(self.solver, And(init_formula(self), Not(cl)))
                if res:
                    model = self.last_solver.get_model()
                    model.print_model()
                    print("cl: %s" % cl.serialize())
                    print("init: %s" % init_formula(self).serialize())
                    assert(0)
        
        print("Inv /\ !P", end =' ')
        result |= self.solve_formula(self.solver, And(inv, Not(prop_formula(self))))
        
        prop_nex = pre2nex(self, prop_formula(self))
        print("Inv /\ T /\ !P+", end =' ')
        result |= self.solve_formula(self.solver, And(inv, Not(prop_nex)))
        
        inv_nex = pre2nex(self, inv)
        print("Inv /\ T /\ !Inv+", end =' ')
        result |= self.solve_formula(self.solver, And(inv, Not(inv_nex)))
        
        return result
#         assert (not result)
        
    def check_init_implies_clause(self, inv, quiet=False):
        result = self.solve_formula(self.solver, And(init_formula(self), Not(And(inv))), quiet)
        return result
        
    def check_init_T_implies_clause(self, inv):
        inv_nex = pre2nex(self, inv)
        result = self.solve_formula(self.solver, And(init_formula(self), Not(inv_nex)))
        return result
        
    def print_init_formula(self, inv, quiet=False):
        if not quiet:
            print("Printing Init /\ !Inv:")
        s = self.init_solver(self.qf)
        formulae = []
        formulae.append(init_formula(self))
        formulae.append(Not(And(inv)))
        formulae.append(axiom_formula(self))
        s.add_assertion(And(formulae))
        self.print_formula(s, And(formulae), "init")
    
    def print_induct_formula(self, inv, quiet=False):
        if not quiet:
            print("Printing Inv /\ T /\ !Inv+:")
        inv_nex = pre2nex(self, inv)
        s = self.init_solver(self.qf)
        formulae = []
        formulae.append(inv)
        formulae.append(Not(inv_nex))
        formulae.append(trel_formula(self))
        formulae.append(axiom_formula(self))
        s.add_assertion(And(formulae))
        self.print_formula(s, And(formulae), "induct")
    
    def check_init_implies_invariant(self, inv_set_l, quiet=False):
        count = 0
        inv_fail = set()
        if not quiet:
            print("Checking Init /\ !Inv:")
        for label, i in inv_set_l:
            count += 1
            if not quiet:
                print("\t#%d %s" % (count, label), end =' ')
                if (i == prop_formula(self) or i in self.system.curr._prop):
                    print(" (property)", end =' ')
            result = self.check_init_implies_clause(i, quiet)
            if result:
                inv_fail.add(i)
        if not quiet:
            if len(inv_fail) == 0:
                print("\tInit /\ !Inv: passed")
            else:
                print("\tInit /\ !Inv: %d failed" % len(inv_fail))
        return inv_fail
        
    def check_init_T_implies_invariant(self, inv_set_l):
        count = 0
        inv_fail = set()
        print("Checking Init /\ T /\ !Inv+:")
        for label, i in inv_set_l:
            count += 1
            print("\t#%d %s" % (count, label), end =' ')
            result = self.check_init_T_implies_clause(i)
            if result:
                inv_fail.add(i)
        if len(inv_fail) == 0:
            print("\tInit /\ T /\ !Inv+: passed")
        else:
            print("\tInit /\ T /\ !Inv+: %d failed" % len(inv_fail))
        return inv_fail
        
    def check_self_inductive_clause(self, inv):
        inv_nex = pre2nex(self, inv)
        result = self.solve_formula(self.solver, And(inv, Not(inv_nex)))
        return result
        
    def check_self_inductive_invariant(self, inv_set):
        nFailed = 0
        count = 0
        print("Checking Inv /\ T /\ !Inv+:")
        for i in inv_set:
            count += 1
            print("\t#%d" % count, end =' ')
            result = self.check_self_inductive_clause(i)
            if result:
                nFailed += 1
        if nFailed == 0:
            print("\tInv /\ T /\ !Inv+: passed")
        else:
            print("\tInv /\ T /\ !Inv+: %d failed" % nFailed)
        return nFailed
        
    def check_self_tobad_clause(self, bad, inv):
        result = self.solve_formula(self.solver, And(prop_formula(self), inv, bad))
        return result
        
    def check_self_tobad_invariant(self, inv_set):
        bad = Not(pre2nex(self, prop_formula(self)))
        nFailed = 0
        count = 0
        print("Checking Inv /\ P /\ T /\ !P+:")
        for i in inv_set:
            count += 1
            print("\t#%d" % count, end =' ')
            result = self.check_self_tobad_clause(bad, i)
            if result:
                nFailed += 1
        if nFailed == 0:
            print("\tInv /\ P /\ T /\ !P+: passed")
        else:
            print("\tInv /\ P /\ T /\ !P+: %d failed" % nFailed)
        return nFailed
        
    def check_inductive_clause(self, inv_all, inv, quiet=False):
        inv_nex = pre2nex(self, inv)
        result = self.solve_formula(self.solver, And(inv_all, Not(inv_nex)), quiet)
        return result
        
    def check_inductive_invariant(self, inv_set_l, inv, quiet=False):
        inv_all = inv
        count = 0
        inv_fail = set()
        if not quiet:
            print("Checking Inv_all /\ T /\ !Inv+:")
        for label, i in inv_set_l:
            count += 1
            if not quiet:
                print("\t#%d %s" % (count, label), end =' ')
                if (i == prop_formula(self) or i in self.system.curr._prop):
                    print(" (property)", end =' ')
            result = self.check_inductive_clause(inv_all, i, quiet)
            if result:
                inv_fail.add(i)
        if not quiet:
            if len(inv_fail) == 0:
                print("\tInv_all /\ T /\ !Inv+: passed")
            else:
                print("\tInv_all /\ T /\ !Inv+: %d failed" % len(inv_fail))
        return inv_fail
        
    def check_invariant(self, inv_set_orig, quiet=False):
        self.qtype = "inv"
        if not quiet:
            print(time_str(), "-------------------------------------------------")
            pretty_print_inv(inv_set_orig, "Invariant")

        nFailed = 0
        
        inv_set = set()
        inv_set_l = set()
        for label, cl in inv_set_orig:
            cl_formula = self.get_formula_qf(cl)
            inv_set.add(cl_formula)
            inv_set_l.add((label, cl_formula))

        inv = And(inv_set)
        
        if not quiet:
            print()
            print("Inv_all /\ !P", end =' ')
        result = self.solve_formula(self.solver, And(inv, Not(prop_formula(self))), quiet)
        nFailed += (1 if result else 0)
        
        prop_nex = pre2nex(self, prop_formula(self))
        if not quiet:
            print("Inv_all /\ T /\ !P+", end =' ')
        result = self.solve_formula(self.solver, And(inv, Not(prop_nex)), quiet)
        nFailed += (1 if result else 0)
        
        init_fail = self.check_init_implies_invariant(inv_set_l, quiet)
        nFailed += len(init_fail)
        
        ind_fail = self.check_inductive_invariant(inv_set_l, inv, quiet)
        nFailed += len(ind_fail)
        
#         self.check_self_inductive_invariant(inv_set)
#         self.check_self_tobad_invariant(inv_set)
        
        if not quiet:
            print()
            print("Finite sorts: #%d" % len(self.system._sort2fin))
            for tt, vals in self.system._sort2fin.items():
                print("\t%s -> %s -> %s" % (tt, vals, self.system._enumsorts[vals]))
                
            print("\nInvariant is %sa proof certificate" % ("" if (nFailed == 0) else "not "))
            print(time_str(), "-------------------------------------------------")
        sys.stdout.flush()
        return nFailed

    def check_and_prune_invariant(self, inv_set_l_orig, iter):
        inv_set_l = inv_set_l_orig
#         inv_set_l = set()
#         for label, cl in inv_set_l_orig:
#             clNew = self.system.replaceDefinitions(cl)
#             inv_set_l.add((label, clNew))
        
        self.qtype = "inv"
        push_time()
        print(time_str(), "-------------------------------------------------")
        pretty_print_inv(inv_set_l, "Invariant")
        
        nFailed = 0
        
        inv_set = set()
        for _, cl in inv_set_l:
            inv_set.add(cl)

        inv_all = And(inv_set)
        self.print_init_formula(inv_all)
        self.print_induct_formula(inv_all)
        
        init_fail = self.check_init_implies_invariant(inv_set_l)
        nFailed += len(init_fail)
        
        ind_fail = self.check_inductive_invariant(inv_set_l, inv_all)
        nFailed += len(ind_fail)
        
        inv_pruned = inv_set.copy()
        inv_pruned = inv_pruned.difference(init_fail)
        inv_pruned = inv_pruned.difference(ind_fail)
        
        inv_pruned_l = set()
        failedProp = False
        for label, cl in inv_set_l:
            if cl in inv_pruned:
                inv_pruned_l.add((label, cl))
            elif (cl == prop_formula(self) or cl in self.system.curr._prop):
                inv_pruned_l.add((label, cl))
                failedProp = True
        
        print()
        print("Finite sorts: #%d" % len(self.system._sort2fin))
        for tt, vals in self.system._sort2fin.items():
            print("\t%s -> %s -> %s" % (tt, vals, self.system._enumsorts[vals]))
        
        print("\nGeneralized: %d -> %d" % (len(inv_set_l), len(inv_pruned_l)))
        if (nFailed == 0):
            print("All generalizable clauses")
            inv = And(inv_set)
            
            print()
            print("Inv_all /\ !P", end =' ')
            result = self.solve_formula(self.solver, And(inv, Not(prop_formula(self))))
            nFailed += (1 if result else 0)
            
            prop_nex = pre2nex(self, prop_formula(self))
            print("Inv_all /\ T /\ !P+", end =' ')
            result = self.solve_formula(self.solver, And(inv, Not(prop_nex)))
            nFailed += (1 if result else 0)
            
            print("\nInvariant is %sa proof certificate" % ("" if (nFailed == 0) else "not "))
        else:
            print("Found ungeneralizable clauses")
            if iter == 0:
                if common.gopts.verbosity > 0:
                    eprint(time_str(), "\t(%s elimination required)" % ("unbounded" if (len(self.system._sort2fin) == 0) else "finite"))
                    print(time_str(), "\t(%s elimination required)" % ("unbounded" if (len(self.system._sort2fin) == 0) else "finite"))
#             propF = prop_formula(self)
#             if (not failedProp) and propF not in init_fail and propF not in ind_fail:
#                 nFailed, inv_pruned_l = self.check_and_prune_invariant(inv_pruned_l, iter+1)
            if (not failedProp):
                nFailed, inv_pruned_l = self.check_and_prune_invariant(inv_pruned_l, iter+1)
            else:
                if common.gopts.verbosity > 0:
                    print("Property ungeneralizable")
                if iter == 0:
#                     inv_pruned_l.add(("prop", propF))
                    nFailed, inv_pruned_l = self.check_and_prune_invariant(inv_pruned_l, iter+1)
            
        print(time_str(), "-------------------------------------------------")
        self.update_time_stat("time-inv-check-infinite" if (len(self.system._sort2fin) == 0) else "time-inv-check-finite", pop_time())
        return nFailed, inv_pruned_l
        
    def reusable_invariant(self, inv_set_orig_l):
        inv_set = set()
        inv_set_l = set()
        prop = prop_formula(self)
        for label, v in inv_set_orig_l:
            if (v == prop) or (v in self.system.curr._prop):
                pass
            else:
                f = self.system.replaceDefinitions(v, 1)
                inv_set.add(f)
                inv_set_l.add((label, f))
        
        push_time()
        print(time_str(), "-------------------------------------------------")
        pretty_print_inv(inv_set_l, "Checking reusability of clauses")

        nFailed = 0

        init_fail = self.check_init_implies_invariant(inv_set_l)
        nFailed += len(init_fail)
        
        initT_fail = self.check_init_T_implies_invariant(inv_set_l)
        nFailed += len(initT_fail)
        
        inv_pruned = inv_set.difference(init_fail)
        inv_pruned = inv_pruned.difference(initT_fail)
        
        inv_pruned_l = set()
        for label, cl in inv_set_l:
            if cl in inv_pruned:
                inv_pruned_l.add((label, cl))
            
        print()
        print("Finite sorts: #%d" % len(self.system._sort2fin))
        for tt, vals in self.system._sort2fin.items():
            print("\t%s -> %s -> %s" % (tt, vals, self.system._enumsorts[vals]))
        print()
        print("Reusable: %d -> %d (%d + %d failed)" % (len(inv_set), len(inv_set) - nFailed, len(init_fail), len(initT_fail)))
        if nFailed == 0:
            print("All clauses reusable")
        else:
            print("Some clauses not reusable")
        print(time_str(), "-------------------------------------------------")
        self.update_time_stat("time-inv-reuse", pop_time())
        return inv_pruned_l
        
    def check_property(self, helpers=None):
        """Property Directed Reachability"""
        print("\nChecking property...\n")
        
#         atoms = get_atoms(trel_formula(self))
#         for c in atoms:
#             print("\t%s" % pretty_serialize(c))
#         assert(0)

        self.store_init_values()                
            
        cube = self.check_init_is_safe()
        if cube is not None:
            cubeV = self.get_cube_values(cube)
            self.print_cube_values(cubeV, len(self.frames)-1, None)
            
            print("--> Bug found at step 0")
            print("Explored %d frames" % len(self.frames))
            return None, None

        self.add_init_frame()
        nexbad = Not(pre2nex(self, prop_formula(self)))
        
        for cl, label in self.system.curr._helpers.items():
            self.globals[cl] = label
        self.prospectives = {}

        self.globalEnum = set()
        while True:
            push_time()
            cube = self.get_bad_state(nexbad)
            if cube is not None:
                self.update_time_stat("time-cti-bad-sat", pop_time())
                # Blocking phase of a bad state
                dest = self.get_dest_cube()
                destV = self.get_cube_values(dest)
                self.print_cube_values(destV, -1, None)

                cubeV = self.get_cube_values(cube)
                self.print_cube_values(cubeV, len(self.frames)-1, destV)
                
                if self.recursive_block(len(self.frames)-1, cube, cubeV):
                    print("--> Bug found at step %d" % (len(self.frames)))
                    print("Explored %d frames" % len(self.frames))
                    return None, None
                else:
#                     print("   [PDR] Cube blocked '%s'" % str(cube))
                    pass
            else:
                self.update_time_stat("time-cti-bad-unsat", pop_time())
                print("Frames: #%d" % len(self.frames))
                for i, frame in enumerate(self.frames):
                    print("\tF[%d]: #%d" % (i, len(frame)))
                    for cl in frame:
                        cl_qu = self.get_formula_qu(cl)
                        print("\t\t", end='')
                        pretty_print(Not(cl_qu))
                
                # Checking if the last two frames are equivalent i.e., are inductive
                converged, fidx = self.inductive()
                if converged:
                    print("Explored %d frames" % len(self.frames))
                    frameConv = self.get_frame_clauses(fidx)

                    inv_set = set()
                    for arg in frameConv:
                        arg_qu = self.get_formula_qu(arg)
                        clauses_qu = flatten_and(arg_qu)
                        for cl in clauses_qu:
                            inv_set.add(cl)
                    
                    if self.boosting == "none":
                        print(time_str(), "-------------------------------------------------")
                        pretty_print_inv_set(inv_set, "Invariant (original)")
                        inv_set2 = set()
                        for arg_qu in inv_set:
                            if arg_qu != prop_formula_orig(self):
                                print("\nclause (orig): ", end="")
                                pretty_print(arg_qu)
                                cubesOut = symmetry_cube(self, Not(arg_qu), fidx-1, False)
                                arg_qu = Not(cubesOut[0][0])
                                print("clause (sym.): ", end="")
                                pretty_print(arg_qu)
                            inv_set2.add(arg_qu)
                        inv_set = inv_set2
                    
                    prop = prop_formula_orig(self)
                    inv_set_l = set()
                    
                    propIdx = 0
                    otherIdx = 0
                    labels = set()
                    count = 0
                    for idx, cl in enumerate(inv_set):
                        label = str(idx+1)
                        if cl == prop or cl in self.system.curr._prop:
                            propIdx += 1
                            label = "prop"  + str(propIdx)
                        elif cl in self.globals:
                            label = self.globals[cl]
                        elif cl in self.system.curr._infers:
                            label = self.system.curr._infers[cl]
                        else:
                            otherIdx += 1
                            label = "other" + str(otherIdx)
                        if label in labels:
                            count += 1
                            label += "_" + str(count)
                        labels.add(label)
                        inv_set_l.add((label, cl))
                    
                    push_time()
                    nFailed = self.check_invariant(inv_set_l)
                    self.update_time_stat("time-inv-check-infinite" if (len(self.system._sort2fin) == 0) else "time-inv-check-finite", pop_time())
                    
                    if nFailed != 0:
                        print("--> Error!")
                        assert(0)
                        
                    print("--> The system is safe!")
                    return inv_set_l, None
                
                if (len(self.frames) == 2):
                    assert(len(self.frames[1]) == 0)
                    if helpers is not None and len(helpers) != 0:
                        globalC = 0
                        initC = 0
                        for label, formula in helpers:
                            cl = self.get_formula_qf(formula)
                            if self.check_clause_includes_init(label, cl):
                                if self.check_clause_inductive(label, cl):
                                    self.globals[formula] = label
                                    globalC += 1
                                elif self.check_clause_init(label, cl):
                                    self.learn_cube(len(self.frames) - 1, Not(formula), Not(cl))
                                    initC += 1
                                else:
                                    print(time_str(), "Not using %s" % label)
                            else:
                                print(time_str(), "Not using %s" % label)
                        print("Seeded %d (global: %d, init: %d) helpers out of %d" % (globalC+initC, globalC, initC, len(helpers)))
#                             else:
#                                 self.prospectives[cl] = label
                    if len(self.system.curr._infers) != 0:
                        globalC = 0
                        initC = 0
                        for formula, label in self.system.curr._infers.items():
                            cl = self.get_formula_qf(formula)
                            if self.check_clause_includes_init(label, cl):
                                if self.check_clause_inductive(label, cl):
                                    self.globals[formula] = label
                                    globalC += 1
                                elif self.check_clause_init(label, cl):
                                    self.learn_cube(len(self.frames) - 1, Not(formula), Not(cl))
                                    initC += 1
                                else:
                                    print(time_str(), "Not using %s" % label)
                            else:
                                print(time_str(), "Not using %s" % label)
                        print("Seeded %d (global: %d, init: %d) inferences out of %d" % (globalC+initC, globalC, initC, len(self.system.curr._infers)))

                if (len(self.frames) >= 2):
                    for formula in self.globals.keys():
                        cl = self.get_formula_qf(formula)
                        self.learn_cube(len(self.frames) - 1, Not(formula), Not(cl))
                    
#                             self.frames[-1].add(cl)
                
#                 if len(self.frames) > 4:
#                     print("Explored %d frames" % len(self.frames))
#                     print("--> The system is unknown!")
#                     break
        return None, None

    def get_framesolver(self, fin):
        i = fin
        if (i == -1):
            i = len(self.frames) - 1
        
        assert(i < len(self.framesolver))
        return self.framesolver[i]

    def get_frame(self, fin, addProp=True):
        i = fin
        if (i == -1):
            i = len(self.frames) - 1
        
        
        if i == 0:
            return init_formula(self)
        else:
            frame = []
            if addProp:
                frame = [prop_formula(self)]
            for j in range(i, len(self.frames)):
                for cube in self.frames[j]:
                    frame.append(Not(cube))
#             print("F[%d] = %s" % (i, And(frame).serialize()))
            return And(frame)

    def get_frame_clauses(self, fin):
        i = fin
        if (i == -1):
            i = len(self.frames) - 1
        
        frame = []
        if i == 0:
            frame.append(init_formula(self))
        else:
            frame.append(prop_formula(self))
            for j in range(i, len(self.frames)):
                for cube in self.frames[j]:
                    frame.append(Not(cube))
        return frame

    def possible_reusable_invariant(self, inv_set):
        inv_reuse = set()

        for cl in inv_set:
            if cl != prop_formula(self):
                inv_reuse.add(cl)

#         for j in range(1, len(self.frames)):
#             for cube in self.frames[j]:
#                 inv_reuse.add(Not(cube))
        return inv_reuse

    def subsume_preprocess(self, cube_formula):
        cube = self.get_formula_qu(cube_formula)
        cubeFlat = flatten_cube(cube)        
        return (cube, cubeFlat, cube_formula)

#     returns true if lhs -> rhs
    def subsumes(self, lhs, rhs, fIdx):
        lr = (lhs[0], rhs[0])
        if lr in self._subsume:
            return self._subsume[lr]
        
        self.update_stat("subsumed-calls")
        result = (len(rhs[1]) <= len(lhs[1])) and (rhs[1].issubset(lhs[1]))
        if result:
            self.update_stat("subsumed-subset")
        self._subsume[lr] = result
        if self.subsume_level == 0:
            return result

        if not result:
            lhs_var = lhs[0].get_free_variables()
            rhs_var = rhs[0].get_free_variables()
            intersect_var = rhs_var.difference(lhs_var)
            result_intersect = len(intersect_var) != 0
#             if False and result_intersect:
            if result_intersect:
                result = False
                self.update_stat("subsumed-varintersect-c")
            else:
#                 return result
                push_time()
                lhs_formula = self.get_formula_qf(lhs[0])
                rhs_formula = self.get_formula_qf(rhs[0])
                formula = And(lhs_formula, Not(rhs_formula))
                self.qtype = "sub"
                result_solv = self.solve_formula(self.solver, formula, True)
                self.update_time_stat("time-subsume-query", pop_time())
#                 print("Subsume elim-target in F[%d]: " % (fIdx), end="")
#                 pretty_print(Not(lhs[0]))
#                 print("Subsume retainer in F[%d]: " % (fIdx), end="")
#                 pretty_print(Not(rhs[0]))
                if not result_solv:
                    result = True
                    self.update_stat("subsumed-query-unsat")
#                     print("Subsuming (query) in F[%d]: " % (fIdx), end="")
#                     pretty_print(Not(lhs[0]))
                    if result_intersect:
                        self.update_stat("subsumed-varintersect-e")
#                         print("subsumed-varintersect-e")
#                         print(lhs[0])
#                         print(rhs[0])
#                         print(intersect_var)
#                         lhs_qvar = lhs[0].get_quantifier_variables()
#                         rhs_qvar = rhs[0].get_quantifier_variables()
#                         intersect_qvar = rhs_qvar.difference(lhs_qvar)
#                         print(lhs_qvar)
#                         print(rhs_qvar)
#                         print(intersect_qvar) 
                    else:
                        if result_intersect:
                            self.update_stat("subsumed-varintersect-c")
                else:
                    result = False
                    self.update_stat("subsumed-query-sat")
                    
#         else:
#             print("Subsuming (syntactic) in F[%d]: %s" % (fIdx, str(lhs[0])))
            
        self._subsume[lr] = result
        return result
    
    def subsume_frame(self, i, rhs):
        frame_new = set()
        count = 0
        for cube in self.frames[i]:
            if cube != rhs[0]:
                lhs = self.subsume_preprocess(cube)
                if not self.subsumes(lhs, rhs, i):
                    frame_new.add(cube)
                else:
                    count += 1
            else:
                self.update_stat("subsumed-eq")
                count += 1
#         if count != 0:
#             print("Subsumed #%d in F[%d]" % (count, i))
            
        self.frames[i] = frame_new

    def learn_cube(self, i, cube, cube_formula):
        rhs = self.subsume_preprocess(cube_formula)        
        push_time()
        for j in range(1, i+1):
            self.subsume_frame(j, rhs)
        self.update_time_stat("time-subsume", pop_time())

        self.frames[i].add(cube_formula)
        cl = Not(cube_formula)
        
        print(time_str(), "Learning in F[%d]: " % i, end='')
#         pretty_print(cl)
        pretty_print(Not(self.get_formula_qu(cube_formula)))
        
        for i in range(1, i+1):
            self.get_framesolver(i).add_assertion(cl)
#         print(self.frames)
        self.frame_summary()
    
    def frame_summary(self):
        if common.gopts.verbosity == 0:
            return
        fsummary = ""
        fsum = 0
        fdone = False
        for _, frame in enumerate(self.frames):
            fsum += len(frame)
            if not fdone:
                fsummary += " %d" % len(frame)
                if (len(fsummary) > 30):
                    fsummary = " ..." + fsummary
                    fdone = True

        res = time_str() + " %d:" % (len(self.frames)-1) + fsummary
        res += " :%d" % fsum + "    "
        print(res+"\r", file=sys.stderr, end="")

    def check_tmp(self):
        print(time_str(), "!P", end =' ')
        self.qtype = "init"
        return self.solve_with_model(self.solver, Not(prop_formula(self)), [])

    def check_init(self):
        print(time_str(), "Init", end =' ')
        self.qtype = "init"
        return self.solve_with_model(self.solver, init_formula(self), [])

    def store_init_values(self):
#         if (self.verbose < 4):
#             return
        print(time_str(), "Storing init values:")
        cube = self.check_init()
        if cube is None:
            print("--> Init is UNSAT")
            return
#             assert(0)
        else:
            globValues = dict()
            conditions = []
            for c in flatten_cube(cube):
                ct = c.node_type()
#                 print("\t%s of type %s" % (pretty_serialize(c), ct))
                lhs = None
                rhs = None
                if (ct == pysmt.operators.NOT):
                    lhs = c.arg(0)
                    rhs = FALSE()
                elif (ct == pysmt.operators.SYMBOL):
                    lhs = c
                    rhs = TRUE()
                elif (ct == pysmt.operators.EQUALS):
                    lhs = c.arg(0)
                    rhs = c.arg(1)
                elif (ct == pysmt.operators.FUNCTION):
                    lhs = c
                    rhs = TRUE()
                elif (ct == pysmt.operators.BOOL_CONSTANT):
                    assert(c == TRUE())
                    continue
                else:
                    print("Unexpected initial condition: %s of type %s" % (pretty_serialize(c), ct))
                    assert(0)
                
#                 print("\t\t%s (type: %s) = %s" % (pretty_serialize(lhs), lhs.node_type(),
#                                                   pretty_serialize(rhs)))
                
                s = None
                if lhs.is_function_application():
                    s = lhs.function_name()
                elif lhs.is_symbol():
                    s = lhs
                else:
#                     print("Unexpected LHS in initial condition: %s of type %s" % (pretty_serialize(c), ct))
                    continue
                    assert(0)
                
                if s in self.system.curr._globals:
                    if lhs in globValues:
                        if rhs != globValues[lhs]:
                            print("\tConflicting assignment in initial condition for %s: %s versus %s" % 
                                  (pretty_serialize(lhs),
                                   pretty_serialize(globValues[lhs]),
                                   pretty_serialize(rhs)))
                            assert(0)
                            
                    globValues[lhs] = rhs
                    conditions.append(EqualsOrIff(lhs, rhs))
#                 elif s in self.system.curr._pre2nex:
                else:
                    if lhs in self.init_values:
                        if rhs != self.init_values[lhs]:
                            print("\tConflicting assignment in initial condition for %s: %s versus %s" % 
                                  (pretty_serialize(lhs),
                                   pretty_serialize(self.init_values[lhs]),
                                   pretty_serialize(rhs)))
                            assert(0)
                    self.init_values[lhs] = rhs
                    conditions.append(EqualsOrIff(lhs, rhs))
            
            conditions = self.filter_state(conditions)
            print("(one of the initial states)")
            for v in sorted(conditions, key=str):
                print("\t%s" % (pretty_print_str(v)))
        print("")

    def get_cube_values(self, cube):
        if (self.verbose < 4):
            return None
        cubeValues = dict()
        globValues = dict()
        for c in flatten_cube(cube):
            ct = c.node_type()
#             print("\t%s of type %s" % (pretty_serialize(c), ct))
            lhs = None
            rhs = None
            if (ct == pysmt.operators.NOT):
                lhs = c.arg(0)
                rhs = FALSE()
            elif (ct == pysmt.operators.SYMBOL):
                lhs = c
                rhs = TRUE()
            elif (ct == pysmt.operators.EQUALS):
                lhs = c.arg(0)
                rhs = c.arg(1)
            elif (ct == pysmt.operators.FUNCTION):
                lhs = c
                rhs = TRUE()
            elif (ct == pysmt.operators.BOOL_CONSTANT):
                assert(c == TRUE())
                continue
            else:
#                 print("Unexpected initial condition: %s of type %s" % (pretty_serialize(c), ct))
                assert(0)
            
#             print("\t\t%s (type: %s) = %s" % (pretty_serialize(lhs), lhs.node_type(),
#                                               pretty_serialize(rhs)))
            
            s = None
            if lhs.is_function_application():
                s = lhs.function_name()
            elif lhs.is_symbol():
                s = lhs
            else:
#                 print("Unexpected LHS in initial condition: %s of type %s" % (pretty_serialize(c), ct))
                continue
                assert(0)
            
#             print("\t symbol: %s" % pretty_serialize(s))
            
                
            if (s in self.system.curr._globals):
                if lhs in globValues:
                    if rhs != globValues[lhs]:
                        print("Conflicting assignment in initial condition for %s: %s versus %s" % 
                              (pretty_serialize(lhs),
                               pretty_serialize(globValues[lhs]),
                               pretty_serialize(rhs)))
                        assert(0)
                            
#                 if lhs in self.init_values:
#                     if rhs != self.init_values[lhs]:
#                         globValues[lhs] = rhs
#                 else:
#                     globValues[lhs] = rhs
                globValues[lhs] = rhs
#             elif s in self.system.curr._pre2nex:
            else:
                if lhs in cubeValues:
                    if rhs != cubeValues[lhs]:
                        print("Conflicting assignment in initial condition for %s: %s versus %s" % 
                              (pretty_serialize(lhs),
                               pretty_serialize(cubeValues[lhs]),
                               pretty_serialize(rhs)))
                        assert(0)
                            
#                 if lhs in self.init_values:
#                     if rhs != self.init_values[lhs]:
#                         cubeValues[lhs] = rhs
                cubeValues[lhs] = rhs
        return (cubeValues, globValues)

    def print_cube_values(self, srcValues, fIdx, destValues):
        if (self.verbose < 4):
            return
        if fIdx == -1:
            print("(cube in !P)")
        else:
            print("(cube in F[%d])" % fIdx)
        cubeValues = srcValues[0]
        globValues = srcValues[1]
        if destValues == None:
            assert(fIdx == -1)
            for lhs in sorted(cubeValues.keys(), key=str):
                rhs = cubeValues[lhs]
#                 if lhs in self.init_values:
#                     if (rhs == self.init_values[lhs]):
#                         continue
                print("\t%s = %s" % (pretty_print_str(lhs), pretty_print_str(rhs)))
            for lhs in sorted(globValues.keys(), key=str):
                rhs = globValues[lhs]
#                 if lhs in self.init_values:
#                     if (rhs == self.init_values[lhs]):
#                         continue
                print("\t%s = %s" % (pretty_print_str(lhs), pretty_print_str(rhs)))
#             print("\t(other literals same as init cube)")
        else:
            cubeValuesDest = destValues[0]
            globValuesDest = destValues[1]
            for lhs in sorted(cubeValues.keys(), key=str):
                rhs = cubeValues[lhs]
                if lhs in cubeValuesDest:
                    if (rhs == cubeValuesDest[lhs]):
                        print("\t%s = %s" % (pretty_print_str(lhs), pretty_print_str(rhs)))
                        continue
                print("\t%s = %s\t\t\t--> modified" % (pretty_print_str(lhs), pretty_print_str(rhs)))
            for lhs in sorted(globValues.keys(), key=str):
                rhs = globValues[lhs]
                if lhs in globValuesDest:
                    if (rhs != globValuesDest[lhs]):
                        print("\tConflicting assignment in global condition for %s: %s versus %s" % 
                              (pretty_print_str(lhs),
                               pretty_print_str(rhs),
                               pretty_print_str(globValuesDest[lhs])))
#                         assert(0)
                    print("\t%s = %s" % (pretty_print_str(lhs), pretty_print_str(rhs)))
                    continue
                print("\t%s = %s\t\t\t--> modified" % (pretty_print_str(lhs), pretty_print_str(rhs)))
#             print("\t(other literals same as previous cube)")
        print("")
    
    def print_global_enum(self):
        if (self.verbose < 4):
            return
        print("(global state #%d)" % len(self.globalEnum))
        for v in sorted(self.globalEnum, key=str):
            print("\t%s" % pretty_print_str(v))
        
    def filter_state(self, conditions, quiet=True):
        return conditions
        if not quiet:
            print("(expanded source state)")
        output = list()
        for cond in conditions:
            if cond == TRUE():
                continue
            ev = cond.get_enum_constants()
            evDiff = ev.difference(self.globalEnum)
            addCond = True
            for e in evDiff:
                if str(e.constant_type()).startswith("epoch"):
                    addCond = False
                    break
            if addCond:
                output.append(cond)
                if not quiet:
                    print("\t%s" % pretty_print_str(cond))
            else:
                pass
#             if len(evDiff) == 0:
#                 output.append(cond)
#                 print("\t%s" % pretty_print_str(cond))
#             else:
#                 pass
        return output
        
    def check_init_is_safe(self):
        print(time_str(), "F[0] /\ !P", end =' ')
        self.qtype = "init"
        return self.solve_with_model(self.solver, And(init_formula(self), Not(prop_formula(self))), [])

    def get_bad_state(self, nexbad):
        """Extracts a reachable state that intersects the negation
        of the property and the last current frame"""
        print(time_str(), "F[%d] /\ T /\ !P+" % (len(self.frames)-1), end =' ')
        return self.solve_with_model(self.get_framesolver(-1), nexbad, [nexbad])

    def check_clause_inductive(self, label, cl):
        print(time_str(), "Is %s inductive?" % label, end =' ')
        return not self.solve_formula(self.solver, And(cl, prop_formula(self), Not(pre2nex(self, cl))))

    def check_clause_includes_init(self, label, cl):
        print(time_str(), "Is F[0] -> %s?" % label, end =' ')
        return not self.solve_formula(self.get_framesolver(0), Not(cl))

    def check_clause_init(self, label, cl):
        print(time_str(), "Is F[0] /\ T -> %s+?" % label, end =' ')
        return not self.solve_formula(self.get_framesolver(0), Not(pre2nex(self, cl)))

    def get_state_value(self, f, model):
        return model.get_value(f)

    def get_relation_value(self, s, args, model):
        f = Function(s, args)
        value = self.get_state_value(f, model)
        if self.ordered == "partial" and self.system.curr.is_ordered_state(s):
            assert(value == TRUE() or value == FALSE())
            return TRUE()
        if self.ordered == "zero" and self.system.curr.is_ordered_state(s):
            assert(value == TRUE() or value == FALSE())
            ev = f.get_enum_constants()
            allSet = True
            for v in ev:
                vstr = pretty_print_str(v)
                if vstr != "e0" and vstr != "e1":
                    allSet = False
                    break
            if allSet:
                return TRUE()
#             if (value == TRUE()):
#                 return TRUE()
#         if str(s).startswith("member:"):
#             assert(value == TRUE() or value == FALSE())
#             if (value == FALSE()):
#                 return TRUE()
        return self.get_predicate_value(f, model)

    def get_predicate_value(self, f, model):
        value = self.get_state_value(f, model)
#         print("%s -> %s" % (f, value))
        eq = EqualsOrIff(f, value)
        return eq
    
    def get_state_values(self, s, s_type, model, sorts, conditions, args, idx):
        if (idx == len(s_type.param_types)):
            conditions.append(self.get_relation_value(s, args, model))
        else:
            i_values = sorts[s_type.param_types[idx]]
            for i in i_values:
                args.append(i)
                self.get_state_values(s, s_type, model, sorts, conditions, args, idx+1)
                args.pop()
    
    def get_predicate_values(self, s, s_type, model, sorts, conditions, rhs, a, subs, idx):
        if (idx == len(s_type.param_types)):
            rhsNew = rhs.simple_substitute(subs)
            conditions.append(self.get_predicate_value(rhsNew, model))
        else:
            i_values = sorts[s_type.param_types[idx]]
            for i in i_values:
                subs[a[idx]] = i
                self.get_predicate_values(s, s_type, model, sorts, conditions, rhs, a, subs, idx+1)
                del subs[a[idx]]
    
    def get_formula_qu(self, formula):
        if self.qf >= 2:
            if (len(self.system._fin2sort) == 0 
#                 and len(self.system._sort2fin) == len(self.system._sorts)
                ):
#                 if formula.has_quantifier_variables():
#                     print("Formula has quantifiers: %s" % formula)
#                     assert(0)
                if formula in self.cache_qu:
                    return self.cache_qu[formula]
                else:
                    not_formula = Not(formula)
                    if not_formula in self.cache_qu:
                        return Not(self.cache_qu[not_formula])
#                     else:
#                         print("Formula not found: %s" % formula)
#                         assert(0)
#         else:
#             if formula in self.cache_qu:
#                 return self.cache_qu[formula]
#             else:
#                 not_formula = Not(formula)
#                 if not_formula in self.cache_qu:
#                     return Not(self.cache_qu[not_formula])          
        return formula
    
    def get_formula_qf(self, formula):
        if self.qf >= 2:
            if (len(self.system._fin2sort) == 0 
#                 and len(self.system._sort2fin) == len(self.system._sorts)
                ):
                if formula in self.cache_qf:
                    return self.cache_qf[formula]

                qvars = formula.get_quantifier_variables()
                if len(qvars) == 0:
                    return formula
                
                noScalarVar = True
                for v in qvars:
                    if v.symbol_type().is_enum_type():
                        noScalarVar = False
                        break
                if noScalarVar:
                    return formula
                
#                 print("QE: %s" % formula.serialize())
                
                push_time()
                q_formula = And(formula)
                qf_formula = self.get_qf_form(q_formula)
                self.update_time_stat("time-qf", pop_time())
                
#                 for f in flatten(qf_formula):
#                     print("--- %s" % f.serialize())
#                 assert(0)

#                 print("Adding QF entry: ", end='')
#                 pretty_print(formula)
#                 pretty_print(qf_formula)
        
                self.cache_qf[formula] = qf_formula
                self.cache_qu[qf_formula] = formula
                return qf_formula
#         else:
#             formula_flat = self.system.replaceDefinitions(formula)
#             self.cache_qu[formula_flat] = formula
#             return formula_flat
        return formula
    
    def get_formulae_qf(self, formula):
        formulae = formula
        if self.qf >= 2:
            if len(self.system._fin2sort) == 0:
                push_time()
                print("qf for query type: %s" % self.qtype)
                q_formula = And(formulae)
                qf_formula = self.get_qf_form(q_formula)
                qf_formulae = flatten_cube(qf_formula)
                self.update_time_stat("time-qf", pop_time())
                return qf_formulae
#             formulae.append(axiom_formula(self))
#                 fformulae = []
#                 for f in formulae:
#                     fformulae.append(f)
#                     if self._print:
#                         print("--- %s" % f.serialize())
#                         print("------ vars: %s" % f.get_free_variables())
#                 formulae = fformulae
        return formulae
    
    def get_formulae(self, formula):
        formulae = formula
        if not isinstance(formulae, list):
            formulae = [formula]
        return formulae
    
    def print_query(self, solver, fname, prefix, formulae, force):
        if force or (self.verbose > 9):
            if not isinstance(solver, pysmt.solvers.z3.Z3Solver):
                return
            fname = "%s/%s.smt2" % (common.gopts.out, fname)
            f = open(fname, "w+")
            if prefix != "":
                f.write(prefix)
    #         solver.print_query(f, formulae)
            solver.print_query(f)
            f.close()
    
    def update_max_query(self, solver, name, value, infinite, core):
        name = "time-q-max" + name
        name += "-core" if core else ""
        name += "-infinite" if infinite else "-finite"
        value *= 1000
        modified = self.update_query_stat(name, value)
        if modified:
            prefix = "(set-info :time %.0fms)\n\n" % value
#             print(prefix)
            self.print_query(solver, name, prefix, None, False)
    
    def print_formula(self, solver, formula, name="test"):
#         print("Formula: %s" % formula.serialize())
        formulae = None
        if formula != TRUE():
            formulae = self.get_formulae(formula)
        self.print_query(solver, name, "", formulae, True)
    
    def solve_formula(self, solver, formula, quiet=False):
        """Check whether formula is satisfiable or not"""
#         print("Formula: %s" % formula.serialize())
        self.update_stat("scalls")
        if len(self.system._sort2fin) > 0:
            self.update_stat("scalls-finite")
            if len(self.system._sort2fin) == len(self.system._sorts):
                self.update_stat("scalls-finite-full")
        else:
            self.update_stat("scalls-infinite")
        
        formulae = None
        if formula != TRUE():
            formulae = self.get_formulae(formula)
        push_time()
        res = self.check_query(solver, formulae)
        if res:
            if (not quiet):
                print("-> SAT")
            self.update_max_query(solver, "", pop_time(), len(self.system._sort2fin) == 0, False)
            return True
        else:
            if (not quiet):
                print("-> UNSAT")
            self.update_max_query(solver, "", pop_time(), len(self.system._sort2fin) == 0, False)
            return False
            
    def solve_with_model(self, solver, formula, dest, quiet=False):
        """Provides a satisfiable assignment to the state variables that are consistent with the input formula"""
        result = self.solve_formula(solver, formula, quiet)
        if result:
            model = self.last_solver.get_model()
#             model.print_model()
            sorts = dict()
            isorts = dict()
            if len(self.system._sort2fin) != len(self.system._sorts):
                isorts = model.get_diagram_sorts()       
#             model.get_diagram_funcs()   
            for k, v in isorts.items():
                sorts[k] = v
            for k, v in self.system._enumsorts.items():
                sorts[k] = v
#            print("\tmodel isorts: %s" % isorts)
#             print("\tmodel sorts: %s" % sorts)
            
            conditions = []
            
            for lhs, rhs in self.system.curr._predicates.items():
                assert(lhs.is_function_application())
                s = lhs.function_name()
                a = lhs.args()
                s_type = s.symbol_type()
                assert(len(s_type.param_types) <= 4)

                subs = dict()
                if (len(s_type.param_types) <= 0):
                    rhsNew = rhs.simple_substitute(subs)
                    conditions.append(self.get_predicate_value(rhsNew, model))
                else:
                    subs = {}
                    self.get_predicate_values(s, s_type, model, sorts, conditions, rhs, a, subs, 0)
#                     i_values = sorts[s_type.param_types[0]]
#                     for i in i_values:
#                         subs[a[0]] = i
#                         if (len(s_type.param_types) <= 1):
#                             rhsNew = rhs.simple_substitute(subs)
#                             conditions.append(self.get_predicate_value(rhsNew, model))
#                             continue
#                         j_values = sorts[s_type.param_types[1]]
#                         for j in j_values:
#                             subs[a[1]] = j
#                             if (len(s_type.param_types) <= 2):
#                                 rhsNew = rhs.simple_substitute(subs)
#                                 conditions.append(self.get_predicate_value(rhsNew, model))
#                                 continue
#                             k_values = sorts[s_type.param_types[2]]
#                             for k in k_values:
#                                 subs[a[2]] = k
#                                 if (len(s_type.param_types) <= 3):
#                                     rhsNew = rhs.simple_substitute(subs)
#                                     conditions.append(self.get_predicate_value(rhsNew, model))
#                                     continue
#                                 l_values = sorts[s_type.param_types[3]]
#                                 for l in l_values:
#                                     subs[a[3]] = l
#                                     rhsNew = rhs.simple_substitute(subs)
#                                     conditions.append(self.get_predicate_value(rhsNew, model))
#                                     if (len(s_type.param_types) > 3):
#                                         print("Found a case with more than 5 arguments to a symbol.")
#                                         assert(0)
#             print(conditions)
#             assert(0)

            for s in self.system.curr._states:
#                 print("Symbol: ", s)
                s_type = s.symbol_type()

                if s_type.is_function_type():
                    args = []
                    self.get_state_values(s, s_type, model, sorts, conditions, args, 0)
#                     i_values = sorts[s_type.param_types[0]]
#                     for i in i_values:
#                         if (len(s_type.param_types) == 1):
#                             args = [i]
#                             conditions.append(self.get_relation_value(s, args, model))
#                         elif (len(s_type.param_types) == 2):
#                             j_values = sorts[s_type.param_types[1]]
#                             for j in j_values:
#                                 args = [i, j]
#                                 conditions.append(self.get_relation_value(s, args, model))
#                         elif (len(s_type.param_types) == 3):
#                             j_values = sorts[s_type.param_types[1]]
#                             for j in j_values:
#                                 k_values = sorts[s_type.param_types[2]]
#                                 for k in k_values:
#                                     args = [i, j, k]
#                                     conditions.append(self.get_relation_value(s, args, model))
#                         elif (len(s_type.param_types) == 4):
#                             j_values = sorts[s_type.param_types[1]]
#                             for j in j_values:
#                                 k_values = sorts[s_type.param_types[2]]
#                                 for k in k_values:
#                                     l_values = sorts[s_type.param_types[3]]
#                                     for l in l_values:
#                                         args = [i, j, k, l]
#                                         conditions.append(self.get_relation_value(s, args, model))
#                         elif (len(s_type.param_types) == 5):
#                             j_values = sorts[s_type.param_types[1]]
#                             for j in j_values:
#                                 k_values = sorts[s_type.param_types[2]]
#                                 for k in k_values:
#                                     l_values = sorts[s_type.param_types[3]]
#                                     for l in l_values:
#                                         m_values = sorts[s_type.param_types[4]]
#                                         for m in m_values:
#                                             args = [i, j, k, l, m]
#                                             conditions.append(self.get_relation_value(s, args, model))
#                         else:
#                             print("Found a case with more than 5 arguments to a symbol.")
#                             assert(0)
                else:
                    f = Function(s, [])
                    if f.is_symbol() and f in self.system.curr._globals:
                        rhs = self.get_state_value(f, model)
                        if rhs.is_enum_constant() and str(rhs.constant_type()).startswith("epoch"):
                            self.globalEnum.add(rhs)
#                             print("adding global enum: %s" % pretty_print_str(rhs))

                    eq = self.get_predicate_value(f, model)
                    if self.ordered == "zero":
                        fstr = pretty_print_str(f)
                        if fstr != "zero" and fstr != "firste":
                            conditions.append(eq)
                    else:
                        conditions.append(eq)
#             for c in conditions:
#                 print("%s" % pretty_serialize(c))
#             assert(0)

            ivars = []
            ivarMap = {}
            for s, values in isorts.items():
                for i in range(len(values)):
                    v = values[i]
                    name = "Q:" + str(s) + str(len(ivarMap))
                    qv = Symbol(name, s)
                    ivarMap[v] = qv
                    ivars.append(qv)
#                     ivars.append(v)
                    for j in range(i+1, len(values)):
                        if i != j:
                            neq = Not(EqualsOrIff(v, values[j]))
                            conditions.append(neq)
#                             print("adding to cube: %s" % str(neq))

            if len(dest) != 0:
                print("(action info)")
                inputConditions = []
                actionIdx = -1
                for idx, f in enumerate(self.system.curr._actions):
                    en = f[2]
                    enValue = self.get_state_value(en, model)
                    if (enValue == TRUE()):
                        actionIdx = idx
                        actionName = f[1]
                        print("\taction: %s" % actionName)
    #                     print("\ten: " + str(en) + " with value " + str(enValue))
                        
                        print("\tinputs:")
                        if actionName in self.system.syntax.action2inputs:
                            actionInputs = self.system.syntax.action2inputs[actionName]
                            for inp in actionInputs:
                                inpValueEnum = self.get_state_value(inp, model)
                                if self.allow_inputs_in_cube:
                                    conditions.append(EqualsOrIff(inp, inpValueEnum))
                                inpValue = inpValueEnum.simple_substitute(ivarMap)
                                print("\t\t" + pretty_print_str(inp) + " -> " + pretty_print_str(inpValue))
                                if inpValue.is_enum_constant() and str(inpValue.constant_type()).startswith("epoch"):
                                    self.globalEnum.add(inpValue)
                                
#                                 name = "Q:" + str(inp)
#                                 qv = Symbol(name, inp.symbol_type())
#                                 ivarMap[inpValueEnum] = qv
#                                 ivars.append(qv)
    
#                         self.print_global_enum()
                        conditions = self.filter_state(conditions)
                        break

            if self.random > 3:
                random.shuffle(conditions)
            cube = And(conditions)        
            
            if len(ivars) != 0:
                cube = cube.simple_substitute(ivarMap)
                cube = Exists(ivars, cube)
                
#             print("cube: %s" % cube)
#             print("cube:")
#             for c in flatten_cube(cube):
#                 print("\t%s" % pretty_serialize(c))
#             assert(0)
            
            self.update_stat("cubes")
            self.update_stat("sz-cube-sum", len(conditions))
            return cube
        else:
            return None

    def get_dest_cube(self):
        model = self.last_solver.get_model()
#             model.print_model()
        sorts = dict()
        isorts = dict()
        if len(self.system._sort2fin) != len(self.system._sorts):
            isorts = model.get_diagram_sorts()       
#             model.get_diagram_funcs()   
        for k, v in isorts.items():
            sorts[k] = v
        for k, v in self.system._enumsorts.items():
            sorts[k] = v
#            print("\tmodel isorts: %s" % isorts)
#             print("\tmodel sorts: %s" % sorts)
        
        conditions = []
        
        for s in self.system.curr._nexstates:
#                 print("Symbol: ", s)
            s_type = s.symbol_type()

            if s_type.is_function_type():
                args = []
                self.get_state_values(s, s_type, model, sorts, conditions, args, 0)
#                 i_values = sorts[s_type.param_types[0]]
#                 for i in i_values:
#                     if (len(s_type.param_types) == 1):
#                         args = [i]
#                         conditions.append(self.get_relation_value(s, args, model))
#                     elif (len(s_type.param_types) == 2):
#                         j_values = sorts[s_type.param_types[1]]
#                         for j in j_values:
#                             args = [i, j]
#                             conditions.append(self.get_relation_value(s, args, model))
#                     elif (len(s_type.param_types) == 3):
#                         j_values = sorts[s_type.param_types[1]]
#                         for j in j_values:
#                             k_values = sorts[s_type.param_types[2]]
#                             for k in k_values:
#                                 args = [i, j, k]
#                                 conditions.append(self.get_relation_value(s, args, model))
#                     elif (len(s_type.param_types) == 4):
#                         j_values = sorts[s_type.param_types[1]]
#                         for j in j_values:
#                             k_values = sorts[s_type.param_types[2]]
#                             for k in k_values:
#                                 l_values = sorts[s_type.param_types[3]]
#                                 for l in l_values:
#                                     args = [i, j, k, l]
#                                     conditions.append(self.get_relation_value(s, args, model))
#                     elif (len(s_type.param_types) == 5):
#                         j_values = sorts[s_type.param_types[1]]
#                         for j in j_values:
#                             k_values = sorts[s_type.param_types[2]]
#                             for k in k_values:
#                                 l_values = sorts[s_type.param_types[3]]
#                                 for l in l_values:
#                                     m_values = sorts[s_type.param_types[4]]
#                                     for m in m_values:
#                                         args = [i, j, k, l, m]
#                                         conditions.append(self.get_relation_value(s, args, model))
#                     else:
#                         print("Found a case with more than 5 arguments to a symbol.")
#                         assert(0)
            else:
                f = Function(s, [])
                
                eq = self.get_predicate_value(f, model)
                if self.ordered == "zero":
                    fstr = pretty_print_str(f)
                    if fstr != "zero" and fstr != "firste":
                        conditions.append(eq)
                else:
                    conditions.append(eq)

        ivars = []
        ivarMap = {}
        for s, values in isorts.items():
            for i in range(len(values)):
                v = values[i]
                name = "Q:" + str(s) + str(len(ivarMap))
                qv = Symbol(name, s)
                ivarMap[v] = qv
                ivars.append(qv)
#                     ivars.append(v)
                for j in range(i+1, len(values)):
                    if i != j:
                        neq = Not(EqualsOrIff(v, values[j]))
                        conditions.append(neq)
#                             print("adding to cube: %s" % str(neq))

        conditions = self.filter_state(conditions, True)
                    
        cube = And(conditions)        
        
        if len(ivars) != 0:
            cube = cube.simple_substitute(ivarMap)
            cube = Exists(ivars, cube)
            
#             print("cube: %s" % cube)
#             print("cube:")
#             for c in flatten_cube(cube):
#                 print("\t%s" % pretty_serialize(c))
#             assert(0)
        dest = nex2pre(self, cube)
        return dest

    def ff(self, solver, pz):
        return z3.is_false(solver.z3.model().eval(pz))
    
    def marco(self, fIdx, solver, ps):
        solver = self.new_solver()
        frame = self.get_frame(fIdx)
        assert_permanent(solver, frame)
        
        z3.set_param('smt.core.minimize', True)
        allMus = []
        
        psz = []
        psz2ps = {}
        for idx, p in enumerate(ps):
            z = solver.get_term(p)
#             pz = z
            pz = z3.Bool("marco%d" % idx)
            solver.z3.add(z3.Implies(pz, z))
            psz2ps[pz] = p
            psz.append(pz)
#             print("%s -> %s" % (pz, pretty_print_str(p)))
            
        solver.push()
        while solver.z3.check() == z3.sat:
            seed = []
            for pz in psz:
                seed.append(pz)
            if solver.z3.check(seed) == z3.sat:
                break
            else:
                musz = solver.z3.unsat_core()
                if len(musz) != 0:
                    mz = musz[0]
                    psz.remove(mz)
                solver.z3.add(z3.Not(z3.And(musz)))
                mus = []
                for mz in musz:
                    if mz in psz2ps:
                        m = psz2ps[mz]
                        mus.append(m)
                if len(mus) == 0:
                    break
                mus = And(mus)
#                 print("new mus: %s" % pretty_serialize(mus))
                if mus in allMus:
                    print(solver.z3.assertions())
                    assert(0)
                allMus.append(mus)
        solver.pop()
        z3.set_param('smt.core.minimize', False)
        return allMus
           
    def solve_with_core(self, fIdx, formula, assume):
        self.qtype = "blo"
        """Provides a satisfiable assignment is SAT, else return unsat core"""
#         print("Assume: %s" % assume)
        args = tuple()
        qvars = set()
        v = assume
        if (v.is_exists()):
            vq = v.quantifier_vars()
            for i in vq:
                qvars.add(i)
            v = v.args()[0]
        if (v.is_and()):
            args = v.args()
            
        assumptions = []
        for arg in args:
            assumption = arg
            if arg != TRUE():
                assumptions.append(assumption)
        if self.random > 1:
            random.shuffle(assumptions)
        assumptions = self.get_formulae(assumptions)
        
        if True or self.use_wires:
            assumptions = sorted(assumptions, key=lambda v: (self.system.get_dependency_priority(v, self.use_wires), str(v)))
        else:
            assumptions = sorted(assumptions, key=lambda v: str(v))

        if self._print:
            print("# assumptions: %d" % len(assumptions))
            print("f: %s" % formula.serialize())
            for f in assumptions:
                print("assume: %s" % f.serialize())
        
        formulae = self.get_formulae(formula)
        
        solver = self.get_framesolver(fIdx)
        
        solver.push()
        solver.add_assertion(And(formulae))
        
        solver.push()
        solver.reset_named_assertions()
        
        result = True
        cube = None

        dLast = 0
        for i in assumptions:
            if self.use_wires:
                d = self.system.get_dependency_priority(i, self.use_wires)
                if dLast != d:
                    result = self.solve_formula(solver, TRUE(), True)
                dLast = d
                if not result:
                    break
#                 print("\tassume (%d): %s" % (d, pretty_print_str(i)))
            solver.add_assertion(i, "assume" + str(i))
            
        if result:
            cube = self.solve_with_model(solver, TRUE(), assumptions, True)
            if cube is None:
                result = False
#         assert(0)
        
        ucore = []
        if cube is None:
            assert(not result)
            print(time_str(), "\tAns. UNSAT")
            self.update_stat("unsat-core")
            core = list(self.last_solver.get_unsat_core())
#             print("\nz3 unsat core #%d" % len(core))
#             for c in core:
#                 print("\t%s" % c)
#             print()

#             print("(unsat core)")
#             for c in core:
#                 print("\t%s" % pretty_serialize(c))
                
            self.update_stat("sz-unsat-core-sum", len(core))
            solver.pop()
            
#             allMus = self.marco(fIdx, solver, assumptions)
#             print("(unsat cores #%s)" % len(allMus))
#             for idx, mus in enumerate(allMus):
#                 print("\t#%d: %s" % (idx, pretty_serialize(mus)))
# 
#             eprint("Choose an MUS index? ", end='')
#             ri = raw_input("")
#             if ri:
#                 try:
#                     chosenIdx = int(ri)
#                     if chosenIdx >= 0 and chosenIdx < len(allMus):
#                         print("(choosen unsat core #%d)" % chosenIdx)
#                         core = [allMus[chosenIdx]]
#                     else:
#                         print("index should be in range [0-%d)" % len(allMus))
#                         pass
#                 except ValueError:
#                     pass
            
            required = set()
            assumptions = core
#             required = set(core)
#             assumptions = []
            
#             symSet = set()
#             for c in core:
#                 varc = c.get_free_variables()
#                 for v in varc:
#                     symSet.add(v)
#             print("symbols #%d: %s" % (len(symSet), symSet))
            
            ucSizes = []
            ucSizes.append(len(required) + len(core))
            
            
#             for f in solver.assertions:
#                 print("assertion: %s" % f.serialize())
            while len(assumptions) != 0:
                if self.random > 2:
                    random.shuffle(assumptions)
                
                curr = assumptions.pop()
                if self.use_z3_minimize:
                    required.add(curr)
                    continue
                
                solver.push()
                solver.reset_named_assertions()
                for i in assumptions:
                    solver.add_assertion(i, "assume" + str(i))
                res = self.check_query(solver)
#                 print("curr: %s -> %srequired" % (curr, "" if res else "not "))
#                 named = self.solver.named_assertions
#                 print("named: #%d : %s" % (len(named), named))
                if res:
                    solver.pop()
                    required.add(curr)
                    solver.add_assertion(curr)
                else:
                    tmpCore = list(self.last_solver.get_unsat_core())
                    ucSizes.append(len(required) + len(tmpCore))
                    solver.pop()
                    for i in assumptions:
                        if i not in tmpCore:
                            assumptions.remove(i)
                            
            solver.reset_named_assertions()
            solver.pop()
            self.update_stat("sz-unsat-min-sum", len(required))
            
#             if self._print:
            print(time_str(), "F[%d] unsat core #%d " % (fIdx+1, len(required)), end='')
            print("\t(ucsz: ", end='')
            for i in ucSizes:
                print("%d -> " % i, end='')
            print("%d)" % len(required))
                
            print("(minimal unsat core)")
            for c in required:
                print("\t%s" % pretty_serialize(c))
                
            assert(len(required) != 0)
#             assert(0)

            qvars_new = set()
            for arg in required:
#                 print("Arg: %s" % arg)
                arg_vars = get_free_variables(arg)
                for i in arg_vars:
                    if i in qvars:
                        qvars_new.add(i)
            
            required2 = sorted(required, key=lambda v: str(v))
            mus = And(required2)
            if len(qvars_new) != 0:
                mus = Exists(qvars_new, mus)
            ucore.append(mus)
        else:
            assert(result)
            print(time_str(), "\tAns. SAT")
            solver.pop()
            solver.reset_named_assertions()
            solver.pop()
        return cube, ucore
                     
    def check_implication(self, lhs, rhs, comment="Checking implication"):
        print(time_str(), "%s?" % comment, end =' ')
        return not self.solve_formula(self.solver, And(lhs, Not(rhs)))

    def check_if_global(self, core, corepre):
        self.qtype = "glo"
        isSat = self.solve_formula(self.solver, And(Not(corepre), prop_formula(self), core), True)
        return not isSat
             
    def recursive_block(self, i, cube, cubeV):
        """Blocks the cube at each frame, if possible.

        Returns True if the cube cannot be blocked.
        """
        self.update_stat("cti")
        cube = self.get_formula_qf(cube)
        if (i == 0):
            print(time_str(), "-> Reached F[0]")
            return True
        if self.debug:
            if (i == 1):
                if self.solve_formula(self.get_framesolver(0), cube, True):
                    print("-> Cube in F[1] intersects Init")
                    print("(sanity check) assert failed")
                    assert(0)
                    return True
        
        cubeprime = pre2nex(self, cube)
#         print("cube: %s" % cubeprime)
        
        while True:
            print(time_str(), "F[%d] /\ T /\ C+ ?" % (i-1))
            push_time()
            cubepre, muses = self.solve_with_core(i-1, TRUE(), cubeprime)
            if cubepre is None:
                assert(len(muses) != 0)
                self.update_time_stat("time-cti-unsat", pop_time())
                
                cubesOut = list()
                for ucore in muses:
                    if self.boosting == "none":
                        cubesOut.append((ucore, False))
                    else:
                        ucoreQ = symmetry_cube(self, ucore, i-1, True, cubeprime)
                        cubesOut.extend(ucoreQ)
                assert(len(cubesOut) != 0)
                if len(cubesOut) != 1:
                    print("Found multiple generalized cubes #%d" % len(cubesOut))
                for core, fancy in cubesOut:
                    print("(clause-type: %s)" % fancy, end="\t")
                    pretty_print(Not(core))
#                     assert(0)
                
                numLearnt = 0
                for core, fancy in cubesOut:
                    if fancy == "non-epr" and len(cubesOut) > 1:
                        continue
                    corepre = nex2pre(self, core)
                    
#                     if fancy:
#                         print("blocked: sanity check? ", end="")
#                         result = self.solve_formula(self.get_framesolver(i-1), core)
#                         if result:
#                             print("Error in learning: cube unblocked")
#                             eprint("nblock triggerred")
#                             assert(0)

                    core_formula = self.get_formula_qf(core)
                    corepre_formula = self.get_formula_qf(corepre)

                    isGlobal = self.check_if_global(core_formula, corepre_formula)
                    print(time_str(), "is global clause? %s" % ("Yes" if isGlobal else "No"))
                    iNew = i
                    if isGlobal:
                        iNew = len(self.frames) - 1
                        label = "global" + str(iterationCount) + "_" + str(len(self.globals)+1)
                        self.globals[Not(corepre)] = label
    #                     assert(0)
#                     if fancy:
#                         self.extend_cube(iNew, corepre)
                    self.learn_cube(iNew, corepre, corepre_formula)
                    numLearnt += 1
#                     break
                assert(numLearnt != 0)
                return False
            else:
                cubepreV = self.get_cube_values(cubepre)
                self.print_cube_values(cubepreV, i-1, cubeV)
#                 assert(0)
                
                self.update_time_stat("time-cti-sat", pop_time())
                res2 = self.recursive_block(i-1, cubepre, cubepreV)
                if res2:
                    return True

    def inductive(self):
        """Checks if frames have converged """
        
        push_time()
        N = len(self.frames)
        self.add_frame()
        set_solver(self)
        
        if N > 1:            
            """Syntactic check"""
            self.qtype = "fc"
            for i in range(N):
                if (i != N-1) and len(self.frames[i]) == 0:
                    print(time_str(), "F[%d] converged!" % i)
#                     print("F[%d] = " % i, self.frames[i])
#                     print("Is F[%d] != F[%d]" % (i, i+1), end =' ')
                    if self.debug:
                        cube = self.solve_with_model(self.solver, Not(EqualsOrIff(self.get_frame(i), self.get_frame(i+1))), [])
                        if cube is not None:
                            print("But solver gives a model: %s" % cube.serialize())
                            assert(0)
                    print("\n", file=sys.stderr, end="")
                    return True, i
            
            for i in range(N):
                if (i != 0):
                    forwarded = []
                    framesolver = self.get_framesolver(i)
                    print("Trying forwarding F[%d]" % (i))
                    for cl in self.frames[i]:
                        cl_formula = self.get_formula_qf(cl)
                        cl_nex = pre2nex(self, cl_formula)
                        if not(self.solve_formula(framesolver, cl_nex, True)):
                            forwarded.append((cl, cl_formula))
                    if len(forwarded) != 0:
                        print("Forwarded #%d to F[%d]" % (len(forwarded), i+1))
                        for cl, cl_formula in forwarded:
                            self.learn_cube(i+1, cl, cl_formula)
                if (i != N-1) and len(self.frames[i]) == 0:
                    print(time_str(), "F[%d] converged!" % i)
#                     print("F[%d] = " % i, self.frames[i])
#                     print("Is F[%d] != F[%d]" % (i, i+1), end =' ')
                    if self.debug:
                        cube = self.solve_with_model(self.solver, Not(EqualsOrIff(self.get_frame(i), self.get_frame(i+1))), [])
                        if cube is not None:
                            print("But solver gives a model: %s" % cube.serialize())
                            assert(0)
                    print("\n", file=sys.stderr, end="")
                    return True, i
                            
#             """Check using solver """
#             for i in range(N-1):
#                 j = i+1
#                 if not(self.solve_formula(Not(EqualsOrIff(self.get_frame(i), self.get_frame(j))), True)):
#                     print("[solver check] F[%d] = F[%d]" % (i, j))
#                     print("   [PDR] F[%d] converged!" % i)
#                     return True, i
                
#             """Check F[i] & T -> F[i+1] using solver """
#             for i in range(N-1):
#                 j = i+1
#                 dest = Not(pre2nex(self, self.get_frame(j)))
#                 if (self.solve_formula(And(self.get_frame(i), trel_formula(self),  dest), True)):
#                     print("[solver check] F[%d] & T & !F[%d]+ is SAT" % (i, j))
#                     print("Frames: #%d" % len(self.frames))
#                     for k, frame in enumerate(self.frames):
#                         print("\tF[%d]: #%d" % (k, len(frame)))
#                         for cl in frame:
#                             print("\t\t%s" % cl.serialize())
# #                     model = self.solver.get_model()
# #                     model.print_model()
# #                     print("F[%d]: %s" % (i, self.get_frame(i).serialize()))
# #                     print("dest: %s" % (dest.serialize()))
#                     for cl in flatten_cube(pre2nex(self, self.get_frame(j))):
#                         dest = Not(cl)
#                         if (self.solve_formula(And(self.get_frame(i), trel_formula(self),  dest), True)):
#                             model = self.solver.get_model()
#                             model.print_model()
#                             print("F[%d]: %s" % (i, self.get_frame(i).serialize()))
#                             print("dest: %s" % (dest.serialize()))
#                             assert(0)
#                     assert(0)
                
#             """Inductive check using solver """
#             for i in range(N-1, 0, -1):
#                 frame = self.get_frame(i)
#                 print("Is F[%d] inductive?" % (i))
#                 dest = Not(pre2nex(self, frame))
#                 if not(self.solve_formula(And(frame, dest))):
#                     print("   [PDR] F[%d] converged!" % i)
#                     return True, i

        self.update_time_stat("time-forward", pop_time())
        return False, -1

    def minimize_invariant(self, inv_list_orig):
        push_time()
        
        inv_list = []
        for label, v in inv_list_orig:
            outF, outE = count_quantifiers(v)
#             cost = outF + 1000*outE
            cost = formula_cost(v)
            print("raw invariant [%s] (cost: %d, %dF, %dE) \t%s" % (label, cost, outF, outE, v))
            inv_list.append((cost, label, v))
            
        print(time_str(), "Minimizing certificate of size %d" % len(inv_list))
        nFailed = 0
        inv_tmp = set()
        for cost, label, v in inv_list:
            inv_tmp.add((label, v))
        prop = prop_formula(self)
        inv_required = []
        inv_optional = []
        for cost, label, v in sorted(inv_list, key=lambda k: k[0], reverse=True):
            print(time_str(), "\t%s\t(cost: %d) -> " % (label, cost), end='')
            if (v == prop) or (v in self.system.curr._prop):
                print("property")
#                 if not label.endswith("_required"):
#                     label += "_required"
                inv_required.append((label, v))
                continue
            inv_tmp.remove((label, v))
            nFailed = self.check_invariant(inv_tmp, True)
            if nFailed != 0:
                print("add")
                inv_tmp.add((label, v))
#                 if not label.endswith("_required"):
#                     label += "_required"
                inv_required.append((label, v))
            else:
                print("remove")
#                 if not label.endswith("_optional"):
#                     label += "_optional"
                inv_optional.append((label, v))
        print("\tMinimized certificate: %d -> %d" % (len(inv_list), len(inv_required)))
        print(time_str(), "-------------------------------------------------")
        self.update_time_stat("time-minimize", pop_time())
        return inv_required, inv_optional

def backwardReach(fname, system=None):
    global start_time, iterationCount
    parseSystem = system == None
    if parseSystem:
        utils.start_time = time.time()
        system = TransitionSystem()
    p = PDR(system)
    checkInfers = False
    if parseSystem:
        read_problem(p, fname)
    else:
#         p.system.set_finite_extend()
        p.system.set_curr()
        checkInfers = True
        eprint(time_str(), "(running ic3po with %d inferences)" % len(p.system.curr._infers))

    set_problem(p)
    set_solver(p)
    
    print_sizes1(p, "finite-size-init")
    print_stat("opt-antecedent", "true" if common.gopts.opt > 0 else "false")
    print_num_state_bits1(p, "total-state-bits-init")

    if len(p.system.curr._infers) != 0:
        print()
        syntax_infers = []
        for cl, label in p.system.curr._infers.items():
            syntax_infers.append((label, cl))
        pretty_print_inv(syntax_infers, "Inferences")
    
    helpers = set()
    done = False
    result = "unknown"
    num_uc_prev = -1    
    while not done:
        iterationCount += 1
        inv_set_l = None
        cex = None
        forceMinimize = False
        forceReset = False
        nFailed = 0
        nFailed_ind = 0
        if checkInfers:
            assert(len(p.system.curr._infers) != 0)
            inv_set_l = set()
#             inv_set.add(prop_formula(p))
            for formula, label in p.system.curr._infers.items():
                cl = formula
#                 cl = p.get_formula_qf(cl)
                inv_set_l.add((cl, label))
            
            eprint(time_str(), "(checking inferences)")
            print("Checking if inferences are inductive")
            push_time()
            p.check_invariant(inv_set_l)
            p.update_time_stat("time-inv-check-infinite" if (len(p.system._sort2fin) == 0) else "time-inv-check-finite", pop_time())
            
            checkInfers = False
        else:
            inv_set_l = set()
            inv_set_optional_l = set()
            inv_set_l, cex = p.check_property(helpers)
            if inv_set_l != None and common.gopts.min == 2:
                inv_full_fin = []
                prop = prop_formula(p)
                for label, cl in inv_set_l:
                    if cl == p or cl in p.system.curr._prop:
                        inv_full_fin.insert(0, (label, cl))
                        continue
                    inv_full_fin.append((label, cl))
                eprint(time_str(), "Minimizing...")
                inv_minimized_fin, inv_optional_fin = p.minimize_invariant(inv_full_fin)
                eprint(time_str(), "Minimized proof certificate (finite) of size %d." % len(inv_minimized_fin))
#                 p.print_stats()
                pretty_print_inv(inv_minimized_fin, "Proof certificate (required)")
                invSz = len(inv_minimized_fin)
                if len(inv_optional_fin) != 0:
                    pretty_print_inv(inv_optional_fin, "Optional invariants", "_optional")

                inv_set_l = set()
                inv_set_optional_l = set()
                for label, cl in inv_minimized_fin:
                    inv_set_l.add((label, cl))
                for label, cl in inv_optional_fin:
                    inv_set_optional_l.add((label, cl))
                
        last_tsb = p.system.get_num_state_bits()
        p.print_stats()
        if inv_set_l == None:
            result = "unsafe"
            eprint(time_str(), "Property violated.")
            print_sizes1(p, "finite-size-final")
            print_num_state_bits2(p, "total-state-bits-final", last_tsb)
            break
        
        num_uc_new = p.stat["unsat-core"]
        if (num_uc_new == num_uc_prev):
            forceReset = True
        num_uc_prev = num_uc_new
            
        p.reset()
        for tt in list(p.system._sort2fin.keys()):
            p.system.unbound_sort(tt)
        p.system.infinitize()
        set_problem(p, True)
        set_solver(p)
        
        inv_set_inf_l = set()
        inv_set_all_inf_l = set()
        long_clauses = set()
        for label, i in inv_set_l:
            i_inf = i.fsubstitute()
            if is_long_clause(p.system, i):
                long_clauses.add(i_inf)
#                 continue
            inv_set_inf_l.add((label, i_inf))
            inv_set_all_inf_l.add((label, i_inf))
        for label, i in inv_set_optional_l:
            i_inf = i.fsubstitute()
            if is_long_clause(p.system, i):
                long_clauses.add(i_inf)
#                 continue
            inv_set_all_inf_l.add((label, i_inf))
        inv_set_check_inf_l = inv_set_inf_l
        
        inductCheck = True
        if inductCheck and len(p.system._fin2sort) != 0:
            eprint(time_str(), "(finite convergence checks)")
            print(time_str(), "(finite convergence checks)")
            
            for k, v in p.system._fin2sort.items():
                p.system._sort2fin[v] = k
            p.system._fin2sort.clear()
            
            sorts_ind = { str(i) : i for i in p.system._sort2fin.keys() }
            extended_sorts = set()
            while (nFailed_ind == 0) and (len(sorts_ind) != 0):
#                 s_inf = sorts_ind.pop()
                minSz = -1
                s_inf = None
                s_inf_str = ""
                for tt_str, tt in sorts_ind.items():
                    assert(tt in p.system._sort2fin)
                    tt_fin = p.system._sort2fin[tt]
                    assert(tt_fin in p.system._enumsorts)
                    ttSz = len(p.system._enumsorts[tt_fin])
                    if (minSz == -1) or ttSz < minSz:
                        s_inf = tt
                        s_inf_str = tt_str
                        minSz = ttSz
                sorts_ind.pop(s_inf_str, None)
                
                print(time_str(), "(performing finite convergence checks for %s)" % str(s_inf))
                
                p.reset()
                newSz = -1
                for tt in p.system._sort2fin.keys():
                    if tt == s_inf:
                        sz = p.system.extend_sort(tt, 1)
                        newSz = sz
                        extended_sorts.add(tt)
                    else:
                        sz = p.system.extend_sort(tt, 0)
                        
                p.system.set_curr()
                set_problem(p)
                set_solver(p)
                
                inv_set_ind_l = set()
                inv_set_all_ind_l = set()
                for label, i in inv_set_inf_l:
                    i_ind = i.fsubstitute()
                    inv_set_ind_l.add((label, i_ind))
                for label, i in inv_set_all_inf_l:
                    i_ind = i.fsubstitute()
                    inv_set_all_ind_l.add((label, i_ind))
                
#                 nFailed_s, inv_pruned_ind = p.check_and_prune_invariant(inv_set_ind, 0)
#                 if nFailed_s != 0 and len(inv_set_all_ind) != len(inv_set_ind):
#                     nFailed_s, inv_pruned_ind = p.check_and_prune_invariant(inv_set_all_ind, 0)
                    
                push_time()
                nFailed_s = p.check_invariant(inv_set_ind_l)
                p.update_time_stat("time-inv-check-finite", pop_time())
            
                if nFailed_s != 0:
                    nFailed_ind += nFailed_s
                    eprint(time_str(), "\t|%s| = %d :\tfail" % (str(s_inf), newSz))
                    eprint(time_str(), "(extended |%s| to %d)" % (str(s_inf), newSz))
                    print(time_str(), "(extended |%s| to %d)" % (str(s_inf), newSz))
                else:
                    eprint(time_str(), "\t|%s| = %d :\tpass" % (str(s_inf), newSz))

            if nFailed_ind == 0:
                print(time_str(), "(all finite convergence checks passed)")
                eprint(time_str(), "(all finite convergence checks passed)")
                p.reset()
                for tt in p.system._sort2fin.keys():
                    if tt in extended_sorts:
                        sz = p.system.extend_sort(tt, -1)
                    else:
                        sz = p.system.extend_sort(tt, 0)
                p.system.set_curr()
                set_problem(p)
                set_solver(p)
            else:
                print(time_str(), "(finite convergence checks failed for %s)" % str(s_inf))
                eprint(time_str(), "(finite convergence checks failed for %s)" % str(s_inf))
                nFailed = nFailed_ind
                p.reset()
                for tt in p.system._sort2fin.keys():
                    if tt in extended_sorts and tt != s_inf:
                        sz = p.system.extend_sort(tt, -1)
                    else:
                        sz = p.system.extend_sort(tt, 0)
                p.system.set_curr()
                set_problem(p)
                set_solver(p)
                
            p.reset()
            for tt in list(p.system._sort2fin.keys()):
                p.system.unbound_sort(tt)
            p.system.infinitize()
            set_problem(p, True)
            set_solver(p)
            
        if nFailed == 0:
#             set_problem(p, True)
#             set_solver(p)
            nFailed, inv_pruned_inf_l = p.check_and_prune_invariant(inv_set_check_inf_l, 0)
            if nFailed != 0 and len(inv_set_all_inf_l) != len(inv_set_inf_l):
                nFailed, inv_pruned_inf_l = p.check_and_prune_invariant(inv_set_all_inf_l, 0)
                if common.gopts.gen == "epr_strict":
                    forceMinimize = True

        if nFailed == 0:
            if common.gopts.verbosity > 0:
                eprint(time_str(), "(unbounded induction checks passed)")
                print(time_str(), "(unbounded induction checks passed)")
            result = "safe"
            done = True
            eprint("Finite sorts (final): #%d" % len(p.system._fin2sort))
            for s_fin, s_inf in p.system._fin2sort.items():
                eprint("\t|%s| = %s" % (s_inf, len(p.system._enumsorts[s_fin])))
            print_sizes2(p, "finite-size-final")
            print_num_state_bits2(p, "total-state-bits-final", last_tsb)

            inv_full_inf = []
            for label, cl in inv_pruned_inf_l:
                if cl == p or cl in p.system.curr._prop:
                    inv_full_inf.insert(0, (label, cl))
                    continue
                inv_full_inf.append((label, cl))
            p.print_stats()
            pretty_print_inv(inv_full_inf, "Proof certificate")
            
            invName = "%s/%s.inv" % (common.gopts.out, common.gopts.name)
            eprint("\t(invariant file: %s)" % invName)
            print("\t(invariant file: %s)" % invName)
            common.gopts.invF = open(invName, "w")
            pretty_print_inv_file(common.gopts.invF, inv_full_inf)
            common.gopts.invF.close()
    
            inv_final = inv_full_inf
            invSz = len(inv_final)
            print_stat("sz-invariant-ic3", invSz)
            eprint(time_str(), "Property proved. Proof certificate of size %d" % len(inv_full_inf))
            if forceMinimize or (common.gopts.min == 1):
                eprint(time_str(), "Minimizing...")
                inv_minimized_inf, inv_optional_inf = p.minimize_invariant(inv_full_inf)
                inv_final = inv_minimized_inf
                eprint(time_str(), "Minimized proof certificate of size %d." % len(inv_minimized_inf))
                p.print_stats()
                pretty_print_inv(inv_minimized_inf, "Proof certificate (required)")
                if len(inv_optional_inf) != 0:
                    pretty_print_inv(inv_optional_inf, "Optional invariants", "_optional")
#                 p.print_smt2_set(inv_minimized)
            
            totalF = 0
            totalE = 0
            totalA = 0
            totalC = 0
            print("### Final proof certificate (stats): #%d" % (len(inv_final)))
            for label, f in inv_final:
                v = p.system.replaceDefinitions(f)
                outF, outE = count_quantifiers(v)
                outA = len(v.get_atoms())
                outC = len(flatten_and(v))
                totalF += outF
                totalE += outE
                totalA += outA
                totalC += outC
                print("invariant [%s] (%dF, %dE, %dA, %dC) \t%s" % (label, outF, outE, outA, outC, pretty_print_str(v)))
            print("###\n")
            print_stat("sz-invariant", totalC)
            print_stat("sz-invariant-forall", totalF)
            print_stat("sz-invariant-exists", totalE)
            print_stat("sz-invariant-atoms", totalA)
            
            p.system.stratify_invariant(inv_final)
            
            break
        elif inductCheck and (nFailed_ind == 0):
            eprint(time_str(), "(unbounded induction checks failed)")
            print(time_str(), "(unbounded induction checks failed)")
#             done = True
#             break
            
        
        reuse_set = set()
        
#             reuse_set = inv_pruned_inf
#             reuse_set = set()
#             for i in all_clauses:
#                 reuse_set.add(i.fsubstitute())
        if len(long_clauses) != 0:
            eprint(time_str(), "(removed %d long clauses)" % len(long_clauses))
            print(time_str(), "(removed %d long clauses)" % len(long_clauses))

        for label, cl in inv_set_inf_l:
            if cl not in long_clauses:
                reuse_set.add((label, cl))
            else:
                print("\t\t", end='')
                pretty_print(cl)

        inv_reusable_l = set()
        if common.gopts.reuse > 0:
            inv_reusable_l = p.reusable_invariant(reuse_set)
        
        p.print_stats()
        
        if common.gopts.mode == "updr":
            done = True
            eprint(time_str(), "updr failed. Property unknown. Giveup.")
            print(time_str(), "updr failed. Property unknown. Giveup.")
            break
        if iterationCount > 50:
            done = True
            eprint(time_str(), "Too many iterations. Property unknown. Giveup.")
            print(time_str(), "Too many iterations. Property unknown. Giveup.")
            break
        
        p.reset()
        
        minSz = -1
        min_s_inf = None
        for tt_fin, tt in p.system._fin2sort.items():
            p.system._sort2fin[tt] = tt_fin
            assert(tt_fin in p.system._enumsorts)
            ttSz = len(p.system._enumsorts[tt_fin])
            if (minSz == -1) or ttSz < minSz:
                min_s_inf = tt
                minSz = ttSz
        p.system._fin2sort.clear()
        
        if nFailed_ind != 0:
            eprint(time_str(), "(incremental SymIC3)")
            print(time_str(), "(incremental SymIC3)")
        else:
            if common.gopts.verbosity > 0:
                eprint(time_str(), "(unbounded checks failed due to base size being too small)")
                print(time_str(), "(unbounded checks failed due to base size being too small)")
            if (iterationCount == 1) and (len(long_clauses) != 0):
                if common.gopts.verbosity > 0:
                    eprint(time_str(), "(cleaning up clauses too specific to current size)")
                    print(time_str(), "(cleaning up clauses too specific to current size)")
                    eprint(time_str(), "(incremental SymIC3)")
                    print(time_str(), "(incremental SymIC3)")
            else:
                if inductCheck:
                    if False:
                        done = True
                        eprint(time_str(), "Property unknown. Giveup.")
                        print(time_str(), "Property unknown. Giveup.")
                        eprint(time_str(), "ic3po failed (hint: increase base size).")
                        print(time_str(), "ic3po failed (hint: increase base size).")
                        break
                    else:
                        if common.gopts.verbosity > 0:
                            eprint(time_str(), "(rerunning SymIC3 with increased base size)")
                            print(time_str(), "(rerunning SymIC3 with increased base size)")
                        
                    if forceReset:
                        inv_reusable_l.clear()
                        eprint(time_str(), "(cleanup)")
                        print(time_str(), "(cleanup)")
                else:
                    if len(p.system._sort2fin) > 1:
                        done = True
                        eprint(time_str(), "ic3po failed. Property unknown. Giveup.")
                        print(time_str(), "ic3po failed. Property unknown. Giveup.")
                        break
#                 p.system.set_finite_extend(True)
                for tt in p.system._sort2fin.keys():
                    if True or (tt == min_s_inf):
                        sz = p.system.extend_sort(tt, 1)
                        eprint(time_str(), "(extended |%s| to %d)" % (str(tt), sz))
                        print(time_str(), "(extended |%s| to %d)" % (str(tt), sz))
                    else:
                        sz = p.system.extend_sort(tt, 0)
        
        sys.stdout.flush()
        eprint()
        eprint("Finite sorts (step %d): #%d" % (iterationCount, len(p.system._sort2fin)))
        for tt, vals in p.system._sort2fin.items():
            eprint("\t|%s| = %s" % (tt, len(p.system._enumsorts[vals])))

        p.system.set_curr()
        helpers = set()
        for label, i in inv_reusable_l:
            cl = i.fsubstitute()
            helpers.add((label, cl))

        set_problem(p)
        set_solver(p)
    print_stat("result-ic3po", result)
    p.print_stats(print_stat)

if __name__ == "__main__":  
    args = sys.argv
    if len(args) != 2:
        print("Usage %s <file.smt2>" % args[0])
        exit(1)
    fname = args[1]
    backwardReach(fname)
