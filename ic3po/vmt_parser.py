# ------------------------------------------
# IC3PO: IC3 for Proving Protocol Properties
# ------------------------------------------
# Copyright (c) 2021  Aman Goel and Karem Sakallah, University of Michigan. 
# All rights reserved.
#
# Author: Aman Goel (amangoel@umich.edu), University of Michigan
# ------------------------------------------

from __future__ import print_function
import sys

from pysmt.smtlib.parser import SmtLibParser

from pysmt.shortcuts import Symbol, And, Or, EqualsOrIff, Not, Int, Ite, ForAll,\
    Function, Enum, UnsatCoreSolver, Exists, Implies, TRUE
from pysmt.typing import INT, BVType, EnumType, BOOL, FunctionType

from pysmt.environment import get_env

from utils import eprint, time_str, pretty_print_set, pretty_print, pretty_print_str, SORT_SUFFIX, flatten_and, num_majority, substituteDefinitions, parseSizes
from stratify import StratificationOracle
from syntax import SyntaxInference
import common
from pysmt.pretty_printer import pretty_serialize

class System():
    def __init__(self):
        self.reset()
    
    def reset(self):
        self._init = set()
        self._axiom = set()
        self._prop = set()
        self._vars = set()
        self._axiomvars = set()
        self._states = set()
        self._nexstates = set()
        self._globals = set()
        self._le = set()
        self._others = set()
        self._pre2nex = dict()
        self._nex2pre = dict()
        self._trel = None
        self._actions = list()
        self._action_en2idx = dict()
        self._predicates = dict()
        self._helpers = dict()
        self._infers = dict()
        self._definitions = dict()
        self._definitionMap = dict()
    
    def copy(self, rhs):
        self._init = rhs._init
        self._axiom = rhs._axiom
        self._prop = rhs._prop
        self._vars = rhs._vars
        self._axiomvars = rhs._axiomvars
        self._states = rhs._states
        self._nexstates = rhs._nexstates
        self._globals = rhs._globals
        self._le = rhs._le
        self._others = rhs._others
        self._pre2nex = rhs._pre2nex
        self._nex2pre = rhs._nex2pre
        self._trel = rhs._trel
        self._actions = rhs._actions
        self._action_en2idx = rhs._action_en2idx
        self._predicates = rhs._predicates
        self._helpers = rhs._helpers
        self._infers = rhs._infers
        self._definitions = rhs._definitions
        self._definitionMap = rhs._definitionMap
        
    def add_helper(self, formula, name):
        self._helpers[formula] = "user_" + name

    def add_pred(self, formula, name):
        args = []
        types = []
        if formula.is_quantifier():
            for a in formula.quantifier_vars():
                args.append(a)
                types.append(a.symbol_type())
            formula = formula.arg(0)
        ft = FunctionType(BOOL, tuple(types))
        f = Symbol(name, ft)
        lhs = Function(f, args)
        self._predicates[lhs] = formula

    def add_init(self, formula):
        self._init.add(formula)

    def add_axiom(self, formula):
        if (formula.is_and()):
            for f in formula.args():
                self._axiom.add(f)
        else:
            self._axiom.add(formula)

    def add_definition(self, formula, name):
        self._definitions[name] = formula

    def add_prop(self, formula):
        clauses = flatten_and(formula)
        for cl in clauses:
            self._prop.add(cl)

    def add_state(self, formula, fnex):
        if formula.is_function_application():
            pre = formula.function_name()
        else:
            pre = formula
        self._states.add(pre)
        nex = Symbol(fnex, pre.symbol_type())
        self._nexstates.add(nex)
        self._pre2nex[pre] = nex
        self._nex2pre[nex] = pre

    def add_global_state(self, formula):
        if formula.is_function_application():
            pre = formula.function_name()
            pret = pre.symbol_type()
            paramt = pret.param_types
            if (len(paramt) == 2 
                and pret.return_type.is_bool_type()
                and paramt[0] == paramt[1]
                ):
                name_pre = str(pre)
                if name_pre == "le" or name_pre.endswith(".le"):
                    self.add_le_state(pre)
        else:
            pre = formula
        self._globals.add(pre)
        self._states.add(pre)
        self._nexstates.add(pre)

    def add_le_state(self, pre):
        self._le.add(pre)
            
    def is_ordered_state(self, s):
        res = s in self._le
        return res
            
    def add_other(self, formula):
        self._others.add(formula)
        
    def add_var(self, formula):
        pre = formula
#         if not(pre in self._nex2pre):
        self._vars.add(pre)
#             if not(pre in self._pre2nex):
#                 pre_s = pre.symbol_name()
#                 if pre_s.startswith("__"):
#                     fnex = pre_s[2:]
#                 else:
#                     fnex = pre_s + "$next"
#                 nex = Symbol(fnex, pre.symbol_type())
#                 self._pre2nex[pre] = nex
#                 self._nex2pre[nex] = pre
    
    def action_noop(self):
        f = dict()
        for s in self._states:
            if s in self._pre2nex:
                n = self._pre2nex[s]
                
                s_type = s.symbol_type()
                
                args = []
                if s_type.is_function_type():
                    i = 0
                    for paramt in s_type.param_types:
                        i += 1
                        paramt_name = str(i) + ":" + str(paramt) 
                        args.append(Symbol(paramt_name, paramt))
                lhs = Function(s, args)
                rhs = Function(n, args)
                eq = ForAll(args, EqualsOrIff(lhs, rhs))
                f[n] = eq
        return f
        
    def noop_name(self):
        return "noop"
    
    def is_noop(self, name):
        return name == self.noop_name()

    def input_action_name(self):
        return "__input_action_"
        
    def get_action_noop(self):
        noop = self.action_noop()
        name = self.noop_name()
        return (name, noop)
    
    def add_action_noop(self):
        name, noop = self.get_action_noop()
        formula = And([i for i in noop.values()])
        self.add_action(formula, name)
        return noop

    def add_action(self, formula, name):
        if name in self._actions:
            assert(0)
        action = formula
        if action.is_exists():
            qvars = action.quantifier_vars()
            for v in qvars:
                self.add_var(v)
                self.add_other(v)
            action = action.arg(0)
        self._actions.append([action, name, None])

#     def get_axiom_vars(self):
#         axiom_vars = set()
#         if len(self._axiom) != 0:
#             av = And(self._axiom).get_free_variables()
#             for v in av:
#                 axiom_vars.add(v)
#         return axiom_vars
    
    def add_trel(self):
        eprint("\t(found #%d actions)" % len(self._actions))
        print("\t(found #%d actions)" % len(self._actions))
        if len(self._actions) == 0:
            eprint("\t(error: no action found)")
            print("\t(error: no action found)")
            assert(0)
        if len(self._axiom) != 0:
            ax = And(self._axiom)
            axvar = ax.get_free_variables()
            for v in axvar:
                self._axiomvars.add(v)

        noop_name, noop = self.get_action_noop()
        noop_all = And([i for i in noop.values()])
        self._trel = noop_all
        self._input_action = Symbol(self.input_action_name(), INT)
        self.add_var(self._input_action)
#         axiom_vars = self.get_axiom_vars()
#         action_en = []
#         self.add_action(noop_all, noop_name)
        for idx, f in enumerate(self._actions):
            action = f[0]
            action_name = f[1]
#             action_vars = axiom_vars.copy()
#             for v in action.get_free_variables():
#                 action_vars.add(v)
            action_vars = action.get_free_variables()
            qvars = None
            if action.is_exists():
                qvars = action.quantifier_vars()
                action = action.arg(0)
            action_all = [action]
            missing_nex = [] 
            for n in self._nex2pre.keys():
                if n not in action_vars:
                    if str(n) not in self._definitions:
                        if True or (str(n) != "choosable"):
                            action_all.append(noop[n])
                            missing_nex.append(n)
            if len(missing_nex) != 0:
                print("adding #%d noops to action %s" % (len(missing_nex), f[1]))
                for n in missing_nex:
                    print("\tnoop(%s)" % n)
            action = And(action_all)
            if qvars != None:
                action = Exists(qvars, action)
            self._actions[idx][0] = action
            
#             self._trel = Or(action, self._trel)

            action_symbol = Int(idx)
            self._actions[idx][-1] = action_symbol
            cond = EqualsOrIff(self._input_action, action_symbol)
            self._trel = Ite(cond, action, self._trel)
            
#             action_symbol = Symbol("en_"+action_name)
#             action_en.append(action_symbol)
#             self._trel = Ite(action_symbol, action, self._trel)
        
#         action_cond = []
#         action_cond.append(self._trel)
#         for i in range(len(action_en)-1):
#             fi = Not(action_en[i])
#             for j in range(i+1, len(action_en)):
#                 fj = Not(action_en[j])
#                 cond = Or(fi, fj)
#                 action_cond.insert(0, cond)
#         self._trel = And(action_cond)
            
#         if len(self._axiom) != 0:
#             q = []
#             q.extend(self._axiom)
# #             self.add_init(And(q))
#             q.append(self._trel)
#             self._trel = And(q)
            
        self.add_action(noop_all, noop_name)
        
    def add_trel_new(self):
        eprint("\t(found #%d actions)" % len(self._actions))
        print("\t(found #%d actions)" % len(self._actions))
        if len(self._actions) == 0:
            eprint("\t(error: no action found)")
            print("\t(error: no action found)")
            assert(0)
        if len(self._axiom) != 0:
            ax = And(self._axiom)
            axvar = ax.get_free_variables()
            for v in axvar:
                self._axiomvars.add(v)

        tcond = []
        enVar = []
        enOr = []
        noop = self.add_action_noop()
        
        for idx, f in enumerate(self._actions):
            action = f[0]
            action_name = f[1]
            action_vars = action.get_free_variables()
            
            en = Symbol("en_"+action_name, BOOL)
            self._action_en2idx[en] = idx
            enVar.append(en)
            
            qvars = None
            if action.is_exists():
                qvars = action.quantifier_vars()
                action = action.arg(0)

            action_all = [action]
            missing_nex = [] 
            for n in self._nex2pre.keys():
                if n not in action_vars:
                    if str(n) not in self._definitions:
                        if True or (str(n) != "choosable"):
                            action_all.append(noop[n])
                            missing_nex.append(n)
            if len(missing_nex) != 0:
                print("adding #%d noops to action %s" % (len(missing_nex), f[1]))
                for n in missing_nex:
                    print("\tnoop(%s)" % n)
            action = And(action_all)
            if qvars != None:
                action = Exists(qvars, action)
                
            self._actions[idx][0] = action
            self._actions[idx][2] = en
            
            cond = Implies(en, action)
            tcond.append(cond)
            enOr.append(en)
        
        cond = Or(enOr)
        tcond.append(cond)
        for i in range(len(enVar)-1):
            ei = enVar[i]
            for j in range(i+1, len(enVar)):
                assert(i != j)
                ej = enVar[j]
                cond = Or(Not(ei), Not(ej))
                tcond.append(cond)
        self._trel = And(tcond)
        
    def __str__(self):
        res = []
        res.append("-----------------------------------------------------------------")
        res.append("\nInit #")
        res.append(str(len(self._init)) + "\n")
        for f in self._init:
            res.append("\t" + str(f) + "\n\t\twith variables %s\n" % f.get_free_variables())
        res.append("\nAxioms #")
        res.append(str(len(self._axiom)) + "\n")
        for f in self._axiom:
            res.append("\t" + f.serialize() + "\n\t\twith variables %s\n" % f.get_free_variables())
        res.append("\nActions #")
        res.append(str(len(self._actions)) + "\n")
        for idx, f in enumerate(self._actions):
            res.append("\t" + str(idx) + ":\t" + f[1] + " (en: " + str(f[2]) + ")\t" + str(f[0]) + "\n\t\twith variables %s\n" % f[0].get_free_variables())
        res.append("\nProperties #")
        res.append(str(len(self._prop)) + "\n")
        for f in self._prop:
            res.append("\t" + str(f) + "\n\t\twith variables %s\n" % f.get_free_variables())
        res.append("\nVariables #")
        res.append(str(len(self._vars)) + "\n")
        for f in self._vars:
            res.append("\t" + str(f) + " of type %s\n" % f.symbol_type())
        res.append("\nState variables #")
        res.append(str(len(self._states)) + "\n")
        for f in self._states:
            res.append("\t" + str(f) + " of type %s\n" % f.symbol_type())
        res.append("\nNex state variables #")
        res.append(str(len(self._nexstates)) + "\n")
        for f in self._nexstates:
            res.append("\t" + str(f) + " of type %s\n" % f.symbol_type())
        res.append("\nGlobal variables #")
        res.append(str(len(self._globals)) + "\n")
        for f in self._globals:
            res.append("\t" + str(f) + " of type %s\n" % f.symbol_type())
        res.append("\nOrdered variables #")
        res.append(str(len(self._le)) + "\n")
        for f in self._le:
            res.append("\t" + str(f) + " of type %s\n" % f.symbol_type())
        res.append("\nNex to pre #")
        res.append(str(len(self._nex2pre)) + "\n")
        for nex, pre in self._nex2pre.items():
            res.append("\t" + str(nex) + " <- " + str(pre) + "\n")
        res.append("\nPre to nex #")
        res.append(str(len(self._pre2nex)) + "\n")
        for pre, nex in self._pre2nex.items():
            res.append("\t" + str(pre) + " -> " + str(nex) + "\n")
        res.append("\nOther variables #")
        res.append(str(len(self._others)) + "\n")
        for f in self._others:
            res.append("\t" + str(f) + " of type %s\n" % f.symbol_type())
        res.append("\nAxiom variables #")
        res.append(str(len(self._axiomvars)) + "\n")
        for f in self._axiomvars:
            res.append("\t" + str(f) + "\n")
        res.append("\nPredicates #")
        res.append(str(len(self._predicates)) + "\n")
        for k, v in self._predicates.items():
            res.append("\t%s := %s\n\t\twith variables %s\n" % (str(k), str(v), v.get_free_variables()))
        res.append("\nHelpers #")
        res.append(str(len(self._helpers)) + "\n")
        for k, v in self._helpers.items():
            res.append("\t%s := %s\n\t\twith variables %s\n" % (str(v), str(k), k.get_free_variables()))
        res.append("\nInferences #")
        res.append(str(len(self._infers)) + "\n")
        for k, v in self._infers.items():
            res.append("\t%s := %s\n\t\twith variables %s\n" % (str(v), str(k), k.get_free_variables()))
        res.append("\nDefinitions #")
        res.append(str(len(self._definitions)) + "\n")
        for k, v in self._definitions.items():
            res.append("\t%s := %s\n\t\twith variables %s\n" % (str(k), str(v), v.get_free_variables()))
        res.append("\nDefinition Map #")
        res.append(str(len(self._definitionMap)) + "\n")
        for k, v in self._definitionMap.items():
            res.append("\t%s := %s\n\t\twith variables %s\n" % (str(k), str(v[0]), v[-1]))
        res.append("\nTrel:\n%s\n" % (self._trel.serialize()))
        res.append("-----------------------------------------------------------------")
        return "".join(res)

    
class TransitionSystem(SmtLibParser):
    """Handles and stores the transition system"""
    def __init__(self, env=None, interactive=False):
        self._parser = SmtLibParser()
        SmtLibParser.__init__(self, env, interactive)        
        
        self.orig = System()
        self.curr = System()
        
        self.strat = StratificationOracle()
        self.syntax = SyntaxInference()
        
        self._sorts = set()
        self._sort2fin = dict()
        self._enumsorts = dict()
        self._enum2qvar = dict()
        self._fin2sort = dict()
        self._enum2inf = dict()
        
        self._ordered_sorts = dict()
        self._ordered_min = dict()
        self._ordered_first = dict()
        self._ordered_max = dict()
        self._dependency_height = dict()
        self._enum_height = dict()

        self._quorums_symbols = set()
        self._quorums_sorts = dict()
        self._quorums_consts = dict()
        self._quorums_parent = set()
        self._quorums_child = set()

        self.dependent_sort_en = True
        self._child_sort = set()
        self._parent_sort = dict()
        
        self._idx = 0
        self.gen = common.gopts.gen
        
        self.modified = set()
        

    def set_curr(self):
        self.curr.copy(self.orig)
        self.finitize()
        self.process_enums()
#         print(self.curr)
    
    def reset_ordered_sort(self):
        self._ordered_sorts = dict()
        self._ordered_min = dict()
        self._ordered_first = dict()
        self._ordered_max = dict()
        
    def reset_quorums_sort(self):
        self._quorums_symbols = set()
        self._quorums_sorts = dict()
        self._quorums_consts = dict()
        self._quorums_parent = set()
        self._quorums_child = set()
    
    def is_quorum_symbol(self, s):
        return s in self._quorums_symbols
        
    def get_ordered_zero(self):
        self.zero = None
        self.firste = None
        self.le = None
        res = []
                
        for pre in self.curr._le:
            pret = pre.symbol_type()
            orderedt = pret.param_types[0]
            if orderedt in self._enumsorts:
                self._ordered_sorts[orderedt] = pre
                self.le = pre
                domain = self._enumsorts[orderedt]
#                 end = 2
                end = len(domain)
                for i in range(end):
                    for j in range(i, end):
                        arg1 = domain[i]
                        arg2 = domain[j]
                        rel1 = Function(pre, [arg1, arg2])
                        rel2 = Function(pre, [arg2, arg1])
                        if (i == j):
                            res.append(rel1)
                        elif (i < j):
                            res.append(rel1)
                            res.append(Not(rel2))
                        elif (i > j):
                            res.append(Not(rel1))
                            res.append(rel2)
                        else:
                            assert(0)
                            
        for g in self.curr._globals:
            gt = g.symbol_type()
            gstr = pretty_print_str(g)
            if gt not in self._ordered_sorts:
                continue
            if gstr == "zero" or gstr == "negone":
                gt = g.symbol_type()
                assert(gt in self._enumsorts)
                domain = self._enumsorts[gt]
                eq = EqualsOrIff(g, domain[0])
                res.append(eq)
                self.zero = (domain[0], g)
            elif gstr == "firste":
                gt = g.symbol_type()
                assert(gt in self._enumsorts)
                domain = self._enumsorts[gt]
                eq = EqualsOrIff(g, domain[1])
                res.append(eq)
                self.firste = (domain[1], g)
                
        if len(res) == 0:
            return TRUE()
        else:
            print("\nZero axiom: ")
            for v in res:
                print("\t", end="")
                pretty_print(v)
            return And(res)
                
    
    def get_ordered_le(self):
        self.reset_ordered_sort()
        res = []
        
        for pre in self.curr._le:
            pret = pre.symbol_type()
            orderedt = pret.param_types[0]
            if orderedt in self._enumsorts:
                self._ordered_sorts[orderedt] = pre
                domain = self._enumsorts[orderedt]
                for i in range(len(domain)):
                    for j in range(i, len(domain)):
                        arg1 = domain[i]
                        arg2 = domain[j]
                        rel1 = Function(pre, [arg1, arg2])
                        rel2 = Function(pre, [arg2, arg1])
                        if (i == j):
                            res.append(rel1)
                        elif (i < j):
                            res.append(rel1)
                            res.append(Not(rel2))
                        elif (i > j):
                            res.append(Not(rel1))
                            res.append(rel2)
                        else:
                            assert(0)
                            
#                 for i in range(len(domain)-1, 0, -1):
#                     arg1 = domain[i]
#                     arg2 = domain[i-1]
#                     rel = Function(pre, [arg1, arg2])
#                     res.append(Not(rel))

        for g in self.curr._globals:
            gt = g.symbol_type()
            if gt not in self._ordered_sorts:
                continue
            gstr = pretty_print_str(g)
            print(gstr)
            if gstr == "zero" or gstr == "negone":
                gt = g.symbol_type()
                if gt in self._enumsorts:
                    self._ordered_min[gt] = g
                    assert(gt in self._enumsorts)
                    domain = self._enumsorts[gt]
                    eq = EqualsOrIff(g, domain[0])
                    res.append(eq)
            elif gstr == "max":
                gt = g.symbol_type()
                if gt in self._enumsorts:
                    self._ordered_max[gt] = g
                    assert(gt in self._enumsorts)
                    domain = self._enumsorts[gt]
                    eq = EqualsOrIff(g, domain[-1])
                    res.append(eq)
            elif gstr == "firste":
                gt = g.symbol_type()
                if gt in self._enumsorts:
                    self._ordered_first[gt] = g
                    
        if len(res) == 0:
            return TRUE()
        else:
            print("\nOrdering axiom: ")
            for v in res:
                print("\t", end="")
                pretty_print(v)
            return And(res)
    
    def get_quorum_axiom(self):
        self.reset_quorums_sort()
        res = []
        pre = None
        for g in self.curr._globals:
            name = str(g)
            if name.startswith("member:"):
                pre = g
                break
        if pre != None:
            pret = pre.symbol_type()
            assert(len(pret.param_types) == 2)
            tA = pret.param_types[0]
            tQ = pret.param_types[1]
            
            if tA in self._enumsorts and tQ in self._enumsorts:
                domainA = self._enumsorts[tA]
                domainQ = self._enumsorts[tQ]
                if not str(tQ).startswith("quorum:"):
                    return TRUE()
                
                qMap = {}

                if (len(domainA) == 1) and (len(domainQ) == 1):
                    qMap[0] = set([0])
                elif (len(domainA) == 2) and (len(domainQ) == 1):
                    qMap[0] = set([0, 1])
                elif (len(domainA) == 3) and (len(domainQ) == 3):
                    qMap[0] = set([0, 1])
                    qMap[1] = set([0, 2])
                    qMap[2] = set([1, 2])
                elif (len(domainA) == 4) and (len(domainQ) == 4):
                    qMap[0] = set([0, 1, 2])
                    qMap[1] = set([0, 1, 3])
                    qMap[2] = set([0, 2, 3])
                    qMap[3] = set([1, 2, 3])
                elif (len(domainA) == 5) and (len(domainQ) == 10):
                    qMap[0] = set([0, 1, 2])
                    qMap[1] = set([0, 1, 3])
                    qMap[2] = set([0, 1, 4])
                    qMap[3] = set([0, 2, 3])
                    qMap[4] = set([0, 2, 4])
                    qMap[5] = set([0, 3, 4])
                    qMap[6] = set([1, 2, 3])
                    qMap[7] = set([1, 2, 4])
                    qMap[8] = set([1, 3, 4])
                    qMap[9] = set([2, 3, 4])
                elif (len(domainA) == 6) and (len(domainQ) == 15):
                    qMap[0] = set([0, 1, 2, 3])
                    qMap[1] = set([0, 1, 2, 4])
                    qMap[2] = set([0, 1, 2, 5])
                    qMap[3] = set([0, 1, 3, 4])
                    qMap[4] = set([0, 1, 3, 5])
                    qMap[5] = set([0, 1, 4, 5])
                    qMap[6] = set([0, 2, 3, 4])
                    qMap[7] = set([0, 2, 3, 5])
                    qMap[8] = set([0, 2, 4, 5])
                    qMap[9] = set([0, 3, 4, 5])
                    qMap[10] = set([1, 2, 3, 4])
                    qMap[11] = set([1, 2, 3, 5])
                    qMap[12] = set([1, 2, 4, 5])
                    qMap[13] = set([1, 3, 4, 5])
                    qMap[14] = set([2, 3, 4, 5])
                else:
                    print("Sort dependency mismatch: check size relation between %s and %s" % (str(tA), str(tQ)))
                    assert(0)
                
                self._quorums_symbols.add(pre)
                self._quorums_sorts[tQ] = (pre, tA)
                self._quorums_consts[tQ] = dict()
                self._quorums_parent.add(tQ)
                self._quorums_child.add(tA)
                
                for k, v in qMap.items():
                    arg2 = domainQ[k]
                    self._quorums_consts[tQ][k] = set()
                    for j in range(len(domainA)):
                        arg1 = domainA[j]
                        rel = Function(pre, [arg1, arg2])
                        val = j in v
                        if val:
                            res.append(rel)
                            self._quorums_consts[tQ][k].add(j)
                        else:
                            res.append(Not(rel))
        if len(res) == 0:
            return TRUE()
        else:
            print("\nQuorum axiom: ")
            for v in res:
                print("\t", end="")
                pretty_print(v)
            return And(res)
        
    def finitize(self):
        get_env().fsubstituter.set_ssubs(self._sort2fin, self._idx, False)

        self.curr._init = set()
        for v in self.orig._init:
            self.curr._init.add(v.fsubstitute())
            
        self.curr._axiom = set()
        for v in self.orig._axiom:
            self.curr._axiom.add(v.fsubstitute())
            
        self.curr._prop = set()
        for v in self.orig._prop:
            self.curr._prop.add(v.fsubstitute())
            
        self.curr._trel =  self.orig._trel.fsubstitute()
        
        self.curr._actions = list()
        for v in self.orig._actions:
            self.curr._actions.append([v[0].fsubstitute(), v[1], v[2].fsubstitute()])
        
        self.curr._action_en2idx = dict()
        for l, r in self.orig._action_en2idx.items():
            self.curr._action_en2idx[l.fsubstitute()] = r
            
        self.curr._vars = set()
        for v in self.orig._vars:
            self.curr._vars.add(v.fsubstitute())
            
        self.curr._axiomvars = set()
        for v in self.orig._axiomvars:
            self.curr._axiomvars.add(v.fsubstitute())
            
        self.curr._states = set()
        for v in self.orig._states:
            self.curr._states.add(v.fsubstitute())
            
        self.curr._nexstates = set()
        for v in self.orig._nexstates:
            self.curr._nexstates.add(v.fsubstitute())
            
        self.curr._globals = set()
        for v in self.orig._globals:
            self.curr._globals.add(v.fsubstitute())
            
        self.curr._le = set()
        for v in self.orig._le:
            self.curr._le.add(v.fsubstitute())
            
        self.curr._others = set()
        for v in self.orig._others:
            self.curr._others.add(v.fsubstitute())
            
        self.curr._pre2nex = dict()
        for l, r in self.orig._pre2nex.items():
            self.curr._pre2nex[l.fsubstitute()] = r.fsubstitute()
            
        self.curr._nex2pre = dict()
        for l, r in self.orig._nex2pre.items():
            self.curr._nex2pre[l.fsubstitute()] = r.fsubstitute()
            
        self.curr._predicates = dict()
        for l, r in self.orig._predicates.items():
            self.curr._predicates[l.fsubstitute()] = r.fsubstitute()
            
        self.curr._helpers = dict()
        for l, r in self.orig._helpers.items():
            self.curr._helpers[l.fsubstitute()] = r
            
        self.curr._infers = dict()
        for l, r in self.orig._infers.items():
            self.curr._infers[l.fsubstitute()] = r
            
        self.curr._definitions = dict()
        for l, r in self.orig._definitions.items():
            self.curr._definitions[l] = r.fsubstitute()

        self.curr._definitionMap = dict()
        for l, r in self.orig._definitionMap.items():
            argsNew = []
            for a in r[-1]:
                argsNew.append(a.fsubstitute())
            self.curr._definitionMap[l.fsubstitute()] = [r[0].fsubstitute(), r[1].fsubstitute(), argsNew]

        self.syntax.substitute(self.curr)
        self._idx += 1
        
    def infinitize(self):
        get_env().fsubstituter.set_ssubs(self._fin2sort, self._idx, True)

        self.tmp = System()
        self.tmp.copy(self.curr)
        self.curr.reset()
        
        self.curr._init = set()
        for v in self.tmp._init:
            self.curr._init.add(v.fsubstitute())
            
        self.curr._axiom = set()
        for v in self.tmp._axiom:
            self.curr._axiom.add(v.fsubstitute())
            
        self.curr._prop = set()
        for v in self.tmp._prop:
            self.curr._prop.add(v.fsubstitute())
            
        self.curr._trel =  self.tmp._trel.fsubstitute()
        
        self.curr._actions = list()
        for v in self.tmp._actions:
            self.curr._actions.append([v[0].fsubstitute(), v[1], v[2].fsubstitute()])
        
        self.curr._action_en2idx = dict()
        for l, r in self.tmp._action_en2idx.items():
            self.curr._action_en2idx[l.fsubstitute()] = r
        
        self.curr._vars = set()
        for v in self.tmp._vars:
            self.curr._vars.add(v.fsubstitute())
            
        self.curr._axiomvars = set()
        for v in self.tmp._axiomvars:
            self.curr._axiomvars.add(v.fsubstitute())
            
        self.curr._states = set()
        for v in self.tmp._states:
            self.curr._states.add(v.fsubstitute())
            
        self.curr._nexstates = set()
        for v in self.tmp._nexstates:
            self.curr._nexstates.add(v.fsubstitute())
            
        self.curr._globals = set()
        for v in self.tmp._globals:
            self.curr._globals.add(v.fsubstitute())
            
        self.curr._le = set()
        for v in self.tmp._le:
            self.curr._le.add(v.fsubstitute())
            
        self.curr._others = set()
        for v in self.tmp._others:
            self.curr._others.add(v.fsubstitute())
            
        self.curr._pre2nex = dict()
        for l, r in self.tmp._pre2nex.items():
            self.curr._pre2nex[l.fsubstitute()] = r.fsubstitute()
            
        self.curr._nex2pre = dict()
        for l, r in self.tmp._nex2pre.items():
            self.curr._nex2pre[l.fsubstitute()] = r.fsubstitute()
            
        self.curr._predicates = dict()
        for l, r in self.tmp._predicates.items():
            self.curr._predicates[l.fsubstitute()] = r.fsubstitute()
            
        self.curr._helpers = dict()
        for l, r in self.tmp._helpers.items():
            self.curr._helpers[l.fsubstitute()] = r
            
        self.curr._infers = dict()
        for l, r in self.tmp._infers.items():
            self.curr._infers[l.fsubstitute()] = r
            
        self.curr._definitions = dict()
        for l, r in self.tmp._definitions.items():
            self.curr._definitions[l] = r.fsubstitute()

        self.curr._definitionMap = dict()
        for l, r in self.tmp._definitionMap.items():
            argsNew = []
            for a in r[-1]:
                argsNew.append(a.fsubstitute())
            self.curr._definitionMap[l.fsubstitute()] = [r[0].fsubstitute(), r[1].fsubstitute(), argsNew]

        self.syntax.substitute(self.curr)

    def add_sort(self, inf, size):
        self._sorts.add(inf)
        sz = int(size)
        if common.gopts.mode == "updr":
            return
        if sz and sz > 0:
            enum = []
            suffix = SORT_SUFFIX + str(self._idx) + ":"
            for i in range(sz):
                name = str(inf) + ":f" + str(i)
                val = Symbol(name, inf)
                enum.append(str(inf) + suffix + str(i))
            enumname = str(inf) + suffix
            enumsort = EnumType(enumname,  enum)
            
            enumvals = []
            enumqvar = []
            for name in enum:
                val = Enum(name, enumsort)
                enumvals.append(val)
                name = "Q:" + name                
                qv = Symbol(name, enumsort)
                enumqvar.append(qv)
            self._enum2qvar[enumsort] = enumqvar
            self._enumsorts[enumsort] = enumvals
            
            self._sort2fin[inf] = enumsort
            self._enum2inf[enumsort] = inf
            print("(enumsort) %s <-> %s" % (inf, enumsort))
            print("\t%s <-> %s" % (pretty_print_set(enumqvar), pretty_print_set(enumvals)))
            
#             print(enumsort.is_enum_type())
#             e = []
#             n = 3
#             for i in range(n):
#                 ei = Enum(str(inf) + ":enum" + str(i), enumsort)
#                 e.append(ei)
#             solver = UnsatCoreSolver(name="z3")
#             for i in range(n-1):
#                 for j in range(i+1, n):
#                     if i != j:
#                         eq = EqualsOrIff(e[i], e[j])
#                         solver.add_assertion(Not(eq))
#             res = solver.check_sat()
#             print(res)
#             model = solver.get_model()
#             print(model)
#             assert(0)

    def extend_sort(self, inf, increment):
        enumsort = self._sort2fin[inf]
        oldsz = len(self._enumsorts[enumsort])
        if inf in self._child_sort:
            return oldsz
        self._enumsorts.pop(enumsort, None)
        self._enum2qvar.pop(enumsort, None)
        self._sort2fin.pop(inf, None)
        self.add_sort(inf, oldsz+increment)
        if (inf in self._parent_sort):
            child = self._parent_sort[inf]
            if child not in self._sort2fin:
                print("Error: dependent sort mismatch for %s -> %s" % (inf, child))
                assert(0)
            enumsort_child = self._sort2fin[child]
            self._enumsorts.pop(enumsort_child, None)
            self._enum2qvar.pop(enumsort_child, None)
            self._sort2fin.pop(child, None)
            parent_sz = oldsz + increment
            child_sz = num_majority(parent_sz)
            self.add_sort(child, child_sz)
        return oldsz+increment

    def unbound_sort(self, inf):
        enumsort = self._sort2fin[inf]
#         self._enumsorts.pop(enumsort)
#         self._enum2qvar.pop(enumsort)
        self._sort2fin.pop(inf)
        self._fin2sort[enumsort] = inf
        print("sort: %s <-> unbounded" % (inf))
    
    def allowed_arc(self, lhs, rhs):
        if lhs in self._enumsorts:
            lhs = self._enum2inf[lhs]
        if rhs in self._enumsorts:
            rhs = self._enum2inf[rhs]
        return self.strat.allowed_arc(lhs, rhs)
    
    def is_epr(self):
        return self.strat.is_epr()
    
    def replaceDefinitions(self, formula, mode=0):
#        print("orig: %s" % pretty_serialize(formula))
        f = substituteDefinitions(formula, self.curr._definitionMap, mode)
#        print("new : %s" % pretty_serialize(f))
        return f
    
    def stratify(self):
        print("\nstratifying state variables:")
        for f in self.orig._states:
            ft = f.symbol_type()
            if ft.is_function_type():
                rt = ft.return_type
                if rt != BOOL:
                    for paramt in ft.param_types:
                        self.strat.update_stratify_function(paramt, rt)
                
        print("\nstratifying axioms:")
        for v in self.orig._axiom:
            f = self.replaceDefinitions(v)
#             print("%s" % pretty_serialize(f))
            self.strat.update_stratify(f)
        for v in self.orig._actions:
            print("\nstratifying action %s:" % v[1])
            f = self.replaceDefinitions(v[0])
#             print("%s" % pretty_serialize(f))
            self.strat.update_stratify(f)
        print("\nstratifying property:")
        for v in self.orig._prop:
            f = self.replaceDefinitions(v)
#             print("%s" % pretty_serialize(f))
            print("    pos:")
            self.strat.update_stratify(f)
            print("    neg:")
            self.strat.update_stratify(Not(f))

        if not self.strat.has_exists:
            print("\t(no exists detected)")
            eprint("\t(no exists detected)")
        print("\t(epr: %s)" % self.is_epr())
        eprint("\t(epr: %s)" % self.is_epr())

        print("\nstratifying helpers:")
        for v in self.orig._helpers.keys():
            f = self.replaceDefinitions(v)
#             print("%s" % pretty_serialize(f))
            self.strat.update_stratify(f)
        
        self.strat.print_all_arcs()
        print("-----------------------------------------------------------------")
        
        if self.gen == "auto":
            self.gen = "prefer_epr"
            if not self.strat.has_exists:
                self.gen = "epr_strict"
            elif self.is_epr():
                self.gen = "epr_strict"
        print("\t(gen: %s)" % self.gen)
        eprint("\t(gen: %s)" % self.gen)
        print("-----------------------------------------------------------------")
    
    def stratify_invariant(self, inv_set_l):
        print("\nstratifying inductive invariant:")
        for label, v in inv_set_l:
            f = self.replaceDefinitions(v)
#             print("%s" % pretty_serialize(f))
            print("  %s:" % label)
            print("    pos:")
            self.strat.update_stratify(f)
            print("    neg:")
            self.strat.update_stratify(Not(f))

        if not self.strat.has_exists:
            print("\t(with inv: no exists detected)")
            eprint("\t(with inv: no exists detected)")
        print("\t(with inv: epr: %s)" % self.is_epr())
        eprint("\t(with inv: epr: %s)" % self.is_epr())

        self.strat.print_all_arcs()
        print("-----------------------------------------------------------------")
        
    def syntax_infer(self):
        print("\nPerforming syntax-guided inference:")
        self.syntax.infer()
        print("\nStratifying inferences:")
        for k in self.orig._infers.keys():
            self.strat.update_stratify(k)
        self.strat.print_all_arcs()
        if len(self.orig._infers) != 0:
            eprint("\t(adding %d syntax inferences)" % len(self.orig._infers))
        print("-----------------------------------------------------------------")
    
    def is_finite(self):
        for tt in self._sorts:
            if tt not in self._sort2fin:
                return False
        return True

    def set_enum_height(self, x, i):
        self._enum_height[x] = i

    def set_dependency_height(self, x, useMap):
        h = 1
        useSet = set()
        if x in useMap:
            useSet = useMap[x]
        if len(useSet) != 0:
            for y in useSet:
                yh = self.set_dependency_height(y, useMap)
                if (yh > h):
                    h = yh
            h += 1
        if x in self.orig._definitionMap:
#             h = (h+1) * (1+len(self.orig._definitionMap[x][-1]))
#             h = 0
            pass
        elif x in self.orig._vars:
            h = 1000
#         h = 0
        self._dependency_height[str(x)] = h
        return h
    
    def preprocess_definitions(self):
        if len(self.orig._definitions) != 0:
            eprint("\t(found #%d definitions)" % len(self.orig._definitions))
            
            print("Definitions #%s" % len(self.orig._definitions))
            for k, v in self.orig._definitions.items():
                print("\t%s := %s\n\t\twith variables %s" % (str(k), str(v), v.get_free_variables()))
            
            for k, v in self.orig._definitions.items():
                rel = None
                args = []
                lhs = None
                rhs = None
                formula = v
                if formula.is_forall():
#                     qvars = formula.quantifier_vars()
#                     for qv in qvars:
#                         args.append(qv)
                    formula = formula.arg(0)
                if formula.is_iff() or formula.is_equals():
                    lhs = formula.arg(0)
                    rhs = formula.arg(1)
                    
                    if rhs.is_function_application():
                        if str(rhs.function_name()) == k:
                            lhs, rhs = rhs, lhs
                    elif rhs.is_symbol():
                        lhs, rhs = rhs, lhs
                    rel = lhs 

#                     print("rel: %s" % rel)
#                     print("args: %s" % args)
#                     print("lhs: %s" % lhs)
#                     print("rhs: %s" % rhs)
#                     print("sym: %s" % lhs.is_symbol())
                    if lhs.is_function_application():
                        rel = lhs.function_name()
                        for arg in lhs.args():
                            args.append(arg)
                    assert(str(rel) == k)
                assert(rel != None)
                assert(lhs != None)
                assert(rhs != None)
#                 print("rel: %s" % rel)
#                 print("args: %s" % args)
#                 print("lhs: %s" % lhs)
#                 print("rhs: %s" % rhs)
#                 assert(0)
                self.orig._definitionMap[rel] = [rhs, lhs, args]

            useMap = dict()
            for k, entry in self.orig._definitionMap.items():
                v = entry[0]
                freeVars = v.get_free_variables()
                freeVars = freeVars.difference(set(entry[-1]))
                for x in freeVars:
                    if x not in useMap:
                        useMap[x] = set()
                    if (x != k):
                        useMap[x].add(k)
#             print("useMap: ", useMap)
            for x in useMap.keys():
                self.set_dependency_height(x, useMap)
            for x in self.orig._states:
                if str(x) not in self._dependency_height:
                    self._dependency_height[str(x)] = 0
            for x in self.orig._nexstates:
                if str(x) not in self._dependency_height:
                    self._dependency_height[str(x)] = 0
            for lhs in sorted(self._dependency_height.keys(), key=lambda v: (self._dependency_height[v])):
                rhs = self._dependency_height[lhs]
                print("\tdep_height[%s] = %d" % (lhs, rhs))
    
    def postprocess_definitions(self):
        return
        if len(self.orig._definitions) != 0:
            print("\nConverting definitions to axioms")
            for k, v in self.orig._definitions.items():
                self.orig.add_axiom(v)
    
    def process_enums(self):
        self._enum_height = dict()
        idx = 0
        for k, v in self._enumsorts.items():
            for i, x in enumerate(v):
                self.set_enum_height(x, i + 100*idx)
#                 self.set_enum_height(x, i)
                print("\tdep_height[%s] = %d" % (pretty_print_str(x), self._enum_height[x]))
            idx += 1
    
    def print_modified(self):
        print("(modified) #%d" % len(self.modified))
        for v in self.modified:
            print("\t%s" % pretty_print_str(v))
    
    def get_dependency_priority(self, v, use_wires=False):
#         if v in self.modified:
#             return 0
        p = 1
        fv = v.get_free_variables()
        for w in fv:
            x = pretty_print_str(w)
            if x in self._dependency_height:
                h = self._dependency_height[x]
#                 wt = w.symbol_type()
#                 if wt.is_function_type():
#                     h *= (1+len(wt.param_types))
                if (h > p):
                    p = h
            else:
                p = 0
        
        e = 1
        fv = v.get_enum_constants()
        for w in fv:
            assert(w in self._enum_height)
            h = self._enum_height[w]
#             e += h
            if (h > e):
                e = h
#         e *= len(fv)

#         p = 0
#         e = 0
#         return (p, e)
        return p
    
    def set_sort_dependency(self):
        if self.dependent_sort_en:
            pre = None
            for g in self.orig._globals:
                name = str(g)
                if name == "member":
                    pre = g
                    break
            if pre != None:
                pret = pre.symbol_type()
                assert(len(pret.param_types) == 2)
                tA = pret.param_types[0]
                tQ = pret.param_types[1]
                
                if str(tQ) == "quorum":
                    self._parent_sort[tA] = tQ
                    self._child_sort.add(tQ)
                    print("\t(found sort dependency: %s -> %s)" % (tA, tQ))
        
    def read_ts(self, script_ss):
        script = self._parser.get_script(script_ss)
        ann = script.annotations.get_annotations()

        for f, amap in ann.items():
            for a, lst in amap.items():
                if a == "sort":
                    for v in lst:
                        sz = v
                        if (common.gopts.init >= 0) and (sz != "0"):
                            sz = str(common.gopts.init)
                        self.add_sort(f.symbol_type(), sz)
                if a == "init":
                    self.orig.add_init(f)
                if a == "axiom":
                    for v in lst:
                        self.orig.add_axiom(f)
                if a == "action":
                    for v in lst:
                        self.orig.add_action(f, v)
                if a == "invar-property":
                    for v in lst:
                        self.orig.add_prop(f)
                if a == "next":
                    for v in lst:
                        self.orig.add_state(f, v)
                if a == "global":
                    for v in lst:
                        self.orig.add_global_state(f)
                if a == "pred":
                    for v in lst:
                        self.orig.add_pred(f, v)
                if a == "help":
                    for v in lst:
                        self.orig.add_helper(f, v)
#                         self.orig.add_axiom(f)
                if a == "definition":
                    for v in lst:
                        self.orig.add_definition(f, v)
        
        if len(self.orig._helpers) != 0:
            eprint("\t(found #%d user-provided helpers)" % len(self.orig._helpers))
            print("\t(found #%d user-provided helpers)" % len(self.orig._helpers))
#             assert(0)

#             print("\nConverting helpers to axioms")
#             print("Helpers #%s" % len(self.orig._helpers))
#             for k, v in self.orig._helpers.items():
#                 print("\t%s := %s\n\t\twith variables %s" % (str(v), str(k), k.get_free_variables()))
#                 self.orig.add_axiom(k)
#                 knext = k.simple_substitute(self.orig._pre2nex)
#                 self.orig.add_axiom(knext)
#             self.orig._helpers.clear()
            
            print("\nConverting helpers to inferences")
            print("Helpers #%s" % len(self.orig._helpers))
            for k, v in self.orig._helpers.items():
                print("\t%s := %s\n\t\twith variables %s" % (str(v), str(k), k.get_free_variables()))
                self.orig._infers[k] = v
            self.orig._helpers.clear()
        
        print("-----------------------------------------------------------------")
            
        symbols = script.get_declared_symbols()
        for sym in symbols:
            self.orig.add_var(sym)
            if sym not in self.orig._states:
                if sym not in self.orig._nexstates:
                    self.orig.add_other(sym)
        
        self.preprocess_definitions()

        self.syntax.setup(self.orig, self.strat)
#         assert(0)
        self.stratify()

        self.postprocess_definitions()

#         self.syntax_infer()

#         self.orig.add_trel()
        self.orig.add_trel_new()
        
        self.syntax.process_inputs()
        
        self.set_sort_dependency()
        
        print(self.orig)
        self.set_finite_curr()
        self.set_curr()
        eprint("\t(input is %sin epr)" % ("" if self.strat.is_epr() else "not "))
#         assert(0)
    
    def set_finite_curr(self):
        if common.gopts.mode == "updr":
            return
        if common.gopts.size == "default":
            if len(self._sort2fin) == 0:
                for tt in sorted(self._sorts, key=str):
                    ri = "0"
                    if (common.gopts.init >= 0):
                        ri = str(common.gopts.init)
                    else:
                        eprint("Finitize %s ? " % (str(tt)), end='')
                        ri = raw_input("")
    
                    if ri:
                        try:
                            sz = int(ri)
                            if sz > 0:
                                self.add_sort(tt, sz)
                                eprint("\t(setting |%s| to %d)" % (str(tt), sz))
                        except ValueError:
                            pass
        else:
            sizes = parseSizes(common.gopts.size)
            for tt in sorted(self._sorts, key=str):
                ri = "0"
                k = str(tt)
                if k in sizes:
                    ri = sizes[k]

                if ri:
                    try:
                        sz = int(ri)
                        if sz > 0:
                            self.add_sort(tt, sz)
                            eprint("\t(setting |%s| to %d)" % (str(tt), sz))
                    except ValueError:
                        pass

        eprint()
        eprint("Finite sorts: #%d" % len(self._sort2fin))
        for tt, vals in self._sort2fin.items():
            eprint("\t|%s| = %s" % (tt, len(self._enumsorts[vals])))

    def set_finite_extend(self, increment=False):
        if common.gopts.mode == "updr":
            return
        changed = False
        for tt in sorted(self._sorts, key=str):
            if tt not in self._sort2fin:
                continue
            
            ri = "1"
            if (not increment):
                eprint("Extend %s ? " % (str(tt)), end='')
                if (len(self._sort2fin) > 1):
                    ri = raw_input("")
                else:
                    eprint()
            
            if ri:
                try:
                    delta = int(ri)
                    if delta >= 0:
                        sz = self.extend_sort(tt, delta)
                        if delta > 0:
                            eprint(time_str(), "(extended |%s| to %d)" % (str(tt), sz))
                            print(time_str(), "(extended |%s| to %d)" % (str(tt), sz))
                            changed = True
                    else:
                        self.unbound_sort(tt)
                        eprint("\t(unbounding %s)" % (str(tt)))
                        changed = True
                except ValueError:
                    pass

        if changed:
#             eprint("Finite sorts (new): #%d" % len(self._sort2fin))
#             for tt, vals in self._sort2fin.items():
#                 eprint("\t|%s| = %s" % (tt, len(self._enumsorts[vals])))
            pass
            
    def get_num_state_bits(self):
        val = 0
        for s in self.curr._states:
            if s in self.curr._le:
#                 eprint("skipping " + str(s))
                continue
            if s in self._quorums_symbols:
#                 eprint("skipping " + str(s))
                continue
            if s in self.curr._definitionMap:
#                 eprint("skipping " + str(s))
                continue
            sz = self.get_num_state_bits_symbol(s)
            if sz <= 0:
                return -1
            val += sz
#         eprint("tsb=%d" % val)
        return val
            
    def get_num_state_bits_symbol(self, s):
        s_type = s.symbol_type()
#         eprint(str(s) + " of type %s\n" % s_type)
        val = 1
        rett = s_type
        if s_type.is_function_type():
            rett = s_type.return_type
            for paramt in s_type.param_types:
                if paramt in self._enumsorts:
                    sz = len(self._enumsorts[paramt])
                    val *= sz
#                     eprint("  arg |%s|=%d" % (paramt, sz))
                else:
                    return -1
        if not rett.is_bool_type():
            if rett in self._enumsorts:
                sz = len(self._enumsorts[rett])
                val *= sz
#                 eprint("  ret |%s|=%d" % (rett, sz))
            else:
                return -1
#         eprint("symbol |%s|=%d" % (str(s), val))
        return val
                        
# Time to try out the parser !!!

if __name__ == "__main__":
    import sys

    def main():
        """Simple testing script"""
        args = sys.argv
        if len(args) != 2:
            print("Usage %s <file.smt2>" % args[0])
            exit(1)
        fname = args[1]
        ts_parser = TransitionSystem()
        with open(fname, 'r') as script:
            ts_parser.read_ts(script)
            print(ts_parser)
    main()
