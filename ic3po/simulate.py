# ------------------------------------------
# IC3PO: IC3 for Proving Protocol Properties
# ------------------------------------------
# Copyright (c) 2018 - Present  Aman Goel and Karem Sakallah, University of Michigan. 
# All rights reserved.
#
# Author: Aman Goel (amangoel@umich.edu), University of Michigan
# ------------------------------------------

from __future__ import print_function

import pysmt
from pysmt.shortcuts import And, Or, Not, ForAll, EqualsOrIff, Implies, Exists, \
        Symbol, TRUE, FALSE, Function
from pysmt.pretty_printer import pretty_serialize
from utils import pretty_print_str
import itertools
from utils import flatten_and

class EvalEngine():
    
    def __init__(self, system, mgr):
        self.system = system
        self.mgr = mgr
        self.reset()
        
    def reset(self):
        self.enum_domain = {}
        self.instances_cache = {}
        self.global_model = {}
        self.reset_model()
        self.wire_instances = {}
    
    def reset_model(self):
        self.state_model = {}
        self.wire_model = {}
        self.expr_model = {}
    
    def print_global_model(self):
        print("(global model) #%d" % len(self.global_model))
        for s, v in self.global_model.items():
            print("\t%s = %s" % (pretty_print_str(s), pretty_print_str(v)))
        print()
    
    def print_state_model(self):
        print("(state model) #%d" % len(self.state_model))
        for s, v in self.state_model.items():
            print("\t%s = %s" % (pretty_print_str(s), pretty_print_str(v)))
        print()
    
    def print_wire_model(self):
        if len(self.wire_model) == 0:
            print("(wire model) none")
        else:
            print("(wire model) #%d" % len(self.wire_model))
            for s, v in self.wire_model.items():
                print("\t%s = %s" % (pretty_print_str(s), pretty_print_str(v)))
        print()
    
    def set_global_model(self, axioms):
        self.global_model = {}
        mdl = flatten_and(axioms)
        for formula in mdl:
            s = None
            v = None
            if formula.is_iff() or formula.is_equals():
                s = formula.arg(0)
                v = formula.arg(1)
            elif formula.is_not():
                s = formula.arg(0)
                v = FALSE()
            else:
                s = formula
                v = TRUE()
            assert(s != None)
            assert(v != None)
            sym = s
            if s.is_function_application():
                sym = s.function_name()
            if sym in self.system.curr._globals:
                if sym not in self.system.curr._definitionMap:
                    self.global_model[s] = v
#             else:
#                 print("sym: %s" % sym)
#                 print("s: %s" % s)
#                 print("v: %s" % v)
#                 assert(0)
        self.print_global_model()
     
    def read_model(self, mdl):
        for formula in mdl:
            s = None
            v = None
            if formula.is_iff() or formula.is_equals():
                s = formula.arg(0)
                v = formula.arg(1)
            elif formula.is_not():
                s = formula.arg(0)
                v = FALSE()
            else:
                s = formula
                v = TRUE()
            assert(s != None)
            assert(v != None)
            sym = s
            if s.is_function_application():
                sym = s.function_name()
            if sym in self.system.curr._nexstates:
                if sym in self.system.curr._definitionMap:
                    self.state_model[s] = v
                else:
                    self.state_model[s] = v
            else:
                print("sym: %s" % sym)
                print("s: %s" % s)
                print("v: %s" % v)
                assert(0)
        self.print_state_model()
    
    def _eval_not(self, args):
        assert(len(args) == 1)
        a = args[0]
        if a == None:
            return None
        if a == TRUE():
            return FALSE()
        assert(a == FALSE())
        return TRUE()
    
    def _eval_implies(self, args):
        assert(len(args) == 2)
        a = args[0]
        b = args[1]
        if a == None:
            return None
        if a == TRUE():
            return b
        assert(a == FALSE())
        return TRUE()
    
    def _eval_ite(self, args):
        assert(len(args) == 3)
        a = args[0]
        b = args[1]
        c = args[2]
        if a == None:
            return None
        if a == TRUE():
            return b
        assert(a == FALSE())
        return c
    
    def _eval_iff(self, args):
        return self._eval_iff(args)
        assert(len(args) == 2)
        a = args[0]
        b = args[1]
        if a == None or b == None:
            return None
        assert(a.is_bool_constant())
        assert(b.is_bool_constant())
        if a == b:
            return TRUE()
        return FALSE()
    
    def _eval_eq(self, args):
        assert(len(args) == 2)
        a = args[0]
        b = args[1]
        if a == None or b == None:
            return None
        assert(a.is_enum_constant())
        assert(b.is_enum_constant())
        if a == b:
            return TRUE()
        return FALSE()
    
    def _eval_and(self, args):
        allTrue = True
        for a in args:
            if a == FALSE():
                return FALSE()
            elif a == None:
                allTrue = False
        if allTrue:
            return TRUE()
        return None
    
    def _eval_or(self, args):
        allFalse = True
        for a in args:
            if a == TRUE():
                return TRUE()
            elif a == None:
                allFalse = False
        if allFalse:
            return FALSE()
        return None
    
    def eval_expr(self, formula):
        if formula in self.expr_model:
            return self.expr_model[formula]
        if formula in self.global_model:
            return self.global_model[formula]
        if formula in self.state_model:
            return self.state_model[formula]
        if formula in self.wire_model:
            return self.wire_model[formula]
        res = None
        args = []
        hasNone = False
        for ch in formula.args():
            chNew = self.eval_expr(ch)
            if chNew == None:
                hasNone = True
            args.append(chNew)
        if formula.is_not():
            res = self._eval_not(args)
        elif formula.is_implies():
            res = self._eval_implies(args)
        elif formula.is_ite():
            res = self._eval_ite(args)
        elif formula.is_iff():
            res = self._eval_iff(args)
        elif formula.is_equals():
            res = self._eval_eq(args)
        elif formula.is_and():
            res = self._eval_and(args)
        elif formula.is_or():
            res = self._eval_or(args)
        elif formula.is_bool_constant():
            res = formula
        elif formula.is_enum_constant():
            res = formula
        elif formula.is_function_application():
            if not hasNone:
                sym = formula.function_name()
                formulaNew = Function(sym, args)
                if formula != formulaNew:
                    res = self.eval_expr(formulaNew)
                else:
#                     print("expr_fun1: %s" % formula)
                    pass
            else:
#                 print("expr_fun2: %s" % formula)
#                 assert(0)
                pass
        elif formula.is_symbol():
#             print("expr_sym: %s" % formula)
#             assert(0)
            pass
        else:
            print("expr_oth: %s" % formula)
            assert(0)
        self.expr_model[formula] = res
        return res
    
    def _assert_var_scalar(self, v):
        if not v.symbol_type().is_enum_type():
            print(
                "Scalar Shannon Quantifier Elimination only supports "\
                "quantification over Enum variables: "\
                "(%s is %s)" % (v, v.symbol_type()))
            assert(0)

    def _scalar_domain(self, v):
        if v in self.enum_domain:
            return self.enum_domain[v]

        self._assert_var_scalar(v)
        vt = v.symbol_type()
        econsts = self.system._enumsorts[vt]
#         econsts = [self.mgr.Enum(d, vt) for d in vt.domain]
        self.enum_domain[v] = econsts
        return econsts

    def _scalar_instances(self, variables):
        vstr = str(variables)
        if vstr in self.instances_cache:
            return self.instances_cache[vstr]

        enums = []
        for v in variables:
            enums.append(self._scalar_domain(v))
            
        instances = []
        for d in itertools.product(*enums):
            instances.append(d)
#         instances = list(itertools.product(*enums))

        self.instances_cache[vstr] = instances
        return instances

    def _all_scalar_assignments(self, variables):
        """Generates all possible assignments for a set of variables."""
        for d in self._scalar_instances(variables):
            yield d
#             yield dict((v, d[idx]) for idx, v in enumerate(variables))
    
    def set_wire_instances(self):
        self.wire_instances = {}
        for w in self.system.curr._definitionMap.keys():
            if w in self.system.curr._nexstates:
                self.set_wire(w)
        
    def set_wire(self, w):
        entry = self.system.curr._definitionMap[w]
        largs = entry[-1]
        for inst in self._all_scalar_assignments(largs):
            self.set_wire_instance(entry, inst)
        
    def set_wire_instance(self, entry, args):
        rhs = entry[0]
        rhs = self.system.replaceDefinitions(rhs)
        lhs = entry[1]
        largs = entry[-1]
        subs = {}
        for idx, v in enumerate(largs):
            subs[v] = args[idx]
        lhs = lhs.simple_substitute(subs)
        rhs = rhs.simple_substitute(subs)
#         print("Wire %s -> %s" % (pretty_print_str(lhs), pretty_print_str(rhs)))
#        if self.mgr.qf < 2:
#            rhs = self.mgr.get_qf_form(rhs)
#        else:
        rhs = self.mgr.get_formula_qf(rhs)
        val = self.eval_expr(rhs)
        if val == None:
            self.wire_instances[lhs] = rhs
        else:
            print("\t%s = %s\t[static value]" % (pretty_print_str(lhs), pretty_print_str(val)))
            pass
    
    def eval_wires(self):
        for lhs, rhs in self.wire_instances.items():
            val = self.eval_expr(rhs)
            if val != None:
                self.wire_model[lhs] = val
            else:
                print("\t%s = ??" % (pretty_print_str(lhs)))
                pass
#         assert(0)
    
    def get_extended_mdl(self):
#         if len(self.wire_model) == 0:
#             return None
        res = []
        hasWires = len(self.wire_model) != 0
        for s, v in self.wire_model.items():
            eq = EqualsOrIff(s, v)
#             if self.mgr.qf < 2:
#                 eq = self.system.replaceDefinitions(eq)
            res.append(eq)
#         for s, v in self.state_model.items():
#             eq = EqualsOrIff(s, v)
#             res.append(eq)
        return res, hasWires
               
    def process_model(self, mdl):
        self.reset_model()
        self.read_model(mdl)
        self.eval_wires()
        self.print_wire_model()
        return self.get_extended_mdl()
