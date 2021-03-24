# ------------------------------------------
# IC3PO: IC3 for Proving Protocol Properties
# ------------------------------------------
# Copyright (c) 2021  Aman Goel and Karem Sakallah, University of Michigan. 
# All rights reserved.
#
# Author: Aman Goel (amangoel@umich.edu), University of Michigan
# ------------------------------------------

from __future__ import print_function

import pysmt
from pysmt.shortcuts import And, ForAll, EqualsOrIff, Implies, Exists, Symbol
from pysmt.pretty_printer import pretty_serialize

class SyntaxInference():
    
    def __init__(self):
        self.reset()
        
    def reset(self):
        self.system = None
        self.strat = None
        self.nex2actions = {}
        self.action2prefix = {}
        self.action2suffix = {}
        self.action2def = {}
        self.action2inputs = {}
        self.inputs = set()
        self.nexinputs = set()
#         self.inp2nex = dict()
#         self.nex2inp = dict()
        self.nexinfer = {}
    
    def process_assign(self, formula, conditions):
        if formula.is_ite():
            cond = formula.arg(0)
            the = formula.arg(1)
            for c in self.flatten_cube(cond):
                conditions.append(c)
            return self.process_assign(the, conditions)
        else:
            return formula
        
    def process_prospectives(self):
        print("\nProcessing prospectives")
        for nv, (action, cond) in self.nexinfer.items():
            print("\tprocessing %s in %s" % (nv, action))
            action_suffix = self.action2suffix[action]
            action_nvars = And(action_suffix).get_free_variables()
            action_nvars = action_nvars.intersection(self.system._nex2pre.keys())
            action_pvars = set()
            for n in action_nvars:
                action_pvars.add(self.system._nex2pre[n])
            action_prefix = self.action2prefix[action]
            concs_global = []
            concs = []
            for c in action_prefix:
                cvars = c.get_free_variables()
                common = cvars.intersection(action_pvars)
                if len(common) == 0:
                    statevars = cvars.intersection(self.system._states)
                    statevars = statevars.difference(self.system._globals)
                    if len(statevars) == 0:
                        concs_global.append(c)
                    else:
                        concs.append(c)
            if (len(concs)+len(concs_global)) == 0:
                print("\t\tskipping %s since no static precondition found" % nv)
                continue
            qvars = set()
            if cond.is_forall():
                cqvars = cond.quantifier_vars()
                for v in cqvars:
                    qvars.add(v)
                cond = cond.arg(0)
            if not (cond.is_iff() or cond.is_equals()):
                continue
            lhs = cond.arg(0)
            rhs = cond.arg(1)
            lvars = lhs.get_free_variables()
            rvars = rhs.get_free_variables()
            if nv in rvars:
                lhs, rhs = rhs, lhs
                lvars, rvars = rvars, lvars
            if nv in rvars:
                continue
            ldvars = lvars.difference(qvars)
            if len(ldvars) != 1:
                continue
            ldvar = next(iter(ldvars))
            if nv != ldvar:
                continue
            if len(qvars) != 0:
                if not lhs.is_function_application():
                    continue
                nsym = lhs.function_name()
                if nv != nsym:
                    continue
            if len(self.action2def) != 0:
                rhs = rhs.substitute(self.action2def[action])
            rconds = []
            rval = self.process_assign(rhs, rconds)
            premise = []
            qsubs = {}
            for c in rconds:
                if c.is_iff() or c.is_equals():
                    lc = c.arg(0)
                    rc = c.arg(1)
                    if rc.is_symbol():
                        if rc in qvars:
                            lc, rc = rc, lc
                    if lc.is_symbol():
                        if lc in qvars:
                            if rc in self.system._others:
                                qsubs[rc] = lc
                                continue
                premise.append(c)
            eq = EqualsOrIff(lhs, rval)
            premise.insert(0, eq)
            prem = And(premise)
            qsubs[nv] = self.system._nex2pre[nv]
        
            prem = prem.substitute(qsubs)
            ivars = prem.get_free_variables()
            ivars = ivars.intersection(self.system._others)
            if len(ivars) != 0:
                for v in ivars:
                    vname = "Q"+str(v)
                    vname = vname.replace(":", "")
                    vnew = Symbol(vname, v.symbol_type())
                    qsubs[v] = vnew
                    qvars.add(vnew)
            
            prem = prem.substitute(qsubs)
            if len(concs_global) != 0:
                concs.append(None)
            for conc in concs:
                if conc == None:
                    conc = And(concs_global)
                else:
                    if len(concs_global) != 0:
                        conc = And(conc, And(concs_global))
                conc = conc.substitute(qsubs)
                
                ivars = conc.get_free_variables()
                ivars = ivars.intersection(self.system._others)
                evars = []
                if len(ivars) != 0:
                    esubs = {}
                    for v in ivars:
                        vname = "Q"+str(v)
                        vname = vname.replace(":", "")
                        vnew = Symbol(vname, v.symbol_type())
                        esubs[v] = vnew
                        evars.append(vnew)
                    conc = conc.substitute(esubs)
    #                 conc = Exists(evars, conc)
    #                 evars = []
                
#                 print("evars ", evars)
#                 print("conc ", conc)
                inference = Implies(prem, conc)
                
                qvars2 = []
#                 if len(qvars) != 0:
#                     for u in qvars:
#                         ut = u.symbol_type()
#                         for e in evars:
#                             et = e.symbol_type()
#                             if not self.strat.allowed_arc(ut, et):
#                                 qvars2.append(u)
                uqvars = qvars.difference(qvars2)
#                     for u in qvars2:
#                         if u in qvars:
#                             qvars.remove(u)

#                 print("qvars2 ", qvars2)
#                 print("uqvars ", uqvars)
                        
                if len(qvars2) != 0:
                    inference = ForAll(qvars2, inference)
                
                if len(evars) != 0:
                    inference = Exists(evars, inference)
                
                if len(uqvars) != 0:
                    inference = ForAll(uqvars, inference)
                
                iname = "syntax" + str(len(self.system._infers)+1)
                self.system._infers[inference] = iname
                print("\t\tinferred %s: %s" % (iname, inference))
#                 assert(0)
    
    def flatten_cube(self, cube):
        flat = set()
        cube_flat = cube
        if (cube_flat.is_and()):
            for arg in cube_flat.args():
                for flat_arg in self.flatten_cube(arg):
                    flat.add(flat_arg)
        else:
            flat.add(cube_flat)
        return flat
    
    def process_inputs(self):
        for k, v in self.action2inputs.items():
            for inp in v:
                self.inputs.add(inp)
#                 nex = Symbol(str(inp)+"$next", inp.symbol_type())
#                 self.system._pre2nex[inp] = nex
#                 self.system._nex2pre[nex] = inp
#                 self.nexinputs.add(nex)
    
    def build_update_map(self):
        for a in self.system._actions:
            action = a[0]
            name = a[1]
            if name not in self.action2def:
                self.action2def[name] = {}
            if name not in self.action2inputs:
                self.action2inputs[name] = set()
            if name not in self.action2prefix:
                self.action2prefix[name] = list()
            if name not in self.action2suffix:
                self.action2suffix[name] = list()
            
            if action.is_exists():
                qvars = action.quantifier_vars()
                for v in qvars:
                    self.system._others.add(v)
                action = action.arg(0)
            flat_action = self.flatten_cube(action)
            for cond in flat_action:
                cvars = cond.get_free_variables()
                ovars = cvars.intersection(self.system._others)
                for c in ovars:
                    if not c.symbol_type().is_function_type():
                        self.action2inputs[name].add(c)
                nexcvars = cvars.intersection(self.system._nex2pre.keys())
                if len(nexcvars) == 0:
                    if len(ovars) != 0:
                        if cond.is_iff() or cond.is_equals():
                            lhs = cond.arg(0)
                            rhs = cond.arg(1)
                            if rhs in ovars:
                                if rhs not in self.action2def[name]:
                                    self.action2def[name][rhs] = lhs
                                    continue
                            if lhs in ovars:
                                if lhs not in self.action2def[name]:
                                    self.action2def[name][lhs] = rhs
                                    continue
                    self.action2prefix[name].append(cond)
                else:
                    self.action2suffix[name].append(cond)
                    for nv in nexcvars:
                        if nv not in self.nex2actions:
                            self.nex2actions[nv] = list()
                        self.nex2actions[nv].append(name)
            for k in self.action2def[name].keys():
                self.action2inputs[name].discard(k)
                     
    def build_prospectives(self):
        for nv, actions in self.nex2actions.items():
            if len(actions) == 1:
                action = next(iter(actions))
                if action not in self.action2prefix:
                    continue
                precond = And(self.action2prefix[action])
                pvars = precond.get_free_variables()
                pv = self.system._nex2pre[nv]
                if pv not in pvars:
                    postconds = self.action2suffix[action]
                    for cond in postconds:
                        cvars = cond.get_free_variables()
                        if nv in cvars:
                            assert(nv  not in self.nexinfer)
                            self.nexinfer[nv] = (action, cond)
    
    def print_action_inputs(self):
        print("\nAction inputs:")
        for k, v in self.action2inputs.items():
            print("\t%s: %s" % (k, v))
#             for inp in v:
#                 print("\t\t%s -> %s" % (inp, self.system._pre2nex[inp]))
            
    def print_action_defs(self):
        print("\nAction definitions:")
        for k, v in self.action2def.items():
            print("\t%s: %s" % (k, v))
            
    def print_prospectives(self):
        print("\nProspectives:")
        for k, v in self.nexinfer.items():
            print("\t%s in %s: %s" % (k, v[0], v[1].serialize()))
            
    def print_update_map(self):
        print("\nUpdate map:")
        for nv, actions in self.nex2actions.items():
            print("\t%s -> " % nv, end='')
            for action in actions:
                print(" %s" % action, end='')
            print("")
            
    def print_prefix(self):
        print("\nAction preconditions:")
        for action, conds in self.action2prefix.items():
            print("\n\t%s:" % action)
            for cond in conds:
                print("\t\t%s" % (cond.serialize()))
#                 print("\t\twith variables %s" % (cond.get_free_variables()))
            
    def print_suffix(self):
        print("\nAction postconditions:")
        for action, conds in self.action2suffix.items():
            print("\n\t%s:" % action)
            for cond in conds:
                print("\t\t%s" % (cond.serialize()))
#                 print("\t\twith variables %s" % (cond.get_free_variables()))
    
    def print_inferences(self):
        print("\nInferences:")
        for k, v in self.system._infers.items():
            print("\t%s: %s" % (v, k.serialize()))
        
    def print_action(self):
        self.print_action_inputs()
        self.print_action_defs()
        self.print_prefix()
        self.print_suffix()
        self.print_update_map()
    
    def substitute(self, rhs):
        self.system = rhs
        
        nex2actions = self.nex2actions.copy()
        self.nex2actions = {}
        for l, r in nex2actions.items():
            self.nex2actions[l.fsubstitute()] = r
            
        action2prefix = self.action2prefix.copy()
        self.action2prefix = {}
        for l, r in action2prefix.items():
            self.action2prefix[l] = list()
            for c in r:
                self.action2prefix[l].append(c.fsubstitute())
        
        action2suffix = self.action2suffix.copy()
        self.action2suffix = {}
        for l, r in action2suffix.items():
            self.action2suffix[l] = list()
            for c in r:
                self.action2suffix[l].append(c.fsubstitute())
        
        action2def = self.action2def.copy()
        self.action2def = {}
        for l, r in action2def.items():
            self.action2def[l] = {}
            for k, v in r.items():
                self.action2def[l][k.fsubstitute()] = v.fsubstitute()
        
        action2inputs = self.action2inputs.copy()
        self.action2inputs = {}
        for l, r in action2inputs.items():
            self.action2inputs[l] = set()
            for c in r:
                self.action2inputs[l].add(c.fsubstitute())        
        
        inputs = self.inputs.copy()
        self.inputs = set()
        for l in inputs:
            self.inputs.add(l.fsubstitute())
        
        nexinputs = self.nexinputs.copy()
        self.nexinputs = set()
        for l in nexinputs:
            self.nexinputs.add(l.fsubstitute())
#         
#         inp2nex = self.inp2nex.copy()
#         self.inp2nex = dict()
#         for l, r in inp2nex.items():
#             self.inp2nex[l.fsubstitute()] = r.fsubstitute()
#         
#         nex2inp = self.nex2inp.copy()
#         self.nex2inp = dict()
#         for l, r in nex2inp.items():
#             self.nex2inp[l.fsubstitute()] = r.fsubstitute()
            
                
    def setup(self, system, strat):
        self.system = system
        self.strat = strat
        self.build_update_map()
        self.print_action()
        
    def infer(self):
        self.build_prospectives()
        self.print_prospectives()
        
        self.process_prospectives()
        self.print_inferences()
