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

class StratificationOracle():
    
    def __init__(self):
        self.reset()
        
    def reset(self):
        self.skolem_map = {}
        self.epr = True
        self.has_exists = False
            
    def is_epr(self):
        return self.epr
        
    def arcs(self):
        return self.skolem_map
        
    def update_stratify_function(self, k, t):
        modified = False
        self.print_arc(k, t, "\tfunction ")
        if self.has_path(t, k):
            self.epr = False
            print("\tcycle detected")
        if k not in self.skolem_map:
            self.skolem_map[k] = set()
        self.skolem_map[k].add(t)
        modified = True
        return modified
    
    def update_stratify(self, formula):
        modified = False
        sk_map = self.get_stratify_arcs(formula)
        for k, v in sk_map.items():
            for t in v:
                self.print_arc(k, t, "\tskolem ")
                if self.has_path(t, k):
                    self.epr = False
                    print("\tcycle detected")
                if k not in self.skolem_map:
                    self.skolem_map[k] = set()
                self.skolem_map[k].add(t)
                modified = True
        return modified
    
    def allowed_arc(self, ut, et):
        print("\tallowed(arc: %s -> %s)? " % (ut, et), end='')
        if not self.is_epr():
            res = True
        else:
            res = not self.has_path(et, ut)
        print(res)
        return res
        
    def has_path(self, src, dest):
        dests = set()
        dests.add(dest)
        return self.check_path(src, dests)
    
    def check_path(self, src, dests_orig):
        dests = dests_orig.copy()
        if src in dests:
            return True
        dests.add(src)
        if src in self.skolem_map:
            for v in self.skolem_map[src]:
                if v in dests:
                    return True
                if self.check_path(v, dests):
                    return True
        return False
        
    
    def get_stratify_arcs(self, formula):
        sk_map = {}
        self.get_arcs(sk_map, formula, True, [])
        return sk_map
    
    def print_all_arcs(self):
        self.print_arcs(self.skolem_map)
    
    def print_arcs(self, sk_map):
        print("\nArcs:")
        for k, v in sk_map.items():
            print("\t%s ->" % k, end='')
            for t in v:
                print(" %s" % t, end='')
            print("")
        print("\nEPR: %s" % self.epr)
    
    def print_arc(self, lhs, rhs, prefix=""):
        print("%sarc: %s -> %s" % (prefix, str(lhs), str(rhs)))
    
    def get_arcs(self, sk_map, formula, pol, univs):
#         print("formula: %s %s %s" % (formula, pol, univs))
#         self.print_arcs(sk_map)
        
        if formula.is_not():
            self.get_arcs(sk_map, formula.arg(0), not pol, univs)
            return
        if formula.is_implies():
            self.get_arcs(sk_map, formula.arg(0), not pol, univs)
            self.get_arcs(sk_map, formula.arg(1), pol, univs)
            return
        is_e = formula.is_exists()
        is_a = formula.is_forall()
        if (is_e and pol) or (is_a and not pol):
            self.has_exists = True
            qvars = formula.quantifier_vars()
            fvs = set(formula.get_free_variables())
            for u in univs:
                if u in fvs:
                    for e in qvars:
                        ut = u.symbol_type()
                        et = e.symbol_type()
                        if ut not in sk_map:
                            sk_map[ut] = set()
                        if et not in sk_map[ut]:
                            sk_map[ut].add(et)
#                             self.print_arc(ut, et, "adding ")
        if (is_e and not pol) or (is_a and pol):
            self.get_arcs(sk_map, formula.arg(0), pol, univs + list(formula.quantifier_vars()))
#         print("args: ", formula.args())
        for arg in formula.args():
            self.get_arcs(sk_map, arg, pol, univs)
        if formula.is_ite():
            self.get_arcs(sk_map, formula.arg(0), not pol, univs)
        if formula.is_iff() or formula.is_equals():
            self.get_arcs(sk_map, formula.arg(0), not pol,univs)
            self.get_arcs(sk_map, formula.arg(1), not pol,univs)
        
