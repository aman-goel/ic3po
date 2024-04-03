# ------------------------------------------
# IC3PO: IC3 for Proving Protocol Properties
# ------------------------------------------
# Copyright (c) 2018 - Present  Aman Goel and Karem Sakallah, University of Michigan. 
# All rights reserved.
#
# Author: Aman Goel (amangoel@umich.edu), University of Michigan
# ------------------------------------------

from __future__ import print_function
from cStringIO import StringIO # Python3 use: from io import StringIO

import sys
import os
import subprocess
import pysmt
import utils

# import repycudd


from utils import *
from problem import *
from vmt_parser import TransitionSystem
from pysmt.environment import get_env
from pysmt.shortcuts import Solver, QuantifierEliminator, Enum
from pysmt.logics import BOOL

import common

outFile = "out"
outF = None
def fprint(s):
    global outF
    outF.write(s + "\n")

class CTI(object):
    def __init__(self, p):
        self.main = p
        self.system = p.system
        self.solver = self.main.solver
        self.debug = False
    
    def init(self):
        set_solver(self.main)
        self.F = TRUE()
        self.nexbad = Not(pre2nex(self.main, prop_formula(self.main)))
        self.ctiList = []
        self.states = None

    def get_cti(self):
        print(time_str(), "F /\ T /\ !P+", end =' ')
        return self.main.solve_with_model(self.solver, self.nexbad, [self.nexbad])
    
    def func2inst(self, f, ft):
        if ft.is_function_type():
            args = []
            i = 0
            for paramt in ft.param_types:
                i += 1
                paramt_name = str(i) + ":" + str(paramt) 
                args.append(Symbol(paramt_name, paramt))
            fi = Function(f, args)
            return fi
        else:
            return f

    def instantiate_function(self, f, ft, fi):
#         print("processing: %s" % f)
        instantiated = True
        if ft.is_function_type():
#             for idx, paramt in enumerate(ft.param_types):
            for idx in range(len(ft.param_types)-1, -1, -1):
                paramt = ft.param_types[idx]
                assert paramt.is_enum_type()
                arg = f.arg(idx)
                if not arg.is_enum_constant():
                    instantiated = False
                    dom = [Enum(d, paramt) for d in paramt.domain]
                    for d in reversed(dom):
                        subs = {}
                        subs[arg] = d
                        fn = f.substitute(subs)
#                         print("%s to %s" % (f, fn))
                        self.instantiate_function(fn, ft, fi)
            
        if instantiated:
            rt = ft
            if ft.is_function_type():
                rt = ft.return_type
            if rt.is_enum_type():
                dom = [Enum(d, rt) for d in rt.domain]
                for d in dom:
                    eq = EqualsOrIff(f, d)
                    if eq not in fi:
                        fi.append(eq)
            elif rt.is_bool_type():
                if f not in fi:
                    fi.append(f)
            else:
                assert(0)
        
    def initialize_atoms(self):
        self.atoms = []
        self.patoms = {}
        self.natoms = {}
        self.gatoms = {}
        self.p2natoms = {}
        
        states_ordered = {}
        for s in self.system.curr._states:
            if s in self.system.curr._definitionMap:
                continue
            currSign = 0
            prefix = "2_"
            st = s.symbol_type()
            if st.is_function_type():
                currSign += len(st.param_types)
                st = st.return_type
            if st.is_enum_type():
                prefix = "1_"
            if s in self.system.curr._globals:
                prefix = "0_"
            states_ordered[prefix+str(currSign)+str(s)] = s
        
        self.states = sorted(states_ordered.items(), key=lambda v: v, reverse=True)
#         print(states)
        for nf, f in self.states:
            print("-> processing %s" % pretty_serialize(f))
            ft = f.symbol_type()
            fi = []
            self.instantiate_function(self.func2inst(f, ft), ft, fi)
#             print(fi)
            
            for atom in fi:
                self.atoms.append(atom)
                natom = pre2nex(self, atom)
                self.p2natoms[atom] = natom
                if atom != natom:
                    self.atoms.append(natom)
                
                self.patoms[atom] = atom
                
                if atom == natom:
                    self.gatoms[atom] = atom
                    print("\tadding glo: %s" % (pretty_serialize(atom)))
                else:
                    print("\tadding pre: %s" % (pretty_serialize(atom)))
                    
                self.natoms[natom] = natom
#                 print("adding nex: %s <-> %s := %d" % (natom, var, bdd.NodeReadIndex()))
                
        eprint("\t(#%d atoms)" % (len(self.atoms)))
        print("\t(#%d atoms)" % (len(self.atoms)))
    
    def initialize_cti(self):
        cti = dict()
        for a in self.patoms:
            cti[a] = FALSE()
        return cti
            
    def print_cti(self, cti, comment=""):
        print("-> CTI %s" % comment)
        for a in self.patoms:
            assert(a in cti)
            v = cti[a]
            if v == TRUE():
                print("\t%s" % (pretty_serialize(a)))
        print()

    def cti2cube(self, cti):
        formula = []
        for lhs, rhs in cti.items():
            formula.append(EqualsOrIff(lhs, rhs))
        assert(len(formula) != 0)
        return And(formula)

    def process_cti(self, srcValues):
        cti = self.initialize_cti()
        
        cubeValues = srcValues[0]
        globValues = srcValues[1]
        for lhs in sorted(cubeValues.keys(), key=str):
            rhs = cubeValues[lhs]
            s = lhs
            v = rhs
            vt = v.node_type()
            if (vt != pysmt.operators.BOOL_CONSTANT):
                s = EqualsOrIff(s, rhs)
                v = TRUE()
            if s in cti:
                cti[s] = v
        for lhs in sorted(globValues.keys(), key=str):
            rhs = globValues[lhs]
            s = lhs
            v = rhs
            vt = v.node_type()
            if (vt != pysmt.operators.BOOL_CONSTANT):
                s = EqualsOrIff(s, rhs)
                v = TRUE()
            if s in cti:
                cti[s] = v
            else:
                assert(0)
        self.print_cti(cti)
        return cti
    
    def print_espresso(self):
        global outF
        name = "%s/cti.pla" % (common.gopts.out)
        eprint("\t(cti file: %s)" % name)
        print("\t(cti file: %s)" % name)
        outF = open(name, "w")
        
        str_head = ".ilb "
        self.espresso_head = []
        
        self.espresso_head = sorted(self.patoms.keys(), key=lambda v: str(v))
#         for a in self.patoms.keys():
#             self.espresso_head.append(a)
        
        for atom in self.espresso_head:
            atomStr = pretty_print_str(atom, 1, False)
            str_head += atomStr.replace(" ", "") + " "
        fprint(".i %d" % len(self.espresso_head))
        fprint(".o 1")
        fprint(str_head)
        fprint(".ob out")
        fprint(".phase 0")

        print("\t(printing pla)")
        for cti, repcti in self.ctiList:
            str_cube = ""
            for atom in self.espresso_head:
#                 self.print_cti(cti)
                if atom not in cti:
                    print("\t absent %s" % (pretty_serialize(atom)))
                assert(atom in cti)
                v = cti[atom]
                if v == TRUE():
                    str_cube += "1"
                elif v == FALSE():
                    str_cube += "0"
                else:
                    assert(0)
            fprint(str_cube)
        fprint(".e")
        outF.close()
    
    def execute(self):
        """CTI Printer"""
        prop = prop_formula(self.main)
        print("\nChecking property %s...\n" % prop)
        
        iterLimit = 1000
        iterCount = 0
        
        self.main.verbose = 100
        self.main.system.gen = "univ"
        self.main.boost_ordered_en = False
        self.main.boost_quorums_en = False
        self.main.use_wires = False
        self.main.eval_wires = False

        self.initialize_atoms()
        self.solver.add_assertion(prop)
        
        cube = self.get_cti()
        while cube is not None:
            print("-> found new cti")
            # Blocking phase of a bad state
            dest = self.main.get_dest_cube()
            destV = self.main.get_cube_values(dest)
            self.main.print_cube_values(destV, -1, None)

            ctiV = self.main.get_cube_values(cube)
            self.main.print_cube_values(ctiV, 1, destV)
            
            cti = self.process_cti(ctiV)
            self.ctiList.append((cti, cti))
            
            ctiCube = self.cti2cube(cti)
#             cl = Not(ctiCube)
#             print("\tLearning: %s" % (pretty_serialize(cl)))
#             self.solver.add_assertion(cl)
            
            cubesOut = symmetry_cube(self.main, ctiCube, 0, False)
            assert(len(cubesOut) == 1)
            for cubeSym, _ in cubesOut:
                print("Learning sym clause: ", end='')
                print(pretty_print_str(Not(cubeSym), mode=1, reset=False))
                self.solver.add_assertion(Not(cubeSym))
            cube = self.get_cti()
            if cube == None:
                print("-> no new cti")
                break
            iterCount += 1
            if iterCount == iterLimit:
                print("-> max cti limit reached")
                break
        eprint("\t(cti printer done) found #%d CTIs" % (len(self.ctiList)))
        print("\t(cti printer done) found #%d CTIs" % (len(self.ctiList)))
        self.print_espresso()
