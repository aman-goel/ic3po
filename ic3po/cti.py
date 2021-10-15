# ------------------------------------------
# IC3PO: IC3 for Proving Protocol Properties
# ------------------------------------------
# Copyright (c) 2021  Aman Goel and Karem Sakallah, University of Michigan. 
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
from _pytest.compat import enum

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
    
    def header_espresso(self):
        self.espresso_in = []
        res = ""
        for idx, var in self.converter.idx2var.items():
            if var in self.converter.var2atom:
                atom = self.converter.var2atom[var]
                self.espresso_in.append(atom)
                res += str(atom).replace(" ", "") + " "
            else:
                atom = Symbol("v%d" % idx)
                self.espresso_in.append(atom)
                res += str(atom) + " "
                print("Found ")
                assert(0)
        return res

    def print_espresso(self, bdd, restricted, name):
        global outF
        outF =open(name + ".pla", "w")
        
        str_head = ".ilb "
        self.espresso_head = []
        abvars = set(self.converter.var2atom.keys())
        atomList = []
        for idx in range(self.numvars):
            var = self.converter.idx2var[idx]
            atom = self.converter.var2atom[var]
            atomList.append(atom)
            if atom in restricted:
                self.espresso_head.append(atom)
                abvars.remove(var)
        
        for atom in self.espresso_head:
            str_head += pretty_serialize(atom).replace(" ", "") + " "
        fprint(".i %d" % len(self.espresso_head))
        fprint(".o 1")
        fprint(str_head)
        fprint(".ob out")
        fprint(".phase 0")
        abcube = self.converter.cube_from_var_list(list(abvars))
#         bddnew = bdd
        bddnew = self.ddmanager.ExistAbstract(bdd, abcube)
        print("\t(printing pla)")
#         for cube_tup in repycudd.ForeachCubeIterator(self.ddmanager, bddnew):
#             str_cube = ""
#             for idx, char in enumerate(cube_tup):
#                 if idx >= self.numvars:
#                     break
#                 atom = atomList[idx]
# #                 var = self.converter.idx2var[idx]
# #                 atom = self.converter.var2atom[var]
#                 if atom in restricted:
#                     if char == 2:
#                         str_cube += '-'
#                     else:
#                         str_cube += str(char)
#             str_cube += " 1"
#             fprint(str_cube)
        fprint(".e")
        outF.close()
    
    def execute_espresso(self, bdd, restricted, mode="exact"):
        global outF
        name = "%s/espresso_in" % (common.gopts.out)
        self.print_espresso(bdd, restricted, name)
        cmd = "exec ./utils/espresso/espresso.linux"
        if mode == "exact":
            cmd += " -D exact -o kiss %s.pla" % name
            eprint("\t(running espresso in exact mode)")
            print("\t(running espresso in exact mode)")
        elif mode == "primes":
            cmd += " -D primes -o kiss %s.pla" % name
            eprint("\t(running espresso in primes mode)")
            print("\t(running espresso in primes mode)")
        else:
            cmd += " -e fast -o kiss %s.pla" % name
            eprint("\t(running espresso in fast mode)")
            print("\t(running espresso in fast mode)")
        print(cmd)
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, shell=True)
        (out, err) = proc.communicate()
        
        if err != None:
            print("espresso err: %s" % err)
            assert(0)
        output = out.split(b'\n')
        newCubes = []
        outName = "%s/" % (common.gopts.out)
        if mode == "exact":
            outName += "espresso_out_exact.pla"
        elif mode == "primes":
            outName += "espresso_out_primes.pla"
        else:
            outName += "espresso_out_fast.pla"
        outF =open(outName, "w")
        str_head = ".ilb "
        for atom in self.espresso_head:
            str_head += pretty_serialize(atom).replace(" ", "") + " "
        fprint(".i %d" % len(self.espresso_head))
        fprint(".o 1")
        fprint(str_head)
        fprint(".ob out")
        for l in output:
            if l != "":
                fprint(l)
                cube = []
                cubeMap = {}
                for i in range(len(self.espresso_head)):
                    atom = self.espresso_head[i]
                    val = l[i]
                    if val == "0":
                        cubeMap[atom] = 0
                        cube.append(Not(atom))
                    elif val == "1":
                        cubeMap[atom] = 1
                        cube.append(atom)
                newCubes.append((And(cube), cubeMap, l))
#                 print("%s -> %s" % (l, And(cube)))
        fprint(".e")
        outF.close()
        if len(newCubes) == 0:
            print("No cube in espresso output.")
            print("Something went wrong with espresso (probably memout).")
            assert(0)
        
        return newCubes
    
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
