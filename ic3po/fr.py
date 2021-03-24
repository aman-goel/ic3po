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

import repycudd


from utils import *
from problem import *
from vmt_parser import TransitionSystem
from pysmt.environment import get_env
from pysmt.shortcuts import Solver, QuantifierEliminator, Enum
from pysmt.logics import BOOL
from pysmt.solvers.bdd import BddConverter
from _pytest.compat import enum

from ic3po import *
import common

outFile = "out"
outF = None
def fprint(s):
    global outF
    outF.write(s + "\n")

class FR(object):
    def __init__(self, system):
        self.system = system
        self.reset()
        self.debug = False
    
    def init_solver(self):
        solver = Solver(name="bdd", logic=BOOL)
        return solver

    def reset(self):
        self.qesolver = QuantifierEliminator(name='z3')
        self._faxioms = []
        self._axiom_formula = TRUE()
        get_env().fsubstituter.freset()
        self.inferences = []
    
    def new_solver(self):
        s = self.init_solver()
        formulae = []
        formulae.append(axiom_formula(self))
        formulae.append(trel_formula(self))
#         formulae = self.get_formulae(formulae, True)
        formulae = self.get_formulae(formulae)
        assert_permanent(s, formulae)
        return s
    
    def get_qf_form(self, f):
        qf = self.qesolver.eliminate_quantifiers(f).simplify()
#         print("quantified: \n%s", f.serialize())
#         print("quantifier-free: \n%s", qf.serialize())
        return qf
    
    def get_formulae(self, formula, qf=True):
        formulae = formula
        if not isinstance(formulae, list):
            formulae = [formula]
        if qf:
            push_time()
            q_formula = And(formulae)
            qf = self.get_qf_form(q_formula)
            qf_formulae = flatten_cube(qf)
            return qf_formulae
        return formulae
    
    def check_query(self, solver, formulae=None, timeout=None):
        print("Formulae #%d:" % len(formulae))
        for f in formulae:
            print("\t%s" % f.serialize())
        print()
        
        res = solver.solve() if formulae == None else solver.solve(formulae)
        return res

    def solve_formula(self, solver, formula, quiet=False):
        """Check whether formula is satisfiable or not"""
#         print("Formula: %s" % formula.serialize())
        formulae = self.get_formulae(formula)
        push_time()
        res = self.check_query(solver, formulae)
        if res:
            if (not quiet):
                print("-> SAT")
            return True
        else:
            if (not quiet):
                print("-> UNSAT")
            return False
    
    def get_bdd(self, node):
        bdd_expr = self.converter.convert(node)
        return bdd_expr
    
    def get_symmetric(self, cl, pol=True):
        cube = cl
        if pol:
            cube = Not(cube)
        cubesOut = symmetry_cube(self, cube, 0, False)
        if pol:
            cubesOutNew = set()
            for cubeSym, complex in cubesOut:
                cubeSymNew = Not(cubeSym)
                cubesOutNew.add((cubeSymNew, complex))
            cubesOut = cubesOutNew
        return cubesOut
        
    def build_actions(self):
        self.actions = {}
        for f in self.system.curr._actions:
            action = f[0]
            name = f[1]
            if self.system.curr.is_noop(name):
                continue
            eprint(time_str(), "(building bdd for %s)" % name)
            print(time_str(), "(building bdds for %s)" % name)
            if name not in self.actions:
                self.actions[name] = []
            if action.is_exists():
                instances = self.converter._get_children(action)
                queue = []
                for i in instances:
                    bddi = self.converter.convert(i)
                    queue.append(bddi)

                all_vars = set(self.converter.var2node.keys())
                pnabstract = all_vars.difference(self.pvars)
                pnabstract = pnabstract.difference(self.nvars)
                projAll = self.converter.cube_from_var_list(pnabstract)
                for bddq in queue:
#                     bddq = self.ddmanager.ExistAbstract(bddq, projAll)
                    self.actions[name].append(bddq)
                print("\t\tfound #%d bdd instances for %s)" % (len(queue), name))
#                 if name == "ext:grant":
#                     for bdd in self.actions[name]:
#                         self.dump_dot(bdd)
#                         assert(0)
            else:
                q = self.converter.convert(action)
                self.actions[name] = [q]
        
    def build_axioms(self):
        self.axiom = self.converter.typeok
        if axiom_formula(self) != TRUE():
            bddA = self.formula2bdd(axiom_formula(self))
            self.axiom = self.ddmanager.And(self.axiom, bddA)
        
    def formula2bdd(self, formula, quiet=True):
        f = And(self.get_formulae(formula, False))
        return self.get_bdd(f)

    def set_atoms(self):
        self.patoms = {}
        self.natoms = {}
        self.p2natoms = {}
        formulae = []
        formulae.append(init_formula(self))
        formulae.append(trel_formula(self))
        formulae.append(axiom_formula(self))
        formulae.append(prop_formula(self))
        
        formula = And(formulae)
        formula = And(self.get_formulae(formula))
#         atoms = formula.get_atoms()
        atoms = self.converter.atom2var.keys()
        for p in atoms:
            vars = p.get_free_variables()
            ovars = vars.difference(self.system.curr._states)
            if len(ovars) == 0:
#             nvars = vars.intersection(self.system.curr._nex2pre.keys())
#             if len(nvars) == 0:
                bddp = self.get_bdd(p)
                self.patoms[p] = bddp
                print("adding pre: %s with bdd %s" % (p, bddp.NodeReadIndex()))
                n = pre2nex(self, p)
                bddn = bddp
                if n != p:
                    bddn = self.get_bdd(n)
                self.natoms[n] = bddn
#                 print("adding nex: %s with bdd %s" % (n, bddn))
    
    def add_bddSupport(self, bdd, support):
        ps = self.ddmanager.Support(bdd)
        psA = repycudd.IntArray(self.converter.numvars)
        self.ddmanager.BddToCubeArray(ps, psA)
        for i in range(len(psA)):
            if psA[i] == 0 or psA[i] == 1:
                var = self.converter.idx2var[i]
                support.add(var)
        
    def set_bddvars(self):
        self.pvars = set()
        self.nvars = set()
        eprint("\t(#%d variables)" % self.converter.numvars)
        print("\t(#%d variables)" % self.converter.numvars)
        for p in self.patoms:
            self.pvars.add(self.converter.atom2var[p])
#             bdd = self.patoms[p]
#             self.add_bddSupport(bdd, self.pvars)
        for n in self.natoms:
            self.nvars.add(self.converter.atom2var[n])
#             bdd = self.natoms[n]
#             self.add_bddSupport(bdd, self.nvars)
#         print("pvars: %s" % self.pvars)
#         print("nvars: %s" % self.nvars)
        
    def set_p2nVars(self):
        self.p2nvars = {}
        for p in self.patoms:
            n = pre2nex(self, p)
            if n != p:
                pvar = self.converter.atom2var[p]
                nvar = self.converter.atom2var[n]
                self.p2nvars[pvar] = nvar
        pv = set(self.p2nvars.keys())
        nv = set(self.p2nvars.values())
        diff = pv.intersection(nv)
        if len(diff) != 0:
            print(diff)
            assert(0)
    
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
        for cube_tup in repycudd.ForeachCubeIterator(self.ddmanager, bddnew):
            str_cube = ""
            for idx, char in enumerate(cube_tup):
                if idx >= self.numvars:
                    break
                atom = atomList[idx]
#                 var = self.converter.idx2var[idx]
#                 atom = self.converter.var2atom[var]
                if atom in restricted:
                    if char == 2:
                        str_cube += '-'
                    else:
                        str_cube += str(char)
            str_cube += " 1"
            fprint(str_cube)
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
    
    def bdd2atoms(self, bdd, atomset=None):
        psA = repycudd.IntArray(self.converter.numvars)
        self.ddmanager.BddToCubeArray(bdd, psA)
        atoms = []
        atomval = {}
        for i in range(len(psA)):
            if psA[i] == 0 or psA[i] == 1:
                var = self.converter.idx2var[i]
                if var in self.converter.var2atom:
                    atom = self.converter.var2atom[var]
#                     print("%d -> %s" % (i, atom))
                    if atomset != None and atom not in atomset:
                        continue
                    if psA[i] == 0:
                        atomval[atom] = 0
                        atom = Not(atom)
                    else:
                        atomval[atom] = 1
                    atoms.append(atom)
        return (And(atoms), atomval)
    
    def extract_pcubes(self, bdd, prefix="Cube"):
        cubes = self.extract_cubes(bdd, self.patoms)
        print("%s: #%d" % (prefix, len(cubes)))
        if len(cubes) < 500:
            for cube, cubeMap in cubes:
                print(cube)
        return cubes
    
    def extract_ncubes(self, bdd, prefix="Cube"):
        cubes = self.extract_cubes(bdd, self.natoms)
        print("%s: #%d" % (prefix, len(cubes)))
        if len(cubes) < 100:
            for cube, cubeMap in cubes:
                print(cube)
        return cubes
    
    def extract_cubes(self, bdd, allowed):
        cubes = []
        for cube in repycudd.ForeachCubeIterator(self.ddmanager, bdd):
            atoms = []
            atomval = {}
            for i in range(self.numvars):
                lit = cube[i]
                if lit == 0 or lit == 1:
                    var = self.converter.idx2var[i]
                    if var in self.converter.var2atom:
                        atom = self.converter.var2atom[var]
    #                     print("%d -> %s" % (i, atom))
                        if atom not in allowed:
                            continue
                        if lit == 0:
                            atomval[atom] = 0
                            atom = Not(atom)
                        else:
                            atomval[atom] = 1
                        atoms.append(atom)
            cubeNew = (And(atoms), atomval)
            cubes.append(cubeNew)
        return cubes
    
    def dump_dot(self, bdd):
        add = self.ddmanager.BddToAdd(bdd)
        self.ddmanager.DumpDot(add)
        
        idx2atom = {}
        for idx in range(self.numvars):
            var = self.converter.idx2var[idx]
            atom = self.converter.var2atom[var]
            k = "\" %d \"" % idx
            idx2atom[k] = "\" %s \"" % pretty_serialize(atom)
        inF = open('out.dot', 'r')
        str_dot = inF.read()
        inF.close()
        global outF
        outF = open("out.dot", "w")
        for k, v in idx2atom.items():
            str_dot = str_dot.replace(k, v)
        fprint(str_dot)
    
    def dump_blif(self, bdd):
        add = self.ddmanager.BddToAdd(bdd)
        self.ddmanager.DumpBlif(add)
    
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
            elif rt == BOOL:
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
        self.pvars = set()
        self.nvars = set()
        self.converter.pre2nex = self.system.curr._pre2nex
        
        states_ordered = {}
        for s in self.system.curr._states:
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
        
        states = sorted(states_ordered.items(), key=lambda v: v, reverse=True)
#         print(states)
        for nf, f in states:
            print("processing %s" % pretty_serialize(f))
            if self.converter.zero != None and str(f).startswith("zero"):
                print("skipping %s" % pretty_serialize(f))
                continue
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
                
                bdd = self.get_bdd(atom)
                self.patoms[atom] = bdd
                var = self.converter.atom2var[atom]
                self.pvars.add(var)
#                 self.add_bddSupport(bdd, self.pvars)
                print("adding pre: %s <-> %s := %d" % (pretty_serialize(atom), var, bdd.NodeReadIndex()))
                
                if atom == natom:
                    self.gatoms[atom] = bdd
                    
                bdd = self.get_bdd(natom)
                self.natoms[natom] = bdd
                var = self.converter.atom2var[natom]
                self.nvars.add(var)
#                 print("adding nex: %s <-> %s := %d" % (natom, var, bdd.NodeReadIndex()))
                
#                 self.add_bddSupport(bdd, self.nvars)
        eprint("\t(#%d atoms with #%d variables)" % (len(self.atoms), self.converter.numvars))
        print("\t(#%d atoms with #%d variables)" % (len(self.atoms), self.converter.numvars))
#         print(self.atoms)
#         print(self.patoms)
#         print(self.natoms)
#         assert(0)
        self.set_p2nVars()
#         self.check_typeok()
        self.print_atoms()
        self.converter.pnset = True
        self.numvars = self.converter.numvars
    
    def print_atoms(self):
        for i in range(self.converter.numvars):
            var = self.converter.idx2var[i]
            if var in self.converter.var2atom:
                atom = self.converter.var2atom[var]
                print("%d -> %s" % (i, pretty_serialize(atom)))
            else:
                print("%d has no var" % (i))
    
    def check_typeok(self):
        print("#typeok = %d" % len(self.converter.typeconst))
#         self.print_atoms()
#         for idx, t in enumerate(self.converter.typeconst):
#             if idx == 2:
#                 bdd = self.converter.typeok
#                 self.dump_dot(bdd)
#                 self.ddmanager.PrintMinterm(bdd)
#                 assert(0)
    
    def set_abstract(self):
        all_vars = set(self.converter.var2node.keys())
        pabstract = all_vars.difference(self.pvars)
        nabstract = all_vars.difference(self.nvars)
        self.projPre = self.converter.cube_from_var_list(pabstract)
        self.projNex = self.converter.cube_from_var_list(nabstract)

        pnabstract = all_vars.difference(self.pvars)
        pnabstract = pnabstract.difference(self.nvars)
        self.projAll = self.converter.cube_from_var_list(pnabstract)

        self.N = len(self.p2nvars)
        self.preV = repycudd.DdArray(self.ddmanager, self.N)
        self.nexV = repycudd.DdArray(self.ddmanager, self.N)
        count = 0
        for pv, nv in self.p2nvars.items():
            self.preV[count] = self.converter.var2node[pv]
            self.nexV[count] = self.converter.var2node[nv]
            assert(self.preV[count] != self.nexV[count])
            count += 1

    def print_pla(self, bddI, bddT):
        self.print_espresso(bddI, self.patoms, gopts.out+"/init")
#         bddT = self.axiom
#         for action, actionBdds in self.actions.items():
#             for actionBdd in actionBdds:
#                 bddT = self.ddmanager.Or(bddT, actionBdd)
        allowed = self.patoms
        for k, v in self.natoms.items():
            allowed[k] = v
        self.dump_dot(bddT)
        self.print_espresso(bddT, allowed, gopts.out+"/trel_formula")
#         allowed = self.patoms
#         for lhs, rhs in self.natoms.items():
#             if lhs not in allowed:
#                 allowed[lhs] = rhs
#                 name = str(lhs)
#                 self.print_espresso(bddT, allowed, name)
#                 del allowed[lhs]

    def experiment(self, bdd):
        ab_vars = set(self.converter.var2node.keys())
        allowed_atoms = set()
        allowed_atoms.add("__semaphore(s0)")
#         allowed_atoms.add("__semaphore(s1)")
#         allowed_atoms.add("__semaphore(s2)")
        allowed_atoms.add("__link(c0, s0)")
#         allowed_atoms.add("__link(c1, s0)")
        for atom in self.patoms.keys():
            if str(atom) in allowed_atoms:
                var = self.converter.atom2var[atom]
                ab_vars.discard(var)
        proj = self.converter.cube_from_var_list(ab_vars)
        
        bddNew = self.ddmanager.ExistAbstract(bdd, proj)
        self.dump_dot(bddNew)
        assert(0)
    
    def check_safe(self, bdd):
        bddC = self.ddmanager.And(bdd, self.bddnotP)
        if bddC != self.ddmanager.ReadLogicZero():
            print("-- Finite check: violated --")
#             bddC = self.ddmanager.ExistAbstract(bddC, self.projPre)
            self.dump_dot(bddC)
            assert(0)
        else:
            print("-- Finite check: safe --")
    
    def execute(self):
        """Forward Reachability using BDDs."""
        prop = prop_formula(self)
        print("\nChecking property %s...\n" % prop)
        
        self.ddmanager = repycudd.DdManager()
        self.converter = BddConverter(environment=get_env(),
                                      ddmanager=self.ddmanager)
#         self.ddmanager.AutodynDisable()

        for k, v in self.system._enumsorts.items():
            if str(k).startswith("epoch"):
                self.converter.zero = v[0]
                break
        
        self.initialize_atoms()
        
        eprint(time_str(), "(building bdds)")
        bddI = self.formula2bdd(init_formula(self))
#         pathCount = bddI.CountPathsToNonZero()
#         print("Found %d paths in init" % pathCount)
#         self.dump_dot(bddI)
#         assert(0)
        
        self.build_actions()
        self.build_axioms()
                  
#         bddT = self.formula2bdd(trel_formula(self))
#         eprint(time_str(), "(building bdd for T done)")
# #         self.dump_dot(bddT)
# #         assert(0)
#            
#         if axiom_formula(self) != TRUE():
#             bddA = self.formula2bdd(axiom_formula(self))
# #             self.dump_dot(bddA)
# #             assert(0)
#             bddT = self.ddmanager.And(bddT, bddA)
# #             pathCount = bddT.CountPathsToNonZero()
# #             print("Found %d paths in trel /\ axioms" % pathCount)
#   
#         self.print_pla(bddI, bddT)
#         assert(0)
        
#         bddP = self.formula2bdd(prop_formula(self))
#         pathCount = bddP.CountPathsToNonZero()
#         print("Found %d paths in prop" % pathCount)
        
        
#         self.extract_pcubes(bddI, "Init")
#         self.extract_pcubes(bddT, "Trel")
#         self.extract_pcubes(bddA, "Axiom")
#         self.extract_pcubes(bddP, "Property")

#         self.set_atoms()
#         self.set_bddvars()
#         self.set_p2nVars()

        self.bddP = self.formula2bdd(prop_formula(self))
        self.bddnotP = self.ddmanager.Not(self.bddP)
#         self.dump_dot(self.bddP)
#         self.execute_espresso(self.bddP, self.patoms, True)
#         assert(0)
        
        self.set_abstract()
        
        sources = list()
        initSrc = self.ddmanager.AndAbstract(bddI, self.axiom, self.projPre)
        totalR = initSrc
        sources.append((initSrc, "init"))
        iteration = 0
        eprint("\t(running forward reachability)")
        while (len(sources) != 0):
#             print("#sources = %d" % len(sources))
            src, comment = sources.pop()
            iteration += 1
            
            if src == self.ddmanager.ReadLogicZero():
                print("#%d Found no new states" % iteration)
                continue
            else:
                print("#%d Found #%d new states: %s" % (iteration, len(sources)+1, comment))
            self.check_safe(src)
                
#                 src = self.ddmanager.And(src, self.axiom)
            notTotalR = self.ddmanager.Not(totalR)
            
            destinations = []
            for action, actionBdds in self.actions.items():
                nex = self.ddmanager.Zero()
                done = False
                for actionBdd in actionBdds:
                    image = self.ddmanager.AndAbstract(src, actionBdd, self.projNex)
                    if image == self.ddmanager.ReadLogicZero(): continue
                    image = self.ddmanager.SwapVariables(image, self.preV, self.nexV, self.N)
                    image = self.ddmanager.AndAbstract(image, self.axiom, self.projPre)
                    if image == self.ddmanager.ReadLogicZero(): continue
                    image = self.ddmanager.And(image, notTotalR)
                    if image == self.ddmanager.ReadLogicZero(): continue
                    nex = self.ddmanager.Or(nex, image)
                    done = True
#                     print("found a state in %s" % action)
#                         break
                if done:
                    destinations.append((nex, action))
            
            for dest, comment in destinations:
                sources.append((dest, comment))
                totalR = self.ddmanager.Or(totalR, dest)

#         eprint("\t(found total #%d paths)" % totalPathCount)
#         print("\t(found total #%d paths)" % totalPathCount)
        
#         print("Reachable states:")
#         self.ddmanager.PrintMinterm(totalR)

        totalR = self.ddmanager.ExistAbstract(totalR, self.projPre)
        
        if self.converter.zero != None:
            proj_vars = set(self.converter.var2node.keys())
            proj_vars = proj_vars.difference(self.pvars)
            for atom in self.gatoms.keys():
                enumc = atom.get_enum_constants()
                if self.converter.zero in enumc:
                    var = self.converter.atom2var[atom]
                    proj_vars.add(var)
                    self.patoms.pop(atom)
            projCustom = self.converter.cube_from_var_list(proj_vars)
            totalR = self.ddmanager.ExistAbstract(totalR, projCustom)
        
        self.dump_dot(totalR)
        
#         self.experiment(totalR)
        
#         assert(0)
        eprint("\t(forward reachability done)")
        print("\t(forward reachability done)")
        self.check_safe(totalR)
        
        notCubes_fast = self.execute_espresso(totalR, self.patoms, "fast")
        notCubes = notCubes_fast
#         notCubes_primes = self.execute_espresso(totalR, self.patoms, "primes")
#         notCubes = notCubes_primes
#         notCubes_exact = self.execute_espresso(totalR, self.patoms, "exact")
#         notCubes = notCubes_exact
        symCubes = set()
        eprint("\t(invoking symmetry on #%d)" % len(notCubes))
        print("\t(invoking symmetry on #%d)" % len(notCubes))
        for cube, cubeMap, l in notCubes:
            print("%s i.e. " % l, end='')
            pretty_print(cube)
            cubesOut = symmetry_cube(self, cube, 0, False)
            assert(len(cubesOut) == 1)
            for cubeSym, _ in cubesOut:
                symCubes.add(cubeSym)
                print("\t", end="")
                pretty_print(Not(cubeSym))
#         print("Symmetric notR: #%d" % len(symCubes))
        for idx, cubeSym in enumerate(symCubes):
            label = "frpo%d" % str(len(self.inferences)+1)
            clause = Not(cubeSym)
            self.inferences.append((label, clause))
        pretty_print_inv(self.inferences, "Forward inferences")
        return self.inferences
    
def forwardReach(fname):
    global start_time
    utils.start_time = time.time()
    system = TransitionSystem()
    p = FR(system)
    
    read_problem(p, fname)
    print("\t(running: frpo)")
    
    set_axiom_formula(p)

    if len(p.system.curr._infers) != 0:
        print()
        syntax_infers = []
        for cl, label in p.system.curr._infers.items():
            syntax_infers.append((label, cl))
        pretty_print_inv(syntax_infers, "Syntax-guided inferences")
    
    if not p.system.is_finite():
        print("System has unbounded sorts")
        print("All sorts should be finite for BDD-based forward reachability")
        assert(0)

#     set_solver(p)
    inferences = p.execute()
    eprint("\t(adding %d forward inferences)" % len(inferences))
    print("\t(adding %d forward inferences)" % len(inferences))
    p.reset()
    for tt in p.system._sort2fin.keys():
        p.system.unbound_sort(tt)
    p.system.infinitize()
    inferences_inf = {}
    for label, i in inferences:
        inferences_inf[i.fsubstitute()] = label
    for cl, label in inferences_inf.items():
        if cl not in p.system.orig._infers:
            p.system.orig._infers[cl] = label
            
    for k, v in iteritems(p.system._fin2sort):
        p.system._sort2fin[v] = k
    p.system._fin2sort.clear()

    return p.system
    
if __name__ == "__main__":  
    args = sys.argv
    if len(args) != 2:
        print("Usage %s <file.smt2>" % args[0])
        exit(1)
    fname = args[1]
    forwardReach(fname)
    
