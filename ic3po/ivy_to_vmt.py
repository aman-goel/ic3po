# ------------------------------------------
# IC3PO: IC3 for Proving Protocol Properties
# ------------------------------------------
# Copyright (c) 2018 - Present  Aman Goel and Karem Sakallah, University of Michigan. 
# All rights reserved.
#
# Author: Aman Goel (amangoel@umich.edu), University of Michigan
# ------------------------------------------

import sys

from ivy import ivy_logic
from ivy import ivy_utils as iu
from ivy import ivy_actions as ia
from ivy import logic as lg
from ivy import ivy_printer as ip

from ivy.ivy_logic import UninterpretedSort, UnionSort
from ivy import ivy_logic_utils as lut
from ivy import ivy_art
from ivy import ivy_interp as itp
from ivy import logic as lg
from ivy import logic_util as lgu
from ivy import ivy_init
from ivy import ivy_module as im
from ivy import ivy_utils as utl
from ivy import ivy_compiler
from ivy import ivy_isolate
from ivy import ivy_ast

outFile = "out.vmt"
outF = None
def fprint(s):
    global outF
    outF.write(s + "\n")


for cls in [lg.Eq, lg.Not, lg.And, lg.Or, lg.Implies, lg.Iff, lg.Ite, lg.ForAll, lg.Exists,
            lg.Apply, lg.Var, lg.Const, lg.Lambda, lg.NamedBinder]:
    if hasattr(cls,'__vmt__'):
        cls.__str__ = cls.__vmt__

class print_module_vmt():
    def __init__(self, mod):
        self.mod = mod
        self.sorts = {}
        self.pre = set()
        self.nex = set()
        self.updated = set()
        self.glo = set()
        self.vars = set()
        self.allvars = set()
        self.nex2pre = {}
        self.pre2nex = {}
        self.actions = set()
        self.helpers = {}
        self.definitions = set()
        self.defn_labels = []
        self.defs = set()
        self.str = {}
        self.vmt = {}
        self.prefix = "__"
        self.execute()

    def execute(self):
        if len(self.mod.labeled_props) != 0:
            print("labeled_props: %s" % str(self.mod.labeled_props))
            assert(0)
        if len(self.mod.labeled_inits) != 0:
            print("labeled_inits: %s" % str(self.mod.labeled_inits))
            assert(0)
        if len(self.mod.native_definitions) != 0:
            print("native_definitions: %s" % str(self.mod.native_definitions))
            assert(0)
        if len(self.mod.sig.interp) != 0:
            print("sig.interp: %s" % str(self.mod.sig.interp))
            assert(0)

        for i in range(len(self.mod.updates)):
            if type(self.mod.updates[i]) == ia.DerivedUpdate:
                defn = self.mod.updates[i].defn
#                 print("definitions: %s" % str(defn))
                self.definitions.add(defn)
            self.mod.definitions = []
#         if len(self.mod.definitions) != 0:
#             print("definitions: %s" % str(self.mod.definitions))
#             for defn in self.mod.definitions:
#                 self.definitions.add(defn)
#             self.mod.definitions = []
            
        with self.mod.theory_context():
            self.process_sig()
            self.process_defs()
            self.process_conj()
            self.process_axiom()
            self.process_init()
            self.process_actions()
            self.process_global()
    
            self.print_vmt()
            
    def print_vmt(self):
        global outF, outFile
        outF = open(outFile, 'w')
        
        for s in sorted(self.sorts.keys(), key=lambda v: str(v)):
            fprint(self.str[str(s)])
        fprint("")
        for s, v in sorted(self.sorts.iteritems(), key=lambda v: str(v)):
            self.print_sort_size(str(s), v)
        fprint("")
        for pre in sorted(self.pre, key=lambda v: str(v)):
            fprint(self.str[str(pre)])
        fprint("")
        for pre in sorted(self.pre, key=lambda v: str(v)):
            nex = self.pre2nex[pre]
            fprint(self.str[str(nex)])
        fprint("")
        for pre in sorted(self.pre, key=lambda v: str(v)):
            nex = self.pre2nex[pre]
            fprint(self.str[str(pre)+str(nex)])
        fprint("")
        if len(self.glo) != 0:
            for g in sorted(self.glo, key=lambda v: str(v)):
                fprint(self.str[str(g)])
            fprint("")
            for g in sorted(self.glo, key=lambda v: str(v)):
                pre = self.nex2pre[g]
                fprint(self.str[str(pre)+str(g)])
            fprint("")
        if len(self.vars) != 0:
            for v in sorted(self.vars, key=lambda v: str(v)):
                fprint(self.str[str(v)])
            fprint("")
        for h in sorted(self.defn_labels, key=lambda v: str(v)):
#            fprint(self.get_vmt_string_def(h))
            fprint(self.get_vmt_string(h))
            fprint("")
        fprint(self.get_vmt_string("$prop"))
        fprint("")
        if len(self.mod.labeled_axioms) != 0:
            fprint(self.get_vmt_string("$axiom"))
            fprint("")
        fprint(self.get_vmt_string("$init"))
        fprint("")
        for actname in sorted(self.actions, key=lambda v: str(v)):
            fprint(self.get_vmt_string(actname))
            fprint("")
        for h in sorted(self.helpers.keys(), key=lambda v: str(v)):
            fprint(self.get_vmt_string(h))
            fprint("")
        
    def process_sig(self):
        for name,sort in ivy_logic.sig.sorts.iteritems():
            if name == 'bool':
                continue
            if not isinstance(sort,UninterpretedSort):
                assert("todo")
            res = ''
            res += '(declare-sort {} 0)'.format(name)
            self.sorts[sort] = 0
            self.str[str(sort)] = res
            
        for sym in ivy_logic.sig.symbols.values():
            if isinstance(sym.sort,UnionSort):
                assert("todo")
            
            psym = sym.prefix('__')
            nsym = sym
            self.pre.add(psym)
            self.nex.add(nsym)
            self.pre2nex[psym] = nsym
            self.nex2pre[nsym] = psym
            self.allvars.add(psym)
            self.allvars.add(nsym)
            
            self.add_constant(sym, True)
        
        for lf in self.definitions:
            sym = lf.defines()
            if sym in self.allvars:
                continue
            if isinstance(sym.sort,UnionSort):
                assert("todo")
            
            psym = sym.prefix('__')
            nsym = sym
            self.pre.add(psym)
            self.nex.add(nsym)
            self.pre2nex[psym] = nsym
            self.nex2pre[nsym] = psym
            self.allvars.add(psym)
            self.allvars.add(nsym)
            
            self.add_constant(sym, True)
    
    def process_defs(self):
        self.process_defs_v2()
#         self.process_defs_v1()

    def process_defs_v0(self):
        for lf in self.definitions:
            f = lf.formula.to_constraint()
            self.add_new_constants(f)
            label = str(lf.label)
            res = (f, label, "axiom", "true")
            self.vmt[label] = res
            self.defn_labels.append(label)
            
            pref = lgu.substitute(f, self.nex2pre)
            self.add_new_constants(pref)
            label = "__" + str(lf.label)
            res = (pref, label, "axiom", "true")
            self.vmt[label] = res
            self.defn_labels.append(label)
            
    def process_defs_v1(self):
        for lf in self.definitions:
#             print(type(lf))
#             print(lf)
            sym = lf.defines()
            label = str(sym)
            lhs = lf.lhs()
            rhs = lf.rhs()
            self.add_new_constants(rhs)
            args = []
            if isinstance(lhs, lg.Apply):
                for arg in lhs.terms:
                    args.append(arg)
            self.add_definition(label, sym, args, rhs)
            
            sym = lgu.substitute(sym, self.nex2pre)
            label = str(sym)
            lhs = lgu.substitute(lf.lhs(), self.nex2pre)
            rhs = lgu.substitute(lf.rhs(), self.nex2pre)
            self.add_new_constants(rhs)
            args = []
            if isinstance(lhs, lg.Apply):
                for arg in lhs.terms:
                    args.append(arg)
            self.add_definition(label, sym, args, rhs)
            self.pre.remove(sym)
            self.defs.add(sym)
            
    def process_defs_v2(self):
        for lf in self.definitions:
#             print(type(lf))
#             print(lf)
            sym = lf.defines()
            print("definition: %s" % str(sym))
            
            label = "def_" + str(sym)
            lhs = lf.lhs()
            rhs = lf.rhs()
            self.add_new_constants(rhs)

            args = {}
            vargs = []
            if isinstance(lhs, lg.Apply):
                for arg in lhs.terms:
                    name = "V" + str(len(vargs))
                    varg = lg.Var(name, arg.sort)
                    args[arg] = varg
                    vargs.append(varg)
                lhs = lgu.substitute(lhs, args)
                rhs = lgu.substitute(rhs, args)
            f = lg.Eq(lhs, rhs)
            if len(vargs) != 0:
                f = lg.ForAll(vargs, f)
            res = (f, label, "definition", str(sym))
            self.vmt[label] = res
            self.defn_labels.append(label)
        
            sym = lgu.substitute(sym, self.nex2pre)
            label = "def_" + str(sym)
            pref = lgu.substitute(f, self.nex2pre)
            res = (pref, label, "definition", str(sym))
            self.vmt[label] = res
            self.defn_labels.append(label)
            
    def process_conj(self):
        fmlas = []
        helpers = []
        for lf in self.mod.labeled_conjs:
            label = str(lf.label)
            if label.startswith("help_"):
                helpers.append(lf)
            else:
                fmlas.append(lf.formula)
        cl = lut.Clauses(fmlas)
        f = self.get_formula(cl)
        pref = lgu.substitute(f, self.nex2pre)
        self.add_new_constants(pref)
        res = (pref, "prop", "invar-property", "0")
        self.vmt["$prop"] = res
        
        for lf in helpers:
            label = str(lf.label)
            self.helpers[label] = lf.formula
            cl = lut.Clauses([lf.formula])
            f = self.get_formula(cl)
            pref = lgu.substitute(f, self.nex2pre)
            self.add_new_constants(pref)
            res = (pref, label, "help", label)
            self.vmt[label] = res
        
    def process_axiom(self):
        fmlas = [lf.formula for lf in self.mod.labeled_axioms]
        cl = lut.Clauses(fmlas)
        f = self.get_formula(cl)
        self.add_new_constants(f)
        res = (f, "axiom", "axiom", "true")
        self.vmt["$axiom"] = res

    def process_init(self):
        init_cl = []
        for name,action in self.mod.initializers:
#             print ("init: ", str(action))
            ag = ivy_art.AnalysisGraph(initializer=lambda x:None)
            history = ag.get_history(ag.states[0])
            post = lut.and_clauses(history.post)
            init_cl.append(post)
        clauses = lut.and_clauses(*init_cl)
        f = self.get_formula(clauses)
        pref = lgu.substitute(f, self.nex2pre)
        self.add_new_constants(pref)
        res = (pref, "init", "init", "true")
        self.vmt["$init"] = res
        
    def process_actions(self):
        for name, action in self.mod.actions.iteritems():
#             print(type(action))
#             print ("action2: ", ia.action_def_to_str(name, action))
            ag = ivy_art.AnalysisGraph()
            pre = itp.State()
            pre.clauses = lut.true_clauses()
#             print(pre.to_formula())
            post = ag.execute(action, pre)
            history = ag.get_history(post)
            clauses = lut.and_clauses(history.post)
            f = self.get_formula(clauses)
            conjuncts = clauses.fmlas
            defn = lut.close_epr(lg.And(*conjuncts))
#             print(defn)
#             assert(0)
            
            update = action.update(pre.domain,pre.in_scope)
            sf = self.standardize_action(f, update[0], name)
            self.add_new_constants(sf)
            
            actname = "action_" + name
            self.actions.add(actname)
            res = (sf, actname, "action", name)
            self.vmt[actname] = res

    def process_global(self):
        for n in self.nex:
            if n not in self.updated:
                self.glo.add(n)
        subs = {}
        for n in self.glo:
            p = self.nex2pre[n]
            subs[p] = n
            def_label = "def_" + str(p)
            if def_label in self.defn_labels:
                self.defn_labels.remove(def_label)
            if p in self.defs:
                self.defn_labels.remove(str(p))
            else:
                self.pre.remove(p)
            self.str.pop(str(p))
            self.set_global(n, str(p)+str(n))
#             print("\treplacing %s -> %s globally" % (p, n))
        if len(subs) != 0:
            for k, v in self.vmt.iteritems():
                f, name, suffix, value = v
                newF = lgu.substitute(f, subs)
                self.vmt[k] = (newF, name, suffix, value)
        
    def standardize_action(self, f, nexvars, name):
        nexSet = set()
        for n in nexvars:
            nexSet.add(n)
            self.updated.add(n)

        cons = lgu.used_constants(f)
        subs = dict()
        evars = []
        for c in cons:
            if c in self.nex:
                if c not in nexSet:
                    subs[c] = self.nex2pre[c]
#             elif False and (c not in self.pre):
            elif c not in self.pre:
                if (not c.sort.dom) and (c.sort != lg.Boolean):
                    vname = "V"+c.name
#                     vname = vname.replace(":", "")
                    qv = lg.Var(vname, c.sort)
                    subs[c] = qv
                    evars.append(qv)
        action = f
        if len(subs) != 0:
#             for k, v in subs.iteritems():
#                 print("\treplacing %s -> %s in %s" % (k, v, name))
            action = lgu.substitute(f, subs)
        if len(evars) != 0:
            action = lg.Exists(evars, action)
        return action
        
  
    def add_new_constants(self, f):
        cons = lgu.used_constants(f)
        for c in cons:
            if c not in self.allvars:
                self.add_constant(c, False)
                self.vars.add(c)
                self.allvars.add(c)
                
    def add_constant(self, sym, addPre):   
        sort = sym.sort
        name = str(sym)
        prefix = ''
        prefix +=  '(declare-fun '
            
        suffix = ''
        suffix += " ("
        if sort.dom:
            suffix += ' '.join('{}'.format(s) for idx,s in enumerate(sort.dom))
        suffix += ")"
        if not sort.is_relational():
            suffix += ' {}'.format(sort.rng)
        else:
            suffix += ' Bool'
        suffix += ')'
        self.str[name] = prefix + name + suffix
        
        if addPre:
            psym = self.nex2pre[sym]
            prename = str(psym)
            prenex = ''
            prenex +=  '(define-fun '
            prenex +=  '.' + name
            prenex += " ("
            if sort.dom:
                prenex += ' '.join('(V{} {})'.format(idx, s) for idx,s in enumerate(sort.dom))
            prenex += ")"
            if not sort.is_relational():
                prenex += ' {}'.format(sort.rng)
            else:
                prenex += ' Bool'
            prenex += ' (! '
            if sort.dom:
                prenex += '(' + prename + ' '
                prenex += ' '.join('V{}'.format(idx) for idx,s in enumerate(sort.dom))
                prenex += ')'
            else:
                prenex += prename
            prenex += ' :next ' + name + '))'
            self.str[prename] = prefix + prename + suffix
            self.str[prename+name] = prenex
            
    def add_definition(self, label, sym, args, rhs):   
        sort = sym.sort
        name = str(sym)

        prenex = ''
        prenex +=  name
        prenex += " ("
        if sort.dom:
            prenex += ' '.join('({} {})'.format(args[idx], s) for idx,s in enumerate(sort.dom))
        prenex += ")"
        if not sort.is_relational():
            prenex += ' {}'.format(sort.rng)
        else:
            prenex += ' Bool'
        
#         No annotation, value is the prenex
        res = (rhs, label, "", prenex)
        self.vmt[label] = res
        self.defn_labels.append(label)
            
    def set_global(self, sym, k):
        sort = sym.sort
        name = str(sym)
        
        prenex = ''
        prenex +=  '(define-fun '
        prenex +=  '.' + name
        prenex += " ("
        if sort.dom:
            prenex += ' '.join('(V{} {})'.format(idx, s) for idx,s in enumerate(sort.dom))
        prenex += ")"
        if not sort.is_relational():
            prenex += ' {}'.format(sort.rng)
        else:
            prenex += ' Bool'
        prenex += ' (! '
        if sort.dom:
            prenex += '(' + name + ' '
            prenex += ' '.join('V{}'.format(idx) for idx,s in enumerate(sort.dom))
            prenex += ')'
        else:
            prenex += name
        prenex += ' :global true))'
        self.str[k] = prenex
                    
    def get_formula(self, clauses):
        cl = lut.and_clauses(clauses)
        f = cl.to_formula()
        return f
    
    def get_vmt_string(self, k):
        f, name, annot, value = self.vmt[k]
        if annot != "":
#            Has annotation
            res = '(define-fun .' + name + ' () Bool (! \n'
            res += ' (let (($v '
            res += str(f)
            res += '\n ))\n (and $v))'
            res += '\n :' + annot + ' ' + value + '))'
        else:
#            No annotation, value is the prefix
            res = '(define-fun ' + value + ' \n '
            res += str(f)
            res += '\n)'
        return res
    
    def get_vmt_string_def(self, k):
        f, name, prenex, value = self.vmt[k]
        
        res = prenex
        res += ' ' + str(f)
        res += '\n)'
        return res
    
    def print_sort_size(self, name, sz):
        res = ''
        res += '(define-fun .{} ((S {})) {} (! S :sort '.format(name, name, name)
        res += '{}))'.format(sz)
        fprint(res)
    

def print_isolate():
    temporals = [p for p in im.module.labeled_props if p.temporal]
    mod = im.module
    if temporals:
        if len(temporals) > 1:
            raise IvyError(None,'multiple temporal properties in an isolate not supported yet')
        from ivy_l2s import l2s
        l2s(mod, temporals[0])
        mod.concept_spaces = []
        mod.update_conjs()
#     ifc.check_fragment()
    print_module_vmt(mod)
    with im.module.theory_context():
#         ip.print_module(mod)
        pass
        return

def print_module():
    isolates = sorted(list(im.module.isolates))
    done_isolates = 0
    for isolate in isolates:
        if isolate != None and isolate in im.module.isolates:
            idef = im.module.isolates[isolate]
            if len(idef.verified()) == 0 or isinstance(idef,ivy_ast.TrustedIsolateDef):
                continue # skip if nothing to verify
        if isolate:
            print "\nPrinting isolate {}:".format(isolate)
        if done_isolates >= 1:
            raise iu.IvyError(None,"Expected exactly one isolate, got %s" % len(isolates))
        with im.module.copy():
            ivy_isolate.create_isolate(isolate) # ,ext='ext'
            print_isolate()
            done_isolates += 1

def usage():
    print "usage: \n  {} file.ivy output.vmt".format(sys.argv[0])
    sys.exit(1)

def main():
    global outFile
    import signal
    signal.signal(signal.SIGINT,signal.SIG_DFL)
    from ivy import ivy_alpha
    ivy_alpha.test_bottom = False # this prevents a useless SAT check
    ivy_init.read_params()
    if len(sys.argv) != 3 or not sys.argv[1].endswith('ivy'):
        usage()
    with im.Module():
        with utl.ErrorPrinter():
            ivy_init.source_file(sys.argv[1],ivy_init.open_read(sys.argv[1]),create_isolate=False)
            outFile = sys.argv[2]
            print_module()
    print "OK"


if __name__ == "__main__":
    main()

