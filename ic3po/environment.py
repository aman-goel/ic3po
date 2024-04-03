# ------------------------------------------
# IC3PO: IC3 for Proving Protocol Properties
# ------------------------------------------
# Copyright (c) 2018 - Present  Aman Goel and Karem Sakallah, University of Michigan. 
# All rights reserved.
#
# Author: Aman Goel (amangoel@umich.edu), University of Michigan
# ------------------------------------------


# The FormulaManager needs to be extended to be able to use these
# operators. Notice that additional checks, and some simplifications
# can be performed at construction time. We keep this example simple.
import pysmt.formula

class FormulaManager(pysmt.formula.FormulaManager):
    """Extension of FormulaManager to handle node data for model checking"""


from pysmt.environment import Environment, pop_env, get_env
from pysmt.environment import push_env as pysmt_push_env

class EnvironmentTS(Environment):
    """Extension of pySMT environment."""
    # Only specify new classes. Classes that have been extended
    # directly do not need to be redefined here (e.g., TypeChecker)
    FormulaManagerClass = FormulaManager

# EOC EnvironmentTS


def push_env(env=None):
    """Overload push_env to default to the new Environment class."""
    if env is None:
        env = EnvironmentTS()
    return pysmt_push_env(env=env)

def reset_env():
    """Overload reset_env to use the new push_env()."""
    pop_env()
    push_env()
    return get_env()

# Create the default environment
reset_env()


if __name__ == "__main__":
    with EnvironmentTS() as env:
        mgr = env.formula_manager
        x = mgr.Symbol("x")
        print(x._content.data)
