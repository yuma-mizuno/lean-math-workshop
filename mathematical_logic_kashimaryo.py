import re

# class Symbol():
#     pass
# class Variable(Symbol):
#     pass
# class Constant(Symbol):
#     pass
# class Function(Symbol):
#     pass
# class Proposition(Symbol):
#     pass
# class Predicate(Symbol):
#     pass
# class Logic(Symbol):
#     pass
# class Quantifier(Logic):
#     pass
# class Auxiliary(Symbol):
#     pass
# class Term(Variable, Constant, ):
#     pass
# class LogicalFormula():
#     pass


def is_variable(x: str) -> bool:
    return re.match(r'^[a-z]$', x) is not None
def is_constant(x: str) -> bool:
    return re.match(r'^[0-9]$', x) is not None
def is_function(x: str) -> bool:
    # S: suc
    return re.match(r'^[+*S]$', x) is not None
def is_proposition(x: str) -> bool:
    return re.match(r'^[A-C]$', x) is not None
def is_predicate(x: str) -> bool:
    return re.match(r'^[=<>QPR]$', x) is not None
def is_quantifier(x: str) -> bool:
    return re.match(r'^[∀∃]$', x) is not None
def is_logic(x: str) -> bool:
    return is_quantifier(x) \
        or re.match(r'^[∧∨¬→↔]$', x) is not None
def is_auxiliary(x: str) -> bool:
    return re.match(r'^[(),]$', x) is not None

def restore_full_form(x_original: str) -> str:
    x = x_original.replace(' ', '')
    # 1. loop
    # 2. if function or predicate or logic add '()'
    return x

def is_correct_block_syntax(x: str) -> bool:



def is_term(x_original: str) -> bool:
    x = x_original.replace(' ', '')
    if len(x) == 0:
        return False

    for i in range(len(x)):
        if is_variable(x[i]) \
                or is_constant(x[i]) \
            or is_function(x[i]) \
            or is_auxiliary(x[i]) \
                :
            continue
        return False
    return True


def is_logical_formula(x_original: str) -> bool:
    x = x_original.replace(' ', '')
    if is_proposition(x):
        return True





## Substitution
example_proposition = '∀a∀y((∃x(z=x))∧(x<(y+x)))'

"""
∀
a
(
    ∀
    y
    (
        (
            ∃
            x
            (
                z
                =
                x
            )
        )
        ∧
        (
            x
            <
            (
                y
                +
                x
            )
        )
    )
)
"""



def is_substitution_possible() -> bool:
    pass
