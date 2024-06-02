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
    # 1char(left: Term, right: Term) -> Term
    # S: suc
    # +(1,2)
    # *(1,2)
    return re.match(r'^[+*S]$', x) is not None

def is_proposition(x: str) -> bool:
    return re.match(r'^[A-C]$', x) is not None


def is_predicate(x: str) -> bool:
    # 1char(left: Term, right: Term) -> bool
    # =(1,2)
    # <(1,2)
    # >(1,2)
    return re.match(r'^[=<>QPR]$', x) is not None


def is_quantifier(x: str) -> bool:
    return re.match(r'^[∀∃]$', x) is not None


def is_logic(x: str) -> bool:
    return is_quantifier(x) \
        or re.match(r'^[∧∨¬→↔]$', x) is not None


def is_auxiliary(x: str) -> bool:
    return re.match(r'^[(),]$', x) is not None


def restore_full_form_and_check_syntax(x_original: str) -> str:
    x = x_original.replace(' ', '')
    if len(x) == 0:
        raise ValueError('Empty string')
    # 1. loop
    for i in range(len(x)):
        current_char = x[i]
        # if current is not last and current is variable.
        if i < len(x) - 1:
            next_char = x[i + 1]
            if is_variable(current_char) or is_constant(current_char):
                if not is_auxiliary(next_char):
                    raise ValueError(f"Syntax Error: {x_original}. Because current '{current_char}' is variable and next '{next_char}'"
                                 f" is not auxiliary.")
            if is_function(current_char) or is_predicate(current_char):
                if not next_char == "(":
                    raise ValueError(f"Syntax Error: {x_original}. Because current '{current_char}' is function and next '{next_char}'"
                                    f" is not '('.")
            if is_quantifier(current_char):
                if


    # 2. if function or predicate or logic then add '()'
    return x


def is_correct_block_syntax(x: str) -> bool:
    pass


def is_term(x_original: str) -> bool:
    x = restore_full_form_and_check_syntax(x_original)
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
    x = restore_full_form_and_check_syntax(x_original)
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
