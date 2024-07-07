import re
from typing import List, Dict, Optional


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
    # 1char(left: Variable|Constant|Function, right: Variable|Constant|Function) -> Variable|Constant|Function
    # Termはこの時点では定義できてないはずシンボルだけを列挙して定義することになる
    # S: suc
    # +(1,2)
    # *(1,2)
    return re.match(r'^[+*]$', x) is not None


def is_proposition(x: str) -> bool:
    return re.match(r'^[A-C]$', x) is not None


def is_predicate(x: str) -> bool:
    # 1char(left: Term, right: Term) -> bool
    # =(1,2)
    # <(1,2)
    # >(1,2)
    # Q(1,2) # Q: is even
    # Q(x,2)
    return re.match(r'^[=<>QR]$', x) is not None


def is_quantifier(x: str) -> bool:
    # ∀(Variable, LogicalFormula) -> LogicalFormula
    # ∃(Variable, LogicalFormula) -> LogicalFormula
    return re.match(r'^[∀∃]$', x) is not None


def is_logic(x: str) -> bool:
    # 1char(LogicalFormula, LogicalFormula) -> LogicalFormula
    # ∧(A,B)
    # ∨(A,B)
    # →(A,B)
    # ¬だけはLogicalFormulaが1つだけ
    # 1char(LogicalFormula) -> LogicalFormula
    # ¬(A)
    # ⊥だけはLogicalFormulaがいらない
    # 1char() -> LogicalFormula
    # ⊥()

    # LogicalFormula: φ,ψ,⊥,
    return is_quantifier(x) \
        or re.match(r'^[∧∨¬→↔⊥]$', x) is not None


def is_auxiliary(x: str) -> bool:
    return re.match(r'^[(),]$', x) is not None


def is_correct_syntax(x_original: str) -> str:
    x = x_original.replace(' ', '')
    if len(x) == 0:
        raise ValueError('Empty string')

    # correct all variable and
    # 1. loop
    stack: List[str] = []
    for i in range(len(x)):
        current_char = x[i]
        previous_char = None
        if i > 0:
            previous_char = x[i - 1]
        # if current is not last and current is variable.
        if i < len(x) - 1:
            next_char = x[i + 1]
            if is_variable(current_char) or is_constant(current_char):
                if not is_auxiliary(next_char):
                    raise ValueError(
                        f"Syntax Error: {x_original}. Because current '{current_char}' is variable and next '{next_char}'"
                        f" is not auxiliary.")
                if next_char == ",":
                    if not is_function(stack[-1]):
                        raise ValueError(
                            f"Syntax Error: {x_original}. Because current '{current_char}' is variable and next '{next_char}'"
                            f" is not auxiliary.")

            if is_function(current_char):
                if not next_char == "(":
                    raise ValueError(
                        f"Syntax Error: {x_original}. Because current '{current_char}' is function and next '{next_char}'"
                        f" is not '('.")
                stack.append(current_char)
            if is_predicate(current_char):
                if not next_char == "(":
                    raise ValueError(
                        f"Syntax Error: {x_original}. Because current '{current_char}' is function and next '{next_char}'"
                        f" is not '('.")

            if is_proposition(current_char):
                pass  # TODO
                # if not is_auxiliary(next_char):
                #     raise ValueError(f"Syntax Error: {x_original}. Because current '{current_char}' is proposition and next '{next_char}'"
                #                     f" is not auxiliary.")

            if is_quantifier(current_char):
                # TODO check
                pass

    # 2. if function or predicate or logic then add '()'
    return x


def is_correct_block_syntax(x: str) -> bool:
    pass


def find_open_parenthesis_index(x: str, current_char_index: int) -> Optional[int]:
    open_parenthesis_index = None
    parenthesis_count = 0
    for j in range(current_char_index):
        candidate_open_parenthesis_index: int = current_char_index - (j + 1)
        candidate_charactor = x[candidate_open_parenthesis_index]
        if candidate_charactor == "(":
            parenthesis_count += 1
        elif candidate_charactor == ")":
            parenthesis_count -= 1
        if parenthesis_count == 1:
            open_parenthesis_index = candidate_open_parenthesis_index
            break
    return open_parenthesis_index


def find_close_parenthesis_index(x: str, current_char_index: int) -> Optional[int]:
    close_parenthesis_index = None
    parenthesis_count = 0
    for j in range(current_char_index, len(x)):
        candidate_close_parenthesis_index: int = current_char_index + (j + 1)
        candidate_charactor = x[candidate_close_parenthesis_index]
        if candidate_charactor == "(":
            parenthesis_count += 1
        elif candidate_charactor == ")":
            parenthesis_count -= 1
        if parenthesis_count == 1:
            close_parenthesis_index = candidate_close_parenthesis_index
            break
    return close_parenthesis_index


def find_deepest_stack_depth(x: str) -> int:
    deepest_stack_depth = 0
    stack_count = 0

    for i in range(len(x)):
        if x[i] == "(":
            stack_count += 1
        elif x[i] == ")":
            stack_count -= 1
        if stack_count > deepest_stack_depth:
            deepest_stack_depth = stack_count
    return deepest_stack_depth


def get_stack_depth(x: str, target_index: int) -> int:
    stack_count = 0
    for i in range(target_index):
        if x[i] == "(":
            stack_count += 1
        elif x[i] == ")":
            stack_count -= 1
    return stack_count


class CharWithDepth:
    def __init__(self, index: int, char: str, depth: int):
        self.index = index
        self.char = char
        self.depth = depth


def is_correct_tree(x: str) -> bool:
    stack_count = 0
    for i in range(len(x)):
        if x[i] == "(":
            stack_count += 1
        elif x[i] == ")":
            stack_count -= 1
        if stack_count < 0:
            return False
    return stack_count == 0


def replace_term_to_t(
        x: str,
        term_mark: str,
        function_mark: str,
) -> str:
    for i in range(len(x)):
        current_char = x[i]
        if is_variable(current_char) or is_constant(current_char):
            x = x.replace(current_char, term_mark)
        if is_function(current_char):
            x = x.replace(current_char, function_mark)

    while f"{function_mark}({term_mark},{term_mark})" in x:
        x = x.replace(f"{function_mark}({term_mark},{term_mark})", term_mark)
    return x


def replace_logical_formula_to_l(
        x: str,
        term_mark: str,
        function_mark: str,
        predicate_mark: str,
        logical_formula_mark: str,
) -> str:
    x = replace_term_to_t(x, term_mark, function_mark)

    for i in range(len(x)):
        current_char = x[i]
        if is_proposition(current_char):
            x = x.replace(current_char, logical_formula_mark)
        if is_predicate(current_char):
            x = x.replace(current_char, predicate_mark)
    # Replaced: Variable, Constant, Function, Predicate

    while (f"{predicate_mark}({term_mark},{term_mark})" in x \
           or f"⊥()" in x \
           or f"¬({logical_formula_mark})" in x \
           or f"∧({logical_formula_mark},{logical_formula_mark})" in x \
           or f"∨({logical_formula_mark},{logical_formula_mark})" in x \
           or f"→({logical_formula_mark},{logical_formula_mark})" in x \
           or f"↔({logical_formula_mark},{logical_formula_mark})" in x \
           or f"∀({term_mark},{logical_formula_mark})" in x \
           or f"∃({term_mark},{logical_formula_mark})" in x \
            ):
        x = x.replace(f"{predicate_mark}({term_mark},{term_mark})", logical_formula_mark)
        x = x.replace(f"⊥()", logical_formula_mark)
        x = x.replace(f"¬({logical_formula_mark})", logical_formula_mark)
        x = x.replace(f"∧({logical_formula_mark},{logical_formula_mark})", logical_formula_mark)
        x = x.replace(f"∨({logical_formula_mark},{logical_formula_mark})", logical_formula_mark)
        x = x.replace(f"→({logical_formula_mark},{logical_formula_mark})", logical_formula_mark)
        x = x.replace(f"↔({logical_formula_mark},{logical_formula_mark})", logical_formula_mark)
        x = x.replace(f"∀({term_mark},{logical_formula_mark})", logical_formula_mark)
        x = x.replace(f"∃({term_mark},{logical_formula_mark})", logical_formula_mark)

        return x


def is_term(x_original: str) -> bool:
    x = x_original
    term_mark = "T"
    function_mark = "F"
    if not is_correct_tree(x):
        return False
    if term_mark in x:
        return False
    if function_mark in x:
        return False
    return replace_term_to_t(x, term_mark, function_mark) == term_mark


def is_logical_formula(x_original: str) -> bool:
    x = x_original

    term_mark = "T"
    function_mark = "F"
    predicate_mark = "P"
    logical_formula_mark = "L"
    if not is_correct_tree(x):
        return False
    elif term_mark in x \
            or function_mark in x \
            or logical_formula_mark in x:
        return False

    if is_proposition(x):
        return True

    for i in range(len(x)):
        current_char = x[i]
        if not is_quantifier(current_char):
            continue
        elif len(x) < i + 2:
            return False
        elif not is_variable(x[i + 2]):
            return False

    x = replace_logical_formula_to_l(x, term_mark, function_mark, predicate_mark, logical_formula_mark)
    return x == logical_formula_mark


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
