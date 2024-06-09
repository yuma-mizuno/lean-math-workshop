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
    return re.match(r'^[=<>QPR]$', x) is not None


def is_quantifier(x: str) -> bool:
    return re.match(r'^[∀∃]$', x) is not None


def is_logic(x: str) -> bool:
    return is_quantifier(x) \
        or re.match(r'^[∧∨¬→↔]$', x) is not None


def is_auxiliary(x: str) -> bool:
    return re.match(r'^[(),]$', x) is not None


def is_correct_sytax(x_original: str) -> str:
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


def is_term(x_original: str) -> bool:
    x = x_original
    if len(x) == 1:
        return is_variable(x) or is_constant(x)
    all_variable_or_constant_with_index: Dict[int, str] = {}
    for i in range(len(x)):
        if is_variable(x[i]) or is_constant(x[i]):
            all_variable_or_constant_with_index[i] = x[i]

    deepest_stack_depth = find_deepest_stack_depth(x)
    all_variable_or_constant_with_index_and_depth: List[CharWithDepth] = []
    # assert is_term('+(a,1)') == True
    for current_char_index, current_cher in all_variable_or_constant_with_index.items():
        # i = 3, current_cher = 'a'
        depth = get_stack_depth(x, current_char_index)
        all_variable_or_constant_with_index_and_depth.append(CharWithDepth(current_char_index, current_cher, depth))

    for stack_depth in range(deepest_stack_depth, 0, -1):
        for char_with_index_and_depth in all_variable_or_constant_with_index_and_depth:
            深いものから変数と定数と置き換え文字を取り出す
            もしくは
            最初に見つけた')'から文字を置き換えていく


            if current_char.depth == stack_depth:
                open_parenthesis_index = find_open_parenthesis_index(x, current_char_index)
                if open_parenthesis_index is None:
                    raise ValueError(f"Syntax Error: {x}. Because current '{current_char_index}' is variable and not found '('")
                close_parenthesis_index = find_close_parenthesis_index(x, current_char_index)
                if close_parenthesis_index is None:
                    raise ValueError(f"Syntax Error: {x}. Because current '{current_char_index}' is variable and not found ')'")
                if open_parenthesis_index > close_parenthesis_index:
                    raise ValueError(f"Syntax Error: {x}. Because current '{current_char_index}' is variable and not found ')'")
                charactor_before_open_parenthesis = x[open_parenthesis_index - 1]
                if not is_function(charactor_before_open_parenthesis):
                    raise ValueError(f"Syntax Error: {x}. Because current '{current_char_index}' is variable and not found ')'")
                characters_between_parenthesis = x[open_parenthesis_index + 1:close_parenthesis_index]
                if not is_term(characters_between_parenthesis):
                    return False

    for current_char_index, current_char in all_variable_or_constant_with_index_and_depth:
        #--------------

        open_parenthesis_index = find_open_parenthesis_index(x, current_char_index)
        if open_parenthesis_index is None:
            raise ValueError(f"Syntax Error: {x}. Because current '{current_char_index}' is variable and not found '('")
        close_parenthesis_index = find_close_parenthesis_index(x, current_char_index)
        if close_parenthesis_index is None:
            raise ValueError(f"Syntax Error: {x}. Because current '{current_char_index}' is variable and not found ')'")
        if open_parenthesis_index > close_parenthesis_index:
            raise ValueError(f"Syntax Error: {x}. Because current '{current_char_index}' is variable and not found ')'")
        charactor_before_open_parenthesis = x[open_parenthesis_index - 1]
        if not is_function(charactor_before_open_parenthesis):
            raise ValueError(f"Syntax Error: {x}. Because current '{current_char_index}' is variable and not found ')'")
        characters_between_parenthesis = x[open_parenthesis_index + 1:close_parenthesis_index]


    for i in range(len(x)):
        if is_variable(x[i]) \
                or is_constant(x[i]) \
                or is_function(x[i]) \
                or is_auxiliary(x[i]) \
                :
            continue
        return False
        # TODO
    return True


def is_logical_formula(x_original: str) -> bool:
    x = is_correct_sytax(x_original)
    if is_proposition(x):
        return True
    # TODO


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
