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


def is_variable(variable: str) -> bool:
    return re.match(r'^[a-z]$', variable) is not None


def is_constant(constant: str) -> bool:
    return re.match(r'^[0-9]$', constant) is not None


def is_function(function: str) -> bool:
    # 1char(left: Term, right: Term) -> Term
    # 1char(left: Variable|Constant|Function, right: Variable|Constant|Function) -> Variable|Constant|Function
    # Termはこの時点では定義できてないはずシンボルだけを列挙して定義することになる
    # S: suc
    # +(1,2)
    # *(1,2)
    return re.match(r'^[+*]$', function) is not None


def is_proposition(proposition: str) -> bool:
    return re.match(r'^[A-C]$', proposition) is not None


def is_predicate(predicate: str) -> bool:
    # 1char(left: Term, right: Term) -> bool
    # =(1,2)
    # <(1,2)
    # >(1,2)
    # Q(1,2) # Q: is even
    # Q(x,2)
    return re.match(r'^[=<>QR]$', predicate) is not None


def is_quantifier(quantifier: str) -> bool:
    # ∀(Variable, LogicalFormula) -> LogicalFormula
    # ∃(Variable, LogicalFormula) -> LogicalFormula
    return re.match(r'^[∀∃]$', quantifier) is not None


def is_logic(logic: str) -> bool:
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
    return is_quantifier(logic) \
        or re.match(r'^[∧∨¬→↔⊥]$', logic) is not None


def is_auxiliary(auxiliary: str) -> bool:
    return re.match(r'^[(),]$', auxiliary) is not None


def find_open_parenthesis_index(expression: str, current_char_index: int) -> Optional[int]:
    open_parenthesis_index = None
    parenthesis_count = 0
    for j in range(current_char_index):
        candidate_open_parenthesis_index: int = current_char_index - (j + 1)
        candidate_charactor = expression[candidate_open_parenthesis_index]
        if candidate_charactor == "(":
            parenthesis_count += 1
        elif candidate_charactor == ")":
            parenthesis_count -= 1
        if parenthesis_count == 1:
            open_parenthesis_index = candidate_open_parenthesis_index
            break
    return open_parenthesis_index


def find_close_parenthesis_index(expression: str, current_char_index: int) -> Optional[int]:
    close_parenthesis_index = None
    parenthesis_count = 0
    for j in range(current_char_index, len(expression)):
        candidate_close_parenthesis_index: int = current_char_index + (j + 1)
        candidate_charactor = expression[candidate_close_parenthesis_index]
        if candidate_charactor == "(":
            parenthesis_count += 1
        elif candidate_charactor == ")":
            parenthesis_count -= 1
        if parenthesis_count == 1:
            close_parenthesis_index = candidate_close_parenthesis_index
            break
    return close_parenthesis_index


def find_deepest_stack_depth(expression: str) -> int:
    deepest_stack_depth = 0
    stack_count = 0

    for i in range(len(expression)):
        if expression[i] == "(":
            stack_count += 1
        elif expression[i] == ")":
            stack_count -= 1
        if stack_count > deepest_stack_depth:
            deepest_stack_depth = stack_count
    return deepest_stack_depth


def get_stack_depth(expression: str, target_index: int) -> int:
    stack_count = 0
    for i in range(target_index):
        if expression[i] == "(":
            stack_count += 1
        elif expression[i] == ")":
            stack_count -= 1
    return stack_count


class CharWithDepth:
    def __init__(self, index: int, char: str, depth: int):
        self.index = index
        self.char = char
        self.depth = depth


def is_correct_tree(expression: str) -> bool:
    stack_count = 0
    for i in range(len(expression)):
        if expression[i] == "(":
            stack_count += 1
        elif expression[i] == ")":
            stack_count -= 1
        if stack_count < 0:
            return False
    return stack_count == 0


def replace_term_to_t(
        expression: str,
        term_mark: str,
        function_mark: str,
) -> str:
    for i in range(len(expression)):
        current_char = expression[i]
        if is_variable(current_char) or is_constant(current_char):
            expression = expression.replace(current_char, term_mark)
        if is_function(current_char):
            expression = expression.replace(current_char, function_mark)

    while f"{function_mark}({term_mark},{term_mark})" in expression:
        expression = expression.replace(f"{function_mark}({term_mark},{term_mark})", term_mark)
    return expression


def replace_logical_formula_to_l(
        expression: str,
        term_mark: str,
        function_mark: str,
        predicate_mark: str,
        logical_formula_mark: str,
) -> str:
    expression = replace_term_to_t(expression, term_mark, function_mark)

    for i in range(len(expression)):
        current_char = expression[i]
        if is_proposition(current_char):
            expression = expression.replace(current_char, logical_formula_mark)
        if is_predicate(current_char):
            expression = expression.replace(current_char, predicate_mark)
    # Replaced: Variable, Constant, Function, Predicate

    while (f"{predicate_mark}({term_mark},{term_mark})" in expression \
           or f"⊥()" in expression \
           or f"¬({logical_formula_mark})" in expression \
           or f"∧({logical_formula_mark},{logical_formula_mark})" in expression \
           or f"∨({logical_formula_mark},{logical_formula_mark})" in expression \
           or f"→({logical_formula_mark},{logical_formula_mark})" in expression \
           or f"↔({logical_formula_mark},{logical_formula_mark})" in expression \
           or f"∀({term_mark},{logical_formula_mark})" in expression \
           or f"∃({term_mark},{logical_formula_mark})" in expression \
            ):
        expression = expression.replace(f"{predicate_mark}({term_mark},{term_mark})", logical_formula_mark)
        expression = expression.replace(f"⊥()", logical_formula_mark)
        expression = expression.replace(f"¬({logical_formula_mark})", logical_formula_mark)
        expression = expression.replace(f"∧({logical_formula_mark},{logical_formula_mark})", logical_formula_mark)
        expression = expression.replace(f"∨({logical_formula_mark},{logical_formula_mark})", logical_formula_mark)
        expression = expression.replace(f"→({logical_formula_mark},{logical_formula_mark})", logical_formula_mark)
        expression = expression.replace(f"↔({logical_formula_mark},{logical_formula_mark})", logical_formula_mark)
        expression = expression.replace(f"∀({term_mark},{logical_formula_mark})", logical_formula_mark)
        expression = expression.replace(f"∃({term_mark},{logical_formula_mark})", logical_formula_mark)

    return expression


def is_term(expression: str) -> bool:
    x = expression
    term_mark = "T"
    function_mark = "F"
    if not is_correct_tree(x):
        return False
    if term_mark in x:
        return False
    if function_mark in x:
        return False
    return replace_term_to_t(x, term_mark, function_mark) == term_mark

def is_no_vioration_of_nested_quantifier(expression: str) -> bool:
    syntax_template = "∀(a,P)"
    for i in range(len(expression)):
        current_char = expression[i]
        if not is_quantifier(current_char):
            continue
        if i + len(syntax_template) > len(expression):
            return False
        next_char = expression[i + 1]
        if next_char != "(":
            return False
        bound_variable = expression[i + 2]
        if not is_variable(bound_variable):
            return False
        stack_count = 0
        for j in range(i + 3, len(expression)):
            current_char_in_quantifier = expression[j]
            if current_char_in_quantifier == "(":
                stack_count += 1
                continue
            elif current_char_in_quantifier == ")":
                stack_count -= 1
                continue
            if stack_count == -1:
                break
            if not is_quantifier(current_char_in_quantifier):
                continue
            if len(expression) < j + 2:
                return False
            if expression[j + 2] == bound_variable:
                return False

    return True

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

    if not is_no_vioration_of_nested_quantifier(x):
        return False

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


def is_expression(expression: str) -> bool:
    return is_logical_formula(expression) or is_term(expression)


def get_variable_symbol_from_term(t: str) -> List[str]:
    variables = [char for char in t if is_variable(char)]
    return list(set(variables))


def find_bound_variables(
        expression: str,
        target_index: int,
) -> List[str]:
    stack_count = 0
    bound_variables = []
    for j in range(len(expression) - target_index):
        current_char_before_target_variable = expression[len(expression) - target_index - j - 1]
        if current_char_before_target_variable == "(":
            stack_count += 1
            continue
        elif current_char_before_target_variable == ")":
            stack_count -= 1
            continue
        if stack_count < 0:
            continue

        if len(expression)-target_index-j-1-2 < 0:
            break
        quantifier_for_current_char_before_target_variable = expression[len(expression) - target_index - j - 1 - 2]
        if not is_quantifier(quantifier_for_current_char_before_target_variable):
            continue
        bound_variables.append(current_char_before_target_variable)

    return bound_variables


def is_substitution_possible(expression: str, target_variable_symbol: str, target_term: str) -> bool:
    phi = expression
    x = target_variable_symbol
    t = target_term

    if not is_logical_formula(phi):
        return False

    # ∀(Variable, LogicalFormula) -> LogicalFormula
    # ∃(Variable, LogicalFormula) -> LogicalFormula

    # y ∈ Var(t)
    variables_in_t = get_variable_symbol_from_term(t)

    for i in range(len(phi)):
        current_char = phi[len(phi)-i-1]
        if current_char != x:
            continue
        bound_variables = find_bound_variables(phi, i)
        if x in bound_variables:
            continue  # x is free variable

        for bound_variable in bound_variables:
            if bound_variable in variables_in_t:
                return False

    return True


def substitute(expression: str, target_variable_symbol: str, target_term: str) -> str:
    phi = expression
    x = target_variable_symbol
    t = target_term

    if not is_substitution_possible(phi, x, t):
        raise ValueError("Substitution is not possible.")

