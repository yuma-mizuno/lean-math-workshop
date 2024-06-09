from sympy.testing import pytest

from mathematical_logic_kashimaryo import find_deepest_stack_depth


def test_is_variable():
    from mathematical_logic_kashimaryo import is_variable
    assert is_variable('x') == True
    assert is_variable('X') == False
    assert is_variable('1') == False
    assert is_variable('a') == True
    assert is_variable('A') == False
    assert is_variable('z') == True
    assert is_variable('Z') == False
    assert is_variable('0') == False
    assert is_variable('9') == False
    assert is_variable(' ') == False
    assert is_variable('') == False
    assert is_variable('aa') == False
    assert is_variable('aA') == False
    assert is_variable('a1') == False
    assert is_variable('a ') == False


def test_is_constant():
    from mathematical_logic_kashimaryo import is_constant
    assert is_constant('x') == False
    assert is_constant('X') == False
    assert is_constant('1') == True
    assert is_constant('a') == False
    assert is_constant('A') == False
    assert is_constant('z') == False
    assert is_constant('Z') == False
    assert is_constant('0') == True
    assert is_constant('9') == True
    assert is_constant(' ') == False
    assert is_constant('') == False
    assert is_constant('aa') == False
    assert is_constant('aA') == False
    assert is_constant('a1') == False
    assert is_constant('a ') == False


def test_is_function():
    from mathematical_logic_kashimaryo import is_function
    assert is_function('x') == False
    assert is_function('X') == False
    assert is_function('1') == False
    assert is_function('a') == False
    assert is_function('A') == False
    assert is_function('z') == False
    assert is_function('Z') == False
    assert is_function('0') == False
    assert is_function('9') == False
    assert is_function(' ') == False
    assert is_function('') == False
    assert is_function('aa') == False
    assert is_function('aA') == False
    assert is_function('a1') == False
    assert is_function('a ') == False
    assert is_function('+') == True
    assert is_function('*') == True
    assert is_function('S') == True
    assert is_function('s') == False
    assert is_function(' ') == False
    assert is_function('') == False
    assert is_function('++') == False
    assert is_function('*+') == False
    assert is_function('S*') == False


def test_is_proposition():
    from mathematical_logic_kashimaryo import is_proposition
    assert is_proposition('x') == False
    assert is_proposition('X') == False
    assert is_proposition('1') == False
    assert is_proposition('a') == False
    assert is_proposition('A') == True
    assert is_proposition('b') == False
    assert is_proposition('B') == True
    assert is_proposition('c') == False
    assert is_proposition('C') == True
    assert is_proposition('z') == False
    assert is_proposition('Z') == False
    assert is_proposition('0') == False
    assert is_proposition('9') == False
    assert is_proposition(' ') == False
    assert is_proposition('') == False
    assert is_proposition('aa') == False
    assert is_proposition('aA') == False
    assert is_proposition('a1') == False
    assert is_proposition('a ') == False


def test_is_predicate():
    from mathematical_logic_kashimaryo import is_predicate
    assert is_predicate('x') == False
    assert is_predicate('X') == False
    assert is_predicate('1') == False
    assert is_predicate('a') == False
    assert is_predicate('A') == False
    assert is_predicate('z') == False
    assert is_predicate('Z') == False
    assert is_predicate('0') == False
    assert is_predicate('9') == False
    assert is_predicate(' ') == False
    assert is_predicate('') == False
    assert is_predicate('aa') == False
    assert is_predicate('aA') == False
    assert is_predicate('a1') == False
    assert is_predicate('a ') == False
    assert is_predicate('=') == True
    assert is_predicate('<') == True
    assert is_predicate('>') == True
    assert is_predicate('<=') == False
    assert is_predicate('=>') == False
    assert is_predicate('==') == False
    assert is_predicate('<>') == False


def test_is_quantifier():
    from mathematical_logic_kashimaryo import is_quantifier
    assert is_quantifier('x') == False
    assert is_quantifier('X') == False
    assert is_quantifier('1') == False
    assert is_quantifier('a') == False
    assert is_quantifier('A') == False
    assert is_quantifier('z') == False
    assert is_quantifier('Z') == False
    assert is_quantifier('0') == False
    assert is_quantifier('9') == False
    assert is_quantifier(' ') == False
    assert is_quantifier('') == False
    assert is_quantifier('aa') == False
    assert is_quantifier('aA') == False
    assert is_quantifier('a1') == False
    assert is_quantifier('a ') == False
    assert is_quantifier('∀') == True
    assert is_quantifier('∃') == True
    assert is_quantifier('∀∃') == False
    assert is_quantifier('∃∀') == False
    assert is_quantifier('∀∀') == False
    assert is_quantifier('∃∃') == False


def test_is_logic():
    from mathematical_logic_kashimaryo import is_logic
    assert is_logic('x') == False
    assert is_logic('X') == False
    assert is_logic('1') == False
    assert is_logic('a') == False
    assert is_logic('A') == False
    assert is_logic('z') == False
    assert is_logic('Z') == False
    assert is_logic('0') == False
    assert is_logic('9') == False
    assert is_logic(' ') == False
    assert is_logic('') == False
    assert is_logic('aa') == False
    assert is_logic('aA') == False
    assert is_logic('a1') == False
    assert is_logic('a ') == False
    assert is_logic('∀') == True
    assert is_logic('∃') == True
    assert is_logic('∧') == True
    assert is_logic('∨') == True
    assert is_logic('¬') == True
    assert is_logic('→') == True
    assert is_logic('↔') == True
    assert is_logic('∀∃') == False
    assert is_logic('∃∀') == False
    assert is_logic('∀∀') == False
    assert is_logic('∃∃') == False
    assert is_logic('∧∨') == False
    assert is_logic('∧∧') == False
    assert is_logic('∨∨') == False
    assert is_logic('∧∨∧') == False
    assert is_logic('∧∨∨') == False
    assert is_logic('∧∨∧∨') == False
    assert is_logic('∧∨∧∧') == False
    assert is_logic('∧∨∨∨') == False
    assert is_logic('∧∨∨∧') == False
    assert is_logic('∧∨∧∧∨') == False
    assert is_logic('∧∨∧∧∧') == False


def test_is_auxiliary():
    from mathematical_logic_kashimaryo import is_auxiliary
    assert is_auxiliary('x') == False
    assert is_auxiliary('X') == False
    assert is_auxiliary('1') == False
    assert is_auxiliary('a') == False
    assert is_auxiliary('A') == False
    assert is_auxiliary('z') == False
    assert is_auxiliary('Z') == False
    assert is_auxiliary('0') == False
    assert is_auxiliary('9') == False
    assert is_auxiliary(' ') == False
    assert is_auxiliary('') == False
    assert is_auxiliary('aa') == False
    assert is_auxiliary('aA') == False
    assert is_auxiliary('a1') == False
    assert is_auxiliary('a ') == False
    assert is_auxiliary('∀') == False
    assert is_auxiliary('∃') == False
    assert is_auxiliary('∧') == False
    assert is_auxiliary('∨') == False
    assert is_auxiliary('¬') == False
    assert is_auxiliary('→') == False
    assert is_auxiliary('↔') == False
    assert is_auxiliary('∀∃') == False
    assert is_auxiliary('∃∀') == False
    assert is_auxiliary('∀∀') == False
    assert is_auxiliary('∃∃') == False
    assert is_auxiliary('∧∨') == False
    assert is_auxiliary('∧∧') == False
    assert is_auxiliary('∨∨') == False
    assert is_auxiliary('∧∨∧') == False
    assert is_auxiliary('∧∨∨') == False
    assert is_auxiliary('∧∨∧∨') == False
    assert is_auxiliary('∧∨∨∨') == False
    assert is_auxiliary('∧∨∨∧') == False
    assert is_auxiliary('∧∨∧∧') == False
    assert is_auxiliary('∧∨∧∨') == False
    assert is_auxiliary('∧∨∨∧') == False


def test_restore_full_form():
    # formula should be full form
    # function should be function_name() style.
    from mathematical_logic_kashimaryo import is_correct_sytax
    is_correct_sytax('+(+(1,1),2)') # TODO


    is_correct_sytax('∀a(A)')
    is_correct_sytax('+(1,2)')
    is_correct_sytax('A^B')
    is_correct_sytax('(B^A)^A')
    with pytest.raises(ValueError):
        is_correct_sytax('+(∀(1,1),2)')
    with pytest.raises(ValueError):
        is_correct_sytax('aa(A)')
    # function
    with pytest.raises(ValueError):
        is_correct_sytax('(a,b)')
    with pytest.raises(ValueError):
        is_correct_sytax('+a')

    with pytest.raises(ValueError):
        is_correct_sytax('+')
    with pytest.raises(ValueError):
        is_correct_sytax('=')


def test_is_correct_block_syntax():
    from mathematical_logic_kashimaryo import is_correct_block_syntax
    assert is_correct_block_syntax('(x)') == True
    assert is_correct_block_syntax('x') == True
    assert is_correct_block_syntax('1') == True
    assert is_correct_block_syntax('a') == True
    assert is_correct_block_syntax('z') == True
    assert is_correct_block_syntax('0') == True
    assert is_correct_block_syntax('9') == True
    assert is_correct_block_syntax('6 * y') == True
    assert is_correct_block_syntax('S(6)') == True
    assert is_correct_block_syntax('S(6,a)') == True
    assert is_correct_block_syntax('∀a(6,a)') == True
    assert is_correct_block_syntax('S(S(6))') == True
    assert is_correct_block_syntax('Q(1)') == True
    assert is_correct_block_syntax('R(1,a)') == True
    assert is_correct_block_syntax('+') == False
    assert is_correct_block_syntax('S') == False
    assert is_correct_block_syntax('*x') == False
    assert is_correct_block_syntax('x*') == False
    assert is_correct_block_syntax('=') == False
    assert is_correct_block_syntax('=6') == False
    assert is_correct_block_syntax('Q') == False
    assert is_correct_block_syntax('Q()') == False
    assert is_correct_block_syntax('Q()') == False
    assert is_correct_block_syntax('<') == False
    assert is_correct_block_syntax('(x') == False
    assert is_correct_block_syntax('(x))') == False
    assert is_correct_block_syntax('aa') == False
    assert is_correct_block_syntax('11') == False
    assert is_correct_block_syntax('SP') == False
    assert is_correct_block_syntax('S P') == False

def test_find_deepest_stack_depth():
    assert find_deepest_stack_depth('+(+(a,1),+(a,1))') == 2
    assert find_deepest_stack_depth('+(+(a,1),+(+(a,a),1))') == 3
    assert find_deepest_stack_depth('a') == 0
    assert find_deepest_stack_depth('+(a,1)') == 1

def test_is_term():
    from mathematical_logic_kashimaryo import is_term
    assert is_term('+(1,a)') == True
    assert is_term('+(+(a,1),a)') == True
    assert is_term('+(+(a,1),+(a,1))') == True
    with pytest.raises(ValueError):
        is_term('+(+(a,1),+(a,1),+(a,1))')
    with pytest.raises(ValueError):
        assert is_term('1+')
    # variable or constant 1,1,2
    # index4-1:  index3-(, index7-)
    # index4-1 syntac:  index3-(, index4-1, ',', variable or constant or function(), index7-)

    # function_char(isTerm())



    assert is_term('x') == True
    assert is_term('1') == True
    assert is_term('a') == True
    assert is_term('z') == True
    assert is_term('0') == True
    assert is_term('9') == True
    assert is_term('aA') == False
    assert is_term('a1') == False
    # assert is_term('6*y') == True
    # assert is_term('(6*y)') == True
    # assert is_term('∀a(6,a)') == False
    # assert is_term('∃a(6,a)') == False
    # assert is_term('x ∧ y ') == False
    # assert is_term('a=b') == False
    # assert is_term('a<b') == False
    # assert is_term('X') == False
    # assert is_term('A') == False
    # assert is_term('Z') == False

#
# ## Term
# example_term_y = 'y'
# example_term_six = '6*y'
# """
# block
# 6
# *
# y
# """
# def is_term(x: str) -> bool:
#     # 1. separate to block
#
#
#     pass
#
#
#
#
#
#
# ## Substitution
# example_proposition = '∀a∀y((∃x(z=x))∧(x<(y+x)))'
#
# """
# ∀
# a
# (
#     ∀
#     y
#     (
#         (
#             ∃
#             x
#             (
#                 z
#                 =
#                 x
#             )
#         )
#         ∧
#         (
#             x
#             <
#             (
#                 y
#                 +
#                 x
#             )
#         )
#     )
# )
# """
#
#
#
# def is_substitution_possible() -> bool:
