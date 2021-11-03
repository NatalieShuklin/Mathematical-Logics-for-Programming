# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *


def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    # Task 3.5

    map_operators = {'->': Formula.parse('(~p|q)'),
                     '+': Formula.parse('((p&~q)|(~p&q))'),
                     '<->': Formula.parse('~((p&~q)|(~p&q))'),
                     '-&': Formula.parse('~(p&q)'),
                     '-|': Formula.parse('~(p|q)'),
                     'F': Formula.parse('(p&~p)'),
                     'T': Formula.parse('~(p&~p)')}
    return formula.substitute_operators(map_operators)


def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # Task 3.6a
    map_operators = {'->': Formula.parse('~(~~p&~q)'),
                     '+': Formula.parse('~(~(p&~q)&~(~p&q))'),
                     '<->': Formula.parse('~~(~(p&~q)&~(~p&q))'),
                     '-&': Formula.parse('~(p&q)'),
                     '-|': Formula.parse('~~(~p&~q)'),
                     'F': Formula.parse('(p&~p)'),
                     'T': Formula.parse('~(p&~p)'),
                     '|': Formula.parse('~(~p&~q)')}
    return formula.substitute_operators(map_operators)


def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # Task 3.6b
    not_in_nand = Formula('-&', Formula('p'), Formula('p'))
    and_in_nand_1 = Formula('-&', Formula('p'), Formula('q'))
    and_in_nand_2 = Formula('-&', and_in_nand_1, and_in_nand_1)
    map_not_and = {'~': not_in_nand, '&': and_in_nand_2}
    formula_not_and = to_not_and(formula)
    return formula_not_and.substitute_operators(map_not_and)


def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # Task 3.6c
    convert_and_op_1 = to_not_and(formula)
    and_formula_1 = Formula('->', Formula('p'), Formula('~', Formula('q')))
    and_formula_2 = Formula('->', Formula('~', Formula('p')), Formula('q'))

    map_and = {'&': Formula('~', Formula('->', and_formula_2, and_formula_1))}
    return convert_and_op_1.substitute_operators(map_and)


def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # Task 3.6d
    convert_implies = to_implies_not(formula)
    map_false = {'~': Formula('->', Formula('p'), Formula('F'))}
    return convert_implies.substitute_operators(map_false)
