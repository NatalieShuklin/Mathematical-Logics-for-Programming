# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: propositions/syntax.py

"""Syntactic handling of propositional formulas."""

from __future__ import annotations
from functools import lru_cache
from typing import Mapping, Optional, Set, Tuple, Union

from logic_utils import frozen, memoized_parameterless_method

LEFT_BRACKET = "("
RIGHT_BRACKET = ")"
NOT_STR = "~"
OR_STR = "|"
AND_STR = "&"
IMPLIES_STR = "->"
EMPTY_STR = ""
ERROR_MESSAGE_PREFIX_PARSE = "Error encountered - incorrect prefix Formula"


@lru_cache(maxsize=100)  # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return string[0] >= 'p' and string[0] <= 'z' and \
           (len(string) == 1 or string[1:].isdigit())


@lru_cache(maxsize=100)  # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant, ``False`` otherwise.
    """
    return string == 'T' or string == 'F'


@lru_cache(maxsize=100)  # Cache the return value of is_unary
def is_unary(string: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return string == '~'


@lru_cache(maxsize=100)  # Cache the return value of is_binary
def is_binary(string: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    # return string == '&' or string == '|' or string == '->'
    # For Chapter 3:
    return string in {'&', '|', '->', '+', '<->', '-&', '-|'}


@frozen
class Formula:
    """An immutable propositional formula in tree representation, composed from
    variable names, and operators applied to them.

    Attributes:
        root (`str`): the constant, variable name, or operator at the root of
            the formula tree.
        first (`~typing.Optional`\\[`Formula`]): the first operand of the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand of the
            root, if the root is a binary operator.
    """
    root: str
    first: Optional[Formula]
    second: Optional[Formula]

    def __init__(self, root: str, first: Optional[Formula] = None,
                 second: Optional[Formula] = None):
        """Initializes a `Formula` from its root and root operands.

        Parameters:
            root: the root for the formula tree.
            first: the first operand for the root, if the root is a unary or
                binary operator.
            second: the second operand for the root, if the root is a binary
                operator.
        """
        if is_variable(root) or is_constant(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert first is not None and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root)
            assert first is not None and second is not None
            self.root, self.first, self.second = root, first, second

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 1.1
        string_repr = EMPTY_STR
        if is_variable(self.root) or is_constant(self.root):
            string_repr += self.root
        elif is_unary(self.root):
            string_repr += NOT_STR + self.first.__repr__()
        elif is_binary(self.root):
            string_repr += LEFT_BRACKET + self.first.__repr__() + self.root + self.second.__repr__() + RIGHT_BRACKET
        return string_repr

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @memoized_parameterless_method
    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        # Task 1.2
        vars_set = set()
        if is_constant(self.root):
            return vars_set
        if is_variable(self.root):
            vars_set.add(self.root)
        if is_unary(self.root):
            vars_set.update(self.first.variables())
        if is_binary(self.root):
            vars_set.update(self.first.variables(), self.second.variables())
        return vars_set

    @memoized_parameterless_method
    def operators(self) -> Set[str]:
        """Finds all operators in the current formula.

        Returns:
            A set of all operators (including ``'T'`` and ``'F'``) used in the
            current formula.
        """
        # Task 1.3
        oper_set = set()
        if is_constant(self.root):
            oper_set.add(self.root)
        if is_variable(self.root):
            return oper_set
        if is_unary(self.root):
            oper_set.update({self.root}, self.first.operators())
        if is_binary(self.root):
            oper_set.update({self.root}, self.first.operators(), self.second.operators())
        return oper_set

    @staticmethod
    def count_digits_in_var(string: str) -> int:
        """
        counts the number of digits in a variable for Formula
        """
        count_digits = 0
        for i in range(0, len(string)):
            if string[i].isdigit():
                count_digits += 1
            else:
                break
        return count_digits

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Union[Formula, None], str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a variable name (e.g.,
            ``'x12'``) or a unary operator followed by a variable name, then the
            parsed prefix will include that entire variable name (and not just a
            part of it, such as ``'x1'``). If no prefix of the given string is a
            valid standard string representation of a formula then returned pair
            should be of ``None`` and an error message, where the error message
            is a string with some human-readable content.
        """
        # Task 1.4
        # recursion exit
        if len(string) == 0:
            return None, ERROR_MESSAGE_PREFIX_PARSE
        elif len(string) == 1 and (is_variable(string) or is_constant(string)):
            return Formula(string, None, None), EMPTY_STR
        elif is_constant(string[0]):
            return Formula(string[0], None, None), string[1:]
        elif 'p' <= string[0] <= 'z':
            count_digits = Formula.count_digits_in_var(string[1:])
            return Formula(string[:count_digits + 1], None, None), string[count_digits + 1:]
        elif is_unary(string[0]):
            prefix, suffix = Formula._parse_prefix(string[1:])
            if prefix is not None:
                return Formula(string[0], prefix, None), suffix
        elif string[0] == LEFT_BRACKET:
            prefix, suffix = Formula._parse_prefix(string[1:])
            if is_binary(suffix[0]):
                binary_index = 0
            elif len(suffix) > 1 and is_binary(suffix[0:2]):
                binary_index = 1
            elif len(suffix) > 1 and is_binary(suffix[0:3]):
                binary_index = 2
            else:
                return None, ERROR_MESSAGE_PREFIX_PARSE
            prefix_in, suffix_in = Formula._parse_prefix(suffix[binary_index + 1:])
            if len(suffix_in) > 0 and prefix_in is not None:
                if suffix_in[0] == RIGHT_BRACKET:
                    suffix_in = suffix_in[1:]
                else:
                    return None, ERROR_MESSAGE_PREFIX_PARSE
            else:
                return None, ERROR_MESSAGE_PREFIX_PARSE
            if prefix_in is not None:
                return Formula(suffix[0:binary_index + 1], prefix, prefix_in), suffix_in
        return None, ERROR_MESSAGE_PREFIX_PARSE

    @staticmethod
    def is_formula(string: str) -> bool:
        """Checks if the given string is a valid representation of a formula.

        Parameters:
            string: string to check.

        Returns:
            ``True`` if the given string is a valid standard string
            representation of a formula, ``False`` otherwise.
        """
        # Task 1.5
        prefix, suffix = Formula._parse_prefix(string)
        if suffix == "":
            return True
        else:
            return False

    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        assert Formula.is_formula(string)
        # Task 1.6
        prefix, suffix = Formula._parse_prefix(string)
        return prefix

    def polish(self) -> str:
        """Computes the polish notation representation of the current formula.

        Returns:
            The polish notation representation of the current formula.
        """
        # Optional Task 1.7

    @staticmethod
    def parse_polish(string: str) -> Formula:
        """Parses the given polish notation representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose polish notation representation is the given string.
        """
        # Optional Task 1.8

    def substitute_variables(self, substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Substitutes in the current formula, each variable name `v` that is a
        key in `substitution_map` with the formula `substitution_map[v]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            variables name occurrences originating in the current formula are
            substituted (i.e., variable name occurrences originating in one of
            the specified substitutions are not subjected to additional
            substitutions).

        Examples:
            >>> Formula.parse('((p->p)|r)').substitute_variables(
            ...     {'p': Formula.parse('(q&r)'), 'r': Formula.parse('p')})
            (((q&r)->(q&r))|p)
        """
        for variable in substitution_map:
            assert is_variable(variable)
        # Task 3.3
        if is_variable(self.root) and (self.root in substitution_map.keys()):
            return substitution_map[self.root]
        if is_variable(self.root):
            return self
        if is_unary(self.root):
            return Formula(self.root, self.first.substitute_variables(substitution_map))
        if is_binary(self.root):
            return Formula(self.root, self.first.substitute_variables(substitution_map),
                           self.second.substitute_variables(substitution_map))
        return self

    def substitute_operators(self, substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Substitutes in the current formula, each constant or operator `op`
        that is a key in `substitution_map` with the formula
        `substitution_map[op]` applied to its (zero or one or two) operands,
        where the first operand is used for every occurrence of ``'p'`` in the
        formula and the second for every occurrence of ``'q'``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            operator occurrences originating in the current formula are
            substituted (i.e., operator occurrences originating in one of the
            specified substitutions are not subjected to additional
            substitutions).

        Examples:
            >>> Formula.parse('((x&y)&~z)').substitute_operators(
            ...     {'&': Formula.parse('~(~p|~q)')})
            ~(~~(~x|~y)|~~z)
        """
        for operator in substitution_map:
            assert is_constant(operator) or is_unary(operator) or \
                   is_binary(operator)
            assert substitution_map[operator].variables().issubset({'p', 'q'})
        # Task 3.4
        if is_constant(self.root) and self.root in substitution_map.keys():
            return substitution_map[self.root]
        if is_constant(self.root) or is_variable(self.root):
            return self
        if self.root in substitution_map.keys():
            if not is_unary(self.root):
                substitute_first = self.first.substitute_operators(substitution_map)
                substitute_second = self.second.substitute_operators(substitution_map)
            else:
                substitute_first = self.first.substitute_operators(substitution_map)
                substitute_second = None
            return substitution_map[self.root].substitute_variables({'p': substitute_first,
                                                                     'q': substitute_second})
        if is_unary(self.root):
            return Formula(self.root, self.first.substitute_operators(substitution_map))
        return Formula(self.root, self.first.substitute_operators(substitution_map),
                       self.second.substitute_operators(substitution_map))
