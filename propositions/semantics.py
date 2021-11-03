# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""
import itertools
from typing import AbstractSet, Iterable, Iterator, Mapping, Sequence, Tuple

from propositions.syntax import *
from propositions.proofs import *

#: A model for propositional-logic formulas, a mapping from variable names to
#: truth values.
Model = Mapping[str, bool]


def is_model(model: Model) -> bool:
    """Checks if the given dictionary is a model over some set of variable
    names.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variable
        names, ``False`` otherwise.
    """
    for key in model:
        if not is_variable(key):
            return False
    return True


def variables(model: Model) -> AbstractSet[str]:
    """Finds all variable names over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variable names over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()


def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variable names of the
            given formula, to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.

    Examples:
        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': False})
        True

        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': True})
        False
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))
    # Task 2.1
    if is_variable(formula.root):
        return model[formula.root]
    if is_constant(formula.root):
        return True if formula.root == "T" else False
    if is_unary(formula.root):
        return not (evaluate(formula.first, model))
    if is_binary(formula.root):
        if formula.root == "&":
            return evaluate(formula.first, model) and evaluate(formula.second, model)
        elif formula.root == "|":
            return evaluate(formula.first, model) or evaluate(formula.second, model)
        elif formula.root == "->":
            return (not evaluate(formula.first, model)) or evaluate(formula.second, model)
        elif formula.root == "+":
            return evaluate(formula.first, model) != evaluate(formula.second, model)
        elif formula.root == "<->":
            return evaluate(formula.first, model) == evaluate(formula.second, model)
        elif formula.root == "-&":
            return not (evaluate(formula.first, model) and evaluate(formula.second, model))
        elif formula.root == "-|":
            return not (evaluate(formula.first, model) or evaluate(formula.second, model))


def all_models(variables: Sequence[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variable names.

    Parameters:
        variables: variable names over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variable names. The
        order of the models is lexicographic according to the order of the given
        variable names, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]

        >>> list(all_models(['q', 'p']))
        [{'q': False, 'p': False}, {'q': False, 'p': True}, {'q': True, 'p': False}, {'q': True, 'p': True}]
    """
    for v in variables:
        assert is_variable(v)
    # Task 2.2
    models_count = len(variables)
    list_models = []
    models = itertools.product([False, True], repeat=models_count)
    for model in models:
        dict_model_var = {}
        for i in range(0, len(model)):
            dict_model_var[variables[i]] = model[i]
        list_models.append(dict_model_var)
    return list_models


def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    models.

    Parameters:
        formula: formula to calculate the truth value of.
        models: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.

    Examples:
        >>> list(truth_values(Formula.parse('~(p&q76)'), all_models(['p', 'q76'])))
        [True, True, True, False]
    """
    # Task 2.3
    truth_vals = []
    for model in models:
        truth_vals.append(evaluate(formula, model))
    return truth_vals


def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    # Task 2.4
    variables_list = formula.variables()
    vars_sorted = sorted(variables_list)
    line_len = 0
    for var in vars_sorted:
        print("| " + var + " ", end="")
        line_len += len(var) + 5
    print("| " + str(formula) + " |")
    line_len += len(str(formula)) + 2
    for var in vars_sorted:
        len_of_var = len(var) + 2
        print("|" + '-' * len_of_var, end="")
    print("|" + '-' * (len(str(formula)) + 2) + "|")
    list_models = list(all_models(vars_sorted))
    for index in range(len(list_models)):
        for key in list_models[index]:
            print("| " + str(list_models[index][key])[0] + ' ' * (len(key)), end="")
        print("| " + str(evaluate(formula, list_models[index]))[0] + ' ' * (len(str(formula))) + "|")


def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    # Task 2.5a
    models = all_models(list(formula.variables()))
    truth_vals = list(truth_values(formula, models))
    for val in truth_vals:
        if val is False:
            return False
    return True


def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    # Task 2.5b
    models = all_models(list(formula.variables()))
    truth_vals = list(truth_values(formula, models))
    for val in truth_vals:
        if val is True:
            return False
    return True


def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    # Task 2.5c
    if is_contradiction(formula) is False:
        return True
    return False


def synthesize_model_recursive(model) -> Formula:
    """
    helper recursion function for synthesize_for_model
    :param model:
    :return:
    """
    last_var, last_value = model[-1]
    if len(model) == 1:
        return Formula(last_var) if last_value else Formula('~', Formula(last_var), None)
    else:
        elem = model[-1]
        model.remove(elem)
        return Formula('&', synthesize_model_recursive(model), Formula(last_var)
        if last_value else Formula('~', Formula(last_var)))


def _synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single conjunctive
    clause that evaluates to ``True`` in the given model, and to ``False`` in
    any other model over the same variable names.

    Parameters:
        model: model over a nonempty set of variable names, in which the
            synthesized formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    # Task 2.6
    list_models = list(model.items())
    return synthesize_model_recursive(list_models)


def synthesize_recursive(true_formulas) -> Formula:
    """
    recursive helper function of synthesize
    :param true_formulas:
    :return:
    """
    formula_elem = true_formulas[-1]
    if len(true_formulas) == 1:
        return formula_elem
    else:
        true_formulas.remove(formula_elem)
        return Formula('|', synthesize_recursive(true_formulas), formula_elem)


def synthesize(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variable names,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variable names for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variable names, in the order returned
            by `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Task 2.7
    index_value = 0
    values_list = list(values)
    true_models = []
    models = list(all_models(list(variables)))
    for model in models:
        if values_list[index_value] is True:
            formula = _synthesize_for_model(model)
            true_models.append(formula)
        index_value += 1
    if len(true_models) == 0:
        return Formula('&', Formula(variables[0], None, None), Formula('~', Formula(variables[0]), None))
    return synthesize_recursive(true_models)


def _synthesize_for_all_except_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single disjunctive
    clause that evaluates to ``False`` in the given model, and to ``True`` in
    any other model over the same variable names.

    Parameters:
        model: model over a nonempty set of variable names, in which the
            synthesized formula is to not hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    # Optional Task 2.8


def synthesize_cnf(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in CNF over the given variable names,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variable names for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variable names, in the order returned
            by `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize_cnf(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Optional Task 2.9


def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.

    Examples:
        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': True, 'q': False})
        False

        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': False, 'q': False})
        True
    """
    assert is_model(model)
    # Task 4.2


def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    # Task 4.3
