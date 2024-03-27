def elim_implication(expr):
    if isinstance(expr, str):
        return expr

    op = expr[0]
    if op == 'and':
        return ['and', elim_implication(expr[1]), elim_implication(expr[2])]
    elif op == 'or':
        return ['or', elim_implication(expr[1]), elim_implication(expr[2])]
    elif op == 'not':
        return ['not', elim_implication(expr[1])]
    elif op == 'implies':
        return ['or', ['not', elim_implication(expr[1])], elim_implication(expr[2])]
    else:
        return expr


def move_neg_inward(expr):
    if isinstance(expr, str):
        return expr

    op = expr[0]
    if op == 'and':
        return ['and', move_neg_inward(expr[1]), move_neg_inward(expr[2])]
    elif op == 'or':
        return ['or', move_neg_inward(expr[1]), move_neg_inward(expr[2])]
    elif op == 'not':
        sub_expr = expr[1]
        if isinstance(sub_expr, str):
            return expr
        elif sub_expr[0] == 'and':
            return ['or', move_neg_inward(['not', sub_expr[1]]), move_neg_inward(['not', sub_expr[2]])]
        elif sub_expr[0] == 'or':
            return ['and', move_neg_inward(['not', sub_expr[1]]), move_neg_inward(['not', sub_expr[2]])]
        elif sub_expr[0] == 'not':
            return move_neg_inward(sub_expr[1])
    else:
        return expr


def remove_dbl_negation(expr):
    if isinstance(expr, str):
        return expr

    op = expr[0]
    if op == 'and':
        return ['and', remove_dbl_negation(expr[1]), remove_dbl_negation(expr[2])]
    elif op == 'or':
        return ['or', remove_dbl_negation(expr[1]), remove_dbl_negation(expr[2])]
    elif op == 'not':
        sub_expr = expr[1]
        if isinstance(sub_expr, str):
            return expr
        elif sub_expr[0] == 'not':
            return remove_dbl_negation(sub_expr[1])
        else:
            return ['not', remove_dbl_negation(sub_expr)]
    else:
        return expr


def standardize_var_scope(expr, var_map=None):
    if var_map is None:
        var_map = {}

    if isinstance(expr, str):
        if expr in var_map:
            return var_map[expr]
        else:
            new_var = expr + '1'
            var_map[expr] = new_var
            return new_var

    op = expr[0]
    if op == 'and' or op == 'or':
        return [op, standardize_var_scope(expr[1], var_map), standardize_var_scope(expr[2], var_map)]
    elif op == 'not':
        return ['not', standardize_var_scope(expr[1], var_map)]
    else:
        return expr


def prenex_form(expr):
    if isinstance(expr, str):
        return expr

    op = expr[0]
    if op == 'and' or op == 'or':
        left = prenex_form(expr[1])
        right = prenex_form(expr[2])
        return [op, left, right]
    elif op == 'not':
        return ['not', prenex_form(expr[1])]
    elif op == 'exists' or op == 'forall':
        quant = expr[0]
        var = expr[1]
        matrix = prenex_form(expr[2])
        return move_quantifier_to_left(quant, var, matrix)
    else:
        return expr


def move_quantifier_to_left(quant, var, matrix):
    if isinstance(matrix, str):
        return [quant, var, matrix]

    op = matrix[0]
    if op == 'and' or op == 'or':
        left = move_quantifier_to_left(quant, var, matrix[1])
        right = move_quantifier_to_left(quant, var, matrix[2])
        return [op, left, right]
    elif op == 'not':
        return ['not', move_quantifier_to_left(quant, var, matrix[1])]
    elif op == 'exists' or op == 'forall':
        inner_quant = matrix[0]
        inner_var = matrix[1]
        inner_matrix = matrix[2]
        if inner_quant == quant:
            return move_quantifier_to_left(inner_quant, inner_var, move_quantifier_to_left(quant, var, inner_matrix))
    return [quant, var, matrix]


def skolemize(expr, sk_consts=None):
    if sk_consts is None:
        sk_consts = {}

    if isinstance(expr, str):
        return expr

    op = expr[0]
    if op == 'and' or op == 'or':
        left = skolemize(expr[1], sk_consts)
        right = skolemize(expr[2], sk_consts)
        return [op, left, right]
    elif op == 'not':
        return ['not', skolemize(expr[1], sk_consts)]
    elif op == 'exists':
        var = expr[1]
        matrix = expr[2]
        sk_const = sk_consts.get(var)
        if sk_const is None:
            sk_const = generate_skolem_const()
            sk_consts[var] = sk_const
        return skolemize(substitute_var(matrix, var, sk_const), sk_consts)
    else:
        return expr

def substitute_var(expr, var, substitute):
    if isinstance(expr, str):
        return substitute if expr == var else expr
    op = expr[0]
    if op == 'and' or op == 'or':
        left = substitute_var(expr[1], var, substitute)
        right = substitute_var(expr[2], var, substitute)
        return [op, left, right]
    elif op == 'not':
        return ['not', substitute_var(expr[1], var, substitute)]
    else:
        return expr

def generate_skolem_const():
    return 'Sk' + str(len(generate_skolem_const.sk_consts))

generate_skolem_const.sk_consts = {}

def eliminate_univ_quantifiers(expr):
    if isinstance(expr, str):
        return expr

    op = expr[0]
    if op == 'and' or op == 'or':
        left = eliminate_univ_quantifiers(expr[1])
        right = eliminate_univ_quantifiers(expr[2])
        return [op, left, right]
    elif op == 'not':
        return ['not', eliminate_univ_quantifiers(expr[1])]
    elif op == 'forall':
        var = expr[1]
        matrix = expr[2]
        return eliminate_univ_quantifiers(substitute_var(matrix, var, ''))
    else:
        return expr

def convert_to_cnf(expr):
    expr = eliminate_univ_quantifiers(expr)
    expr = distribute_or_over_and(expr)
    return expr

def distribute_or_over_and(expr):
    if isinstance(expr, str):
        return expr

    op = expr[0]
    if op == 'and':
        left = distribute_or_over_and(expr[1])
        right = distribute_or_over_and(expr[2])
        return ['and', left, right]
    elif op == 'or':
        left = distribute_or_over_and(expr[1])
        right = distribute_or_over_and(expr[2])

        if isinstance(left, list) and left[0] == 'and':
            left_left = left[1]
            left_right = left[2]
            new_left = ['or', ['and', left_left, right], ['and', left_right, right]]
        elif isinstance(right, list) and right[0] == 'and':
            right_left = right[1]
            right_right = right[2]
            new_left = ['or', ['and', left, right_left], ['and', left, right_right]]
        else:
            return ['or', left, right]

        return distribute_or_over_and(new_left)
    else:
        return expr

def turn_conjunctions_into_clauses(expr):
    if isinstance(expr, str):
        return {expr}

    op = expr[0]
    if op == 'and':
        left = turn_conjunctions_into_clauses(expr[1])
        right = turn_conjunctions_into_clauses(expr[2])
        return left.union(right)
    else:
        return {convert_to_clause(expr)}

def convert_to_clause(expr):
    if isinstance(expr, str):
        return expr

    op = expr[0]
    if op == 'or':
        left = convert_to_clause(expr[1])
        right = convert_to_clause(expr[2])
        return left.union(right)
    else:
        return {expr}

def rename_vars_in_clauses(clauses):
    renamed_clauses = set()
    var_map = {}

    for clause in clauses:
        renamed_clause = rename_vars_in_clause(clause, var_map)
        renamed_clauses.add(renamed_clause)

    return renamed_clauses

def rename_vars_in_clause(clause, var_map):
    if isinstance(clause, str):
        return clause

    op = clause[0]
    if op == 'and':
        left = rename_vars_in_clause(clause[1], var_map)
        right = rename_vars_in_clause(clause[2], var_map)
        return ['and', left, right]
    elif op == 'or':
        left = rename_vars_in_clause(clause[1], var_map)
        right = rename_vars_in_clause(clause[2], var_map)
        return ['or', left, right]
    else:
        var = clause
        if var in var_map:
            return var_map[var]
        else:
            new_var = generate_unique_var()
            var_map[var] = new_var
            return new_var

def generate_unique_var():
    return 'V' + str(len(generate_unique_var.var_count))

generate_unique_var.var_count = 0

# Test case
input_expr = ['forall', 'x', ['exists', 'y', ['or', ['and', 'P', 'Q'], 'R']]]
cnf_expr = convert_to_cnf(input_expr)
print(cnf_expr)

