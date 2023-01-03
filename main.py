import argparse
import copy
import itertools

QUIET = False

def LOG(string, end="\n"):
    if not QUIET:
        print(string, end=end)

def ERROR(string):
    print(string)


def validate_uppercase(string):
    if not (string.isupper() and string.isalpha()):
        # Raise an exception if the string is not uppercase
        raise argparse.ArgumentTypeError(f"'{string}' is not alphabet uppercase")
    return string


class CSP:
    def __init__(self):
        self.X = []
        self.D = {}
        self.C = {}
        self.assignment = {}

    def add_variable(self, var, domain):
        if var not in self.X:
            self.X.append(var)
            self.D[var] = domain

    def add_constraint(self, constraint, variables):
        if variables not in self.C:
            self.C[variables] = constraint

    def is_consistent(self, variable, value):
        self.assignment[variable] = value
        for constrain_vars, constrain in self.C.items():
            if variable in constrain_vars:
                # if all the variables needed for the constraint are assigned
                if set(constrain_vars).issubset(self.assignment.keys()):
                    if not constrain(*[self.assignment[var] for var in constrain_vars]):
                        del self.assignment[variable]
                        return False

        del self.assignment[variable]
        return True

    def get_neighbors(self, X):
        neighbors = []
        constrain_type = self.C[X]
        for constrain_vars, constrain in self.C.items():
            if constrain_vars != X:

                if constrain_type == constrain_alldiff:
                    if constrain == constrain_digit:
                        neighbors.append(constrain_vars)

                if constrain_type == constrain_digit or constrain_type == constrain_most_significant_digit:
                    if constrain == constrain_firstcolsum or constrain == constrain_colsum:
                        if X[0] in constrain_vars:
                            neighbors.append(constrain_vars)
                    if constrain == constrain_alldiff:
                        neighbors.append(constrain_vars)

                if constrain_type == constrain_firstcolsum or constrain_type == constrain_colsum:
                    if constrain == constrain_digit or constrain == constrain_carry:
                        if constrain_vars[0] in X:
                            neighbors.append(constrain_vars)

                if constrain_type == constrain_carry:
                    if constrain == constrain_firstcolsum or constrain == constrain_colsum:
                        if X[0] in constrain_vars:
                            neighbors.append(constrain_vars)
        return neighbors

    def constraint_count(self, variable, value):
        count = 0
        for neighbor in self.get_neighbors(variable):
            if value in self.D[neighbor[neighbor.index(variable[0])]]:
                count += 1
        return count


def degree_heuristic(csp):
    constrains = [
        (len([a for a in csp.C.keys() if var in a]), var) for var in csp.X if var not in csp.assignment.keys()
    ]
    return max(constrains, key=lambda t: t[0])[1]


def MRV(csp):
    remaining = [
        (len(csp.D[var]), (var,)) for var in csp.X if var not in csp.assignment.keys()
    ]
    choice = min(remaining, key=lambda t: t[0])[1]
    LOG(f"MRV: remaining values {remaining} choose {choice[0]}")
    return choice


def select_unassigned_variable(csp):
    return MRV(csp)


def order_domain_values(csp, variable):
    sort = sorted(csp.D[variable[0]], key=lambda x: csp.constraint_count(variable, x))

    LOG(f"LCV: ordered values of {variable[0]}: {sort}")
    return sorted(csp.D[variable[0]], key=lambda x: csp.constraint_count(variable, x))


def combinations(list1, *otherlist):
    result = list(itertools.product(list1, *otherlist))
    return result


def revise(csp, Xi, Xj):
    revised = False
    xi_var = Xi[0]
    xj_vars = list(set(Xj))
    if xi_var in csp.assignment.keys():
        potential_values = [csp.assignment[xi_var]]
    else:
        potential_values = [var for var in csp.D[xi_var]]
    for xi_value in potential_values:
        satisfy = False
        new_list = [
                    csp.D[var] if (var not in Xi and var not in csp.assignment.keys())
                    else [xi_value] if (var in Xi)
                    else [csp.assignment[var]]
                    for var in xj_vars
                    ]
        for xj in combinations(*new_list):
            vars = [xj[xj_vars.index(var)] for var in Xj]
            if csp.C[Xj](*vars):
                satisfy = True
                break
        if not satisfy:
            csp.D[xi_var].remove(xi_value)
            revised = True
    return revised


def ac3(csp, arc=None):
    LOG(f"AC-3: Domains state before {csp.D}")
    if not arc:
        arc = []
        for var in csp.X:
            neighbors = csp.get_neighbors((var,))
            for neighbor in neighbors:
                arc.append(((var,), neighbor))

    while arc:
        Xi, Xj = arc.pop()
        if revise(csp, Xi, Xj):
            if len(csp.D[Xi[0]]) == 0:
                LOG(f"AC-3: Var {Xi[0]} has no valid values")
                return False
            if Xi[0] in csp.assignment.keys() and csp.assignment[Xi[0]] not in csp.D[Xi[0]]:
                LOG(f"AC-3: Var {Xi[0]} has an invalid assignment")
                return False
            for Xk in csp.get_neighbors(Xi):
                if Xj != Xk:
                    arc.append((Xi, Xk))

    LOG(f"AC-3: Domains state after {csp.D}")
    return True


def backtrack(csp):
    if len(csp.assignment) > 0:
        LOG("backtrack: assignment so far: ", end="")
        for d, v in csp.assignment.items():
            res = any(chr.isdigit() for chr in d)
            if not res:
                LOG(f"{d}={v} ", end="")
        LOG("")
    if len(csp.assignment) == len(csp.X):
        return csp.assignment

    variable = select_unassigned_variable(csp)

    for value in order_domain_values(csp, variable):
        if csp.is_consistent(variable[0], value):
            LOG(f"backtrack: Trying to assign {variable[0]} = {value}")
            csp.assignment[variable[0]] = value
            arc = []
            for Xi in csp.get_neighbors(variable):
                if not set(Xi).issubset(csp.assignment.keys()):
                    arc.append((variable, Xi))

            old_csp_domain = copy.deepcopy(csp.D)
            if ac3(csp, arc) and (value in csp.D[variable[0]]):
                result = backtrack(csp)
                if result is not None:
                    return result
            LOG(f"backtrack: Failed removing {variable[0]} = {value}")
            del csp.assignment[variable[0]]
            csp.D = old_csp_domain
    return None


def backtracking_search(csp):
    ac3(csp)
    return backtrack(csp)


# a constraint that expects different variables to have different values
def constrain_alldiff(*args):
    return len(set(args)) == len(args)


def constrain_firstcolsum(s1, s2, s, cr):
    return (s1 + s2) == (s + (10 * cr))


def constrain_colsum(carry, result, new_c, summand1=0, summand2=0):
    return (carry + summand1 + summand2) == (result + (10 * new_c))


def constrain_digit(d):
    return 0 <= d <= 9


def constrain_most_significant_digit(d):
    return 0 < d <= 9


def constrain_carry(c):
    return 0 <= c <= 1


def main(name):
    parser = argparse.ArgumentParser()

    parser.add_argument('summand1', type=validate_uppercase, help='The first summand')
    parser.add_argument('summand2', type=validate_uppercase, help='The second summand')
    parser.add_argument('sum', type=validate_uppercase, help='The sum of the two summands')

    args = parser.parse_args()

    left = args.summand1
    right = args.summand2
    result = args.sum

    if len(result) > max(len(left), len(right)) + 1:
        ERROR("The length of the sum cannot be greater than the maximum summands length + 1")
    if len(result) < min(len(left), len(right)):
        ERROR("The length of the sum cannot be smaller than the minimum summands length")

    left_chars = [c for c in left]
    right_chars = [c for c in right]
    result_chars = [c for c in result]

    # Create a list of all unique characters in the puzzle
    all_chars = list(set(left_chars + right_chars + result_chars))

    left = left.zfill(len(result_chars))[::-1]
    right = right.zfill(len(result_chars))[::-1]
    result = result[::-1]

    csp = CSP()
    for c in all_chars:
        csp.add_variable(c, [i for i in range(0, 10)])
        csp.add_constraint(constrain_digit, (c,))

    csp.add_constraint(constrain_alldiff, tuple(all_chars))

    c = 1
    for lsummand, rsummand, s in zip(left, right, result):
        if c == 1:
            constrain_vars = ()
            if lsummand != "0":
                constrain_vars += (lsummand,)

            if rsummand != "0":
                constrain_vars += (rsummand,)

            constrain_vars += (s,)
            constrain_vars += ("c" + str(c),)
            csp.add_constraint(constrain_firstcolsum, constrain_vars)
            if c == len(result):
                csp.add_variable("c" + str(c), [0])
                csp.C[(s,)] = constrain_most_significant_digit
            else:
                csp.add_variable("c" + str(c), [0, 1])
            csp.add_constraint(constrain_carry, ("c" + str(c),))
            c += 1

        else:
            constrain_vars = ("c" + str(c - 1), s, "c" + str(c))
            if lsummand != "0":
                constrain_vars += (lsummand,)

            if rsummand != "0":
                constrain_vars += (rsummand,)

            csp.add_constraint(constrain_colsum, constrain_vars)
            if c == len(result):
                csp.add_variable("c" + str(c), [0])
                csp.C[(s,)] = constrain_most_significant_digit
            else:
                csp.add_variable("c" + str(c), [0, 1])
            csp.add_constraint(constrain_carry, ("c" + str(c),))
            c += 1

    result = backtracking_search(csp)
    if not result:
        print(f"There is no solution for the puzzle: {args.summand1} + {args.summand2} = {args.sum}")

    else:
        print("\n---------------------------------------")
        for d,v in result.items():
            res = any(chr.isdigit() for chr in d)
            if not res:
                print(f"{d}={v} ", end="")
        print("\n---------------------------------------\n")


if __name__ == '__main__':
    main('PyCharm')
