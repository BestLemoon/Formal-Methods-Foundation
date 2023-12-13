""" The subset problem

The subset problem is a well-known satisfiability problem: given
a multiset (a multiset is like a normal set, expect for the
elements can be duplicated) S, whether or not there is a
non-empty subset T of S, such that:
  \\sum T = 0

For example, given this set
  {-7, -3, -2, 9000, 5, 8}
the answer is yes because the subset
  {-3, -2, 5}
sums to zero.

This problem is NPC, and for more background information of the
subset problem, please refer to:
https://en.wikipedia.org/wiki/Subset_sum_problem

"""

from z3 import *
import time


# LA-based solution
def subset_sum_la(target_set: list):
    solver = Solver()
    flags = [Int(f"x_{i}") for i in range(len(target_set))]

    # 0-1 ILA
    for flag in flags:
        solver.add(Or(flag == 0, flag == 1))

    # the selected set must be non-empty
    solver.add(sum(flags) != 0)

    # @Exercise 9: please fill in the missing src to add
    # the following constraint into the solver.
    #       \sum_i flags[i]*target_set[i] = 0
    # raise NotImplementedError('TODO: Your code here!')
    solver.add(sum([flags[i] * target_set[i] for i in range(len(target_set))]) == 0)
    start = time.time()
    result = solver.check()
    print(f"time used in LA: {(time.time() - start):.6f}s")

    if result == sat:
        return True, [target_set[index] for index, flag in enumerate(flags) if solver.model()[flag] == 1]
    return False, result


# LA-based optimized solution
def subset_sum_la_opt(target_set: list):
    solver = Solver()

    # enable Pseudo-Boolean solver
    # to get more information about Pseudo-Boolean constraints
    # refer to https://theory.stanford.edu/~nikolaj/programmingz3.html
    solver.set("sat.pb.solver", "solver")

    # use Pseudo-Boolean constraints for each flag
    flags = [Bool(f"x_{i}") for i in range(len(target_set))]

    # the selected set must be non-empty
    solver.add(PbGe([(flags[i], 1) for i in range(len(target_set))], 1))

    # selected set must sum to zero
    solver.add(PbEq([(flags[i], target_set[i]) for i in range(len(target_set))], 0))

    start = time.time()
    result = solver.check()
    print(f"time used in LA optimized: {(time.time() - start):.6f}s")

    if result == sat:
        return True, [target_set[index] for index, flag in enumerate(flags) if solver.model()[flag]]
    return False, result


# dynamic programming-based (DP) solution (don't confuse DP with LP):
def subset_sum_dp(target_set: list):
    def subset_sum_dp_do(target_set, target):
        n = len(target_set)

        # Create a 2D array to store the results of subproblems
        dp = [[False for _ in range(target + 1)] for _ in range(n + 1)]

        # An empty set can sum to 0
        for i in range(n + 1):
            dp[i][0] = True

        # Fill the subset sum table
        for i in range(1, n + 1):
            for j in range(1, target + 1):
                if j < target_set[i - 1]:
                    dp[i][j] = dp[i - 1][j]
                else:
                    dp[i][j] = dp[i - 1][j] or dp[i - 1][j - target_set[i - 1]]

        return dp[n][target]

    start = time.time()
    result = subset_sum_dp_do(target_set, 0)
    print(f"time used in DP: {(time.time() - start):.6f}s")
    return result


def gen_large_test(n):
    nums = [10000] * n
    nums[len(nums) - 2] = 1
    nums[len(nums) - 1] = -1
    # print(nums)
    return nums


if __name__ == '__main__':
    # a small test case
    small_set = [-7, -3, -2, 9000, 5, 8]
    subset_sum_dp(small_set)
    print(subset_sum_la(small_set))
    print(subset_sum_la_opt(small_set))

    # a large test case
    max_nums = 20000
    large_set = gen_large_test(max_nums)

    # @Exercise 10: compare the efficiency of the DP and the
    # LP algorithm, by changing the value of "max_nums" to other
    # values, say, 200, 2000, 20000, 200000, ...
    # what's your observation? What conclusion you can draw from these data?
    # raise NotImplementedError('TODO: Your code here!')
    subset_sum_dp(large_set)
    # subset_sum_la(large_set)
    subset_sum_la_opt(large_set)
