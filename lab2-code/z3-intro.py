from pro_print import *

# Z3 is an SMT solver. In this lecture, we'll discuss
# the basis usage of Z3 through some working example, the
# primary goal is to introduce how to use Z3 to solve
# the satisfiability problems we've discussed in the past
# several lectures.
# We must emphasize that Z3 is just one of the many such SMT
# solvers, and by introducing Z3, we hope you will have a
# general understanding of what such solvers look like, and
# what they can do.

########################################
# Basic propositional logic

# In Z3, we can declare two propositions just as booleans, this
# is rather natural, for propositions can have values true or false.
# To declare two propositions P and Q:
P = Bool('P')
Q = Bool('Q')
# or, we can use a more compact shorthand:
P, Q = Bools('P Q')

# We can build propositions by writing Lisp-style abstract
# syntax trees, for example, the disjunction:
# P \/ Q
# can be encoded as the following AST:
F = Or(P, Q)
# Output is : Or(P, Q)
print(F)

# Note that the connective '\/' is called 'Or' in Z3, we'll see
# several other in the next.

# We have designed the function 'pretty_print(expr)' for you, 
# As long as we input the expression defined by z3, we can output 
# propositions that are suitable for us to read.
# Here‘s an example:

P, Q = Bools('P Q')
F = Or(P, Q)
# prove(F)
# solve(F)
# Output is : P \/ Q
pretty_print(F)

################################################################
##                           Part A                           ##
################################################################

# exercises 1 : P -> (Q -> P)
# Please use z3 to define the proposition. 
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')
print("exercises 1 : P -> (Q -> P)")
P, Q = Bools('P Q')
F = Implies(P, Implies(Q, P))
print(F)
pretty_print(F)
prove(F)

# exercise 2 : (P -> Q) -> ((Q -> R) -> (P -> R))
# Please use z3 to define the proposition. 
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')
print("exercise 2 : (P -> Q) -> ((Q -> R) -> (P -> R))")
P, Q, R = Bools('P Q R')
F = Implies(Implies(P, Q), Implies(Implies(Q, R), Implies(P, R)))
print(F)
pretty_print(F)
prove(F)

# exercise 3 : (P /\ (Q /\ R)) -> ((P /\ Q) /\ R)
# Please use z3 to define the proposition. 
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')
print(r"exercise 3 : (P /\ (Q /\ R)) -> ((P /\ Q) /\ R)")
P, Q, R = Bools('P Q R')
F = Implies(And(P, And(Q, R)), And(And(P, Q), R))
print(F)
pretty_print(F)
prove(F)

# exercise 4 : (P \/ (Q \/ R)) -> ((P \/ Q) \/ R)
# Please use z3 to define the proposition. 
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')
print(r"exercise 4 : (P \/ (Q \/ R)) -> ((P \/ Q) \/ R)")
P, Q, R = Bools('P Q R')
F = Implies(Or(P, Or(Q, R)), Or(Or(P, Q), R))
print(F)
pretty_print(F)
prove(F)

# exercise 5 : ((P -> R) /\ (Q -> R)) -> ((P /\ Q) -> R)
# Please use z3 to define the proposition. 
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')
print(r"exercise 5 : ((P -> R) /\ (Q -> R)) -> ((P /\ Q) -> R)")
P, Q, R = Bools('P Q R')
F = Implies(And(Implies(P, R), Implies(Q, R)), Implies(And(P, Q), R))
print(F)
pretty_print(F)
prove(F)

# exercise 6 : ((P /\ Q) -> R) <-> (P -> (Q -> R))
# Please use z3 to define the proposition. 
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')
print(r"exercise 6 : ((P /\ Q) -> R) <-> (P -> (Q -> R))")
P, Q, R = Bools('P Q R')
impl1 = Implies(And(P, Q), R)
impl2 = Implies(P, Implies(Q, R))
F = And(Implies(impl1, impl2), Implies(impl2, impl1))
print(F)
pretty_print(F)
prove(F)

# exercise 7 : (P -> Q) -> (¬Q -> ¬P)
# Please use z3 to define the proposition 
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')
print("exercise 7 : (P -> Q) -> (¬Q -> ¬P)")
P, Q = Bools('P Q')
F = Implies(Implies(P, Q), Implies(Not(Q), Not(P)))
print(F)
pretty_print(F)
prove(F)

################################################################
##                           Part B                           ##
################################################################

# Before writing the code first, we need to understand the 
# quantifier. ∀ x.P (x) means that for any x, P (x) holds, 
# so both x and P should be a sort types. IntSort() and BoolSort() 
# are given in Z3
# IntSort(): Return the integer sort in the given context.
# BoolSort(): Return the Boolean Z3 sort.
isort = IntSort()
bsort = BoolSort()

# Declare a Int variable
x = Int('x')
y = Int('y')
b = Int('b')

# Declare a function P with input of isort type and output 
# of bsort type
P = Function('P', isort, bsort)

# It means ∃x.P(x)
F = Exists(x, P(x))
print(F)
pretty_print(F)

# Now you can complete the following exercise based on the example above

# exercise 8 : # ∀x.(¬P(x) /\ Q(x)) -> ∀x.(P(x) -> Q(x))
# Please use z3 to define the proposition. 
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')
print(r"exercise 8 : # ∀x.(¬P(x) /\ Q(x)) -> ∀x.(P(x) -> Q(x))")
P = Function('P', isort, bsort)
Q = Function('Q', isort, bsort)
F1 = ForAll(x, And(Not(P(x)), Q(x)))
F2 = ForAll(x, Implies(P(x), Q(x)))
F = Implies(F1, F2)
print(F)
pretty_print(F)
prove(F)

# exercise 9 : ∀x.(P(x) /\ Q(x)) <-> (∀x.P(x) /\ ∀x.Q(x))
# Please use z3 to define the proposition. 
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')
print(r"exercise 9 : ∀x.(P(x) /\ Q(x)) <-> (∀x.P(x) /\ ∀x.Q(x))")
P = Function('P', isort, bsort)
Q = Function('Q', isort, bsort)
F1 = ForAll(x, And(P(x), Q(x)))
F2 = And(ForAll(x, P(x)), ForAll(x, Q(x)))
F = And(Implies(F1, F2), Implies(F2, F1))
print(F)
pretty_print(F)
solve(F)
prove(F)

# exercise 10 : ∃x.(¬P(x) \/ Q(x)) -> ∃x.(¬(P(x) /\ ¬Q(x)))
# Please use z3 to define the proposition. 
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')
print(r"exercise 10 : ∃x.(¬P(x) \/ Q(x)) -> ∃x.(¬(P(x) /\ ¬Q(x)))")
P = Function('P', isort, bsort)
Q = Function('Q', isort, bsort)
F1 = Exists(x, Or(Not(P(x)), Q(x)))
F2 = Exists(x, Not(And(P(x), Not(Q(x)))))
F = Implies(F1, F2)
print(F)
pretty_print(F)
prove(F)

# exercise 11 : ∃x.(P(x) \/ Q(x)) <-> (∃x.P(x) \/ ∃x.Q(x))
# Please use z3 to define the proposition. 
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')
print(r"exercise 11 : ∃x.(P(x) \/ Q(x)) <-> (∃x.P(x) \/ ∃x.Q(x))")
P = Function('P', isort, bsort)
Q = Function('Q', isort, bsort)
F1 = Exists(x, Or(P(x), Q(x)))
F2 = Or(Exists(x, P(x)), Exists(x, Q(x)))
F = And(Implies(F1, F2), Implies(F2, F1))
print(F)
pretty_print(F)
prove(F)

# exercise 12 : ∀x.(P(x) -> ¬Q(x)) -> ¬(∃x.(P(x) /\ Q(x)))
# Please use z3 to define the proposition. 
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')
print(r"exercise 12 : ∀x.(P(x) -> ¬Q(x)) -> ¬(∃x.(P(x) /\ Q(x)))")
P = Function('P', isort, bsort)
Q = Function('Q', isort, bsort)
F1 = ForAll(x, Implies(P(x), Not(Q(x))))
F2 = Not(Exists(x, And(P(x), Q(x))))
F = Implies(F1, F2)
print(F)
pretty_print(F)
prove(F)

# exercise 13 : ∃x.(P(x) /\ Q(x)) /\ ∀x.(P(x) -> R(x)) -> ∃x.(R(x) /\ Q(x))
# Please use z3 to define the proposition. 
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')
print(r"exercise 13 : ∃x.(P(x) /\ Q(x)) /\ ∀x.(P(x) -> R(x)) -> ∃x.(R(x) /\ Q(x))")
P = Function('P', isort, bsort)
Q = Function('Q', isort, bsort)
R = Function('R', isort, bsort)
F1 = Exists(x, And(And(P(x), Q(x)), ForAll(x, Implies(P(x), R(x)))))
F2 = Exists(x, And(R(x), Q(x)))
F = Implies(F1, F2)
print(F)
pretty_print(F)
prove(F)

# exercise 14 : ∃x.∃y.P(x, y) -> ∃y.∃x.P(x, y)
# Please use z3 to define the proposition. 
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')
print(r"exercise 14 : ∃x.∃y.P(x, y) -> ∃y.∃x.P(x, y)")
P = Function('P', isort, isort, bsort)
F1 = Exists(x, Exists(y, P(x, y)))
F2 = Exists(y, Exists(x, P(x, y)))
F = Implies(F1, F2)
print(F)
pretty_print(F)
prove(F)

# exercise 15 : P(b) /\ (∀x.∀y.(P(x) /\ P(y) -> x = y)) -> (∀x.(P(x) <-> x = b))
# Please use z3 to define the proposition. 
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')
print(r"exercise 15 : P(b) /\ (∀x.∀y.(P(x) /\ P(y) -> x = y)) -> (∀x.(P(x) <-> x = b))")
P = Function('P', isort, bsort)
F1 = And(P(b), ForAll([x, y], Implies(And(P(x), P(y)), x == y)))
F2 = ForAll(x, P(x) == (x == b))
F = Implies(F1, F2)
print(F)
pretty_print(F)
prove(F)

################################################################
##                           Part C                           ##
################################################################

# Challenge: 
# We provide the following two rules :
#     ----------------(odd_1)
#           odd 1
#
#           odd n
#     ----------------(odd_ss)
#         odd n + 2
#
# Please prove that integers 9, 25, and 99 are odd numbers.

# raise NotImplementedError('TODO: Your code here!')
x = Int('x')
Odd = Function('Odd', isort, bsort)
O1 = Odd(1)
Oss = ForAll(x, Implies(Odd(x), Odd(x + 2)))
F = Implies(And(O1, Oss), And(Odd(9), And(Odd(25), Odd(99))))
prove(F)
