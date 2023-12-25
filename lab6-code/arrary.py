from z3 import *



def array_test():
    # array is an array from integer to integer
    array = Array('A', IntSort(), IntSort())
    x = Int('x')

    print(array[x])
    print(Select(array, x))
    print(Store(array, x, 10))
    print(simplify(Select(Store(array, 2, x+1), 2)))

# @Exercise 13: read and run above src,
# try to get familiarize yourself with the basic usage of Array in Z3py:
# you do not need to write any src here.



##########################################################
# @Exercise 14: This function returns the above formulae:
# Store(A, i, x)[i]>=x
# Now you should fill in the definition of the above formulae:
def array_proof():
    array = Array('a', IntSort(), IntSort())
    value = Int('x')
    index = Int('i')
    solver = Solver()
    
    # your src here
    raise NotImplementedError('TODO: Your code here!') 
    
    result = solver.check()
    if result == sat:
        return True, solver.model()
    else:
        return False, result
    


##########################################################
# @Exercise 15: Try to convert the array formulae
# Store(A, i*i - i*i, x)[0] >= x
# into a Z3 constraint and prove it.
# Whether it's "unknown" or not?
# What's the reason?
def array_non_linear_proof():
    array = Array('a', IntSort(), IntSort())
    value = Int('x')
    index = Int('i')
    solver = Solver()
    
    # your src here
    raise NotImplementedError('TODO: Your code here!') 
    
    result = solver.check()
    if result == sat:
        return True, solver.model()
    else:
        return False, result
    


##########################################################
# To implement an array interface using lambda (function).

# In the class, we discussed that the array interfaces can be
# implemented by reducing these interfaces to functions.
# To understand this, you'll implement a small array module
# by using anonymous function---lambdas, in Python.

# we define 3 APIs on an array:
#  array_new(): create a new array
#  array_select(): array reading
#  array_store(): array writing
def lambda_array():
    def array_new():
        return lambda x: 0

    # array[index]
    def array_select(array, index):
        return array(index)

    # array[index] = element
    def array_store(array, index, element):
        # @Exercise 16: write src to store an "element" into the
        # "index" position of "array" by using lambda expression.
        raise NotImplementedError('TODO: Your code here!') 

    # a small test case
    arr = array_new()
    assert (array_select(array_store(array_store(arr, 5, 88),
                                     7, 99),
                         5) == 88)
    assert (array_select(array_store(array_store(arr, 5, 88),
                                     7, 99),
                         17) == 0)
    print("\033[32mSUCCESS!\033[0m")


if __name__ == '__main__':
    array_test()
    array_proof()
    array_non_linear_proof()
    lambda_array()

