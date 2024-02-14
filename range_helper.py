k = 32 
n = 64 

def to_limbs(number, base=2**n):
    limbs = []
    while number > 0:
        number, remainder = divmod(number, base)
        limbs.append(remainder)
    return limbs


MAX = k * (2**n - 1) * (2**n - 1) 

from math import log2 
max_carry = MAX // 2**n

max_bits_carry = 5 + 64 + 64 - 64
print(max_bits_carry, log2(max_carry))


# print(max_carry)
print(to_limbs(max_carry))
print(to_limbs(max_carry * 2))


# MIN = k * (2**n - 1) * (2**n - 1) + (2**n - 1)
# min_carry = MIN // 2**n
# print(min_carry)
# print(to_limbs(min_carry))


"""
we want something in range [-2, 2] and we work mod 7 

then -2 = 5 and it takes 3 bits, but we want to make sure it's 2 bits 

so somehow we want to normalize it when it's negative 

if we have value that is in [-2^69, 2^70]
given x how xan we check that it's in this interval

x + 2^69 if x negative it will normalize it to the range 2^69

2^n + 2^n = 2^(n+1)



x = -2^69 - offset if offset > 2^69 then x is positive and we are in second case
x + 2^69 = -offset and it is a full field element so it won't pass the 70 bits check


"""

"""
if x is in [-2^5, 2^5] it will be enough to check that 

    x + 2^5 is in range [0, 2^6]

so we have to consider two cases: 

x < 0 
    if x is honest, then shift puts it in the right interval 
    if x is -2^5 - offset


x > 0: 

    2^n + 2^5 < 2^6 then we have a problem that x can be too large and we don't catch it

"""