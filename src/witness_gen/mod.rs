mod check_trace;
mod poly_mul;
pub mod signature;
pub mod trace_gen;
pub mod utils;

/*

# print(hash_object.digest())
byte_array = bytearray(hash_object.digest())
binary_string = ''.join(format(byte, '08b') for byte in byte_array)
# print(binary_string)
digest_int = bytes_to_long(byte_array)
# print(to_limbs_le(digest_int))
print('-------------')

signature = pkcs.sign(hash_object)
s_int = bytes_to_long(signature)

em = _EMSA_PKCS1_V1_5_ENCODE(hash_object, key_bits // 8, True)
em_int = bytes_to_long(em)

tr_gen = TraceGen(rsa_key.n, e)
x, trace = tr_gen.compute_trace(s_int)

assert(em_int == x)

x_limbs = trace.tuples[-1][2]
em_le_limbs = to_limbs_le(em_int)

assert(x_limbs == em_le_limbs)

print(em_le_limbs[0])
print(em_le_limbs[1])
print(em_le_limbs[2])
print(em_le_limbs[3])

print(em_le_limbs[4])
print(em_le_limbs[5])
print(em_le_limbs[6])

print('-------')
for i in range(24):
    print(em_le_limbs[7 + i])

print(em_le_limbs[31])
print(2**49 - 1)

# print('---------------')
# print(int(bin(em_int)[-64:], 2))
# print(int(bin(em_int)[-128:-64], 2))
# print(int(bin(em_int)[-192:-128], 2))
# print(int(bin(em_int)[-256:-192], 2))
# print(int(bin(em_int)[-(256 + 64):-(192 + 64)], 2))
# print(int(bin(em_int)[-(256 + 128):-(192 + 128)], 2))
# print(int(bin(em_int)[-(256 + 192):-(192 + 192)], 2))
# print(int(bin(em_int)[-(256 + 192):-(192 + 192)]))


# print(int(bin(em_int)[-64:], 2))

# 256 from sha = 4 * u64
# then we have 2033 - 265 = 1777,
# these 1777 are 152 for digest info and then all PS + one 1
# so it's 152 hardcoded bits from digest info, and all others are 1
# so next multiple of 64 from 152 is 192 so we can treat next 3 limbs as 152 hardcoded digest info bits and then appended with 8 zeroes and then 32 ones

# then we are left with 1777 - 192 = 1585 ones
# 1585 is 24 full 1 limbs
# and then 49 little endian 1ones so 2^49
*/
