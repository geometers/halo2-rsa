/*
    we want to have a polynomial and we evaluate it with this new gate that we made
    now we will have a lot of different polynomials and we want to call evaluate on all of them
    some of them will be of degree k and some of degree 2k - 1 but we don't really care since our
    gate works generically


    higher level thing we want to do in some kind of fpmul
    1. now we want to be able to output last evaluation and check bunch of constraints with our polynomials


    2. we simply want to code check carry to zero which should be easy



*/

/*
template FpMul2() {
    signal input a[32];
    signal input n[32];
    signal input q[32];
    signal input r[32];

    signal aXa[32][32];
    signal qXn[32][32];
    for (var i = 0; i < 32; i++) {
        for (var j = 0; j < 32; j++) {
            aXa[i][j] <== a[i] * a[j];
            qXn[i][j] <== q[i] * n[j];
        }
    }

    signal aa[63];
    signal qn_r[63];

    var deg = 32;
    // upper part
    for (var k = 0; k < deg; k++) {
        var j = k;
        var acc_lhs = 0;
        var acc_rhs = 0;
        for (var i = 0; i < k + 1; i++) {
            acc_lhs += aXa[i][j];
            acc_rhs += qXn[i][j];

            j -= 1;
        }
        aa[k] <== acc_lhs;
        qn_r[k] <== acc_rhs + r[k];
    }

    // lower part
    for (var k = 1; k < deg; k++) {
        var j = deg - 1;
        var acc_lhs = 0;
        var acc_rhs = 0;
        for (var i = k; i < deg; i++) {
            acc_lhs += aXa[i][j];
            acc_rhs += qXn[i][j];

            j -= 1;
        }
        aa[deg - 1 + k] <== acc_lhs;
        qn_r[deg - 1 + k] <== acc_rhs;
    }

    n = 13
    we work B = 10
    so n = 3 + X, so n = 13 for X = B

    and let's say we do a = 9
    9 * 9 = 81

    81 / 13 = 6 * 13 + 3 | q = 6, r = 3

    81 = 6 * (3 + X) + 3

    if a*a === q * n + r

    each limb will be multiple of basis

    suppose it's not:

    suppose that aa[0] - qn_r[0] is != 0 and not divisible by 10

    then we can write that number as 10*Q + R for R not equal 0

    so if we "normalize number mod B" what this means
    (so simply 81 normalized is 1 + 8X,)

    that limb 0 of aa[0] - qn_r[0] is R so this number can never be 0 because any other limb
    will always have at least 10 * something so it can never substract R from the whole number

    so if we want to check that final bigint === 0 without overflow, it's enough to just prove that each
    limb is divisible by B and to accumulate everything to the top

    so say basis = 8

    then [-72, 1, 1] = 0 as bigint

           -72 + 1 *8 + 1*64

    why

    -72 / 8 = -9

    (1 - 9) / 8 = -1

    -1 + 1 = 0!!

    81 = 6 * (3 + X) + 3
    81 = 18 + 6x + 3
    81 - 21 = 6x

    so 81 - 21 = 60 and it is divisible by 10

    81 - 20 = 6x this could never be 0 at 10 because on rhs we will always have something greater that 10
    and on lhs we would be left with 61 // 10 = 1

    so we would never be able to cancel out this 1 no matter how many limbs we have which are going to be 10, 100, 1000, 100000...

    so for halo2, we would just prove that these limbs can all be dividied by B

    L = q * B, and that q is correcrly range checked, i have all the numbers somewhere here so no worries about that

    assert(poly_eval(63, aa, 2**64) == poly_eval(63, qn_r, 2**64));

    var MAX = (31 + 1) * (2**64 - 1) * (2**64 - 1);

    log("log ceil: ", log_ceil(MAX));

    component tCheck = CheckCarryToZero(64, 64 + 64 + log_ceil(32) + 2, 63);
    for (var i = 0; i < 63; i++) {
        tCheck.in[i] <== aa[i] - qn_r[i];
    }

    signal output out[32];
    for (var i = 0; i < 32; i++) {
        out[i] <== r[i];
    }
}
*/

/*
if we never witness a^2 and if we never instantiate qn_r, can we actually
just check that a(ß) * a(ß) = q(ß) * n(ß) + r(ß)

so what we have to do is:

0. witness a, q, n, r
1. witness aa
2. witness qn_r

3. prove that aa(ß) = a(ß)^2
4. prove that qn_r(ß) = q(ß)*n(ß) + r(ß)

5. prove this CarryToZero relation in aa - qn_r

This implies that if we use RLC at each exponentiation step we do next:

we need rlc of aa, qn_r, a, q, r
since aa and qn_r have 63 coeefs

this is 2 * 63 + 3 * 32 = 126 + 96 = 222


aa = q_0 * n + r_0

r_0r_0 = q_1 + n + r_1

so we can leverge the fact that we already evaluated r_0, so we can just chech that
r_0r_0(ß) = (r_0(ß))^2 and r_0(ß) we have from the privious step so we don't need to evaluate it each time in the loop
*/

/*
1. witness all polynomials in columns of phase 1
2. derive evaluation challenge
3. evaluate all polynomials

FpMul:
    fpmul want's to make sure that
        1. a_sq is indeed a * a
        2. qn_r is indeed q * n + r
        3. call checkcarry to zero on coeffs of a_sq and qn_r



*/

mod fpmul;
mod lookup_range_check;
mod mul_cfgs;
mod poly_eval;
