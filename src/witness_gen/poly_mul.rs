/*
[a0, a1, a2, a3] * [b0, b1, b2, b3]
[
    a0b0, a0b1, a0b2, a0b3
    a1b0, a1b1, a1b2, a1b3
    a2b0, a2b1, a2b2, a2b3
    a3b0, a3b1, a3b2, a3b3
]

coefficients of c can be obtained from traversing diagonals of the above matrix
*/

use ff::Field;

fn pad_with_zeros<F: Field>(a: &mut Vec<F>, b: &mut Vec<F>) {
    let max_length = a.len().max(b.len());

    while a.len() < max_length {
        a.push(F::ZERO);
    }

    while b.len() < max_length {
        b.push(F::ZERO);
    }
}

pub(super) fn poly_mul<F: Field>(a: &[F], b: &[F]) -> Vec<F> {
    let mut a = a.to_vec();
    let mut b = b.to_vec();
    if a.len() != b.len() {
        pad_with_zeros(&mut a, &mut b);
    }

    let degree = a.len() - 1;
    let k = degree + 1;

    let c_coeffs_len = 2 * k - 1;

    let mut c_coeffs = vec![];

    for deg in 0..k {
        let mut row_col_sum = F::ZERO;
        for (i, &a_i) in a.iter().enumerate().take(deg + 1) {
            row_col_sum += a_i * b[deg - i];
        }
        c_coeffs.push(row_col_sum);
    }

    for deg in k..c_coeffs_len {
        let mut b_i = k - 1;

        let bound = c_coeffs_len - deg;
        let mut row_col_sum = F::ZERO;

        for _ in 0..bound {
            let a_i = deg - b_i;
            row_col_sum += a[a_i] * b[b_i];
            b_i -= 1;
        }

        c_coeffs.push(row_col_sum);
    }

    c_coeffs
}
