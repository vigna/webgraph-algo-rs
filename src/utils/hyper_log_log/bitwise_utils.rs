use sux::traits::Word;

/// Performs a multiple precision subtraction, leaving the result in the first operand.
/// The operands MUST have the same length.
///
/// # Arguments
/// * `x`: the first operand. This will contain the final result.
/// * `y`: the second operand that will be subtracted from `x`.
#[inline(always)]
pub(super) fn subtract<W: Word>(x: &mut [W], y: &[W]) {
    debug_assert_eq!(x.len(), y.len());
    let mut borrow = false;

    for (x_word, &y) in x.iter_mut().zip(y.iter()) {
        let mut x = *x_word;
        if !borrow {
            borrow = x < y;
        } else if x != W::ZERO {
            x = x.wrapping_sub(W::ONE);
            borrow = x < y;
        } else {
            x = x.wrapping_sub(W::ONE);
        }
        *x_word = x.wrapping_sub(y);
    }
}

#[inline(always)]
pub(crate) fn merge_hyperloglog_bitwise<W: Word>(
    x: &mut [W],
    y: &[W],
    msb_mask: &[W],
    lsb_mask: &[W],
    acc: &mut Vec<W>,
    mask: &mut Vec<W>,
    register_size: usize,
) {
    // We split x, y and the masks so we treat the last word appropriately.
    let (x_last, x_slice) = x.split_last_mut().unwrap();
    let (&y_last, y_slice) = y.split_last().unwrap();
    let (&msb_last, msb_slice) = msb_mask.split_last().unwrap();

    let register_size_minus_1 = register_size - 1;
    let num_words_minus_1 = x_slice.len();
    let shift_register_size_minus_1 = W::BITS - register_size_minus_1;

    /* We work in two phases. Let H_r (msb_mask) be the mask with the
     * highest bit of each register (of size r) set, and L_r (lsb_mask)
     * be the mask with the lowest bit of each register set.
     * We describe the algorithm on a single word.
     *
     * In the first phase we perform an unsigned strict register-by-register
     * comparison of x and y, using the formula
     *
     * z = ((((y | H_r) - (x & !H_r)) | (y ^ x)) ^ (y | !x)) & H_r
     *
     * Then, we generate a register-by-register mask of all ones or
     * all zeroes, depending on the result of the comparison, using the
     * formula
     *
     * (((z >> r-1 | H_r) - L_r) | H_r) ^ z
     *
     * At that point, it is trivial to select from x and y the right values.
     */

    // We load y | H_r into the accumulator.
    acc.extend(
        y_slice
            .iter()
            .zip(msb_slice)
            .map(|(&y_word, &msb_word)| y_word | msb_word),
    );
    acc.push(y_last | msb_last);

    // We load x & !H_r into mask as temporary storage.
    mask.extend(
        x_slice
            .iter()
            .zip(msb_slice)
            .map(|(&x_word, &msb_word)| x_word & !msb_word),
    );
    mask.push(*x_last & !msb_last);

    // We subtract x & !H_r, using mask as temporary storage
    subtract(acc, mask);

    // We OR with y ^ x, XOR with (y | !x), and finally AND with H_r.
    {
        let (acc_last, acc_slice) = acc.split_last_mut().unwrap();
        acc_slice
            .iter_mut()
            .zip(x_slice.iter())
            .zip(y_slice.iter())
            .zip(msb_slice.iter())
            .for_each(|(((acc_word, &x_word), &y_word), &msb_word)| {
                *acc_word = ((*acc_word | (y_word ^ x_word)) ^ (y_word | !x_word)) & msb_word
            });
        *acc_last = ((*acc_last | (y_last ^ *x_last)) ^ (y_last | !*x_last)) & msb_last;
    }

    // We shift by register_size - 1 places and put the result into mask.
    {
        let (mask_last, mask_slice) = mask.split_last_mut().unwrap();
        mask_slice
            .iter_mut()
            .zip(acc[0..num_words_minus_1].iter())
            .zip(acc[1..].iter())
            .zip(msb_slice.iter())
            .rev()
            .for_each(|(((mask_word, &acc_word), &next_acc_word), &msb_word)| {
                // W is always unsigned so the shift is always with a 0
                *mask_word = (acc_word >> register_size_minus_1)
                    | (next_acc_word << shift_register_size_minus_1)
                    | msb_word
            });
        *mask_last = (acc[num_words_minus_1] >> register_size_minus_1) | msb_last;
    }

    // We subtract L_r from mask.
    subtract(mask, lsb_mask);

    // We OR with H_r and XOR with the accumulator.
    let (mask_last, mask_slice) = mask.split_last_mut().unwrap();
    let (&acc_last, acc_slice) = acc.split_last().unwrap();
    mask_slice
        .iter_mut()
        .zip(msb_slice.iter())
        .zip(acc_slice.iter())
        .for_each(|((mask_word, &msb_word), &acc_word)| {
            *mask_word = (*mask_word | msb_word) ^ acc_word
        });
    *mask_last = (*mask_last | msb_last) ^ acc_last;

    // Finally, we use mask to select the right bits from x and y and store the result.
    x_slice
        .iter_mut()
        .zip(y_slice.iter())
        .zip(mask_slice.iter())
        .for_each(|((x_word, &y_word), &mask_word)| {
            *x_word = *x_word ^ ((*x_word ^ y_word) & mask_word);
        });
    *x_last = *x_last ^ ((*x_last ^ y_last) & *mask_last);
}
