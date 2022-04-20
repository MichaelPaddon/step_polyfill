//! This crate provides a polyfill for the unstable [std::iter::Step] trait.
//!
//! Developers can use this polyfill with the stable Rust compiler.
//! It will be obsoleted when [std::iter::Step] is stabilized.
//!
//! The API and documentation is copied from the Rust Core Library.

/// Objects that have a notion of *successor* and *predecessor* operations.
///
/// The *successor* operation moves towards values that compare greater.
/// The *predecessor* operation moves towards values that compare lesser.
///
/// This is a polyfill for the unstable [std::iter::Step] trait.
pub trait Step: Clone + PartialOrd + Sized {
    /// Returns the number of *successor* steps required to get from
    /// `start` to `end`.
    ///
    /// Returns `None` if the number of steps would overflow `usize`
    /// (or is infinite, or if `end` would never be reached).
    ///
    /// # Invariants
    ///
    /// For any `a`, `b`, and `n`:
    ///
    /// * `steps_between(&a, &b) == Some(n)` if and only if `Step::forward_checked(&a, n) == Some(b)`
    /// * `steps_between(&a, &b) == Some(n)` if and only if `Step::backward_checked(&b, n) == Some(a)`
    /// * `steps_between(&a, &b) == Some(n)` only if `a <= b`
    ///   * Corollary: `steps_between(&a, &b) == Some(0)` if and only if `a == b`
    ///   * Note that `a <= b` does _not_ imply `steps_between(&a, &b) != None`;
    ///     this is the case when it would require more than `usize::MAX` steps to get to `b`
    /// * `steps_between(&a, &b) == None` if `a > b`
    fn steps_between(start: &Self, end: &Self) -> Option<usize>;

    /// Returns the value that would be obtained by taking the *successor*
    /// of `self` `count` times.
    ///
    /// If this would overflow the range of values supported by `Self`,
    /// returns `None`.
    ///
    /// # Invariants
    ///
    /// For any `a`, `n`, and `m`:
    ///
    /// * `Step::forward_checked(a, n).and_then(|x| Step::forward_checked(x, m)) == Step::forward_checked(a, m).and_then(|x| Step::forward_checked(x, n))`
    ///
    /// For any `a`, `n`, and `m` where `n + m` does not overflow:
    ///
    /// * `Step::forward_checked(a, n).and_then(|x| Step::forward_checked(x, m)) == Step::forward_checked(a, n + m)`
    ///
    /// For any `a` and `n`:
    ///
    /// * `Step::forward_checked(a, n) == (0..n).try_fold(a, |x, _| Step::forward_checked(&x, 1))`
    ///   * Corollary: `Step::forward_checked(&a, 0) == Some(a)`
    fn forward_checked(start: Self, count: usize) -> Option<Self>;

    /// Returns the value that would be obtained by taking the *predecessor*
    /// of `self` `count` times.
    ///
    /// If this would overflow the range of values supported by `Self`,
    /// returns `None`.
    ///
    /// # Invariants
    ///
    /// For any `a`, `n`, and `m`:
    ///
    /// * `Step::backward_checked(a, n).and_then(|x| Step::backward_checked(x, m)) == n.checked_add(m).and_then(|x| Step::backward_checked(a, x))`
    /// * `Step::backward_checked(a, n).and_then(|x| Step::backward_checked(x, m)) == try { Step::backward_checked(a, n.checked_add(m)?) }`
    ///
    /// For any `a` and `n`:
    ///
    /// * `Step::backward_checked(a, n) == (0..n).try_fold(a, |x, _| Step::backward_checked(&x, 1))`
    ///   * Corollary: `Step::backward_checked(&a, 0) == Some(a)`
    fn backward_checked(start: Self, count: usize) -> Option<Self>;

    /// Returns the value that would be obtained by taking the *successor*
    /// of `self` `count` times.
    ///
    /// If this would overflow the range of values supported by `Self`,
    /// this function is allowed to panic, wrap, or saturate.
    /// The suggested behavior is to panic when debug assertions are enabled,
    /// and to wrap or saturate otherwise.
    ///
    /// Unsafe code should not rely on the correctness of behavior after
    /// overflow.
    ///
    /// # Invariants
    ///
    /// For any `a`, `n`, and `m`, where no overflow occurs:
    ///
    /// * `Step::forward(Step::forward(a, n), m) == Step::forward(a, n + m)`
    ///
    /// For any `a` and `n`, where no overflow occurs:
    ///
    /// * `Step::forward_checked(a, n) == Some(Step::forward(a, n))`
    /// * `Step::forward(a, n) == (0..n).fold(a, |x, _| Step::forward(x, 1))`
    ///   * Corollary: `Step::forward(a, 0) == a`
    /// * `Step::forward(a, n) >= a`
    /// * `Step::backward(Step::forward(a, n), n) == a`
    fn forward(start: Self, count: usize) -> Self {
        Step::forward_checked(start, count)
            .expect("overflow in `Step::forward`")
    }

    /// Returns the value that would be obtained by taking the *predecessor*
    /// of `self` `count` times.
    ///
    /// If this would overflow the range of values supported by `Self`,
    /// this function is allowed to panic, wrap, or saturate.
    /// The suggested behavior is to panic when debug assertions are enabled,
    /// and to wrap or saturate otherwise.
    ///
    /// Unsafe code should not rely on the correctness of behavior after
    /// overflow.
    ///
    /// # Invariants
    ///
    /// For any `a`, `n`, and `m`, where no overflow occurs:
    ///
    /// * `Step::backward(Step::backward(a, n), m) == Step::backward(a, n + m)`
    ///
    /// For any `a` and `n`, where no overflow occurs:
    ///
    /// * `Step::backward_checked(a, n) == Some(Step::backward(a, n))`
    /// * `Step::backward(a, n) == (0..n).fold(a, |x, _| Step::backward(x, 1))`
    ///   * Corollary: `Step::backward(a, 0) == a`
    /// * `Step::backward(a, n) <= a`
    /// * `Step::forward(Step::backward(a, n), n) == a`
    fn backward(start: Self, count: usize) -> Self {
        Step::backward_checked(start, count)
            .expect("overflow in `Step::forward`")
    }

    /// Returns the value that would be obtained by taking the *successor*
    /// of `self` `count` times.
    ///
    /// # Safety
    ///
    /// It is undefined behavior for this operation to overflow the
    /// range of values supported by `Self`. If you cannot guarantee that this
    /// will not overflow, use `forward` or `forward_checked` instead.
    ///
    /// # Invariants
    ///
    /// For any `a`:
    ///
    /// * if there exists `b` such that `b > a`, it is safe to call `Step::forward_unchecked(a, 1)`
    /// * if there exists `b`, `n` such that `steps_between(&a, &b) == Some(n)`,
    ///   it is safe to call `Step::forward_unchecked(a, m)` for any `m <= n`.
    ///
    /// For any `a` and `n`, where no overflow occurs:
    ///
    /// * `Step::forward_unchecked(a, n)` is equivalent to `Step::forward(a, n)`
    unsafe fn forward_unchecked(start: Self, count: usize) -> Self {
        Step::forward(start, count)
    }

     /// Returns the value that would be obtained by taking the *predecessor*
    /// of `self` `count` times.
    ///
    /// # Safety
    ///
    /// It is undefined behavior for this operation to overflow the
    /// range of values supported by `Self`. If you cannot guarantee that this
    /// will not overflow, use `backward` or `backward_checked` instead.
    ///
    /// # Invariants
    ///
    /// For any `a`:
    ///
    /// * if there exists `b` such that `b < a`, it is safe to call `Step::backward_unchecked(a, 1)`
    /// * if there exists `b`, `n` such that `steps_between(&b, &a) == Some(n)`,
    ///   it is safe to call `Step::backward_unchecked(a, m)` for any `m <= n`.
    ///
    /// For any `a` and `n`, where no overflow occurs:
    ///
    /// * `Step::backward_unchecked(a, n)` is equivalent to `Step::backward(a, n)`
    unsafe fn backward_unchecked(start: Self, count: usize) -> Self {
        Step::forward(start, count)
    }
}

macro_rules! step_integer_impl {
    {$($Integer:ty, $Unsigned:ty);+} => {$(
        impl Step for $Integer {
            fn steps_between(start: &Self, end: &Self) -> Option<usize> {
                if start <= end {
                    let count = (*end as $Unsigned)
                        .wrapping_sub(*start as $Unsigned);
                    usize::try_from(count).ok()
                }
                else {
                    None
                }
            }

            fn forward_checked(start: Self, count: usize) -> Option<Self> {
                let count = <$Unsigned>::try_from(count).ok()?;
                let end = (start as $Unsigned).wrapping_add(count) as $Integer;
                if end >= start {Some(end)} else {None}
            }

            fn backward_checked(start: Self, count: usize) -> Option<Self> {
                let count = <$Unsigned>::try_from(count).ok()?;
                let end = (start as $Unsigned).wrapping_sub(count) as $Integer;
                if end <= start {Some(end)} else {None}
            }
        }
    )+}
}

step_integer_impl!{
    i8, u8; i16, u16; i32, u32; i64, u64; i128, u128; isize, usize;
    u8, u8; u16, u16; u32, u32; u64, u64; u128, u128; usize, usize
}

const UNICODE_HOLE_START:u32 = 0xd800;
const UNICODE_HOLE_END:u32 = 0xdfff;
const UNICODE_HOLE_LENGTH:u32 = UNICODE_HOLE_END - UNICODE_HOLE_START + 1;

impl Step for char {
    fn steps_between(start: &Self, end: &Self) -> Option<usize> {
        if start <= end {
            let start = *start as u32;
            let end = *end as u32;
            let mut count = end - start;
            if start < UNICODE_HOLE_START && end > UNICODE_HOLE_END {
                count -= UNICODE_HOLE_LENGTH;
            }
            usize::try_from(count).ok()
        }
        else {
            None
        }
    }

    fn forward_checked(start: Self, count: usize) -> Option<Self> {
        let start= start as u32;
        let count = u32::try_from(count).ok()?;
        let mut end = start.checked_add(count)?;
        if start < UNICODE_HOLE_START && end >= UNICODE_HOLE_START {
            end = end.checked_add(UNICODE_HOLE_LENGTH)?;
        }
        char::try_from(end).ok()
    }

    fn backward_checked(start: Self, count: usize) -> Option<Self> {
        let start= start as u32;
        let count = u32::try_from(count).ok()?;
        let mut end = start.checked_sub(count)?;
        if start > UNICODE_HOLE_END && end <= UNICODE_HOLE_END {
            end = end.checked_sub(UNICODE_HOLE_LENGTH)?;
        }
        char::try_from(end).ok()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! step_test {
        {$(
            $name:ident, $T:ty, $start:expr, $end:expr, $count:expr,
            $predecessor:expr, $successor:expr
        );+} => {$(
            #[test]
            fn $name(){
                let count = usize::try_from($count).ok();
                assert_eq!(<$T>::steps_between(&$start, &$start), Some(0));
                assert_eq!(<$T>::steps_between(&$end, &$end), Some(0));
                assert_eq!(<$T>::steps_between(&$start, &$end), count);
                if ($start < $end){
                    assert_eq!(<$T>::steps_between(&$end, &$start), None);
                }

                assert_eq!(<$T>::forward_checked($start, 0), Some($start));
                assert_eq!(<$T>::backward_checked($start, 0), Some($start));
                assert_eq!(<$T>::forward_checked($end, 0), Some($end));
                assert_eq!(<$T>::backward_checked($end, 0), Some($end));
                if let Some(count) = count {
                    assert_eq!(<$T>::forward_checked($start, count),
                        Some($end));
                    assert_eq!(<$T>::backward_checked($end, count),
                        Some($start));
                }

                assert_eq!(<$T>::backward_checked($start, 1), $predecessor);
                assert_eq!(<$T>::forward_checked($end, 1), $successor);
            }
        )+}
    }

    step_test!{
        test_i8, i8, -1, 1, 2, Some(-2), Some(2);
        test_i16, i16, -1, 1, 2, Some(-2), Some(2);
        test_i32, i32, -1, 1, 2, Some(-2), Some(2);
        test_i64, i64, -1, 1, 2, Some(-2), Some(2);
        test_i128, i128, -1, 1, 2, Some(-2), Some(2);
        test_u8, u8, 1, 2, 1, Some(0), Some(3);
        test_u16, u16, 1, 2, 1, Some(0), Some(3);
        test_u32, u32, 1, 2, 1, Some(0), Some(3);
        test_u64, u64, 1, 2, 1, Some(0), Some(3);
        test_u128, u128, 1, 2, 1, Some(0), Some(3);

        test_i8_range, i8, i8::MIN, i8::MAX, 0xff as u8, None, None;
        test_i16_range, i16, i16::MIN, i16::MAX, 0xffff as u16, None, None;
        test_i32_range, i32, i32::MIN, i32::MAX, 0xffffffff as u32, None, None;
        test_i64_range, i64, i64::MIN, i64::MAX,
            0xffffffffffffffff as u64, None, None;
        test_i128_range, i128, i128::MIN, i128::MAX,
            0xffffffffffffffffffffffffffffffff as u128, None, None;
        test_u8_range, u8, u8::MIN, u8::MAX, 0xff as u8, None, None;
        test_u16_range, u16, u16::MIN, u16::MAX, 0xffff as u16, None, None;
        test_u32_range, u32, u32::MIN, u32::MAX, 0xffffffff as u32, None, None;
        test_u64_range, u64, u64::MIN, u64::MAX,
            0xffffffffffffffff as u64, None, None;
        test_u128_range, u128, u128::MIN, u128::MAX,
            0xffffffffffffffffffffffffffffffff as u128, None, None;

        test_char_az, char, 'a', 'z', 25, Some('`'), Some('{');
        test_char_hole, char, '\u{d7ff}', '\u{e000}', 1,
            Some('\u{d7fe}'), Some('\u{e001}');
        test_char_range, char, '\u{0000}', char::MAX, 0x10f7ff as u32,
            None, None
    }
}
