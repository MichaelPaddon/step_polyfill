//! Provides a polyfill for unstable feature [std::iter::Step].

/// A type that supports the notion of stepping forward or backward.
pub trait Step: Clone + PartialOrd + Sized {
    fn steps_between(start: &Self, end: &Self) -> Option<usize>;
    fn forward_checked(start: Self, count: usize) -> Option<Self>;
    fn backward_checked(start: Self, count: usize) -> Option<Self>;

    fn forward(start: Self, count: usize) -> Self {
        Step::forward_checked(start, count)
            .expect("overflow in `Step::forward`")
    }

    fn backward(start: Self, count: usize) -> Self {
        Step::backward_checked(start, count)
            .expect("overflow in `Step::forward`")
    }

    unsafe fn forward_unchecked(start: Self, count: usize) -> Self {
        Step::forward(start, count)
    }

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
