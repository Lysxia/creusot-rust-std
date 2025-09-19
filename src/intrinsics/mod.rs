#![allow(unused_variables)]

pub const unsafe fn exact_div<T: Copy>(x: T, y: T) -> T {
    panic!("intrinsics")
}

pub const unsafe fn cttz_nonzero<T: Copy>(x: T) -> u32 {
    panic!("intrinsics")
}

pub const fn mul_with_overflow<T: Copy>(x: T, y: T) -> (T, bool) {
    panic!("intrinsics")
}

pub const unsafe fn unchecked_rem<T: Copy>(x: T, y: T) -> T {
    panic!("intrinsics")
}

pub const unsafe fn unchecked_shl<T: Copy, U: Copy>(x: T, y: U) -> T {
    panic!("intrinsics")
}

pub const unsafe fn unchecked_shr<T: Copy, U: Copy>(x: T, y: U) -> T {
    panic!("intrinsics")
}

pub const unsafe fn unchecked_sub<T: Copy>(x: T, y: T) -> T {
    panic!("intrinsics")
}

pub const fn wrapping_add<T: Copy>(a: T, b: T) -> T {
    panic!("intrinsics")
}

pub const fn wrapping_mul<T: Copy>(a: T, b: T) -> T {
    panic!("intrinsics")
}

pub const fn wrapping_sub<T: Copy>(a: T, b: T) -> T {
    panic!("intrinsics")
}
