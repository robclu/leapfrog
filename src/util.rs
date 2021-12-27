use std::alloc::{Allocator, Layout};
use std::ops::{Add, BitOr, Shr, Sub, SubAssign};

/// Loads the buffer `buf` as a u64.
#[inline]
pub(crate) fn load_u64_le(buf: &[u8], len: usize) -> u64 {
    debug_assert!(len <= buf.len());
    let mut data = 0u64;
    unsafe {
        std::ptr::copy_nonoverlapping(buf.as_ptr(), &mut data as *mut _ as *mut u8, len);
    }
    data.to_le()
}

/// Rounds the `value` up to the nearest power of two.
#[inline]
pub(crate) fn round_to_pow2<T>(value: T) -> T
where
    T: SubAssign
        + Add<Output = T>
        + Sub<Output = T>
        + Shr<Output = T>
        + BitOr<Output = T>
        + Copy
        + From<usize>,
{
    let v = value - T::from(1);
    let res = match std::mem::size_of::<T>() {
        1 => {
            let v = v | (v >> T::from(1));
            let v = v | (v >> T::from(2));
            let v = v | (v >> T::from(4));
            v
        }
        2 => {
            let v = v | (v >> T::from(1));
            let v = v | (v >> T::from(2));
            let v = v | (v >> T::from(4));
            let v = v | (v >> T::from(8));
            v
        }
        4 => {
            let v = v | (v >> T::from(1));
            let v = v | (v >> T::from(2));
            let v = v | (v >> T::from(4));
            let v = v | (v >> T::from(8));
            let v = v | (v >> T::from(16));
            v
        }
        8 => {
            let v = v | (v >> T::from(1));
            let v = v | (v >> T::from(2));
            let v = v | (v >> T::from(4));
            let v = v | (v >> T::from(8));
            let v = v | (v >> T::from(16));
            let v = v | (v >> T::from(32));
            v
        }
        _ => v,
    };
    res + T::from(1)
}

/// Allocates `count` number of elements of type T, using the `allocator`.
pub(crate) fn allocate<T, A: Allocator>(allocator: &A, count: usize) -> *mut T {
    let size = std::mem::size_of::<T>();
    let align = std::mem::align_of::<T>();

    // We unwrap here because we want to panic if we fail to get a valid layout
    let layout = Layout::from_size_align(size * count, align).unwrap();

    // Again, unwrap the allocation result. It should never fail to allocate.
    allocator.allocate(layout).unwrap().as_ptr() as *mut T
}

/// Deallocates `count` number of elements of type T, using the `allocator`.
pub(crate) fn deallocate<T, A: Allocator>(allocator: &A, ptr: *mut T, count: usize) {
    let size = std::mem::size_of::<T>();
    let align = std::mem::align_of::<T>();

    // We unwrap here because we want to panic if we fail to get a valid layout
    let layout = Layout::from_size_align(size * count, align).unwrap();

    // Again, unwrap the allocation result. It should never fail to allocate.
    let raw_ptr = ptr as *mut u8;
    let nonnull_ptr = std::ptr::NonNull::new(raw_ptr).unwrap();
    unsafe {
        allocator.deallocate(nonnull_ptr, layout);
    }
}