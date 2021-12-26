use crate::Value;
use atomic::Atomic;
use std::sync::atomic::Ordering;

/// Stores a reference to an atomic value from a [leapfrog::LeapMap].
pub struct Ref<'a, V: Value> {
    /// The atomic value which is being referenced.
    inner: &'a Atomic<V>,
}

impl<'a, V: Value> Ref<'a, V> {
    /// Creates a new ref type referencing the specified `value`.
    pub fn new(value: &'a Atomic<V>) -> Ref<'a, V> {
        Ref { inner: value }
    }

    /// Attempts to load the value of the referenced atomic value. Since it's
    /// possible that the map which stores the value has moved while holding this
    /// reference, has moved, this will return None in such a case, and will
    /// return Some(value) if the reference is valid.
    pub fn value(&self) -> Option<V> {
        let value = self.inner.load(Ordering::Relaxed);
        if value == V::redirect() {
            return None;
        }
        Some(value)
    }
}

/// Stores a reference to an atomic value.
pub struct RefMut<'a, V: Value> {
    /// The atomic value which is being referenced.
    inner: &'a Atomic<V>,
}

impl<'a, V: Value> RefMut<'a, V> {
    /// Creates a new mutable ref type referencing the specified `value`.
    pub fn new(value: &'a Atomic<V>) -> RefMut<'a, V> {
        RefMut { inner: value }
    }

    /// Attempts to load the value of the referenced atomic value. Since it's
    /// possible that the map which stores the value has moved while holding this
    /// reference, has moved, this will return None in such a case, and will
    /// return Some(value) if the reference is valid.
    pub fn value(&self) -> Option<V> {
        let value = self.inner.load(Ordering::Relaxed);
        if value == V::redirect() {
            return None;
        }
        Some(value)
    }

    /// Tries to set the value of the referenced atomic value. If the table which
    /// stores the referenced value has moved since getting the reference then
    /// this will return `None`, otherwise it will return `Some(old_value)`, where
    /// `old_value` is the previous value.
    pub fn set_value(&self, v: V) -> Option<V> {
        let mut current = self.inner.load(Ordering::Relaxed);
        loop {
            match self
                .inner
                .compare_exchange_weak(current, v, Ordering::Relaxed, Ordering::Relaxed)
            {
                Ok(_) => return Some(current),
                Err(updated) => {
                    // Value is stale
                    if updated == V::redirect() {
                        return None;
                    }
                    current = updated;
                }
            }
        }
    }

    // Updates the referenced value
    //pub fn update<F>(&self, f: F) -> Option<V>
    //where
    //    F: FnMut(V) -> Option<V>,
    //{
    //    self.inner
    //        .fetch_update(Ordering::AcqRel, Ordering::Relaxed, f)
    //        .map_or(None, |old| Some(old))
    //}
}
