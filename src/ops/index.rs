use creusot_contracts::prelude::*;

pub trait Index<Idx: ?Sized> {
    /// The returned type after indexing.
    // #[stable(feature = "rust1", since = "1.0.0")]
    // #[rustc_diagnostic_item = "IndexOutput"]
    type Output: ?Sized;

    /// Performs the indexing (`container[index]`) operation.
    ///
    /// # Panics
    ///
    /// May panic if the index is out of bounds.
    // #[stable(feature = "rust1", since = "1.0.0")]
    #[track_caller]
    #[requires(false)]
    fn index(&self, index: Idx) -> &Self::Output;
}

pub trait IndexMut<Idx: ?Sized>: Index<Idx> {
    /// Performs the mutable indexing (`container[index]`) operation.
    ///
    /// # Panics
    ///
    /// May panic if the index is out of bounds.
    // #[stable(feature = "rust1", since = "1.0.0")]
    #[track_caller]
    #[requires(false)]
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output;
}
