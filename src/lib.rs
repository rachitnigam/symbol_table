#![warn(missing_docs)]
/*!

This crate provides an easy-to-use [`SymbolTable`]
 that's fast, suitable for concurrent access,
 and provides stable `&str` references for resolved symbols.

With the `global` feature enabled, the
 provided [`GlobalSymbol`] type
 provides a lot of convenience methods and trait implementations
 for converting to/from strings.
*/

#[cfg(feature = "global")]
mod global;
mod shard;
mod table;
use ahash::AHasher;
#[cfg(feature = "global")]
pub use global::GlobalSymbol;
use shard::{hash_one, Shard};
pub use table::Table;

use std::{
    hash::{BuildHasher, Hash},
    num::NonZeroU32,
};

use std::sync::Mutex;

/// A `BuildHasher` that builds a determinstically seeded AHasher
#[derive(Default)]
pub struct DeterministicHashBuilder;

impl BuildHasher for DeterministicHashBuilder {
    type Hasher = AHasher;
    fn build_hasher(&self) -> Self::Hasher {
        ahash::RandomState::with_seeds(0, 0, 0, 0).build_hasher()
    }
}

/// The default number of sharded in the [`SymbolTable`].
pub const DEFAULT_N_SHARDS: usize = 16;

/// A table in which you can intern strings and get back [`Symbol`]s.
///
/// The table is sharded `N` times (default [`DEFAULT_N_SHARDS`])
/// for lower contention when accessing concurrently.
pub struct SymbolTable<const N: usize = DEFAULT_N_SHARDS, S = DeterministicHashBuilder> {
    build_hasher: S,
    shards: [Mutex<Shard>; N],
}

impl<const N: usize, S> SymbolTable<N, S> {
    const SHARD_BITS: u32 = 32 - (N as u32 - 1).leading_zeros();
    const MAX_IDX: u32 = u32::MAX >> Self::SHARD_BITS;
}

impl SymbolTable<DEFAULT_N_SHARDS, DeterministicHashBuilder> {
    /// Creates a new [`SymbolTable`] with the default generic arguments.
    /// This symbol table will be determinisitic, using a seeded ahash.
    pub fn new() -> Self {
        Self::default()
    }
}

impl<const N: usize, S: BuildHasher> SymbolTable<N, S> {
    #[allow(clippy::assertions_on_constants)]
    fn with_hasher(build_hasher: S) -> Self {
        assert!(0 < N);
        assert!(N <= 1024);
        // println!("N = {}", N);
        // println!("SHARD_BITS = {}", Self::SHARD_BITS);
        // println!("MAX_IDX = {}", Self::MAX_IDX);
        let mut shards = Vec::with_capacity(N);
        shards.resize_with(N, Default::default);
        Self {
            build_hasher,
            shards: shards.try_into().unwrap_or_else(|_| panic!()),
        }
    }
}

impl<const N: usize, S: Default + BuildHasher> Default for SymbolTable<N, S> {
    fn default() -> Self {
        Self::with_hasher(S::default())
    }
}

impl<const N: usize, S: BuildHasher> Table for SymbolTable<N, S> {
    /// Intern a string into the [`SymbolTable`].
    ///
    /// Note how this method only takes `&self`, so it can be used concurrently.
    ///
    /// Interning the same string will give the same symbol.
    ///
    /// ```
    /// let mut table = symbol_table::SymbolTable::new();
    /// assert_eq!(table.intern("foo"), table.intern("foo"));
    /// ```
    fn intern(&self, string: &str) -> Symbol {
        let hash = hash_one(&self.build_hasher, string);
        let shard_i = hash as usize % N;
        // println!("Interning into shard {shard_i}");

        let mut locked = self.shards[shard_i].lock().unwrap();
        let i = locked.intern(hash, string, &self.build_hasher) + 1;
        drop(locked);

        assert!(i < Self::MAX_IDX, "Can't represent index {} in a Symbol", i);
        let shard_bits: u32 = (shard_i as u32) << (32 - Self::SHARD_BITS);
        // println!("shard_bits = {shard_bits:x}");
        Symbol(NonZeroU32::new(shard_bits | i).unwrap())
    }

    /// Resolve a symbol to the interned string.
    ///
    /// The resolved string is immutable and will live as long as the
    /// [`SymbolTable`].
    ///
    /// ```
    /// let mut table = symbol_table::SymbolTable::new();
    /// let foo = table.intern("foo");
    /// assert_eq!(table.resolve(foo), "foo");
    /// ```
    fn resolve(&self, sym: Symbol) -> &str {
        let shard_i = sym.0.get() >> (32 - Self::SHARD_BITS);
        debug_assert!(shard_i < N as u32);
        // println!("Resolving from shard {shard_i}");
        let i = sym.0.get() & (u32::MAX >> Self::SHARD_BITS);
        debug_assert!(i > 0);
        let i = i - 1; // undo the + 1 from interning
        let shard = self.shards[shard_i as usize].lock().unwrap();
        debug_assert!(
            !shard.strs.is_empty(),
            "Shard shouldn't be empty when resolving!"
        );
        let str: &str = &shard.strs[i as usize];

        // SAFETY:
        // We can "extend" the lifetime of str outside the mutex lock
        // because we know it will never move or be mutated. The only thing to
        // worry about is it getting dropped, but that's ok because it's
        // lifetime is less than `self`.
        unsafe { &*(str as *const str) }
    }
}

/// An interned symbol.
///
/// Resolve it back to the string by using [`Table::resolve`]
///
/// Internally, this is a [`NonZeroU32`], so it will be niche-optimized.
///
/// ```
/// # use std::mem::size_of; use symbol_table::Symbol;
/// assert_eq!(size_of::<Symbol>(), size_of::<u32>());
/// ```
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(NonZeroU32);

impl From<NonZeroU32> for Symbol {
    fn from(i: NonZeroU32) -> Self {
        Symbol(i)
    }
}

impl From<Symbol> for NonZeroU32 {
    fn from(sym: Symbol) -> Self {
        sym.0
    }
}
