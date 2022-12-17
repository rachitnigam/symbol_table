use crate::Symbol;

/// A Table that stores a mapping from strings to symbols
pub trait Table {
    /// Intern a string into the [`Table`].
    ///
    /// Note how this method only takes `&self`, so it can be used concurrently.
    ///
    /// Interning the same string will give the same symbol.
    ///
    /// ```
    /// let mut table = symbol_table::SymbolTable::new();
    /// assert_eq!(table.intern("foo"), table.intern("foo"));
    /// ```
    fn intern(&self, string: &str) -> Symbol;

    /// Resolve a symbol to the interned string.
    ///
    /// The resolved string is immutable and will live as long as the
    /// [`Table`].
    ///
    /// ```
    /// let mut table = symbol_table::SymbolTable::new();
    /// let foo = table.intern("foo");
    /// assert_eq!(table.resolve(foo), "foo");
    /// ```
    fn resolve(&self, sym: Symbol) -> &str;
}
