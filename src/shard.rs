use std::hash::{BuildHasher, Hash};

use hashbrown::hash_map::{HashMap, RawEntryMut};

#[inline(always)]
pub(super) fn hash_one(build_hasher: &impl BuildHasher, string: &str) -> u64 {
    let mut hasher = build_hasher.build_hasher();
    string.hash(&mut hasher);
    std::hash::Hasher::finish(&hasher)
}

#[derive(Default)]
pub(super) struct Shard {
    map: HashMap<u32, (), ()>,
    pub strs: Vec<Box<str>>,
}

impl Shard {
    pub fn intern(&mut self, hash: u64, string: &str, build_hasher: &impl BuildHasher) -> u32 {
        let entry = self
            .map
            .raw_entry_mut()
            .from_hash(hash, |&idx| string == self.strs[idx as usize].as_ref());

        let index = match entry {
            RawEntryMut::Occupied(e) => *e.key(),
            RawEntryMut::Vacant(e) => {
                let idx = self.strs.len() as u32;
                self.strs.push(string.into());

                *e.insert_with_hasher(hash, idx, (), |&idx| {
                    hash_one(build_hasher, self.strs[idx as usize].as_ref())
                })
                .0
            }
        };

        debug_assert!(!self.strs.is_empty());
        debug_assert!(!self.map.is_empty());
        index
    }
}
