use std::collections::BTreeMap;

use super::index::ValueLocation;

#[derive(Debug, Clone, Copy)]
pub(super) struct FreeBlock {
    pub(super) offset: u64,
    pub(super) capacity: u32,
}

/// Manages free space tracking and allocation within the store file.
#[derive(Debug, Default)]
pub(super) struct FreeSpaceManager {
    free_blocks: BTreeMap<u32, Vec<FreeBlock>>,
}

impl FreeSpaceManager {
    pub(super) fn new() -> Self {
        Self {
            free_blocks: BTreeMap::new(),
        }
    }

    pub(super) fn clear(&mut self) {
        self.free_blocks.clear();
    }

    pub(super) fn add(&mut self, location: ValueLocation) {
        if location.record_capacity == 0 {
            return;
        }
        let entry = self
            .free_blocks
            .entry(location.record_capacity)
            .or_default();
        entry.push(FreeBlock {
            offset: location.record_offset,
            capacity: location.record_capacity,
        });
    }

    pub(super) fn take(&mut self, required_payload: u32) -> Option<FreeBlock> {
        let key = {
            let mut iter = self.free_blocks.range(required_payload..);
            iter.next().map(|(size, _)| *size)?
        };
        let mut blocks = self.free_blocks.remove(&key)?;
        let block = blocks.pop()?;
        if !blocks.is_empty() {
            self.free_blocks.insert(key, blocks);
        }
        Some(block)
    }
}
