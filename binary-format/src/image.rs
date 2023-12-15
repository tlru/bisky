use alloc::collections::BTreeMap;

/// A resource that describes the executable code, read-only memory, and initial read-write memory.
#[derive(Clone)]
pub struct MemoryImage {
    pub entry: u32,
    pub image: BTreeMap<u32, u32>,
    pub text_region: (usize, usize),
    pub rodata_region: (usize, usize),
    pub rw_region: (usize, usize),
}

impl MemoryImage {
    pub fn text_memory(&self) -> BTreeMap<u32, u32> {
        let (start, size) = self.text_region;
        self.image
            .range(start as u32..(start + size) as u32)
            .map(|(program_counter, value)| (*program_counter, *value))
            .collect()
    }

    pub fn rodata_memory(&self) -> BTreeMap<u32, u32> {
        let (start, size) = self.rodata_region;
        self.image
            .range(start as u32..(start + size) as u32)
            .map(|(program_counter, value)| (*program_counter, *value))
            .collect()
    }

    pub fn rw_memory(&self) -> BTreeMap<u32, u32> {
        let (start, size) = self.rw_region;
        self.image
            .range(start as u32..(start + size) as u32)
            .map(|(program_counter, value)| (*program_counter, *value))
            .collect()
    }
}
