// #![cfg_attr(any(test, not(feature = "std")), no_std)]
// #![no_std]

// #[cfg(any(test, not(feature = "std")))]
#[macro_use]
extern crate alloc;

use alloc::collections::BTreeMap;

use anyhow::{anyhow, bail, Context};
use elf::endian::LittleEndian;
use elf::segment::ProgramHeader;
use elf::ElfBytes;
use tracing::{debug, info};

use crate::image::MemoryImage;
use crate::rv32im::{instruction_name, WORD_SIZE};

pub mod image;
pub mod rv32im;

pub fn load_elf(input: &[u8], max_mem: u32) -> anyhow::Result<MemoryImage> {
    // TODO: we will know which segments are code and which are data from the linker script so we can analyze
    let mut image = BTreeMap::<u32, u32>::new();
    let elf = ElfBytes::<LittleEndian>::minimal_parse(input)
        .map_err(|err| anyhow!("Elf parse error: {err}"))?;
    if elf.ehdr.class != elf::file::Class::ELF32 {
        bail!("Not a 32-bit ELF");
    }
    if elf.ehdr.e_machine != elf::abi::EM_RISCV {
        bail!("Invalid machine type, must be RISC-V");
    }
    if elf.ehdr.e_type != elf::abi::ET_EXEC {
        bail!("Invalid ELF type, must be executable");
    }

    let entry: u32 = elf
        .ehdr
        .e_entry
        .try_into()
        .map_err(|err| anyhow!("e_entry was larger than 32 bits. {err}"))?;
    if entry >= max_mem || entry % WORD_SIZE as u32 != 0 {
        bail!("Invalid entrypoint");
    }

    println!("entry: {:x}", entry);

    let segments = elf.segments().ok_or(anyhow!("Missing segment table"))?;
    if segments.len() > 256 {
        bail!("Too many program headers");
    }

    // attempt to track the continuous text segment that we have an idea of where it starts from the linker script
    let mut text_segment: Option<(u32 /* start */, u32 /* size */)> = None;

    /// These will not always be present
    let (shdrs_opt, strtab_opt) = elf
        .section_headers_with_strtab()
        .expect("shdrs offsets should be valid");
    let (shdrs, strtab) = (
        shdrs_opt.expect("Should have shdrs"),
        strtab_opt.expect("Should have strtab"),
    );
    let section_headers_by_name = shdrs
        .iter()
        .map(|shdr| (strtab.get(shdr.sh_name as usize).unwrap().to_string(), shdr))
        .collect::<BTreeMap<_, _>>();
    // println!(
    //     "section_headers_by_name: {:?}",
    //     section_headers_by_name.keys().cloned().collect::<Vec<_>>()
    // );
    let text_section = section_headers_by_name.get(".text").unwrap();
    let rodata_section = section_headers_by_name.get(".rodata").unwrap();
    // let data_section = section_headers_by_name.get(".data").unwrap();
    // let bss_section = section_headers_by_name.get(".bss").unwrap();
    println!("text_section: {:?}", text_section);
    println!("rodata_section: {:?}", rodata_section);
    // println!("data_section: {:?}", data_section);
    // println!("bss_section: {:?}", bss_section);
    println!("section headers: {:?}", section_headers_by_name);

    // let executable_program_headers =
    //     segments.iter().filter(|x| (x.p_flags & elf::abi::PF_X) != 0).collect::<Vec<_>>();

    // Denote `.text` as the executable code segment subject to preprocessing.
    let mut text_region: Option<(usize, usize)> = None;

    // Denote `.rodata` as the read-only data segment.
    let mut rodata_region: Option<(usize, usize)> = None;

    let mut rw_regions: Option<(usize, usize)> = None;

    let mut prev_program_header: Option<ProgramHeader> = None;
    for segment in segments.iter().filter(|x| x.p_type == elf::abi::PT_LOAD) {
        if let Some(prev) = prev_program_header {
            assert!(prev.p_vaddr <= segment.p_vaddr);
        }

        let file_size: u32 = segment
            .p_filesz
            .try_into()
            .map_err(|err| anyhow!("filesize was larger than 32 bits. {err}"))?;
        if file_size >= max_mem {
            bail!("Invalid segment file_size");
        }
        let mem_size: u32 = segment
            .p_memsz
            .try_into()
            .map_err(|err| anyhow!("mem_size was larger than 32 bits {err}"))?;
        if mem_size >= max_mem {
            bail!("Invalid segment mem_size");
        }
        let vaddr: u32 = segment
            .p_vaddr
            .try_into()
            .map_err(|err| anyhow!("vaddr is larger than 32 bits. {err}"))?;
        if vaddr % WORD_SIZE as u32 != 0 {
            bail!("vaddr {vaddr:08x} is unaligned");
        }
        let offset: u32 = segment
            .p_offset
            .try_into()
            .map_err(|err| anyhow!("offset is larger than 32 bits. {err}"))?;

        for i in (0..mem_size).step_by(WORD_SIZE) {
            let addr = vaddr.checked_add(i).context("Invalid segment vaddr")?;
            if addr >= max_mem {
                bail!("Address [0x{addr:08x}] exceeds maximum address for guest programs [0x{max_mem:08x}]");
            }
            if i >= file_size {
                // Past the file size, all zeros.
                let prev = image.insert(addr, 0);
                assert!(prev.is_none(), "Overwriting memory: {}", prev.unwrap());
            } else {
                let mut word = 0;
                // Don't read past the end of the file.
                let len = core::cmp::min(file_size - i, WORD_SIZE as u32);
                for j in 0..len {
                    let offset = (offset + i + j) as usize;
                    let byte = input.get(offset).context("Invalid segment offset")?;
                    word |= (*byte as u32) << (j * 8);
                }
                let prev = image.insert(addr, word);
                assert!(prev.is_none(), "Overwriting memory: {}", prev.unwrap());
            }
        }

        let p_flags = segment.p_flags;
        let is_executable = (p_flags & elf::abi::PF_X) != 0;
        let is_writable = (p_flags & elf::abi::PF_W) != 0;
        let is_readable = (p_flags & elf::abi::PF_R) != 0;
        let is_read_only = p_flags == elf::abi::PF_R;

        info!(
            vaddr,
            mem_size,
            vrange = ?(vaddr..vaddr + mem_size),
            is_executable,
            is_writable,
            is_read_only,
            "SEGMENT: {:?}",
            (
                segment.p_type,
                segment.p_align,
            )
        );

        if is_executable && is_readable && !is_writable {
            assert!(text_region.is_none());
            text_region = Some((vaddr as usize, mem_size as usize));
        }

        if is_read_only {
            assert!(rodata_region.is_none());
            rodata_region = Some((vaddr as usize, mem_size as usize));
        }

        if !is_executable && is_writable && is_readable {
            assert!(rw_regions.is_none());
            rw_regions = Some((vaddr as usize, mem_size as usize));
        }

        if vaddr == /*TEXT_START*/ 0x0 {
            // assert_eq!((segment.p_flags & elf::abi::PF_X) as u8, 1);
            // assert!(text_segment.is_none());
            text_segment = Some((vaddr, mem_size));
        }

        prev_program_header = Some(segment);
    }
    let (text_start, text_size) = text_segment.unwrap();

    let mut program = BTreeMap::new();
    for (&addr, &word) in image.range(text_start..text_start + text_size) {
        // debug!(addr = format!("{:#04x}", addr), word, addr, ?TEXT_REGION);
        debug!(ix = instruction_name(word), "ix");
        let prev = program.insert(addr, word);
        assert!(prev.is_none());
    }
    Ok(MemoryImage {
        entry,
        image,
        text_region: text_region.expect("no text region"),
        rodata_region: text_region.expect("no rodata region"),
        rw_region: rw_regions.expect("no rw region"),
    })
}

#[cfg(test)]
pub mod tests {
    use tracing::level_filters::LevelFilter;
    use tracing_forest::ForestLayer;
    use tracing_subscriber::layer::SubscriberExt;
    use tracing_subscriber::util::SubscriberInitExt;
    use tracing_subscriber::{EnvFilter, Registry};

    // #[test]
    // fn test_read() -> anyhow::Result<()> {
    //     init_test_logger();
    //
    //     let input = include_bytes!("/Users/andrewtian/p/_l2btc/din/consensus-core/target/riscv32im-unknown-none-elf/release/example");
    //     let program = load_elf(input, 0x0C00_0000)?;
    //
    //     Ok(())
    // }

    fn init_test_logger() {
        let env_filter = EnvFilter::builder()
            .with_default_directive(LevelFilter::DEBUG.into())
            .from_env_lossy();

        Registry::default()
            .with(env_filter)
            .with(tracing_subscriber::fmt::layer())
            .with(ForestLayer::default())
            .init();
    }
}
