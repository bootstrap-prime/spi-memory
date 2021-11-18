//! Driver for 25-series SPI Flash and EEPROM chips.

use crate::{utils::HexSlice, BlockDevice, Error, Read};
use bitflags::bitflags;
use core::convert::TryInto;
use core::fmt;
use embedded_hal::blocking::delay::DelayUs;
use embedded_hal::blocking::spi::Transfer;
use embedded_hal::blocking::spi::Write;
use embedded_hal::digital::v2::OutputPin;

/// 3-Byte JEDEC manufacturer and device identification.
pub struct Identification {
    /// Data collected
    /// - First byte is the manufacturer's ID code from eg JEDEC Publication No. 106AJ
    /// - The trailing bytes are a manufacturer-specific device ID.
    bytes: [u8; 3],

    /// The number of continuations that precede the main manufacturer ID
    continuations: u8,
}

impl Identification {
    /// Build an Identification from JEDEC ID bytes.
    pub fn from_jedec_id(buf: &[u8]) -> Identification {
        // Example response for Cypress part FM25V02A:
        // 7F 7F 7F 7F 7F 7F C2 22 08  (9 bytes)
        // 0x7F is a "continuation code", not part of the core manufacturer ID
        // 0xC2 is the company identifier for Cypress (Ramtron)

        // Find the end of the continuation bytes (0x7F)
        let mut start_idx = 0;
        for i in 0..(buf.len() - 2) {
            if buf[i] != 0x7F {
                start_idx = i;
                break;
            }
        }

        Self {
            bytes: [buf[start_idx], buf[start_idx + 1], buf[start_idx + 2]],
            continuations: start_idx as u8,
        }
    }

    /// The JEDEC manufacturer code for this chip.
    pub fn mfr_code(&self) -> u8 {
        self.bytes[0]
    }

    /// The manufacturer-specific device ID for this chip.
    pub fn device_id(&self) -> &[u8] {
        self.bytes[1..].as_ref()
    }

    /// Number of continuation codes in this chip ID.
    ///
    /// For example the ARM Ltd identifier is `7F 7F 7F 7F 3B` (5 bytes), so
    /// the continuation count is 4.
    pub fn continuation_count(&self) -> u8 {
        self.continuations
    }
}

impl defmt::Format for Identification {
    fn format(&self, f: defmt::Formatter<'_>) {
        defmt::write!(
            f,
            "Identification {}",
            &HexSlice(self.bytes)
        )
    }
}

impl fmt::Debug for Identification {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Identification")
            .field(&HexSlice(self.bytes))
            .finish()
    }
}

#[allow(unused)] // TODO support more features
enum Opcode {
    /// Read the 8-bit legacy device ID.
    ReadDeviceId = 0xAB,
    /// Read the 8-bit manufacturer and device IDs.
    ReadMfDId = 0x90,
    /// Read 16-bit manufacturer ID and 8-bit device ID.
    ReadJedecId = 0x9F,
    /// Set the write enable latch.
    WriteEnable = 0x06,
    /// Clear the write enable latch.
    WriteDisable = 0x04,
    /// Read the 8-bit status register.
    ReadStatus = 0x05,
    /// Write the 8-bit status register. Not all bits are writeable.
    WriteStatus = 0x01,
    Read = 0x03,
    PageProg = 0x02, // directly writes to EEPROMs too
    SectorErase = 0x20,
    BlockErase = 0xD8,
    DeepPowerDown = 0xB9,
    ChipErase = 0xC7,
}

bitflags! {
    /// Status register bits.
    #[derive(defmt::Format)]
    pub struct Status: u8 {
        /// Erase or write in progress.
        const BUSY = 1 << 0;
        /// Status of the **W**rite **E**nable **L**atch.
        const WEL = 1 << 1;
        /// The 3 protection region bits.
        const PROT = 0b00011100;
        /// **S**tatus **R**egister **W**rite **D**isable bit.
        const SRWD = 1 << 7;
    }
}

/// Driver for 25-series SPI Flash chips.
///
/// # Type Parameters
///
/// * **`SPI`**: The SPI master to which the flash chip is attached.
/// * **`CS`**: The **C**hip-**S**elect line attached to the `\CS`/`\CE` pin of
///   the flash chip.
#[derive(Debug, defmt::Format)]
pub struct Flash<SPI, CS: OutputPin> {
    spi: SPI,
    cs: CS,
}

impl<SPI: Transfer<u8>, CS: OutputPin> Flash<SPI, CS> {
    /// Creates a new 25-series flash driver.
    ///
    /// # Parameters
    ///
    /// * **`spi`**: An SPI master. Must be configured to operate in the correct
    ///   mode for the device.
    /// * **`cs`**: The **C**hip-**S**elect Pin connected to the `\CS`/`\CE` pin
    ///   of the flash chip. Will be driven low when accessing the device.
    pub fn init(spi: SPI, cs: CS) -> Result<Self, Error<SPI::Error, CS>> {
        let mut this = Self { spi, cs };
        let status = this.read_status()?;
        info!("Flash::init: status = {:?}", status);

        // Here we don't expect any writes to be in progress, and the latch must
        // also be deasserted.
        if !(status & (Status::BUSY | Status::WEL)).is_empty() {
            return Err(Error::UnexpectedStatus);
        }

        Ok(this)
    }

    fn command(&mut self, bytes: &mut [u8]) -> Result<(), Error<SPI::Error, CS>> {
        // If the SPI transfer fails, make sure to disable CS anyways
        self.cs.set_low().map_err(Error::Gpio)?;
        let spi_result = self.spi.transfer(bytes).map_err(Error::Spi);
        self.cs.set_high().map_err(Error::Gpio)?;
        spi_result?;
        Ok(())
    }

    /// Reads the JEDEC manufacturer/device identification.
    pub fn read_jedec_id(&mut self) -> Result<Identification, Error<SPI::Error, CS>> {
        // Optimistically read 12 bytes, even though some identifiers will be shorter
        let mut buf: [u8; 12] = [0; 12];
        buf[0] = Opcode::ReadJedecId as u8;
        self.command(&mut buf)?;

        // Skip buf[0] (SPI read response byte)
        Ok(Identification::from_jedec_id(&buf[1..]))
    }

    /// Reads the status register.
    pub fn read_status(&mut self) -> Result<Status, Error<SPI::Error, CS>> {
        let mut buf = [Opcode::ReadStatus as u8, 0];
        self.command(&mut buf)?;

        Ok(Status::from_bits_truncate(buf[1]))
    }

    pub fn deep_power_down<D: DelayUs<u8>>(
        &mut self,
        timer: Option<&mut D>,
    ) -> Result<(), Error<SPI::Error, CS>> {
        let mut buf = [Opcode::DeepPowerDown as u8];
        self.command(&mut buf)?;

        if let Some(timer) = timer {
            // Wait for low power mode to be entered
            timer.delay_us(10);
        }

        Ok(())
    }

    pub fn wake_up<D: DelayUs<u8>>(&mut self, timer: &mut D) -> Result<(), Error<SPI::Error, CS>> {
        // Wait minimum time required to be in low power mode before waking up again (t_DPDD)
        timer.delay_us(30);
        // Pull CS down for at least t_CRCP (20ns)
        self.cs.set_low().map_err(Error::Gpio)?;
        timer.delay_us(1);
        self.cs.set_high().map_err(Error::Gpio)?;
        // Wait for the recovery time
        timer.delay_us(35);

        Ok(())
    }

    fn write_enable(&mut self) -> Result<(), Error<SPI::Error, CS>> {
        let mut cmd_buf = [Opcode::WriteEnable as u8];
        self.command(&mut cmd_buf)?;
        Ok(())
    }

    fn wait_done(&mut self) -> Result<(), Error<SPI::Error, CS>> {
        // TODO: Consider changing this to a delay based pattern
        while self.read_status()?.contains(Status::BUSY) {}
        Ok(())
    }
}

impl<SPI: Transfer<u8>, CS: OutputPin> Read<u32, SPI, CS> for Flash<SPI, CS> {
    /// Reads flash contents into `buf`, starting at `addr`.
    ///
    /// Note that `addr` is not fully decoded: Flash chips will typically only
    /// look at the lowest `N` bits needed to encode their size, which means
    /// that the contents are "mirrored" to addresses that are a multiple of the
    /// flash size. Only 24 bits of `addr` are transferred to the device in any
    /// case, limiting the maximum size of 25-series SPI flash chips to 16 MiB.
    ///
    /// # Parameters
    ///
    /// * `addr`: 24-bit address to start reading at.
    /// * `buf`: Destination buffer to fill.
    fn read(&mut self, addr: u32, buf: &mut [u8]) -> Result<(), Error<SPI::Error, CS>> {
        // TODO what happens if `buf` is empty?

        let mut cmd_buf = [
            Opcode::Read as u8,
            (addr >> 16) as u8,
            (addr >> 8) as u8,
            addr as u8,
        ];

        self.cs.set_low().map_err(Error::Gpio)?;
        let mut spi_result = self.spi.transfer(&mut cmd_buf);
        if spi_result.is_ok() {
            spi_result = self.spi.transfer(buf);
        }
        self.cs.set_high().map_err(Error::Gpio)?;
        spi_result.map(|_| ()).map_err(Error::Spi)
    }
}

impl<E, SPI: Transfer<u8, Error = E> + Write<u8, Error = E>, CS: OutputPin>
    BlockDevice<u32, SPI, CS> for Flash<SPI, CS>
{
    type SpiError = E;
    fn erase_sectors(&mut self, addr: u32, amount: usize) -> Result<(), Error<E, CS>> {
        for c in 0..amount {
            self.write_enable()?;

            let current_addr: u32 = (addr as usize + c * 256).try_into().unwrap();
            let mut cmd_buf = [
                Opcode::SectorErase as u8,
                (current_addr >> 16) as u8,
                (current_addr >> 8) as u8,
                current_addr as u8,
            ];
            self.command(&mut cmd_buf)?;
            self.wait_done()?;
        }

        Ok(())
    }

    fn write_bytes(&mut self, addr: u32, data: &[u8]) -> Result<(), Error<E, CS>> {
        for (c, chunk) in data.chunks(256).enumerate() {
            self.write_enable()?;

            let current_addr: u32 = (addr as usize + c * 256).try_into().unwrap();
            let mut cmd_buf = [
                Opcode::PageProg as u8,
                (current_addr >> 16) as u8,
                (current_addr >> 8) as u8,
                current_addr as u8,
            ];

            self.cs.set_low().map_err(Error::Gpio)?;
            let spi_result = self
                .spi
                .transfer(&mut cmd_buf)
                .and_then(|_| self.spi.write(chunk));

            self.cs.set_high().map_err(Error::Gpio)?;
            spi_result.map(|_| ()).map_err(Error::Spi)?;
            self.wait_done()?;
        }
        Ok(())
    }

    fn erase_all(&mut self) -> Result<(), Error<E, CS>> {
        self.write_enable()?;
        let mut cmd_buf = [Opcode::ChipErase as u8];
        self.command(&mut cmd_buf)?;
        self.wait_done()?;
        Ok(())
    }
}

#[cfg(feature = "littlefs-driver")]
pub struct SpiFlashFs<E, SPI, CS>
where
    SPI: Transfer<u8, Error = E> + Write<u8, Error = E>,
    CS: OutputPin
{
    backend: Flash<SPI, CS>,
}

#[cfg(feature = "littlefs-driver")]
impl<E, SPI, CS> SpiFlashFs<E, SPI, CS>
where
    SPI: Transfer<u8, Error = E> + Write<u8, Error = E>,
    CS: OutputPin
{
    pub fn new(storage: Flash<SPI, CS>) -> SpiFlashFs<E, SPI, CS> {
        SpiFlashFs {
            backend: storage
        }
    }
}

#[cfg(feature = "littlefs-driver")]
impl<E, CS> From<Error<E, CS>> for littlefs2::io::Error
where
    CS: OutputPin
{
    #[allow(unused_variables)]
    fn from(err: Error<E, CS>) -> Self {
        littlefs2::io::Error::Io
    }
}

#[cfg(feature = "littlefs-driver")]
impl<E, SPI, CS> littlefs2::driver::Storage for SpiFlashFs<E, SPI, CS>
where
    SPI: Transfer<u8, Error = E> + Write<u8, Error = E>,
    CS: OutputPin
{
    const READ_SIZE: usize = 16;
    const WRITE_SIZE: usize = 16;
    type CACHE_SIZE = littlefs2::consts::U16;
    const BLOCK_SIZE: usize = 4096;
    const BLOCK_COUNT: usize = 1776;
    const BLOCK_CYCLES: isize = 500;
    // this turns into a lookahead of 32
    // more than this gives buffer overflows
    type LOOKAHEADWORDS_SIZE = littlefs2::consts::U1;

    fn read(&mut self, offset: usize, buf: &mut [u8]) -> littlefs2::io::Result<usize> {
        let read_size: usize = Self::READ_SIZE;
        debug_assert!(offset % read_size == 0);
        debug_assert!(buf.len() % read_size == 0);
        self.backend.read(offset as u32, buf)?;
        Ok(buf.len())
    }

    fn write(&mut self, offset: usize, data: &[u8]) -> littlefs2::io::Result<usize> {
        let write_size: usize = Self::WRITE_SIZE;
        debug_assert!(offset % write_size == 0);
        debug_assert!(data.len() % write_size == 0);
        self.backend.write_bytes(offset as u32, data)?;
        Ok(data.len())
    }

    fn erase(&mut self, offset: usize, len: usize) -> littlefs2::io::Result<usize> {
        let block_size: usize = Self::BLOCK_SIZE;
        debug_assert!(offset % block_size == 0);
        debug_assert!(len % block_size == 0);
        self.backend.erase_sectors(offset as u32, len)?;
        Ok(len)
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_decode_jedec_id() {
        let cypress_id_bytes = [0x7F, 0x7F, 0x7F, 0x7F, 0x7F, 0x7F, 0xC2, 0x22, 0x08];
        let ident = Identification::from_jedec_id(&cypress_id_bytes);
        assert_eq!(0xC2, ident.mfr_code());
        assert_eq!(6, ident.continuation_count());
        let device_id = ident.device_id();
        assert_eq!(device_id[0], 0x22);
        assert_eq!(device_id[1], 0x08);
    }

    #[test]
    fn working_littlefs_numbers() {
        // you need to set RUST_MIN_STACK to a really big number to get this
        // test to pass.
        // RUST_MIN_STACK=8704000000 worked last time.
        use littlefs2::{fs::Filesystem, driver, io::{Error, Result}, consts};
        use littlefs2::ram_storage;

        println!("do I fail here?");

        ram_storage!(
            name=RamStorageForTestingMyThing,
            backend=YetAnotherRam,
            trait=driver::Storage,
            erase_value=0xff,
            read_size=16,
            write_size=16,
            cache_size_ty=consts::U16,
            block_size=4096,
            block_count=1776,
            lookaheadwords_size_ty=consts::U1,
            filename_max_plus_one_ty=consts::U256, // this doesn't do anything
            path_max_plus_one_ty=consts::U256, // this doesn't do anything
            result=Result,
        );

        let mut ram = YetAnotherRam::default();
        println!("do I fail here");
        let mut storage = RamStorageForTestingMyThing::new(&mut ram);
        println!("do I fail here?");

        let mut alloc = Filesystem::allocate();
        Filesystem::format(&mut storage).unwrap();
        // must allocate state statically before use
        let mut fs = Filesystem::mount(&mut alloc, &mut storage).unwrap();

    }
}
