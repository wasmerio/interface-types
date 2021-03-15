use std::io;
use std::io::Write;

/// A trait for converting a value to bytes.
pub trait ToBytes<W>
where
    W: Write,
{
    /// Converts the given value into `&[u8]` in the given `writer`.
    fn to_bytes(&self, writer: &mut W) -> io::Result<()>;
}

/// Encode a `u8` into a byte (well, it's already a byte!).
impl<W> ToBytes<W> for u8
where
    W: Write,
{
    fn to_bytes(&self, writer: &mut W) -> io::Result<()> {
        writer.write_all(&[*self])
    }
}

/// Encode a `u64` into bytes with a LEB128 representation.
///
/// Decoder is `decoders::binary::uleb`.
impl<W> ToBytes<W> for u64
where
    W: Write,
{
    fn to_bytes(&self, writer: &mut W) -> io::Result<()> {
        let mut value = *self;

        // Code adapted from the Rust' `serialize` library.
        loop {
            if value < 0x80 {
                writer.write_all(&[value as u8])?;

                break;
            }

            writer.write_all(&[((value & 0x7f) | 0x80) as u8])?;
            value >>= 7;
        }

        Ok(())
    }
}

/// Encode a `str` into bytes.
///
/// Decoder is `decoders::binary::string`.
impl<W> ToBytes<W> for &str
where
    W: Write,
{
    fn to_bytes(&self, writer: &mut W) -> io::Result<()> {
        // Size first.
        writer.write_all(&[self.len() as u8])?;

        // Then the string.
        writer.write_all(self.as_bytes())?;

        Ok(())
    }
}

/// Encode a String into bytes.
///
/// Decoder is `decoders::binary::string`.
impl<W> ToBytes<W> for String
where
    W: Write,
{
    fn to_bytes(&self, writer: &mut W) -> io::Result<()> {
        self.as_str().to_bytes(writer)
    }
}

/// Encode a vector into bytes.
///
/// Decoder is `decoders::binary::list`.
impl<W, I> ToBytes<W> for Vec<I>
where
    W: Write,
    I: ToBytes<W>,
{
    fn to_bytes(&self, writer: &mut W) -> io::Result<()> {
        // Size first.
        (self.len() as u64).to_bytes(writer)?;

        // Then the items.
        for item in self {
            item.to_bytes(writer)?;
        }

        Ok(())
    }
}
