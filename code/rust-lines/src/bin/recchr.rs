use std::fs::File;
use std::io;
use std::io::prelude::*;
use memchr::*;

fn main() -> io::Result<()> {
    let fname = std::env::args().nth(1).unwrap();
    let mut in_ = RecordSource::new(File::open(fname)?);
    let out = io::stdout().lock();
    let mut out = RecordSink::new(out);

    while let Some(line) = in_.next_line() {
        out.write_bytes(line);
    }
    out.flush_buffer();

    Ok(())
}

const BUFFER_SIZE: usize = 128 * 1024;

// --------------------------------------------------------------------------------------------
// RecordSource
// --------------------------------------------------------------------------------------------

// Read bytes from the input stream to the buffer. If there are
// unprocessed bytes, they are moved to the beginning of the buffer
// prior to reading from the stream.
struct RecordSource<R: Read> {
    reader: R,
    buffer: [u8; BUFFER_SIZE],
    begin: usize,
    length: usize,
    num_available: usize,
    is_eof: bool,
}

impl<R: Read> RecordSource<R> {
    fn new(reader: R) -> Self {
        Self {
            reader,
            buffer: [0; BUFFER_SIZE],
            begin: 0,
            length: 0,
            num_available: 0,
            is_eof: false,
        }
    }

    fn next_line(&mut self) -> Option<&[u8]> {
        // Fast path, a '\n' can be found w/o requiring a read

        let pos = memchr(b'\n', &self.buffer[self.begin..(self.begin + self.num_available)]);

        if let Some(pos) = pos {
            let line = &self.buffer[self.begin..=self.begin + pos];
            let consumed = pos + 1;
            self.begin += consumed;
            self.length = 0;
            self.num_available -= consumed;

            return Some(line);
        }

        // Slow path, fill the buffer, check for eof

        self.fill_buffer();

        if self.is_eof {
            return None;
        }

        let pos = memchr(b'\n', &self.buffer[self.begin..(self.begin + self.num_available)]);

        if let Some(pos) = pos {
            let line = &self.buffer[self.begin..=self.begin + pos];
            let consumed = pos + 1;
            self.begin += consumed;
            self.length = 0;
            self.num_available -= consumed;

            Some(line)
        } else {
            None
        }
    }

    fn fill_buffer(&mut self) {
        // The number of relevant bytes to move. length indicates the
        // in-progress line, and num_available indicates the unconsumed
        // portion of the buffer.
        let total = self.length + self.num_available;

        if self.begin > 0 {
            // Move existing bytes to beginning of buffer
            self.buffer.copy_within(self.begin..(self.begin + total), 0);
            self.begin = 0;
        }

        let count = self
            .reader
            .read(&mut self.buffer[total..BUFFER_SIZE - total])
            .expect("should work");
        self.num_available += count;

        if count == 0 {
            self.is_eof = true;
        }
    }
}

// --------------------------------------------------------------------------------------------
// RecordSink
// --------------------------------------------------------------------------------------------

struct RecordSink<W: Write> {
    writer: W,
    buffer: [u8; BUFFER_SIZE],
    length: usize,
}

impl<W: Write> RecordSink<W> {
    fn new(writer: W) -> Self {
        Self {
            writer,
            buffer: [0; BUFFER_SIZE],
            length: 0,
        }
    }

    fn flush_buffer(&mut self) {
        if self.length > 0 {
            // FIXME: might not write the whole buffer
            self.writer
                .write(&self.buffer[0..self.length])
                .expect("should work");
            self.length = 0;
        }
    }

    fn write_bytes(&mut self, bytes: &[u8]) {
        let len = bytes.len();

        if self.length + len + 1 > BUFFER_SIZE {
            self.flush_buffer();
        }

        self.buffer[self.length..self.length + len].clone_from_slice(bytes);
        self.length += len;
    }
}
