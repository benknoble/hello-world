use std::fs::File;
use std::io::prelude::*;
use std::io;
use memchr::*;

fn main() -> io::Result<()> {
    let fname = std::env::args().nth(1).unwrap();
    let mut in_ = io::BufReader::new(File::open(fname)?);
    let out = io::stdout().lock();
    let mut out = io::BufWriter::new(out);

    let mut start: Vec<u8> = Vec::new();
    // while let Ok(& ref buf) = &mut in_.fill_buf() { // -> buf: &[u8]
    // while let Ok(buf) = &mut in_.fill_buf() { // -> buf: &mut &[u8]
    while let Ok(buf) = (&mut in_).fill_buf() { // -> buf: &[u8]
        let len = buf.len();
        if buf.is_empty() { break; }
        // dbg!(String::from_utf8(buf.to_vec()).unwrap());
        // dbg!(memchr_iter(b'\n', buf).collect::<Vec<usize>>());
        let mut pos = 0;
        for idx in memchr_iter(b'\n', buf) {
            // dbg!(pos, idx);
            // FIXME: might not write the whole buffer
            out.write(start.as_slice())?;
            out.write(&buf[pos..=idx])?;
            start.clear();
            pos = idx + 1;
        }
        start.extend_from_slice(&buf[pos..len]);
        in_.consume(len);
    }

    Ok(())
}
