use std::fs::File;
use std::io::prelude::*;
use std::io;

fn main() -> io::Result<()> {
    let fname = std::env::args().nth(1).unwrap();
    let in_ = io::BufReader::new(File::open(fname)?);
    let out = io::stdout().lock();
    let mut out = io::BufWriter::new(out);

    for line in in_.split(b'\n') {
        // FIXME: might not write the whole buffer
        out.write(&line?)?;
        out.write(&[b'\n'])?;
    }

    Ok(())
}
