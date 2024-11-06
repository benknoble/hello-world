# Benchmarking Rust code to read a large file and process each line

These benchmarks represent roughly the IO costs of reading the lines of a file;
they do almost no work with said lines before dumping them back out. That makes
them a good baseline indicator for transformative programs that still need to
output some version of every line (even if they collect and output other data
along the way).

## Results

```
λ hyperfine -N --warmup=5 --output=null 'target/release/bufchr ../gig-input.txt' 'target/release/bufsplit ../gig-input.txt' 'target/release/record ../gig-input.txt' 'target/release/recchr ../gig-input.txt'
Benchmark 1: target/release/bufchr ../gig-input.txt
  Time (mean ± σ):      2.551 s ±  0.014 s    [User: 1.036 s, System: 1.512 s]
  Range (min … max):    2.531 s …  2.578 s    10 runs

Benchmark 2: target/release/bufsplit ../gig-input.txt
  Time (mean ± σ):      5.964 s ±  0.023 s    [User: 4.601 s, System: 1.358 s]
  Range (min … max):    5.941 s …  6.008 s    10 runs

Benchmark 3: target/release/record ../gig-input.txt
  Time (mean ± σ):      3.700 s ±  0.033 s    [User: 2.785 s, System: 0.911 s]
  Range (min … max):    3.649 s …  3.771 s    10 runs

Benchmark 4: target/release/recchr ../gig-input.txt
  Time (mean ± σ):      1.411 s ±  0.010 s    [User: 0.488 s, System: 0.921 s]
  Range (min … max):    1.402 s …  1.428 s    10 runs

Summary
  target/release/recchr ../gig-input.txt ran
    1.81 ± 0.02 times faster than target/release/bufchr ../gig-input.txt
    2.62 ± 0.03 times faster than target/release/record ../gig-input.txt
    4.23 ± 0.03 times faster than target/release/bufsplit ../gig-input.txt
```

On my machine, that means the average time of the fastest program corresponds to
an IO rate of ~3.86 GiB/sec.

All programs slower as expected when using `--output=pipe`. In that mode,
recchr reports the following timing:

```
Benchmark 1: target/release/recchr ../gig-input.txt
  Time (mean ± σ):      3.346 s ±  0.043 s    [User: 0.585 s, System: 2.427 s]
  Range (min … max):    3.291 s …  3.401 s    10 runs
```

or about 1.6 GiB/sec.

Similarly, bufchr reports:

```
Benchmark 1: target/release/bufchr ../gig-input.txt
  Time (mean ± σ):      3.656 s ±  0.054 s    [User: 1.172 s, System: 2.423 s]
  Range (min … max):    3.589 s …  3.759 s    10 runs
```

or about 1.48 GiB/sec.

When actually writing to a file with `--output=<file>`:

```
hyperfine -N --warmup=5 --output=./output 'target/release/bufchr ../gig-input.txt' 'target/release/bufsplit ../gig-input.txt' 'target/release/record ../gig-input.txt' 'target/release/recchr ../gig-input.txt'
Benchmark 1: target/release/bufchr ../gig-input.txt
  Time (mean ± σ):      9.998 s ±  0.255 s    [User: 1.280 s, System: 8.062 s]
  Range (min … max):    9.546 s … 10.463 s    10 runs

Benchmark 2: target/release/bufsplit ../gig-input.txt
  Time (mean ± σ):     11.609 s ±  0.374 s    [User: 5.136 s, System: 5.916 s]
  Range (min … max):   11.088 s … 12.409 s    10 runs

Benchmark 3: target/release/record ../gig-input.txt
  Time (mean ± σ):      7.758 s ±  0.688 s    [User: 3.368 s, System: 2.679 s]
  Range (min … max):    6.784 s …  8.936 s    10 runs

Benchmark 4: target/release/recchr ../gig-input.txt
  Time (mean ± σ):      6.525 s ±  0.606 s    [User: 0.694 s, System: 3.072 s]
  Range (min … max):    5.720 s …  7.463 s    10 runs

Summary
  target/release/recchr ../gig-input.txt ran
    1.19 ± 0.15 times faster than target/release/record ../gig-input.txt
    1.53 ± 0.15 times faster than target/release/bufchr ../gig-input.txt
    1.78 ± 0.17 times faster than target/release/bufsplit ../gig-input.txt
```

That's a significant slow down (0.83 GiB/sec for the average time of the fastest
program). It appears that waiting on file _output_ creates a significant block
for program…

Machine specs:
- OS: macOS 12.7.6 21H1320 x86_64
- Host: MacBookPro11,5
- Kernel: 21.6.0
- CPU: Intel i7-4870HQ (8) @ 2.50GHz
- GPU: Intel Iris Pro, AMD Radeon R9 M370X
- Memory: 16384MiB
- rustc 1.82.0 (f6e511eec 2024-10-15)

Input specs:
- 5.4 GiB (11378288 blocks)
- 20200000 lines of ASCII text (19:1 ratio of lines exactly 300 characters long
  to lines exactly 48 characters long)

## Programs

Sequential processing:

- bufsplit: stdlib buffered IO readers and writers, with `.split()` to find
  lines
- record: buffered IO from [Brian Adkins](https://github.com/lojic)
- bufchr: bufsplit, but with memchr to find lines
- recchr: record, but with memchr to find lines

The record and memchr variants trade speed for code complexity. The bufchr
program is significantly shorter than any of the record variants while still
being useable on files of this size.

While we know the inputs are made of fixed width records, we actively choose to
ignore that fact when parsing lines out of the file.
