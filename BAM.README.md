*bam* is a crate that allows to read and write BAM, SAM and BGZIP files, written completely in Rust.

## Why?

Having a crate written completely in Rust reduces the number of dependencies and compilation time.
Additionally, it removes the need to install additional C libraries.

Errors produced by this crate are more readable and easier to catch and fix on-the-fly.

## Overview

Currently, there are three readers and two writers:
* `bam::IndexedReader` - fetches records from
random genomic regions.
* `bam::BamReader` - reads a BAM file consecutively.
* `bam::SamReader` - reads a SAM file consecutively.
* `bam::BamWriter` - writes a BAM file.
* `bam::SamWriter` - writes a SAM file.

BAM readers and writers have single-thread and multi-thread modes.

You can construct pileups from all readers using `Pileup`.

You can use `bgzip` module to interact directly with bgzip files (BGZF).

The crate also allows to conviniently work with SAM/BAM `records`
and their fields, such as `CIGAR` or `tags`.

## Usage

The following code would load BAM file `in.bam` and its index `in.bam.bai`, take all records
from `3:600001-700000` and print them on the stdout.

```rust
extern crate bam;

use std::io;
use bam::RecordWriter;

fn main() {
    let mut reader = bam::IndexedReader::from_path("in.bam").unwrap();
    let output = io::BufWriter::new(io::stdout());
    let mut writer = bam::SamWriter::build()
        .write_header(false)
        .from_stream(output, reader.header().clone()).unwrap();

    for record in reader.fetch(&bam::Region::new(2, 600_000, 700_000)).unwrap() {
        let record = record.unwrap();
        writer.write(&record).unwrap();
    }
}
```

You can find more detailed usage [here](https://docs.rs/bam).

