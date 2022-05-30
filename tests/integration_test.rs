extern crate rand;
extern crate bam;

use std::fs::File;
use std::process::Command;
use std::time::Instant;
use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};

use rand::Rng;
use glob::glob;

use bam::{RecordReader, RecordWriter};

fn compare_sam_files<P: AsRef<Path>, T: AsRef<Path>, W: Write>(filename1: P, filename2: T, log: &mut W) {
    let filename1 = filename1.as_ref();
    let filename2 = filename2.as_ref();
    let mut file1 = BufReader::new(File::open(&filename1).unwrap());
    let mut file2 = BufReader::new(File::open(&filename2).unwrap());
    let mut line1 = String::new();
    let mut line2 = String::new();

    for i in 1_usize.. {
        line1.clear();
        line2.clear();
        match (file1.read_line(&mut line1), file2.read_line(&mut line2)) {
            (Ok(x), Ok(y)) => {
                if x == 0 && y != 0 {
                    writeln!(log, "Comparing files {} and {}", filename1.display(), filename2.display()).unwrap();
                    writeln!(log, "Samtools output: {}", line2.trim()).unwrap();
                    writeln!(log, "Samtools output is longer").unwrap();
                    panic!("Samtools output is longer");
                } else if x != 0 && y == 0 {
                    writeln!(log, "Comparing files {} and {}", filename1.display(), filename2.display()).unwrap();
                    writeln!(log, "Crate output:    {}", line1.trim()).unwrap();
                    writeln!(log, "Crate output is longer").unwrap();
                    panic!("Crate output is longer");
                } else if x == 0 && y == 0 {
                    break;
                }
            },
            (Ok(_), Err(e)) => panic!("Could not read samtools output: {:?}", e),
            (Err(e), Ok(_)) => panic!("Could not read crate output: {:?}", e),
            (Err(e1), Err(e2)) => panic!("Could not read both outputs: {:?}, {:?}", e1, e2),
        }
        if line1 != line2 {
            writeln!(log, "Comparing files {} and {}", filename1.display(), filename2.display()).unwrap();
            writeln!(log, "Crate output:    {}", line1.trim()).unwrap();
            writeln!(log, "Samtools output: {}", line2.trim()).unwrap();
            writeln!(log, "Outputs do not match on line {}", i).unwrap();
            panic!("Outputs do not match on line {}", i);
        }
    }
}

fn test_indexed_reader<W: Write>(path: &str, additional_threads: u16, log: &mut W) {
    let mut reader = bam::IndexedReader::build()
        .additional_threads(additional_threads)
        .from_path(path).unwrap();
    let header = reader.header().clone();

    const ITERATIONS: usize = 100;
    let mut rng = rand::thread_rng();
    let mut record = bam::Record::new();

    let output1 = format!("tests/data/tmp/bamcrate.ind_reader_t{}.sam", additional_threads);
    let output2 = format!("tests/data/tmp/samtools.ind_reader_t{}.sam", additional_threads);
    let mut non_empty = 0;
    for i in 0..10 * ITERATIONS {
        if non_empty == ITERATIONS {
            break;
        }
        let ref_id = rng.gen_range(0, header.n_references());
        let length = header.reference_len(ref_id as u32).unwrap();
        let start = rng.gen_range(0, length);
        let end = rng.gen_range(start + 1, length + 1);

        let mut count = 0;
        let ref_name = header.reference_name(ref_id as u32).unwrap();
        writeln!(log, "    Iteration {}", i).unwrap();
        writeln!(log, "    Fetching {}:{}-{}", ref_name, start + 1, end).unwrap();

        let timer = Instant::now();
        let mut sam_writer = bam::SamWriter::from_path(&output1, header.clone()).unwrap();
        let mut viewer = reader.fetch(&bam::Region::new(ref_id as u32, start, end)).unwrap();
        loop {
            match viewer.read_into(&mut record) {
                Ok(true) => {},
                Ok(false) => break,
                Err(e) => panic!("{}", e),
            }
            count += 1;
            sam_writer.write(&record).unwrap();
        }
        sam_writer.finish().unwrap();
        writeln!(log, "        bam::IndexedReader: {:?}", timer.elapsed()).unwrap();

        let timer = Instant::now();
        let mut child = Command::new("samtools")
            .args(&["view", "-h"])
            .arg(path)
            .arg(format!("{}:{}-{}", ref_name, start + 1, end))
            .args(&["-o", &output2])
            .spawn()
            .expect("Failed to run samtools view");
        let ecode = child.wait().expect("Failed to wait on samtools view");
        assert!(ecode.success());
        writeln!(log, "        samtools view:      {:?}", timer.elapsed()).unwrap();
        writeln!(log, "        total {} records", count).unwrap();
        compare_sam_files(&output1, &output2, log);
        if count > 0 {
            non_empty += 1;
        }
    }
}

fn test_bam_reader<W: Write>(path: &str, additional_threads: u16, log: &mut W) {
    let mut reader = bam::BamReader::from_path(path, additional_threads).unwrap();

    let mut record = bam::Record::new();
    let mut count = 0;

    let output1 = format!("tests/data/tmp/bamcrate.bam_reader_t{}.sam", additional_threads);
    let output2 = format!("tests/data/tmp/samtools.bam_reader_t{}.sam", additional_threads);
    let timer = Instant::now();
    let mut sam_writer = bam::SamWriter::from_path(&output1, reader.header().clone()).unwrap();
    loop {
        match reader.read_into(&mut record) {
            Ok(true) => {},
            Ok(false) => break,
            Err(e) => panic!("{}", e),
        }
        count += 1;
        sam_writer.write(&record).unwrap();
    }
    sam_writer.finish().unwrap();
    writeln!(log, "        bam::BamReader: {:?}", timer.elapsed()).unwrap();

    let timer = Instant::now();
    let mut child = Command::new("samtools")
        .args(&["view", "-h"])
        .arg(path)
        .args(&["-o", &output2])
        .spawn()
        .expect("Failed to run samtools view");
    let ecode = child.wait().expect("Failed to wait on samtools view");
    assert!(ecode.success());
    writeln!(log, "        samtools view:  {:?}", timer.elapsed()).unwrap();
    writeln!(log, "        total {} records", count).unwrap();
    compare_sam_files(&output1, &output2, log);
}

fn test_bam_to_bam<W: Write>(path: &str, additional_threads: u16, log: &mut W) {
    let mut reader = bam::BamReader::from_path(path, additional_threads).unwrap();
    let mut record = bam::Record::new();
    let mut count = 0;

    let bam_output = format!("tests/data/tmp/bamcrate.bam_to_bam_t{}.bam", additional_threads);
    let output1 = format!("tests/data/tmp/bamcrate.bam_to_bam_t{}.sam", additional_threads);
    let output2 = format!("tests/data/tmp/samtools.bam_to_bam_t{}.sam", additional_threads);
    let timer = Instant::now();
    let mut bam_writer = bam::BamWriter::build()
        .additional_threads(additional_threads)
        .from_path(&bam_output, reader.header().clone())
        .unwrap();
    loop {
        match reader.read_into(&mut record) {
            Ok(true) => {},
            Ok(false) => break,
            Err(e) => panic!("{}", e),
        }
        count += 1;
        bam_writer.write(&record).unwrap();
    }
    bam_writer.finish().unwrap();
    writeln!(log, "        bam::BamWriter: {:?}", timer.elapsed()).unwrap();

    let timer = Instant::now();
    let mut child = Command::new("samtools")
        .args(&["view", "-h"])
        .arg(&path)
        .args(&["-o", &output2])
        .spawn()
        .expect("Failed to run samtools view");
    let ecode = child.wait().expect("Failed to wait on samtools view");
    assert!(ecode.success());
    writeln!(log, "        samtools view:  {:?}", timer.elapsed()).unwrap();
    writeln!(log, "        total {} records", count).unwrap();

    let mut child = Command::new("samtools")
        .args(&["view", "-h"])
        .arg(&bam_output)
        .args(&["-o", &output1])
        .spawn()
        .expect("Failed to run samtools view");
    let ecode = child.wait().expect("Failed to wait on samtools view");
    assert!(ecode.success());

    compare_sam_files(&output1, &output2, log);
}

fn test_bam_to_bam_pause<W: Write>(path: &str, additional_threads: u16, log: &mut W) {
    assert!(additional_threads > 0);
    let mut reader = bam::BamReader::from_path(path, additional_threads).unwrap();
    let mut record = bam::Record::new();
    let mut count = 0;

    let bam_output = format!("tests/data/tmp/bamcrate.bam_to_bam_pause_t{}.bam", additional_threads);
    let output1 = format!("tests/data/tmp/bamcrate.bam_to_bam_pause_t{}.sam", additional_threads);
    let output2 = format!("tests/data/tmp/samtools.bam_to_bam_pause_t{}.sam", additional_threads);
    let timer = Instant::now();
    let mut bam_writer = bam::BamWriter::build()
        .additional_threads(additional_threads)
        .from_path(&bam_output, reader.header().clone())
        .unwrap();
    for i in 1.. {
        match reader.read_into(&mut record) {
            Ok(true) => {},
            Ok(false) => break,
            Err(e) => panic!("{}", e),
        }
        count += 1;
        bam_writer.write(&record).unwrap();
        if i % 10000 == 0 {
            reader.pause();
            bam_writer.pause();
            std::thread::sleep(std::time::Duration::from_secs(1));
        }
    }
    bam_writer.finish().unwrap();
    writeln!(log, "        bam::BamWriter: {:?}", timer.elapsed()).unwrap();

    let timer = Instant::now();
    let mut child = Command::new("samtools")
        .args(&["view", "-h"])
        .arg(&path)
        .args(&["-o", &output2])
        .spawn()
        .expect("Failed to run samtools view");
    let ecode = child.wait().expect("Failed to wait on samtools view");
    assert!(ecode.success());
    writeln!(log, "        samtools view:  {:?}", timer.elapsed()).unwrap();
    writeln!(log, "        total {} records", count).unwrap();

    let mut child = Command::new("samtools")
        .args(&["view", "-h"])
        .arg(&bam_output)
        .args(&["-o", &output1])
        .spawn()
        .expect("Failed to run samtools view");
    let ecode = child.wait().expect("Failed to wait on samtools view");
    assert!(ecode.success());

    compare_sam_files(&output1, &output2, log);
}

fn test_ind_bam_to_bam<W: Write>(path: &str, additional_threads: u16, log: &mut W) {
    let mut reader = bam::IndexedReader::build()
        .additional_threads(additional_threads)
        .from_path(path).unwrap();
    let header = reader.header().clone();

    const ITERATIONS: usize = 100;
    let mut rng = rand::thread_rng();
    let mut record = bam::Record::new();

    let bam_output = format!("tests/data/tmp/bamcrate.ind_bam_to_bam_t{}.bam", additional_threads);
    let output1 = format!("tests/data/tmp/bamcrate.ind_bam_to_bam_t{}.sam", additional_threads);
    let output2 = format!("tests/data/tmp/samtools.ind_bam_to_bam_t{}.sam", additional_threads);
    let mut non_empty = 0;
    for i in 0..10 * ITERATIONS {
        if non_empty == ITERATIONS {
            break;
        }
        let ref_id = rng.gen_range(0, header.n_references());
        let length = header.reference_len(ref_id as u32).unwrap();
        let start = rng.gen_range(0, length);
        let end = rng.gen_range(start + 1, length + 1);

        let mut count = 0;
        let ref_name = header.reference_name(ref_id as u32).unwrap();
        writeln!(log, "    Iteration {}", i).unwrap();
        writeln!(log, "    Fetching {}:{}-{}", ref_name, start + 1, end).unwrap();

        let timer = Instant::now();
        let mut bam_writer = bam::BamWriter::build()
            .additional_threads(additional_threads)
            .from_path(&bam_output, reader.header().clone())
            .unwrap();
        let mut viewer = reader.fetch(&bam::Region::new(ref_id as u32, start, end)).unwrap();
        loop {
            match viewer.read_into(&mut record) {
                Ok(true) => {},
                Ok(false) => break,
                Err(e) => panic!("{}", e),
            }
            count += 1;
            bam_writer.write(&record).unwrap();
        }
        bam_writer.finish().unwrap();
        writeln!(log, "        bam::IndexedReader: {:?}", timer.elapsed()).unwrap();

        let timer = Instant::now();
        let mut child = Command::new("samtools")
            .args(&["view", "-h"])
            .arg(&path)
            .arg(format!("{}:{}-{}", ref_name, start + 1, end))
            .args(&["-o", &output2])
            .spawn()
            .expect("Failed to run samtools view");
        let ecode = child.wait().expect("Failed to wait on samtools view");
        assert!(ecode.success());
        writeln!(log, "        samtools view:  {:?}", timer.elapsed()).unwrap();
        writeln!(log, "        total {} records", count).unwrap();

        let mut child = Command::new("samtools")
        .args(&["view", "-h"])
        .arg(&bam_output)
        .args(&["-o", &output1])
        .spawn()
        .expect("Failed to run samtools view");
        let ecode = child.wait().expect("Failed to wait on samtools view");
        assert!(ecode.success());

        compare_sam_files(&output1, &output2, log);
        if count > 0 {
            non_empty += 1;
        }
    }
}

fn test_sam_to_bam<W: Write>(path: &str, log: &mut W) {
    let mut reader = bam::SamReader::from_path(path).unwrap();
    let mut record = bam::Record::new();
    let mut count = 0;

    let bam_output = format!("tests/data/tmp/bamcrate.sam_to_bam.bam");
    let output1 = format!("tests/data/tmp/bamcrate.sam_to_bam.sam");
    let timer = Instant::now();
    let mut bam_writer = bam::BamWriter::from_path(&bam_output, reader.header().clone()).unwrap();
    loop {
        match reader.read_into(&mut record) {
            Ok(true) => {},
            Ok(false) => break,
            Err(e) => panic!("{}", e),
        }
        count += 1;
        bam_writer.write(&record).unwrap();
    }
    bam_writer.finish().unwrap();
    writeln!(log, "        bam::BamWriter: {:?}", timer.elapsed()).unwrap();

    let timer = Instant::now();
    let mut child = Command::new("samtools")
        .args(&["view", "-h"])
        .arg(&bam_output)
        .args(&["-o", &output1])
        .spawn()
        .expect("Failed to run samtools view");
    let ecode = child.wait().expect("Failed to wait on samtools view");
    assert!(ecode.success());
    writeln!(log, "        samtools view:  {:?}", timer.elapsed()).unwrap();
    writeln!(log, "        total {} records", count).unwrap();

    compare_sam_files(&output1, &path, log);
}

fn sam_files() -> impl Iterator<Item = PathBuf> {
    glob("tests/data/*.sam").unwrap().map(glob::GlobResult::unwrap)
}

// Consecutive BAM reader: c_*.bam and b_*.bam
// Indexed BAM reader:     i_*.bam and b_*.bam

fn bam_files() -> impl Iterator<Item = PathBuf> {
    glob("tests/data/[cb]_*.bam").unwrap().map(glob::GlobResult::unwrap)
}

fn indexed_bam_files() -> impl Iterator<Item = PathBuf> {
    glob("tests/data/[ib]_*.bam").unwrap().map(glob::GlobResult::unwrap)
        .filter(|path| Path::new(&format!("{}.bai", path.display())).is_file())
}

#[test]
fn indexed_reader_singlethread() {
    let mut log = File::create("tests/data/log/indexed_reader_singlethread.log").unwrap();
    for entry in indexed_bam_files() {
        writeln!(log, "Analyzing {}", entry.display()).unwrap();
        let entry_str = entry.as_os_str().to_str().unwrap();
        test_indexed_reader(entry_str, 0, &mut log);
    }
}

#[test]
fn simple_bam_reader_singlethread() {
    let mut log = File::create("tests/data/log/simple_bam_reader_singlethread.log").unwrap();
    for entry in bam_files() {
        writeln!(log, "Analyzing {}", entry.display()).unwrap();
        let entry_str = entry.as_os_str().to_str().unwrap();
        test_bam_reader(entry_str, 0, &mut log);
    }
}

#[test]
fn simple_bam_to_bam_singlethread() {
    let mut log = File::create("tests/data/log/simple_bam_to_bam_singlethread.log").unwrap();
    for entry in bam_files() {
        writeln!(log, "Analyzing {}", entry.display()).unwrap();
        let entry_str = entry.as_os_str().to_str().unwrap();
        test_bam_to_bam(entry_str, 0, &mut log);
    }
}

#[test]
fn sam_to_bam() {
    let mut log = File::create("tests/data/log/sam_to_bam.log").unwrap();
    for entry in sam_files() {
        writeln!(log, "Analyzing {}", entry.display()).unwrap();
        let entry_str = entry.as_os_str().to_str().unwrap();
        test_sam_to_bam(entry_str, &mut log);
    }
}

#[test]
fn indexed_reader_multithread() {
    let mut log = File::create("tests/data/log/indexed_reader_multithread.log").unwrap();
    for entry in indexed_bam_files() {
        writeln!(log, "Analyzing {}", entry.display()).unwrap();
        let entry_str = entry.as_os_str().to_str().unwrap();
        test_indexed_reader(entry_str, 2, &mut log);
    }
}

#[test]
fn simple_bam_reader_multithread() {
    let mut log = File::create("tests/data/log/simple_bam_reader_multithread.log").unwrap();
    for entry in bam_files() {
        writeln!(log, "Analyzing {}", entry.display()).unwrap();
        let entry_str = entry.as_os_str().to_str().unwrap();
        test_bam_reader(entry_str, 2, &mut log);
    }
}

#[test]
fn simple_bam_to_bam_multithread() {
    let mut log = File::create("tests/data/log/simple_bam_to_bam_multithread.log").unwrap();
    for entry in bam_files() {
        writeln!(log, "Analyzing {}", entry.display()).unwrap();
        let entry_str = entry.as_os_str().to_str().unwrap();
        test_bam_to_bam(entry_str, 10, &mut log);
    }
}

#[test]
fn bam_to_bam_pause() {
    let mut log = File::create("tests/data/log/bam_to_bam_pause.log").unwrap();
    for entry in bam_files() {
        writeln!(log, "Analyzing {}", entry.display()).unwrap();
        let entry_str = entry.as_os_str().to_str().unwrap();
        test_bam_to_bam_pause(entry_str, 2, &mut log);
    }
}

#[test]
fn ind_bam_to_bam_singlethread() {
    let mut log = File::create("tests/data/log/ind_bam_to_bam_singlethread.log").unwrap();
    for entry in indexed_bam_files() {
        writeln!(log, "Analyzing {}", entry.display()).unwrap();
        let entry_str = entry.as_os_str().to_str().unwrap();
        test_ind_bam_to_bam(entry_str, 0, &mut log);
    }
}

#[test]
fn ind_bam_to_bam_multithread() {
    let mut log = File::create("tests/data/log/ind_bam_to_bam_multithread.log").unwrap();
    for entry in indexed_bam_files() {
        writeln!(log, "Analyzing {}", entry.display()).unwrap();
        let entry_str = entry.as_os_str().to_str().unwrap();
        test_ind_bam_to_bam(entry_str, 2, &mut log);
    }
}
