use std::io::BufRead;

use crate::*;

pub fn convert<L: SynthLanguage>(params: ConvertParams) {
    let infile = std::fs::File::open(&params.cvc_log).expect("can't open file");
    let reader = std::io::BufReader::new(infile);

    let mut report = SlimReport {
        time: -1.0,
        eqs: vec![],
    };

    for line in reader.lines() {
        let line = line.unwrap();
        if line.contains("rewrite") {
            if let Some(eq) = L::convert_eq(&line) {
                report.eqs.push(eq);
            } else {
                eprintln!("Failed to make eq for {}", line);
            }
        } else if line.starts_with("real") {
            let s = line[4..].trim();
            report.time = s.parse().unwrap();
        };
    }

    let outfile = std::fs::File::create(&params.out).expect("can't open file");
    serde_json::to_writer_pretty(outfile, &report).unwrap()
}
