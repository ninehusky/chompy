use std::{
    fs::File,
    io::{BufRead, BufReader},
};

/// Return the `i`th letter from the English alphabet.
pub fn letter(i: usize) -> &'static str {
    let alpha = "abcdefghijklmnopqrstuvwxyz";
    &alpha[i..i + 1]
}

/// Helper function to cross product a list of values `ts` across `n` variables.
pub fn self_product<T: Clone>(ts: &[T], n: usize) -> Vec<Vec<T>> {
    let num_consts = ts.len();
    let num_rows = num_consts.pow(n as u32);
    let mut res = vec![];
    for i in 0..n {
        let mut entry = vec![];
        while entry.len() < num_rows {
            for c in ts {
                for _ in 0..num_consts.pow(i as u32) {
                    entry.push(c.clone());
                }
            }
        }
        res.push(entry);
    }
    res
}

#[macro_export]
macro_rules! map {
    ($get:ident, $a:ident => $body:expr) => {
        $get($a)
            .iter()
            .map(|a| match a {
                Some($a) => $body,
                _ => None,
            })
            .collect::<Vec<_>>()
    };

    ($get:ident, $a:ident, $b:ident => $body:expr) => {
        $get($a)
            .iter()
            .zip($get($b).iter())
            .map(|tup| match tup {
                (Some($a), Some($b)) => $body,
                _ => None,
            })
            .collect::<Vec<_>>()
    };
    ($get:ident, $a:ident, $b:ident, $c:ident => $body:expr) => {
        $get($a)
            .iter()
            .zip($get($b).iter())
            .zip($get($c).iter())
            .map(|tup| match tup {
                ((Some($a), Some($b)), Some($c)) => $body,
                _ => None,
            })
            .collect::<Vec<_>>()
    };
}

/// Helper function to count the number of lines in a file
pub fn count_lines(name: &str) -> Option<usize> {
    let filepath = format!("tests/recipes/{name}.rs");
    if let Ok(file) = File::open(filepath) {
        Some(BufReader::new(file).lines().count())
    } else {
        None
    }
}
