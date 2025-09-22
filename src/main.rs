use ruler::conditions::assumption::Assumption;
use ruler::conditions::implication::Implication;
use ruler::conditions::implication_set::ImplicationSet;
use ruler::enumo::Rule;
use ruler::enumo::Ruleset;
use ruler::halide::mini_recipe;
use ruler::halide::og_recipe_plus_select;
use ruler::halide::Pred;

use ruler::halide::og_recipe;
use ruler::recipe_utils::LLMEnumerationConfig;
use ruler::recipe_utils::LLMFilterConfig;
use ruler::recipe_utils::LLMUsage;
use ruler::Limits;
use ruler::SynthLanguage;

use std::fs::File;
use std::path::PathBuf;
use std::str::FromStr;

use clap::Parser;

// Outlines how to perform Halide rule synthesis.
#[derive(Debug)]
pub enum Recipe {
    MiniRecipe,
    NormalRecipe,
    SelectRecipe,
}

impl FromStr for Recipe {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "mini" => Ok(Self::MiniRecipe),
            "full" => Ok(Self::NormalRecipe),
            "select" => Ok(Self::SelectRecipe),
            _ => Err("Invalid mode.".to_string()),
        }
    }
}

#[derive(Parser, Debug)]
struct ChompyArgs {
    #[clap(long)]
    recipe: Recipe,
    #[clap(long)]
    llm_usage: String,
    #[clap(long)]
    output_path: String,
}

#[tokio::main]
pub async fn main() {
    let args = ChompyArgs::parse();

    let default_filter_cfg = LLMFilterConfig::default().with_on_threshold(10);
    let default_enum_cfg = LLMEnumerationConfig::default()
        .with_num_conditions(20)
        .with_num_terms(100);

    let llm_usage = match args.llm_usage.as_str() {
        "baseline" => LLMUsage::None,
        "enum_only" => LLMUsage::EnumerationOnly(default_enum_cfg.clone()),
        "baseline_and_enum" => LLMUsage::Enumeration(default_enum_cfg.clone()),
        "baseline_and_filter_1" => LLMUsage::Filter(default_filter_cfg.clone().with_top_k(1)),
        "baseline_and_filter_5" => LLMUsage::Filter(default_filter_cfg.clone().with_top_k(5)),
        "baseline_with_filter_5_and_enum" => LLMUsage::Combined(vec![
            LLMUsage::Filter(default_filter_cfg.clone()),
            LLMUsage::Enumeration(default_enum_cfg.clone()),
        ]),
        _ => panic!("Invalid llm_usage"),
    };

    // create the output file if it doesn't exist.

    if let Err(e) = File::create(&args.output_path) {
        panic!("Failed to create output file: {}", e);
    }

    let rules = match args.recipe {
        Recipe::MiniRecipe => mini_recipe(llm_usage).await,
        Recipe::SelectRecipe => og_recipe_plus_select(llm_usage).await,
        Recipe::NormalRecipe => og_recipe(llm_usage).await,
    };

    rules.to_file(&args.output_path);

    println!("Wrote {} rules to {:?}", rules.len(), args.output_path);

    for against in &[Against::Halide, Against::Caviar] {
        get_derivability_results(
            rules.clone(),
            against.clone(),
            args.output_path.clone(),
            true,
        );
    }
}

#[derive(Debug, Clone)]
pub enum Against {
    Halide,
    Caviar,
}

// Grabbed using the script in python/halide_to_chompy.py.
const HALIDE_RULES: &str = r#"
(< (* x c0) (* y c0)) ==> (< x y) if (> c0 0)
(< (* x c0) (* y c0)) ==> (< y x) if (< c0 0)
(< (/ x c0) c1) ==> (< x (* c1 c0)) if (> c0 0)
(< (min z y) (min x (+ y c0))) ==> (< (min z y) x) if (> c0 0)
(< (min z y) (min (+ y c0) x)) ==> (< (min z y) x) if (> c0 0)
(< (min z (+ y c0)) (min x y)) ==> (< (min z (+ y c0)) x) if (< c0 0)
(< (min z (+ y c0)) (min y x)) ==> (< (min z (+ y c0)) x) if (< c0 0)
(< (min y z) (min x (+ y c0))) ==> (< (min z y) x) if (> c0 0)
(< (min y z) (min (+ y c0) x)) ==> (< (min z y) x) if (> c0 0)
(< (min (+ y c0) z) (min x y)) ==> (< (min z (+ y c0)) x) if (< c0 0)
(< (min (+ y c0) z) (min y x)) ==> (< (min z (+ y c0)) x) if (< c0 0)
(< (max z y) (max x (+ y c0))) ==> (< (max z y) x) if (< c0 0)
(< (max z y) (max (+ y c0) x)) ==> (< (max z y) x) if (< c0 0)
(< (max z (+ y c0)) (max x y)) ==> (< (max z (+ y c0)) x) if (> c0 0)
(< (max z (+ y c0)) (max y x)) ==> (< (max z (+ y c0)) x) if (> c0 0)
(< (max y z) (max x (+ y c0))) ==> (< (max z y) x) if (< c0 0)
(< (max y z) (max (+ y c0) x)) ==> (< (max z y) x) if (< c0 0)
(< (max (+ y c0) z) (max x y)) ==> (< (max z (+ y c0)) x) if (> c0 0)
(< (max (+ y c0) z) (max y x)) ==> (< (max z (+ y c0)) x) if (> c0 0)
(< x (* (/ x c1) c1)) ==> 0 if (> c1 0)
(< (/ (+ x c1) c0) (/ (+ x c2) c0)) ==> 0 if (> c0 (&& 0 (>= c1 c2)))
(< (/ (+ x c1) c0) (/ (+ x c2) c0)) ==> 1 if (> c0 (&& 0 (<= c1 (- c2 c0))))
(< (/ x c0) (/ (+ x c2) c0)) ==> 0 if (> c0 (&& 0 (>= 0 c2)))
(< (/ x c0) (/ (+ x c2) c0)) ==> 1 if (> c0 (&& 0 (<= 0 (- c2 c0))))
(< (/ (+ x c1) c0) (/ x c0)) ==> 0 if (> c0 (&& 0 (>= c1 0)))
(< (/ (+ x c1) c0) (/ x c0)) ==> 1 if (> c0 (&& 0 (<= c1 (- 0 c0))))
(< (/ (+ x c1) c0) (+ (/ x c0) c2)) ==> 0 if (> c0 (&& 0 (>= c1 (* c2 c0))))
(< (/ (+ x c1) c0) (+ (/ x c0) c2)) ==> 1 if (> c0 (&& 0 (<= c1 (- (* c2 c0) c0))))
(< (/ (+ x c1) c0) (+ (min (/ x c0) y) c2)) ==> 0 if (> c0 (&& 0 (>= c1 (* c2 c0))))
(< (/ (+ x c1) c0) (+ (max (/ x c0) y) c2)) ==> 1 if (> c0 (&& 0 (<= c1 (- (* c2 c0) c0))))
(< (/ (+ x c1) c0) (min (/ (+ x c2) c0) y)) ==> 0 if (> c0 (&& 0 (>= c1 c2)))
(< (/ (+ x c1) c0) (max (/ (+ x c2) c0) y)) ==> 1 if (> c0 (&& 0 (<= c1 (- c2 c0))))
(< (/ (+ x c1) c0) (min (/ x c0) y)) ==> 0 if (> c0 (&& 0 (>= c1 0)))
(< (/ (+ x c1) c0) (max (/ x c0) y)) ==> 1 if (> c0 (&& 0 (<= c1 (- 0 c0))))
(< (/ (+ x c1) c0) (+ (min y (/ x c0)) c2)) ==> 0 if (> c0 (&& 0 (>= c1 (* c2 c0))))
(< (/ (+ x c1) c0) (+ (max y (/ x c0)) c2)) ==> 1 if (> c0 (&& 0 (<= c1 (- (* c2 c0) c0))))
(< (/ (+ x c1) c0) (min y (/ (+ x c2) c0))) ==> 0 if (> c0 (&& 0 (>= c1 c2)))
(< (/ (+ x c1) c0) (max y (/ (+ x c2) c0))) ==> 1 if (> c0 (&& 0 (<= c1 (- c2 c0))))
(< (/ (+ x c1) c0) (min y (/ x c0))) ==> 0 if (> c0 (&& 0 (>= c1 0)))
(< (/ (+ x c1) c0) (max y (/ x c0))) ==> 1 if (> c0 (&& 0 (<= c1 (- 0 c0))))
(< (max (/ (+ x c2) c0) y) (/ (+ x c1) c0)) ==> 0 if (> c0 (&& 0 (>= c2 c1)))
(< (min (/ (+ x c2) c0) y) (/ (+ x c1) c0)) ==> 1 if (> c0 (&& 0 (<= c2 (- c1 c0))))
(< (max (/ x c0) y) (/ (+ x c1) c0)) ==> 0 if (> c0 (&& 0 (>= 0 c1)))
(< (min (/ x c0) y) (/ (+ x c1) c0)) ==> 1 if (> c0 (&& 0 (<= 0 (- c1 c0))))
(< (max y (/ (+ x c2) c0)) (/ (+ x c1) c0)) ==> 0 if (> c0 (&& 0 (>= c2 c1)))
(< (min y (/ (+ x c2) c0)) (/ (+ x c1) c0)) ==> 1 if (> c0 (&& 0 (<= c2 (- c1 c0))))
(< (max y (/ x c0)) (/ (+ x c1) c0)) ==> 0 if (> c0 (&& 0 (>= 0 c1)))
(< (min y (/ x c0)) (/ (+ x c1) c0)) ==> 1 if (> c0 (&& 0 (<= 0 (- c1 c0))))
(< (max (/ (+ x c2) c0) y) (+ (/ x c0) c1)) ==> 0 if (> c0 (&& 0 (>= c2 (* c1 c0))))
(< (min (/ (+ x c2) c0) y) (+ (/ x c0) c1)) ==> 1 if (> c0 (&& 0 (<= c2 (- (* c1 c0) c0))))
(< (max y (/ (+ x c2) c0)) (+ (/ x c0) c1)) ==> 0 if (> c0 (&& 0 (>= c2 (* c1 c0))))
(< (min y (/ (+ x c2) c0)) (+ (/ x c0) c1)) ==> 1 if (> c0 (&& 0 (<= c2 (- (* c1 c0) c0))))
(< (/ x c0) (min (/ (+ x c2) c0) y)) ==> 0 if (> c0 (&& 0 (< c2 0)))
(< (/ x c0) (max (/ (+ x c2) c0) y)) ==> 1 if (> c0 (&& 0 (<= c0 c2)))
(< (/ x c0) (min y (/ (+ x c2) c0))) ==> 0 if (> c0 (&& 0 (< c2 0)))
(< (/ x c0) (max y (/ (+ x c2) c0))) ==> 1 if (> c0 (&& 0 (<= c0 c2)))
(< (max (/ (+ x c2) c0) y) (/ x c0)) ==> 0 if (> c0 (&& 0 (>= c2 0)))
(< (min (/ (+ x c2) c0) y) (/ x c0)) ==> 1 if (> c0 (&& 0 (<= (+ c2 c0) 0)))
(< (max y (/ (+ x c2) c0)) (/ x c0)) ==> 0 if (> c0 (&& 0 (>= c2 0)))
(< (min y (/ (+ x c2) c0)) (/ x c0)) ==> 1 if (> c0 (&& 0 (<= (+ c2 c0) 0)))
(< (/ (+ (max x (+ (* y c0) c1)) c2) c0) y) ==> (< (/ (+ x c2) c0) y) if (> c0 (&& 0 (< (+ c1 c2) 0)))
(< (/ (+ (max x (+ (* y c0) c1)) c2) c0) y) ==> 0 if (> c0 (&& 0 (>= (+ c1 c2) 0)))
(< (/ (+ (max x (* y c0)) c1) c0) y) ==> (< (/ (+ x c1) c0) y) if (> c0 (&& 0 (< c1 0)))
(< (/ (+ (max x (* y c0)) c1) c0) y) ==> 0 if (> c0 (&& 0 (>= c1 0)))
(< (/ (+ (max (+ (* x c0) c1) y) c2) c0) x) ==> (< (/ (+ y c2) c0) x) if (> c0 (&& 0 (< (+ c1 c2) 0)))
(< (/ (+ (max (+ (* x c0) c1) y) c2) c0) x) ==> 0 if (> c0 (&& 0 (>= (+ c1 c2) 0)))
(< (/ (+ (max (* x c0) y) c1) c0) x) ==> (< (/ (+ y c1) c0) x) if (> c0 (&& 0 (< c1 0)))
(< (/ (+ (max (* x c0) y) c1) c0) x) ==> 0 if (> c0 (&& 0 (>= c1 0)))
(< (/ (max x (+ (* y c0) c1)) c0) y) ==> (< (/ x c0) y) if (> c0 (&& 0 (< c1 0)))
(< (/ (max x (+ (* y c0) c1)) c0) y) ==> 0 if (> c0 (&& 0 (>= c1 0)))
(< (/ (max x (* y c0)) c20) y) ==> 0 if (> c0 0)
(< (/ (max (+ (* x c0) c1) y) c0) x) ==> (< (/ y c0) x) if (> c0 (&& 0 (< c1 0)))
(< (/ (max (+ (* x c0) c1) y) c0) x) ==> 0 if (> c0 (&& 0 (>= c1 0)))
(< (/ (max (* x c0) y) c0) x) ==> 0 if (> c0 0)
(< (/ (+ (min x (+ (* y c0) c1)) c2) c0) y) ==> 1 if (> c0 (&& 0 (< (+ c1 c2) 0)))
(< (/ (+ (min x (+ (* y c0) c1)) c2) c0) y) ==> (< (/ (+ x c2) c0) y) if (> c0 (&& 0 (>= (+ c1 c2) 0)))
(< (/ (+ (min x (* y c0)) c1) c0) y) ==> 1 if (> c0 (&& 0 (< c1 0)))
(< (/ (+ (min x (* y c0)) c1) c0) y) ==> (< (/ (+ x c1) c0) y) if (> c0 (&& 0 (>= c1 0)))
(< (/ (+ (min (+ (* x c0) c1) y) c2) c0) x) ==> 1 if (> c0 (&& 0 (< (+ c1 c2) 0)))
(< (/ (+ (min (+ (* x c0) c1) y) c2) c0) x) ==> (< (/ (+ y c2) c0) x) if (> c0 (&& 0 (>= (+ c1 c2) 0)))
(< (/ (+ (min (* x c0) y) c1) c0) x) ==> 1 if (> c0 (&& 0 (< c1 0)))
(< (/ (+ (min (* x c0) y) c1) c0) x) ==> (< (/ (+ y c1) c0) x) if (> c0 (&& 0 (>= c1 0)))
(< (/ (min x (+ (* y c0) c1)) c0) y) ==> 1 if (> c0 (&& 0 (< c1 0)))
(< (/ (min x (+ (* y c0) c1)) c0) y) ==> (< (/ x c0) y) if (> c0 (&& 0 (>= c1 0)))
(< (/ (min x (* y c0)) c0) y) ==> (< (/ x c0) y) if (> c0 0)
(< (/ (min (+ (* x c0) c1) y) c0) x) ==> 1 if (> c0 (&& 0 (< c1 0)))
(< (/ (min (+ (* x c0) c1) y) c0) x) ==> (< (/ y c0) x) if (> c0 (&& 0 (>= c1 0)))
(< (/ (min (* x c0) y) c0) x) ==> (< (/ y c0) x) if (> c0 0)
(< (min x c0) (min x c1)) ==> 0 if (>= c0 c1)
(< (min x c0) (+ (min x c1) c2)) ==> 0 if (>= c0 (&& (+ c1 c2) (<= c2 0)))
(< (max x c0) (max x c1)) ==> 0 if (>= c0 c1)
(< (max x c0) (+ (max x c1) c2)) ==> 0 if (>= c0 (&& (+ c1 c2) (<= c2 0)))
(max x c0) ==> b if (is_max_value c0)
(max x c0) ==> x if (is_min_value c0)
(max (* (/ x c0) c0) x) ==> b if (> c0 0)
(max x (* (/ x c0) c0)) ==> a if (> c0 0)
(max (min x c0) c1) ==> b if (>= c1 c0)
(max (+ (* (/ (+ x c0) c1) c1) c2) x) ==> a if (> c1 (&& 0 (>= (+ c0 c2) (- c1 1))))
(max x (+ (* (/ (+ x c0) c1) c1) c2)) ==> b if (> c1 (&& 0 (>= (+ c0 c2) (- c1 1))))
(max (+ (* (/ (+ x c0) c1) c1) c2) x) ==> b if (> c1 (&& 0 (<= (+ c0 c2) 0)))
(max x (+ (* (/ (+ x c0) c1) c1) c2)) ==> a if (> c1 (&& 0 (<= (+ c0 c2) 0)))
(max (* (/ x c0) c0) (+ (* (/ x c1) c1) c2)) ==> b if (>= c2 (&& c1 (> c1 (&& 0 (!= c0 0)))))
(max (+ (* (/ x c1) c1) c2) x) ==> a if (> c1 (&& 0 (>= c2 (- c1 1))))
(max x (+ (* (/ x c1) c1) c2)) ==> b if (> c1 (&& 0 (>= c2 (- c1 1))))
(max (* (/ (+ x c0) c1) c1) x) ==> a if (> c1 (&& 0 (>= c0 (- c1 1))))
(max x (* (/ (+ x c0) c1) c1)) ==> b if (> c1 (&& 0 (>= c0 (- c1 1))))
(max (+ (* (/ x c1) c1) c2) x) ==> b if (> c1 (&& 0 (<= c2 0)))
(max x (+ (* (/ x c1) c1) c2)) ==> a if (> c1 (&& 0 (<= c2 0)))
(max (* (/ (+ x c0) c1) c1) x) ==> b if (> c1 (&& 0 (<= c0 0)))
(max x (* (/ (+ x c0) c1) c1)) ==> a if (> c1 (&& 0 (<= c0 0)))
(max x (+ (min x y) c0)) ==> a if (<= c0 0)
(max x (+ (min y x) c0)) ==> a if (<= c0 0)
(max (+ (min x y) c0) x) ==> b if (<= c0 0)
(max (+ (min x y) c0) y) ==> b if (<= c0 0)
(max (min (- c0 x) x) c1) ==> b if (>= (* 2 c1) (- c0 1))
(max (min x (- c0 x)) c1) ==> b if (>= (* 2 c1) (- c0 1))
(max (max (/ x c0) y) (/ z c0)) ==> (max (/ (max x z) c0) y) if (> c0 0)
(max (+ (max x y) c0) x) ==> (max x (+ y c0)) if (< c0 0)
(max (+ (max x y) c0) x) ==> (+ (max x y) c0) if (> c0 0)
(max (+ (max y x) c0) x) ==> (max (+ y c0) x) if (< c0 0)
(max (+ (max y x) c0) x) ==> (+ (max y x) c0) if (> c0 0)
(max x (+ (max x y) c0)) ==> (max x (+ y c0)) if (< c0 0)
(max x (+ (max x y) c0)) ==> (+ (max x y) c0) if (> c0 0)
(max x (+ (max y x) c0)) ==> (max x (+ y c0)) if (< c0 0)
(max x (+ (max y x) c0)) ==> (+ (max x y) c0) if (> c0 0)
(max (max x y) (+ x c0)) ==> (max (+ x c0) y) if (> c0 0)
(max (max x y) (+ x c0)) ==> (max x y) if (< c0 0)
(max (max y x) (+ x c0)) ==> (max y (+ x c0)) if (> c0 0)
(max (max y x) (+ x c0)) ==> (max y x) if (< c0 0)
(max (* (+ (* x c0) y) c1) (+ (* x c2) z)) ==> (+ (max (* y c1) z) (* x c2)) if (== (* c0 c1) c2)
(max (* (+ y (* x c0)) c1) (+ (* x c2) z)) ==> (+ (max (* y c1) z) (* x c2)) if (== (* c0 c1) c2)
(max (* (+ (* x c0) y) c1) (+ z (* x c2))) ==> (+ (max (* y c1) z) (* x c2)) if (== (* c0 c1) c2)
(max (* (+ y (* x c0)) c1) (+ z (* x c2))) ==> (+ (max (* y c1) z) (* x c2)) if (== (* c0 c1) c2)
(max (/ x c0) (/ y c0)) ==> (/ (max x y) c0) if (> c0 0)
(max (/ x c0) (/ y c0)) ==> (/ (min x y) c0) if (< c0 0)
(max (* (/ (+ x c0) c1) c1) (+ x c2)) ==> (* (/ (+ x c0) c1) c1) if (> c1 (&& 0 (>= (+ c0 1) (+ c1 c2))))
(max (/ (+ x c0) c1) (* (/ (+ x c2) c3) c4)) ==> (/ (+ x c0) c1) if (<= c2 (&& c0 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(max (/ (+ x c0) c1) (* (/ (+ x c2) c3) c4)) ==> (* (/ (+ x c2) c3) c4) if (<= (- (+ c0 c3) c1) (&& c2 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(max (/ x c1) (* (/ (+ x c2) c3) c4)) ==> (/ x c1) if (<= c2 (&& 0 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(max (/ x c1) (* (/ (+ x c2) c3) c4)) ==> (* (/ (+ x c2) c3) c4) if (<= (- c3 c1) (&& c2 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(max (/ (+ x c0) c1) (* (/ x c3) c4)) ==> (/ (+ x c0) c1) if (<= 0 (&& c0 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(max (/ (+ x c0) c1) (* (/ x c3) c4)) ==> (* (/ x c3) c4) if (<= (- (+ c0 c3) c1) (&& 0 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(max (/ x c1) (* (/ x c3) c4)) ==> (/ x c1) if (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))
(== (+ (max x c0) c1) 0) ==> 0 if (> (+ c0 c1) 0)
(== (+ (min x c0) c1) 0) ==> 0 if (< (+ c0 c1) 0)
(== (+ (max x c0) c1) 0) ==> (<= x c0) if (== (+ c0 c1) 0)
(== (+ (min x c0) c1) 0) ==> (<= c0 x) if (== (+ c0 c1) 0)
(== (max x c0) 0) ==> (== x 0) if (< c0 0)
(== (min x c0) 0) ==> (== x 0) if (> c0 0)
(== (max x c0) 0) ==> 0 if (> c0 0)
(== (min x c0) 0) ==> 0 if (< c0 0)
(/ (- (* x c1) y) c0) ==> (- (/ (- 0 y) c0) x) if (== (+ c0 c1) 0)
(/ (- (- (* x c1) y) z) c0) ==> (- (/ (- (- 0 y) z) c0) x) if (== (+ c0 c1) 0)
(!= x (&& c0 (== x c1))) ==> b if (!= c0 c1)
(== x (&& c0 (== x c1))) ==> 0 if (!= c0 c1)
(<= x (&& c1 (< c0 x))) ==> 0 if (<= c1 c0)
(<= c0 (&& x (< x c1))) ==> 0 if (<= c1 c0)
(<= c0 (&& x (<= x c1))) ==> 0 if (< c1 c0)
(<= x (&& c1 (<= c0 x))) ==> 0 if (< c1 c0)
(- (min x y) (min z w)) ==> (- y w) if (can_prove (== (- x y) (- z w)) this)
(- (min x y) (min w z)) ==> (- y w) if (can_prove (== (- x y) (- z w)) this)
(- (min (* x c0) c1) (* (min x c2) c0)) ==> (min (- c1 (* (min x c2) c0)) 0) if (> c0 (&& 0 (<= c1 (* c2 c0))))
(- (max x y) (max z w)) ==> (- y w) if (can_prove (== (- x y) (- z w)) this)
(- (max x y) (max w z)) ==> (- y w) if (can_prove (== (- x y) (- z w)) this)
(- (min x y) (min x w)) ==> (min (- y (min x w)) 0) if (can_prove (<= y w) this)
(- (min x y) (min x w)) ==> (max (- (min x y) w) 0) if (can_prove (>= y w) this)
(- (min (+ x c0) y) (min x w)) ==> (min (- y (min x w)) c0) if (can_prove (<= y (+ w c0)) this)
(- (min (+ x c0) y) (min x w)) ==> (max (- (min (+ x c0) y) w) c0) if (can_prove (>= y (+ w c0)) this)
(- (min y x) (min w x)) ==> (min (- y (min x w)) 0) if (can_prove (<= y w) this)
(- (min y x) (min w x)) ==> (max (- (min x y) w) 0) if (can_prove (>= y w) this)
(- (min y (+ x c0)) (min w x)) ==> (min (- y (min x w)) c0) if (can_prove (<= y (+ w c0)) this)
(- (min y (+ x c0)) (min w x)) ==> (max (- (min (+ x c0) y) w) c0) if (can_prove (>= y (+ w c0)) this)
(- (min x y) (min w x)) ==> (min (- y (min x w)) 0) if (can_prove (<= y w) this)
(- (min x y) (min w x)) ==> (max (- (min x y) w) 0) if (can_prove (>= y w) this)
(- (min (+ x c0) y) (min w x)) ==> (min (- y (min x w)) c0) if (can_prove (<= y (+ w c0)) this)
(- (min (+ x c0) y) (min w x)) ==> (max (- (min (+ x c0) y) w) c0) if (can_prove (>= y (+ w c0)) this)
(- (min y x) (min x w)) ==> (min (- y (min x w)) 0) if (can_prove (<= y w) this)
(- (min y x) (min x w)) ==> (max (- (min x y) w) 0) if (can_prove (>= y w) this)
(- (min y (+ x c0)) (min x w)) ==> (min (- y (min x w)) c0) if (can_prove (<= y (+ w c0)) this)
(- (min y (+ x c0)) (min x w)) ==> (max (- (min (+ x c0) y) w) c0) if (can_prove (>= y (+ w c0)) this)
(- (max x y) (max x w)) ==> (max (- y (max x w)) 0) if (can_prove (>= y w) this)
(- (max x y) (max x w)) ==> (min (- (max x y) w) 0) if (can_prove (<= y w) this)
(- (max (+ x c0) y) (max x w)) ==> (max (- y (max x w)) c0) if (can_prove (>= y (+ w c0)) this)
(- (max (+ x c0) y) (max x w)) ==> (min (- (max (+ x c0) y) w) c0) if (can_prove (<= y (+ w c0)) this)
(- (max y x) (max w x)) ==> (max (- y (max x w)) 0) if (can_prove (>= y w) this)
(- (max y x) (max w x)) ==> (min (- (max x y) w) 0) if (can_prove (<= y w) this)
(- (max y (+ x c0)) (max w x)) ==> (max (- y (max x w)) c0) if (can_prove (>= y (+ w c0)) this)
(- (max y (+ x c0)) (max w x)) ==> (min (- (max (+ x c0) y) w) c0) if (can_prove (<= y (+ w c0)) this)
(- (max x y) (max w x)) ==> (max (- y (max x w)) 0) if (can_prove (>= y w) this)
(- (max x y) (max w x)) ==> (min (- (max x y) w) 0) if (can_prove (<= y w) this)
(- (max (+ x c0) y) (max w x)) ==> (max (- y (max x w)) c0) if (can_prove (>= y (+ w c0)) this)
(- (max (+ x c0) y) (max w x)) ==> (min (- (max (+ x c0) y) w) c0) if (can_prove (<= y (+ w c0)) this)
(- (max y x) (max x w)) ==> (max (- y (max x w)) 0) if (can_prove (>= y w) this)
(- (max y x) (max x w)) ==> (min (- (max x y) w) 0) if (can_prove (<= y w) this)
(- (max y (+ x c0)) (max x w)) ==> (max (- y (max x w)) c0) if (can_prove (>= y (+ w c0)) this)
(- (max y (+ x c0)) (max x w)) ==> (min (- (max (+ x c0) y) w) c0) if (can_prove (<= y (+ w c0)) this)
(- (/ (+ (+ x y) z) c0) (/ (+ (+ y x) w) c0)) ==> (- (/ (+ (+ x y) z) c0) (/ (+ (+ x y) w) c0)) if (> c0 0)
(- (/ (+ x y) c0) (/ (+ y x) c0)) ==> 0 if (!= c0 0)
(- (/ (min (+ (* x c0) y) z) c1) (* x c2)) ==> (/ (min y (- z (* x c0))) c1) if (== c0 (* c1 c2))
(- (/ (min z (+ (* x c0) y)) c1) (* x c2)) ==> (/ (min y (- z (* x c0))) c1) if (== c0 (* c1 c2))
(- (/ (+ (min (+ (* x c0) y) z) w) c1) (* x c2)) ==> (/ (+ (min y (- z (* x c0))) w) c1) if (== c0 (* c1 c2))
(- (/ (+ (min z (+ (* x c0) y)) w) c1) (* x c2)) ==> (/ (+ (min (- z (* x c0)) y) w) c1) if (== c0 (* c1 c2))
(!= x (|| c0 (== x c1))) ==> a if (!= c0 c1)
(<= x (|| c0 (< c1 x))) ==> 1 if (<= c1 c0)
(<= c1 (|| x (< x c0))) ==> 1 if (<= c1 c0)
(< x (|| c0 (< c1 x))) ==> 1 if (< c1 c0)
(< c1 (|| x (< x c0))) ==> 1 if (< c1 c0)
(+ (min x (+ y c0)) c1) ==> (min (+ x c1) y) if (== (+ c0 c1) 0)
(+ (min (+ y c0) x) c1) ==> (min y (+ x c1)) if (== (+ c0 c1) 0)
(+ (max x (+ y c0)) c1) ==> (max (+ x c1) y) if (== (+ c0 c1) 0)
(+ (max (+ y c0) x) c1) ==> (max y (+ x c1)) if (== (+ c0 c1) 0)
(+ (min x (+ y (* z c0))) (* z c1)) ==> (min (+ x (* z c1)) y) if (== (+ c0 c1) 0)
(+ (min x (+ (* y c0) z)) (* y c1)) ==> (min (+ x (* y c1)) z) if (== (+ c0 c1) 0)
(+ (min x (* y c0)) (* y c1)) ==> (min (+ x (* y c1)) 0) if (== (+ c0 c1) 0)
(+ (min (+ x (* y c0)) z) (* y c1)) ==> (min (+ (* y c1) z) x) if (== (+ c0 c1) 0)
(+ (min (+ (* x c0) y) z) (* x c1)) ==> (min y (+ (* x c1) z)) if (== (+ c0 c1) 0)
(+ (min (* x c0) y) (* x c1)) ==> (min (+ (* x c1) y) 0) if (== (+ c0 c1) 0)
(+ (max x (+ y (* z c0))) (* z c1)) ==> (max (+ x (* z c1)) y) if (== (+ c0 c1) 0)
(+ (max x (+ (* y c0) z)) (* y c1)) ==> (max (+ x (* y c1)) z) if (== (+ c0 c1) 0)
(+ (max x (* y c0)) (* y c1)) ==> (max (+ x (* y c1)) 0) if (== (+ c0 c1) 0)
(+ (max (+ x (* y c0)) z) (* y c1)) ==> (max x (+ (* y c1) z)) if (== (+ c0 c1) 0)
(+ (max (+ (* x c0) y) z) (* x c1)) ==> (max (+ (* x c1) z) y) if (== (+ c0 c1) 0)
(+ (max (* x c0) y) (* x c1)) ==> (max (+ (* x c1) y) 0) if (== (+ c0 c1) 0)
(min x c0) ==> b if (is_min_value c0)
(min x c0) ==> x if (is_max_value c0)
(min (* (/ x c0) c0) x) ==> a if (> c0 0)
(min x (* (/ x c0) c0)) ==> b if (> c0 0)
(min (max x c0) c1) ==> b if (<= c1 c0)
(min (+ (* (/ (+ x c0) c1) c1) c2) x) ==> b if (> c1 (&& 0 (>= (+ c0 c2) (- c1 1))))
(min x (+ (* (/ (+ x c0) c1) c1) c2)) ==> a if (> c1 (&& 0 (>= (+ c0 c2) (- c1 1))))
(min (+ (* (/ (+ x c0) c1) c1) c2) x) ==> a if (> c1 (&& 0 (<= (+ c0 c2) 0)))
(min x (+ (* (/ (+ x c0) c1) c1) c2)) ==> b if (> c1 (&& 0 (<= (+ c0 c2) 0)))
(min (* (/ x c0) c0) (+ (* (/ x c1) c1) c2)) ==> a if (>= c2 (&& c1 (> c1 (&& 0 (!= c0 0)))))
(min (+ (* (/ x c1) c1) c2) x) ==> b if (> c1 (&& 0 (>= c2 (- c1 1))))
(min x (+ (* (/ x c1) c1) c2)) ==> a if (> c1 (&& 0 (>= c2 (- c1 1))))
(min (* (/ (+ x c0) c1) c1) x) ==> b if (> c1 (&& 0 (>= c0 (- c1 1))))
(min x (* (/ (+ x c0) c1) c1)) ==> a if (> c1 (&& 0 (>= c0 (- c1 1))))
(min (+ (* (/ x c1) c1) c2) x) ==> a if (> c1 (&& 0 (<= c2 0)))
(min x (+ (* (/ x c1) c1) c2)) ==> b if (> c1 (&& 0 (<= c2 0)))
(min (* (/ (+ x c0) c1) c1) x) ==> a if (> c1 (&& 0 (<= c0 0)))
(min x (* (/ (+ x c0) c1) c1)) ==> b if (> c1 (&& 0 (<= c0 0)))
(min x (+ (max x y) c0)) ==> a if (<= 0 c0)
(min x (+ (max y x) c0)) ==> a if (<= 0 c0)
(min (+ (max x y) c0) x) ==> b if (<= 0 c0)
(min (+ (max x y) c0) y) ==> b if (<= 0 c0)
(min (max x (+ y c0)) y) ==> y if (> c0 0)
(min (max (- c0 x) x) c1) ==> b if (<= (* 2 c1) (+ c0 1))
(min (max x (- c0 x)) c1) ==> b if (<= (* 2 c1) (+ c0 1))
(min (min (/ x c0) y) (/ z c0)) ==> (min (/ (min x z) c0) y) if (> c0 0)
(min (max x c0) c1) ==> (max (min x c1) c0) if (<= c0 c1)
(min (+ (min x y) c0) x) ==> (min x (+ y c0)) if (> c0 0)
(min (+ (min x y) c0) x) ==> (+ (min x y) c0) if (< c0 0)
(min (+ (min y x) c0) x) ==> (min (+ y c0) x) if (> c0 0)
(min (+ (min y x) c0) x) ==> (+ (min y x) c0) if (< c0 0)
(min x (+ (min x y) c0)) ==> (min x (+ y c0)) if (> c0 0)
(min x (+ (min x y) c0)) ==> (+ (min x y) c0) if (< c0 0)
(min x (+ (min y x) c0)) ==> (min x (+ y c0)) if (> c0 0)
(min x (+ (min y x) c0)) ==> (+ (min x y) c0) if (< c0 0)
(min (min x y) (+ x c0)) ==> (min x y) if (> c0 0)
(min (min x y) (+ x c0)) ==> (min (+ x c0) y) if (< c0 0)
(min (min y x) (+ x c0)) ==> (min y x) if (> c0 0)
(min (min y x) (+ x c0)) ==> (min y (+ x c0)) if (< c0 0)
(min (max (+ x c0) y) x) ==> x if (> c0 0)
(min (* (+ (* x c0) y) c1) (+ (* x c2) z)) ==> (+ (min (* y c1) z) (* x c2)) if (== (* c0 c1) c2)
(min (* (+ y (* x c0)) c1) (+ (* x c2) z)) ==> (+ (min (* y c1) z) (* x c2)) if (== (* c0 c1) c2)
(min (* (+ (* x c0) y) c1) (+ z (* x c2))) ==> (+ (min (* y c1) z) (* x c2)) if (== (* c0 c1) c2)
(min (* (+ y (* x c0)) c1) (+ z (* x c2))) ==> (+ (min (* y c1) z) (* x c2)) if (== (* c0 c1) c2)
(min (/ x c0) (/ y c0)) ==> (/ (min x y) c0) if (> c0 0)
(min (/ x c0) (/ y c0)) ==> (/ (max x y) c0) if (< c0 0)
(min (* (/ (+ x c0) c1) c1) (+ x c2)) ==> (+ x c2) if (> c1 (&& 0 (>= (+ c0 1) (+ c1 c2))))
(min (* (min (/ (+ y c0) c1) x) c1) (+ y c2)) ==> (min (* x c1) (+ y c2)) if (> c1 (&& 0 (<= (+ c1 c2) (+ c0 1))))
(min (+ (* (min (/ (+ y c0) c1) x) c1) c2) y) ==> (min (+ (* x c1) c2) y) if (> c1 (&& 0 (<= c1 (+ (+ c0 c2) 1))))
(min (* (min (/ (+ y c0) c1) x) c1) y) ==> (min (* x c1) y) if (> c1 (&& 0 (<= c1 (+ c0 1))))
(min (/ (+ x c0) c1) (* (/ (+ x c2) c3) c4)) ==> (/ (+ x c0) c1) if (<= (- (+ c0 c3) c1) (&& c2 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(min (/ (+ x c0) c1) (* (/ (+ x c2) c3) c4)) ==> (* (/ (+ x c2) c3) c4) if (<= c2 (&& c0 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(min (/ x c1) (* (/ (+ x c2) c3) c4)) ==> (/ x c1) if (<= (- c3 c1) (&& c2 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(min (/ x c1) (* (/ (+ x c2) c3) c4)) ==> (* (/ (+ x c2) c3) c4) if (<= c2 (&& 0 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(min (/ (+ x c0) c1) (* (/ x c3) c4)) ==> (/ (+ x c0) c1) if (<= (- (+ c0 c3) c1) (&& 0 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(min (/ (+ x c0) c1) (* (/ x c3) c4)) ==> (* (/ x c3) c4) if (<= 0 (&& c0 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(min (/ x c1) (* (/ x c3) c4)) ==> (* (/ x c3) c4) if (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))
"#;

const CAVIAR_RULES: &str = r#"
(== ?x ?y) ==> (== ?y ?x)
(== ?x ?y) ==> (== (- ?x ?y) 0)
(== (+ ?x ?y) ?z) ==> (== ?x (- ?z ?y))
(== ?x ?x) ==> 1
(== (* ?x ?y) 0) ==> (|| (== ?x 0) (== ?y 0))
( == (max ?x ?y) ?y) ==> (<= ?x ?y)
( == (min ?x ?y) ?y) ==> (<= ?y ?x)
(<= ?y ?x) ==> ( == (min ?x ?y) ?y)
(== (* ?a ?x) ?b) ==> 0 if (&& (!= ?a 0) (!= (% ?b ?a) 0))
(== (max ?x ?c) 0) ==> 0 if (> ?c 0)
(== (max ?x ?c) 0) ==> (== ?x 0) if (< ?c 0)
(== (min ?x ?c) 0) ==> 0 if (< ?c 0)
(== (min ?x ?c) 0) ==> (== ?x 0) if (> ?c 0)
(|| ?x ?y) ==> (! (&& (! ?x) (! ?y)))
(|| ?y ?x) ==> (|| ?x ?y)
(+ ?a ?b) ==> (+ ?b ?a)
(+ ?a (+ ?b ?c)) ==> (+ (+ ?a ?b) ?c)
(+ ?a 0) ==> ?a
(* ?a (+ ?b ?c)) ==> (+ (* ?a ?b) (* ?a ?c))
(+ (* ?a ?b) (* ?a ?c)) ==> (* ?a (+ ?b ?c))
(+ (/ ?a ?b) ?c) ==> (/ (+ ?a (* ?b ?c)) ?b)
(/ (+ ?a (* ?b ?c)) ?b) ==> (+ (/ ?a ?b) ?c)
( + ( / ?x 2 ) ( % ?x 2 ) ) ==> ( / ( + ?x 1 ) 2 )
( + (* ?x ?a) (* ?y ?b)) ==> ( * (+ (* ?x (/ ?a ?b)) ?y) ?b) if (&& (!= ?b 0) (== (% ?a ?b) 0))
(/ 0 ?x) ==> (0)
(/ ?a ?a) ==> 1 if (!= ?a 0)
(/ (* -1 ?a) ?b) ==> (/ ?a (* -1 ?b))
(/ ?a (* -1 ?b)) ==> (/ (* -1 ?a) ?b)
(* -1 (/ ?a ?b)) ==> (/ (* -1 ?a) ?b)
(/ (* -1 ?a) ?b) ==> (* -1 (/ ?a ?b))
( / ( * ?x ?a ) ?b ) ==> ( / ?x ( / ?b ?a ) ) if (&& (> ?a 0) (== (% ?b ?a) 0))
( / ( * ?x ?a ) ?b ) ==> ( * ?x ( / ?a ?b ) ) if (&& (> ?b 0) (== (% ?a ?b) 0))
( / ( + ( * ?x ?a ) ?y ) ?b ) ==> ( + ( * ?x ( / ?a ?b ) ) ( / ?y ?b ) ) if (&& (> ?b 0) (== (% ?a ?b) 0))
( / ( + ?x ?a ) ?b ) ==> ( + ( / ?x ?b ) ( / ?a ?b ) ) if (&& (> ?b 0) (== (% ?a ?b) 0))
(!= ?x ?y) ==> (! (== ?x ?y))
(max ?a ?b) ==> (* -1 (min (* -1 ?a) (* -1 ?b)))
(&& ?y ?x) ==> (&& ?x ?y)
(&& ?a (&& ?b ?c)) ==> (&& (&& ?a ?b) ?c)
(&& 1 ?x) ==> ?x
(&& ?x ?x) ==> ?x
(&& ?x (! ?x)) ==> 0
( && ( == ?x ?c0 ) ( == ?x ?c1 ) ) ==> 0 if (!= ?c1 ?c0)
( && ( != ?x ?c0 ) ( == ?x ?c1 ) ) ==> ( == ?x ?c1 ) if (!= ?c1 ?c0)
(&& (< ?x ?y) (< ?x ?z)) ==> (< ?x (min ?y ?z))
(< ?x (min ?y ?z)) ==> (&& (< ?x ?y) (< ?x ?z))
(&& (<= ?x ?y) (<= ?x ?z)) ==> (<= ?x (min ?y ?z))
(<= ?x (min ?y ?z)) ==> (&& (<= ?x ?y) (<= ?x ?z))
(&& (< ?y ?x) (< ?z ?x)) ==> (< (max ?y ?z) ?x)
(> ?x (max ?y ?z)) ==> (&& (< ?z ?x) (< ?y ?x))
(&& (<= ?y ?x) (<= ?z ?x)) ==> (<= (max ?y ?z) ?x)
(>= ?x (max ?y ?z)) ==> (&& (<= ?z ?x) (<= ?y ?x))
( && ( < ?c0 ?x ) ( < ?x ?c1 ) ) ==> 0 if (<= ?c1 (+ ?c0 1))
( && ( <= ?c0 ?x ) ( <= ?x ?c1 ) ) ==> 0 if (< ?c1 ?c0)
( && ( <= ?c0 ?x ) ( < ?x ?c1 ) ) ==> 0 if (<= ?c1 ?c0)
(&& ?a (|| ?b ?c)) ==> (|| (&& ?a ?b) (&& ?a ?c))
(|| ?a (&& ?b ?c)) ==> (&& (|| ?a ?b) (|| ?a ?c))
(|| ?x (&& ?x ?y)) ==> ?x
(- ?a ?b) ==> (+ ?a (* -1 ?b))
(* ?a ?b) ==> (* ?b ?a)
(* ?a (* ?b ?c)) ==> (* (* ?a ?b) ?c)
(* ?a 0) ==> 0
(* ?a 1) ==> ?a
(* (/ ?a ?b) ?b) ==> (- ?a (% ?a ?b))
(* (max ?a ?b) (min ?a ?b)) ==> (* ?a ?b)
(/ (* ?y ?x) ?x) ==> ?y
(<= ?x ?y) ==> (! (< ?y ?x))
(! (< ?y ?x)) ==> (<= ?x ?y)
(>= ?x ?y) ==> (! (< ?x ?y))
(! (== ?x ?y)) ==> (!= ?x ?y)
(! (! ?x)) ==> ?x
(> ?x ?z) ==> (< ?z ?x)
(< ?x ?y) ==> (< (* -1 ?y) (* -1 ?x))
(< ?a ?a) ==> 0
(< (+ ?x ?y) ?z) ==> (< ?x (- ?z ?y))
(< ?z (+ ?x ?y)) ==> (< (- ?z ?y) ?x)
(< (- ?a ?y) ?a ) ==> 1 if (> ?y 0)
(< 0 ?y ) ==> 1 if (> ?y 0)
(< ?y 0 ) ==> 1 if (< ?y 0)
( < ( min ?x ?y ) ?x ) ==> ( < ?y ?x )
( < ( min ?z ?y ) ( min ?x ?y ) ) ==> ( < ?z ( min ?x ?y ) )
( < ( max ?z ?y ) ( max ?x ?y ) ) ==> ( < ( max ?z ?y ) ?x )
( < ( min ?z ?y ) ( min ?x ( + ?y ?c0 ) ) ) ==> ( < ( min ?z ?y ) ?x ) if (> ?c0 0)
( < ( max ?z ( + ?y ?c0 ) ) ( max ?x ?y ) ) ==> ( < ( max ?z ( + ?y ?c0 ) ) ?x ) if (> ?c0 0)
( < ( min ?z ( + ?y ?c0 ) ) ( min ?x ?y ) ) ==> ( < ( min ?z ( + ?y ?c0 ) ) ?x ) if (< ?c0 0)
( < ( max ?z ?y ) ( max ?x ( + ?y ?c0 ) ) ) ==> ( < ( max ?z ?y ) ?x ) if (< ?c0 0)
( < ( min ?x ?y ) (+ ?x ?c0) ) ==> 1 if (> ?c0 0)
(< (max ?a ?c) (min ?a ?b)) ==> 0
(< (* ?x ?y) ?z) ==> (< ?x ( / (- ( + ?z ?y ) 1 ) ?y ) )) if (> ?y 0)
(< ?y (/ ?x ?z)) ==> ( < ( - ( * ( + ?y 1 ) ?z ) 1 ) ?x ) if (> ?z 0)
(< ?a (% ?x ?b)) ==> 1 if (<= ?a (- 0 (abs ?b)))
(< ?a (% ?x ?b)) ==> 0 if (>= ?a (abs ?b))
(min ?a ?b) ==> (min ?b ?a)
(min (min ?x ?y) ?z) ==> (min ?x (min ?y ?z))
(min ?x ?x) ==> ?x
(min (max ?x ?y) ?x) ==> ?x
(min (max ?x ?y) (max ?x ?z)) ==> (max (min ?y ?z) ?x)
(min (max (min ?x ?y) ?z) ?y) ==> (min (max ?x ?z) ?y)
(min (+ ?a ?b) ?c) ==> (+ (min ?b (- ?c ?a)) ?a)
(+ (min ?x ?y) ?z) ==> (min (+ ?x ?z) (+ ?y ?z))
(min ?x (+ ?x ?a)) ==> ?x if (> ?a 0)
(min ?x (+ ?x ?a)) ==> (+ ?x ?a) if (< ?a 0)
(* (min ?x ?y) ?z) ==> (min (* ?x ?z) (* ?y ?z)) if (> ?z 0)
(min (* ?x ?z) (* ?y ?z)) ==> (* (min ?x ?y) ?z) if (> ?z 0)
(* (min ?x ?y) ?z) ==> (max (* ?x ?z) (* ?y ?z)) if (< ?z 0)
(max (* ?x ?z) (* ?y ?z)) ==> (* (min ?x ?y) ?z) if (< ?z 0)
(/ (min ?x ?y) ?z) ==> (min (/ ?x ?z) (/ ?y ?z)) if (> ?z 0)
(min (/ ?x ?z) (/ ?y ?z)) ==> (/ (min ?x ?y) ?z) if (> ?z 0)
(/ (max ?x ?y) ?z) ==> (min (/ ?x ?z) (/ ?y ?z)) if (< ?z 0)
(min (/ ?x ?z) (/ ?y ?z)) ==> (/ (max ?x ?y) ?z) if (< ?z 0)
( min ( max ?x ?c0 ) ?c1 ) ==> ?c1 if (<= ?c1 ?c0)
( min ( * ( / ?x ?c0 ) ?c0 ) ?x ) ==> ( * ( / ?x ?c0 ) ?c0 ) if (> ?c0 0)
(min (% ?x ?c0) ?c1) ==> (% ?x ?c0) if (>= ?c1 (- (abs ?c0) 1))
(min (% ?x ?c0) ?c1) ==> ?c1 if (<= ?c1 (- 0 (abs (+ ?c0 1))))
( min ( max ?x ?c0 ) ?c1 ) ==> ( max ( min ?x ?c1 ) ?c0 ) if (<= ?c0 ?c1)
( max ( min ?x ?c1 ) ?c0 ) ==> ( min ( max ?x ?c0 ) ?c1 ) if (<= ?c0 ?c1)
( < ( min ?y ?c0 ) ?c1 ) ==> ( || ( < ?y ?c1 ) ( < ?c0 ?c1 ) )
( < ( max ?y ?c0 ) ?c1 ) ==> ( && ( < ?y ?c1 ) ( < ?c0 ?c1 ) )
( < ?c1 ( max ?y ?c0 ) ) ==> ( || ( < ?c1 ?y ) ( < ?c1 ?c0 ) )
( min ( * ?x ?a ) ?b ) ==> ( * ( min ?x ( / ?b ?a ) ) ?a ) if (&& (> ?a 0) (== (% ?b ?a) 0))
( min ( * ?x ?a ) ( * ?y ?b ) ) ==> ( * ( min ?x ( * ?y ( / ?b ?a ) ) ) ?a ) if (&& (> ?a 0) (== (% ?b ?a) 0))
( min ( * ?x ?a ) ?b ) ==> ( * ( max ?x ( / ?b ?a ) ) ?a ) if (&& (< ?a 0) (== (% ?b ?a) 0))
( min ( * ?x ?a ) ( * ?y ?b ) ) ==> ( * ( max ?x ( * ?y ( / ?b ?a ) ) ) ?a ) if (&& (< ?a 0) (== (% ?b ?a) 0))
(% 0 ?x) ==> 0
(% ?x ?x) ==> 0
(% ?x 1) ==> 0
(% ?x ?c1) ==> (% (+ ?x ?c1) ?c1) if (<= ?c1 (abs ?x))
(% ?x ?c1) ==> (% (- ?x ?c1) ?c1) if (<= ?c1 (abs ?x))
(% (* ?x -1) ?c) ==> (* -1 (% ?x ?c))
(* -1 (% ?x ?c)) ==> (% (* ?x -1) ?c)
(% (- ?x ?y) 2) ==> (% (+ ?x ?y) 2)
( % ( + ( * ?x ?c0 ) ?y ) ?c1 ) ==> ( % ?y ?c1 ) if (&& (!= ?c1 0) (== (% ?c0 ?c1) 0))
(% (* ?c0 ?x) ?c1) ==> 0 if (&& (!= ?c1 0) (== (% ?c0 ?c1) 0))
"#;

fn read_rules(rules: &str) -> Ruleset<Pred> {
    let mut ruleset = Ruleset::default();
    for line in rules.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let rule: Result<_, _> = Rule::from_string(line);
        if let Ok((rule, _)) = rule {
            if rule.is_valid() {
                ruleset.add(rule);
            } else {
                println!("Failed to validate rule: {}", line);
            }
        } else {
            println!("Failed to parse rule: {}", line);
        }
    }

    ruleset
}

// The naive O(n^2) algorithm to build implications.
// Good for what we'll expect to see in the Caviar
// eval; bad for large sets of assumptions generated
// bottom-up.
fn pairwise_implication_building<L: SynthLanguage>(
    assumptions: &[Assumption<L>],
) -> ImplicationSet<L> {
    let mut implications = ImplicationSet::default();
    for a1 in assumptions {
        for a2 in assumptions {
            let name = format!("{a1} -> {a2}");
            let implication = Implication::new(name.into(), a1.clone(), a2.clone());
            if let Ok(implication) = implication {
                if !implications.contains(&implication) && implication.is_valid() {
                    implications.add(implication);
                }
            }
        }
    }
    implications
}

struct DerivabilityResult<L: SynthLanguage> {
    can: Ruleset<L>,
    cannot: Ruleset<L>,
}

fn run_derivability_tests<L: SynthLanguage>(
    base: &Ruleset<L>,
    against: &Ruleset<L>,
    implications: &ImplicationSet<L>,
) -> DerivabilityResult<L> {
    let impl_rules = implications.to_egg_rewrites();

    let (can, cannot) = base.derive(
        ruler::DeriveType::LhsAndRhs,
        against,
        Limits::deriving(),
        Some(&impl_rules),
    );

    DerivabilityResult { can, cannot }
}

pub fn get_derivability_results(
    ours: Ruleset<Pred>,
    against: Against,
    output_path: String,
    only_conditional: bool,
) {
    // remove the ".txt" from output_path, and add "against_halide.json" or "against_caviar.json"
    let output_path = if output_path.ends_with(".txt") {
        format!(
            "{}{}",
            &output_path[..output_path.len() - 4],
            match against {
                Against::Halide => "_against_halide.json",
                Against::Caviar => "_against_caviar.json",
            }
        )
    } else {
        panic!("Output path must end with .txt");
    };

    let against: Ruleset<Pred> = match against {
        Against::Halide => read_rules(HALIDE_RULES),
        Against::Caviar => read_rules(CAVIAR_RULES),
    };

    let all_conditions: Vec<_> = against
        .iter()
        .chain(ours.iter())
        .filter_map(|r| {
            r.cond.as_ref().and_then(|c| {
                Assumption::new(
                    Pred::generalize(
                        &Pred::instantiate(&c.chop_assumption()),
                        &mut Default::default(),
                    )
                    .to_string(),
                )
                .ok()
            })
        })
        .collect();

    let mut all_conditions = all_conditions.clone();
    all_conditions.sort_by(|a, b| a.to_string().cmp(&b.to_string()));
    all_conditions.dedup();

    let mut implication_rules: ImplicationSet<Pred> =
        pairwise_implication_building(&all_conditions);

    let and_implies_left: Implication<Pred> = Implication::new(
        "and_implies_left".into(),
        Assumption::new("(&& ?a ?b)".to_string()).unwrap(),
        Assumption::new_unsafe("?a".to_string()).unwrap(),
    )
    .unwrap();

    let and_implies_right: Implication<Pred> = Implication::new(
        "and_implies_right".into(),
        Assumption::new("(&& ?a ?b)".to_string()).unwrap(),
        Assumption::new_unsafe("?b".to_string()).unwrap(),
    )
    .unwrap();

    implication_rules.add(and_implies_left);
    implication_rules.add(and_implies_right);

    let keep_conditional = |rs: &Ruleset<Pred>| -> Ruleset<Pred> {
        let (conditional, _) = rs.partition(|r| r.cond.is_some());
        conditional
    };

    let against_forward = if only_conditional {
        &keep_conditional(&against)
    } else {
        &against
    };

    let ours_backward = if only_conditional {
        &keep_conditional(&ours)
    } else {
        &ours
    };

    let forward_result = run_derivability_tests(&ours, against_forward, &implication_rules);

    let backward_result = run_derivability_tests(&against, ours_backward, &implication_rules);

    let to_json = |result: DerivabilityResult<Pred>| {
        serde_json::json!({
            "can": result.can.iter().map(|r| r.to_string()).collect::<Vec<_>>(),
            "cannot": result.cannot.iter().map(|r| r.to_string()).collect::<Vec<_>>(),
        })
    };

    let to_write = serde_json::json!({
        "forwards": to_json(forward_result),
        "backwards": to_json(backward_result),
    });

    println!("wrote derivability results to {}", output_path);

    std::fs::write(
        output_path,
        serde_json::to_string_pretty(&to_write).unwrap(),
    )
    .expect("Failed to write derivability results to file");
}
