use ruler::enumo::Ruleset;
use ruler::halide::mini_recipe;
use ruler::halide::Pred;

use ruler::halide::og_recipe;
use ruler::recipe_utils::LLMEnumerationConfig;
use ruler::recipe_utils::LLMFilterConfig;
use ruler::recipe_utils::LLMUsage;

use std::fs::File;
use std::path::PathBuf;
use std::str::FromStr;

use clap::Parser;

// Outlines how to perform Halide rule synthesis.
#[derive(Debug)]
pub enum Recipe {
    MiniRecipe,
    FullRecipe,
}

impl FromStr for Recipe {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "mini" => Ok(Self::MiniRecipe),
            "full" => Ok(Self::FullRecipe),
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
    let default_enum_cfg = LLMEnumerationConfig::default().with_num_conditions(20).with_num_terms(100);

    let llm_usage = match args.llm_usage.as_str() {
        "baseline" => LLMUsage::None,
        "enum_only" => LLMUsage::EnumerationOnly(default_enum_cfg.clone()),
        "baseline_andenum" => LLMUsage::Enumeration(default_enum_cfg.clone()),
        "baseline_and_filter_1" => LLMUsage::Filter(default_filter_cfg.clone().with_top_k(1)),
        "baseline_and_filter_5" => LLMUsage::Filter(default_filter_cfg.clone().with_top_k(5)),
        "baseline_with_filter_5_and_enum" => LLMUsage::Combined(
            vec![
                LLMUsage::Filter(default_filter_cfg.clone()),
                LLMUsage::Enumeration(default_enum_cfg.clone()),
            ]
        ),
        _ => panic!("Invalid llm_usage"),
    };

    // create the output file if it doesn't exist.

    if let Err(e) = File::create(&args.output_path) {
        panic!("Failed to create output file: {}", e);
    }

    let rules = match args.recipe {
        Recipe::MiniRecipe => mini_recipe(llm_usage).await,
        Recipe::FullRecipe => og_recipe(llm_usage).await,
    };

    rules.to_file(&args.output_path);

    println!("Wrote {} rules to {:?}", rules.len(), args.output_path);
}
