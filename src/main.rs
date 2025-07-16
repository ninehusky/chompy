use ruler::halide::Pred;
use ruler::enumo::{Ruleset};

use ruler::halide::{og_recipe};

use std::fs::File;
use std::path::PathBuf;
use std::str::FromStr;

use clap::Parser;

// Outlines how to perform Halide rule synthesis.
#[derive(Debug)]
pub enum ChompyMode {
    HandwrittenRecipe,
    LLMAlphabetSoup,
    LLMRecipe,
}

impl FromStr for ChompyMode {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "handwritten" => Ok(Self::HandwrittenRecipe),
            "llm_alphabet_soup" => Ok(Self::LLMAlphabetSoup),
            "llm_recipes" => Ok(Self::LLMRecipe),
            _ => Err("Invalid mode.".to_string()),
        }
    }
}

#[derive(Debug)]
pub enum RecipeType {
    // what we used to run: the default recipe with added nesting
    // that we can't express in the JSON format.
    OgRecipe,
}

impl FromStr for RecipeType {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "og_recipe" => Ok(Self::OgRecipe),
            _ => Err("Invalid recipe type.".to_string()),
        }
    }
}


#[derive(Parser, Debug)]
struct ChompyArgs {
    #[clap(long)]
    mode: ChompyMode,
    #[clap(long)]
    output_path: PathBuf,
    #[clap(long)]
    recipe_path: Option<PathBuf>,
    #[clap(long)]
    old_recipe_type: Option<String>,
}

#[tokio::main]
pub async fn main() {
    let args = ChompyArgs::parse();
    let mode = args.mode;
    let output_file = args.output_path;

    // create the output file if it doesn't exist.
    if let Err(e) = File::create(output_file.clone()) {
        panic!("Failed to create output file: {}", e);
    }
    let rules = match mode {
        ChompyMode::HandwrittenRecipe => {
            let old_recipe_type = args.old_recipe_type;
            let recipe_path = args.recipe_path;
            match (old_recipe_type, recipe_path) {
                (Some(recipe_type), None) => {
                    let recipe: RecipeType = recipe_type.parse().unwrap();
                    match recipe {
                        RecipeType::OgRecipe => og_recipe(),
                    }
                },
                (Some(_), Some(_)) => panic!("both recipe types provided."),
                (None, _) => panic!("no recipe type provided.")

            }
        }
        ChompyMode::LLMAlphabetSoup => {
            run_gpt_eval().await
        }
        ChompyMode::LLMRecipe => {
            todo!("Not implemented yet.");
        }
    };
    rules.to_file(output_file.to_str().unwrap());
}


pub async fn run_gpt_eval() -> Ruleset<Pred> {
    todo!("This is pretty out of date.");
}
