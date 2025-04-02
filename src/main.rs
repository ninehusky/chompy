use ruler::{halide, llm};
use ruler::halide::Pred;
use ruler::enumo::Ruleset;
use ruler::json_to_recipe;

use ruler::halide::recipe_to_rules;
use ruler::Recipe;

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

#[derive(Parser, Debug)]
struct ChompyArgs {
    #[clap(short, long)]
    mode: ChompyMode,
    #[clap(short, long)]
    output_path: PathBuf,
    #[clap(short, long)]
    recipe_path: Option<PathBuf>,
}

#[tokio::main]
pub async fn main() {
    let args = ChompyArgs::parse();
    println!("args: {:?}", args);
    // second to last argument is the mode.
    let mode = args.mode;
    // last argument is the output file path.
    let output_file = args.output_path;
    // create the output file if it doesn't exist.
    if let Err(e) = File::create(output_file.clone()) {
        panic!("Failed to create output file: {}", e);
    }
    let rules = match mode {
        ChompyMode::HandwrittenRecipe => {
            // make this path relative to this file.
            let recipe_path = args.recipe_path.unwrap();
            let recipe = json_to_recipe(recipe_path.to_str().unwrap());
            recipe_to_rules(&recipe)
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
    // let equality_recipe = Recipe {
    //     max_size: 5,
    //     vals: vec!["-1".to_string(), "0".to_string(), "1".to_string(), "2".to_string()],
    //     vars: vec!["a".to_string(), "b".to_string(), "c".to_string()],
    //     ops: vec![
    //         vec![],
    //         vec!["!".to_string()],
    //         vec!["==".to_string(), "!=".to_string(), "<".to_string(), ">".to_string(), "<=".to_string(), ">=".to_string(), "min".to_string(), "max".to_string()], // Conditional operators
    //     ],
    // };

    // let equality_cond_recipe = None;

    // let bool_recipe = Recipe {
    //     max_size: 5,
    //     vals: vec!["0".to_string(), "1".to_string()],
    //     vars: vec!["a".to_string(), "b".to_string(), "c".to_string()],
    //     ops: vec![
    //         vec![],
    //         vec!["!".to_string()],
    //         vec!["&&".to_string(), "||".to_string()],
    //     ],
    // };

    // let bool_cond_recipe = None;

    // let rat_recipe = Recipe {
    //     max_size: 5,
    //     vals: vec!["-1".to_string(), "0".to_string(), "1".to_string(), "2".to_string()],
    //     vars: vec!["a".to_string(), "b".to_string(), "c".to_string()],
    //     ops: vec![
    //         vec![],
    //         vec!["abs".to_string()],
    //         vec!["+".to_string(), "-".to_string(), "*".to_string(), "/".to_string()],
    //     ],
    // };

    // let rat_cond_recipe = Some(Recipe {
    //     max_size: 3,
    //     vals: vec!["0".to_string()],
    //     vars: rat_recipe.vars.clone(),
    //     ops: vec![
    //         vec![],
    //         vec![],
    //         vec!["<".to_string(), "<=".to_string(), "!=".to_string()],
    //     ],
    // });

    // let min_lt_le_recipe = Recipe {
    //     max_size: 7,
    //     vals: vec![],
    //     vars: vec!["a".to_string(), "b".to_string(), "c".to_string()],
    //     ops: vec![
    //         vec![],
    //         vec!["!".to_string()],
    //         vec!["<".to_string(), "<=".to_string(), "min".to_string(), "&&".to_string(), "||".to_string()],
    //     ]
    // };

    // let min_lt_le_cond_recipe = None;

    // let recipe_list = vec![
    //     (equality_recipe, equality_cond_recipe),
    //     (bool_recipe, bool_cond_recipe),
    //     (rat_recipe, rat_cond_recipe),
    //     (min_lt_le_recipe, min_lt_le_cond_recipe)
    // ];

    let mut prior_ruleset: Ruleset<Pred> = Ruleset::default();

    // for (recipe, cond_recipe) in recipe_list {
    //     let (workload, cond_r) = llm::generate_alphabet_soup(&recipe, cond_recipe.as_ref()).await;
    //     let ruleset = halide::soup_to_rules(
    //         &workload,
    //         cond_r.as_ref(),
    //         &prior_ruleset,
    //         recipe.max_size
    //     );

    //     prior_ruleset.extend(ruleset);
    // }

    prior_ruleset
}
