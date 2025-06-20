use ruler::{halide, llm};
use ruler::halide::Pred;
use ruler::enumo::{Ruleset, Workload};
use ruler::json_to_recipe;

use ruler::halide::{og_recipe, og_recipe_no_conditions};
use ruler::{ConditionRecipe, Recipe};

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
    OgRecipeNoConditions,
}

impl FromStr for RecipeType {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "og_recipe" => Ok(Self::OgRecipe),
            "og_recipe_no_conditions" => Ok(Self::OgRecipeNoConditions),
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
                        RecipeType::OgRecipeNoConditions => og_recipe_no_conditions(),
                    }
                },
                (None, Some(recipe_path)) => {
                    // let recipe = json_to_recipe(recipe_path.to_str().unwrap());
                    // recipe_to_rules(&recipe)
                    Default::default()
                }
                (Some(_), Some(_)) => panic!("both recipe types provided."),
                (None, None) => panic!("no recipe type provided.")

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
    // TODO: @ninehusky -- in the eval, this should be replaced eventually with reading straight from the JSON representing
    // the handwritten recipe.
    let minmax_recipe = Recipe {
        name: "minmax".to_string(),
        max_size: 7,
        vals: vec!["-1".to_string(), "0".to_string(), "1".to_string(), "2".to_string()],
        vars: vec!["a".to_string(), "b".to_string(), "c".to_string()],
        ops: vec![
            vec!["!".to_string()],
            vec!["==".to_string(), "!=".to_string(), "<".to_string(), ">".to_string(), "<=".to_string(), ">=".to_string(), "min".to_string(), "max".to_string(),
                "&&".to_string(), "||".to_string()], // Conditional operators
        ],
        conditions: None,
    };

    let bool_recipe = Recipe {
        name: "bool".to_string(),
        max_size: 5,
        vals: vec!["0".to_string(), "1".to_string()],
        vars: vec!["a".to_string(), "b".to_string(), "c".to_string()],
        ops: vec![
            vec!["!".to_string()],
            vec!["&&".to_string(), "||".to_string()],
        ],
        conditions: None,
    };

    let rat_recipe = Recipe {
        name: "rat".to_string(),
        max_size: 5,
        vals: vec!["-1".to_string(), "0".to_string(), "1".to_string(), "2".to_string()],
        vars: vec!["a".to_string(), "b".to_string(), "c".to_string()],
        ops: vec![
            vec![],
            vec!["+".to_string(), "-".to_string(), "*".to_string(), "/".to_string()],
        ],
        conditions: Some(
            ConditionRecipe {
                max_size: 7,
                ops: vec![vec![],
                    vec!["<".to_string(), "<=".to_string(), "!=".to_string(), "&&".to_string(), "||".to_string()],
                ],
                vals: vec!["0".to_string()],
            }
        )
    };

    let min_lt_le_recipe = Recipe {
        name: "min_lt_le".to_string(),
        max_size: 7,
        vals: vec![],
        vars: vec!["a".to_string(), "b".to_string(), "c".to_string()],
        ops: vec![
            vec![],
            vec!["!".to_string()],
            vec!["<".to_string(), "<=".to_string(), "min".to_string(), "&&".to_string(), "||".to_string()],
        ],
        conditions: None,
    };

    let recipe_list = vec![bool_recipe, rat_recipe, minmax_recipe, min_lt_le_recipe];

    let mut prior_ruleset: Ruleset<Pred> = Ruleset::default();

    for recipe in recipe_list {
        let vars = recipe.vars.clone();
        let cond_recipe = recipe.conditions.clone();
        let (workload, mut cond_r) = llm::generate_alphabet_soup(&recipe, cond_recipe.as_ref()).await;
        if let Some(c) = cond_r {
            // we append `vars` here because without them, we don't get the correct cvec length.
            cond_r = Some(c.append(Workload::new(vars.clone())));
        }
        // let ruleset = halide::soup_to_rules(
        //     &workload,
        //     cond_r.as_ref(),
        //     &prior_ruleset,
        //     recipe.max_size
        // );
        let ruleset = Default::default();

        prior_ruleset.extend(ruleset);
    }

    prior_ruleset
}
