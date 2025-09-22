use egg::RecExpr;
use rand::rngs::StdRng;
use rand::seq::SliceRandom;
use rand::{thread_rng, SeedableRng};
use reqwest::Client;
use serde::{Deserialize, Serialize};
use serde_json::json;
use sha2::{Digest, Sha256};

use std::fmt::Display;
use std::fs;
use std::path::Path;

use crate::enumo::{Rule, Ruleset, Sexp};
use crate::halide::{get_type, HalideType};
use crate::recipe_utils::iter_metric;
use crate::{enumo::Workload, halide::Pred, SynthLanguage};

use crate::{ConditionRecipe, HashMap, HashSet, IndexMap, Recipe};

pub type CategorizedRuleset<L> = IndexMap<String, Ruleset<L>>;

const CACHE_DIR: &str = "llm_cached";

#[derive(Serialize, Deserialize)]
struct CacheEntry {
    prompt: String,
    model: String,
    response: String,
}

fn hash_request(prompt: &str, model: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(prompt.as_bytes());
    hasher.update(model.as_bytes());
    format!("{:x}", hasher.finalize())
}

const SCORE_RULES_PROMPT: &str = r#"
You are an expert in program optimization and algebraic reasoning.

You will be given:
- A set of existing rewrite rules already accepted.
- A batch of new candidate rewrite rules that are valid.

Your task: For each candidate, assign 3 scores (0–5, where 5 is best):
1. CORE — How strongly this rule expresses a core algebraic property:
   - Distributivity
   - Associativity
   - Commutativity
   - Idempotence
   - Absorption
   - Homomorphism-like transformation
2. IMPORTANCE — How useful this rule is for general simplification and optimization.
3. NOVELTY — How different it is from existing rules; 0 if it’s basically redundant.

Definitions:
- A high CORE score means it clearly expresses a fundamental operator law.
- A high IMPORTANCE score means it can apply in many contexts and enables simplifications.
- A high NOVELTY score means it’s not just a renamed version of existing rules.

Format:
<rule> — CORE:<0–5> — IMPORTANCE:<0–5> — NOVELTY:<0–5>

Existing rules:
prior_text

Candidate rules:
candidates_text
"#;

const GROUP_RULES_PROMPT: &str = r#"
You are the world’s leading expert in program optimization and algebraic reasoning.
You are helping organize rewrite rules for use in an equality saturation system.

You will be given a batch of valid candidate rewrite rules.

Your goal:
  - Group the rules into semantic categories according to what they do.
  - If a rule produces a RHS that is **structurally smaller than the LHS** (fewer operators, less nesting), place it in its own category.
  - If a rule produces a RHS that is **more canonical or normalized** (terms reordered into standard order, consistent structure), place it in its own category.
  - If a rule produces a RHS that is **more balanced or symmetric** than the LHS, place it in its own category.
  - Do not lump simplifications with rules that merely reshuffle or perform minor transformations.
  - Single out important rewrite patterns like idempotency, distributivity, or constant simplifications: they should always get their own category, even if there are only one or two rules of that type.
  - Do not group rules together just because they use the same operators; create new categories for meaningful semantic differences.
  - Place each rule under exactly one category.
  - Remove rules which just look like noise.
  - Strive to capture semantic differences clearly, even if that results in more categories than before.
  - Avoid redundant categories; rules that are semantically similar should be grouped together.

Format your output like this:

Category: <brief description of transformation>
<rule 1>
<rule 2>
...

Category: <next transformation>
<rule 1>
<rule 2>
...

Do not output numeric hints, explanations, or any other text. Only output the categories and rules.

Example Input:
(+ (* ?a 1) ?b) ==> (+ ?b (* ?a 1))
(/ ?a ?a) ==> 1 if (!= ?a 0)
(+ ?a (+ ?b ?c)) ==> (+ ?a (+ ?c ?b))
(min ?a (+ ?a ?b)) ==> (+ ?a ?b) if (< ?b 0)
(+ (+ ?a ?b) (* ?c 1)) ==> (+ (* ?c 1) (+ ?b ?a))
(max (+ ?a ?b) ?c) ==> (max (+ ?b ?a) ?c)
(< ?a (+ ?a ?b)) ==> (< ?a (+ ?b ?a))
(* ?a (* ?b ?c)) ==> (* ?a (* ?c ?b))
(+ (+ ?a ?b) (+ ?c ?d)) ==> (+ (+ ?b ?a) (+ ?d ?c))
(< (?a (+ ?b ?c))) ==> (< ?a (+ ?c ?b)) if (!= ?b 0)
(min ?a ?b) ==> ?a if (< ?a ?b)
(* (* ?a ?b) ?c) ==> (* (* ?b ?a) ?c)
(< (+ ?a ?b) (+ ?b ?a)) ==> 0 if (== ?a ?b)
(min (+ ?a ?b) ?c) ==> (+ ?a (min ?b ?c)) if (< ?a ?c)
(+ ?a (* ?b 0)) ==> ?a if (>= ?b 0)
(+ ?a (+ ?b ?c)) ==> (+ ?b (+ ?a ?c))
(< (+ ?a ?b) (+ ?b ?a)) ==> (< (+ ?b ?a) (+ ?a ?b))
(/ ?a ?a) ==> 1 if (> ?a 0)
(min ?a (+ ?b ?c)) ==> (min (+ ?c ?b) ?a)
(* ?a (+ ?b ?c)) ==> (+ (* ?a ?b) (* ?a ?c)) if (>= ?a 0)
(+ (+ ?a ?b) ?c) ==> (+ (+ ?b ?a) ?c)
(min ?a (+ ?b ?c)) ==> (min ?a (+ ?c ?b))

Example Output (Good):
Category: Simplifications for Division
(/ ?a ?a) ==> 1 if (!= ?a 0)
(/ ?a ?a) ==> 1 if (> ?a 0)

Category: Simplifications for Min
(min ?a ?b) ==> ?a if (< ?a ?b)
(min ?a (+ ?a ?b)) ==> (+ ?a ?b) if (< ?b 0)

Category: Constant Multiplication and Addition Simplifications
(+ ?a (* ?b 0)) ==> ?a if (>= ?b 0)
(+ (* ?a 1) ?b) ==> (+ ?b (* ?a 1))
(+ (+ ?a ?b) (* ?c 1)) ==> (+ (* ?c 1) (+ ?b ?a))

Category: Commutativity and Argument Shuffling
(+ ?a (+ ?b ?c)) ==> (+ ?a (+ ?c ?b))
(+ ?a (+ ?b ?c)) ==> (+ ?b (+ ?a ?c))
(* ?a (* ?b ?c)) ==> (* ?a (* ?c ?b))
(* (* ?a ?b) ?c) ==> (* (* ?b ?a) ?c)
(+ (+ ?a ?b) (+ ?c ?d)) ==> (+ (+ ?b ?a) (+ ?d ?c))
(+ (+ ?a ?b) ?c) ==> (+ (+ ?b ?a) ?c)
(max (+ ?a ?b) ?c) ==> (max (+ ?b ?a) ?c)

Category: Inequality Shuffles
(< ?a (+ ?a ?b)) ==> (< ?a (+ ?b ?a))
(< (+ ?a ?b) (+ ?b ?a)) ==> (< (+ ?b ?a) (+ ?a ?b))
(< (+ ?a ?b) (+ ?b ?a)) ==> 0 if (== ?a ?b)
(< (?a (+ ?b ?c))) ==> (< ?a (+ ?c ?b)) if (!= ?b 0)

Category: Min/Max Transformations
(min (+ ?a ?b) ?c) ==> (+ ?a (min ?b ?c)) if (< ?a ?c)
(min ?a (+ ?b ?c)) ==> (min (+ ?c ?b) ?a)
(min ?a (+ ?b ?c)) ==> (min ?a (+ ?c ?b))

Category: Distributivity of Multiplication over Addition
(* ?a (+ ?b ?c)) ==> (+ (* ?a ?b) (* ?a ?c)) if (>= ?a 0)

Category: Canonicalization / Reordering
(+ ?a (+ ?b ?c)) ==> (+ ?a (+ ?c ?b))
(+ ?a (+ ?b ?c)) ==> (+ ?b (+ ?a ?c))
(max (+ ?a ?b) ?c) ==> (max (+ ?b ?a) ?c)

Category: Structural Simplifications
(min ?a (+ ?a ?b)) ==> (+ ?a ?b) if (< ?b 0)
(/ ?a ?a) ==> 1 if (!= ?a 0)
(+ ?a (* ?b 0)) ==> ?a if (>= ?b 0)

Category: Balanced / Symmetric Transformations
(+ (+ ?a ?b) (+ ?c ?d)) ==> (+ (+ ?b ?a) (+ ?d ?c))
(+ (+ ?a ?b) ?c) ==> (+ (+ ?b ?a) ?c)

Input:
candidates_text
"#;

const FILTER_RULES_PROMPT: &str = r#"
You are an expert in program optimization and algebraic reasoning.

You will be given:
- A set of existing rewrite rules already accepted.
- A batch of new candidate rewrite rules that are valid, each annotated with numeric hints: CORE, IMPORTANCE, NOVELTY (higher values indicate higher importance).

Your goal:
- Select the TOP {keep_max} rules that are most semantically meaningful, non-redundant, and likely to be useful in optimization.
- Rules that express core operator laws should be strongly favored:
   - Distributivity (e.g., (f (g x y)) -> (f (g x) (g y)), with correct guards)
   - Associativity (grouping changes that preserve semantics)
   - Commutativity (order changes without altering meaning)
   - Idempotence (applying an operation twice has the same effect as once)
   - Absorption (one operator absorbs another)
   - Homomorphism-like transformations (distributing a function into multiple arguments)
- Use the numeric hints (CORE, IMPORTANCE, NOVELTY) as guidance.
- Avoid redundant rules: rules equivalent to existing ones, overly narrow, or achievable via sequences of simpler rules.

Instructions:
- Output **only the rules to KEEP**, one per line.
- Do not include scores, reasoning, or DROP rules.

Format:
<rule>

Existing rules:
prior_text

Candidate rules (with numeric hints):
candidates_text


"#;

const ENUMERATE_TERMS_PROMPT: &str = r#"
You are generating new terms in a small programming language.
The syntax is s-expressions with the following operators:
{operators}

You will be given a list of existing terms.
Your task is to propose additional terms that are:
- significantly different from the input set,
- likely to be useful in rewrite rules (e.g., distributivity, commutativity, associativity, idempotence),
- non-trivial (avoid constant-only terms unless they reduce to a single constant),
- and include variables in most cases.

Output requirements:
- Generate about {term_limit} additional terms.
- Produce a variety of sizes and shapes (not just shallow terms, include large terms as well).
- Ensure all terms are distinct and not repeats of the input.
- Output **only the terms**, one per line.
- Do not include any commentary, numbering, or explanations.
- Do not introduce any new variables outside the set given.
- Do not include any markdown backticks.

Example Input Terms:
x
y
0
1
(+ x y)
(abs x)

Example Output:
(+ (* x y) (* x z))
(* (+ x y) z)
(max (abs y) x)
(min x (+ y 1))
(- (* x 0) y)

Input Terms:
{input_text}
"#;

const ENUMERATE_CONDITIONS_PROMPT: &str = r#"
You are generating logical conditions in a small programming language.
The syntax is s-expressions with the following operators:
{operators}

You will be given a list of terms (expressions).
Your task is to propose additional conditions that are:
- syntactically valid Boolean expressions,
- useful for rewrite rules (e.g., inequalities, equalities, divisibility checks, non-negativity tests),
- non-trivial (avoid tautologies or contradictions like `(< x x)`),
- structurally diverse (use different operators and nesting where possible),
- and involve variables where possible.

Conditions can be:
- simple comparisons (like `(< x y)` or `(== a 0)`), or
- compound conditions using logical operators such as `(&& cond1 cond2)` or `(|| cond1 cond2)` when this makes them more useful for rewrite rules.
- assume that variables are numbers, don't enumerate stuff like `(&& a b)`.

Output requirements:
- Generate about {cond_limit} distinct conditions.
- Each condition must evaluate to a Boolean (true/false).
- Conditions should compare or test terms using operators such as <, <=, >, >=, ==, !=, and also include useful checks (e.g., remainder equal to zero, comparisons to constants).
- Output **only the conditions**, one per line.
- Do not repeat the input terms.
- Do not include commentary, numbering, or explanations.
- Do not include any markdown backticks.

Example Input Terms:
a
b
(* a b)
(% a b)

Example Output Conditions:
(< a 0)
(>= (* a b) 1)
(== (% a b) 0)
(!= a b)
(<= b (* a b))
(&& (> a 0) (< b a))

Input Terms:
{input_text}
"#;

fn term_size(sexp: &Sexp) -> usize {
    match sexp {
        Sexp::Atom(_) => 1,
        Sexp::List(children) => 1 + children.iter().map(term_size).sum::<usize>(),
    }
}

fn get_operator_description(terms: &Vec<Sexp>) -> String {
    let mut ops: HashMap<String, usize> = HashMap::default();
    for term in terms {
        if let Sexp::List(children) = term {
            if let Some(Sexp::Atom(op)) = children.first() {
                // ops[operator] = arity
                ops.insert(op.clone(), children.len() - 1);
            } else {
                panic!("Unexpected term format: {:?}", term);
            }
        }
    }

    let mut desc = String::new();
    for (op, arity) in ops {
        // <op>: arity <arity>
        desc.push_str(&format!("- {}: arity {}\n", op, arity));
    }
    desc
}

fn sample_terms(wkld: &Workload) -> Vec<String> {
    let mut rng = StdRng::seed_from_u64(42);
    let all_terms: Vec<Sexp> = wkld.force();
    let mut sampled = Vec::new();

    for size in 1..=10 {
        let mut bucket: Vec<Sexp> = all_terms
            .iter()
            .filter(|t| term_size(t) == size)
            .cloned()
            .collect();

        // Shuffle so we don't always pick the same ones
        bucket.shuffle(&mut rng);

        // Take up to 5 examples from this size
        sampled.extend(bucket.into_iter().take(5));
    }

    sampled.iter().map(|s| s.to_string()).collect()
}

pub async fn send_openai_request(client: &Client, prompt: String) -> Result<String, String> {
    // Build the request payload
    let model = "gpt-4o";
    let h = hash_request(&prompt, model);
    let cache_file = format!("{}/{}.json", CACHE_DIR, h);

    // Replay mode
    if std::env::var("FAKE_LLM").is_ok() {
        if Path::new(&cache_file).exists() {
            let cached = fs::read_to_string(&cache_file)
                .map_err(|e| format!("Failed to read cache: {e}"))?;
            let cached_json: serde_json::Value =
                serde_json::from_str(&cached).map_err(|e| format!("Bad cached JSON: {e}"))?;

            if let Some(resp) = cached_json["response"].as_str() {
                println!("(replay) Using cached LLM response for {}", h);
                return Ok(resp.to_string());
            } else {
                return Err(format!("Cached file missing 'response' field for {}", h));
            }
        } else {
            // return Err(format!("No cached response found for h {}", h));
            println!("We have to make a new API call!");
        }
    }


    let request_body = json!({
        "model": model,
        "messages": [
            { "role": "system", "content": prompt }
        ],
        "temperature": 0.0,
        "max_tokens": 1500
    });

    // Send the request
    let response = client
        .post("https://api.openai.com/v1/chat/completions")
        .header(
            "Authorization",
            format!(
                "Bearer {}",
                std::env::var("OPENAI_API_KEY").expect("OPENAI_API_KEY not set")
            ),
        )
        .header("Content-Type", "application/json")
        .json(&request_body)
        .send()
        .await
        .map_err(|e| format!("Failed: {e}"))?;

    let response_json: serde_json::Value = response
        .json()
        .await
        .map_err(|e| format!("Failed to parse response: {e}"))?;

    // Return raw text content
    let text_output = response_json["choices"][0]["message"]["content"]
        .as_str()
        .unwrap_or("")
        .to_string()
        .replace("`", ""); // Strip markdown backticks if any

    println!("OUTPUT:\n{}", text_output);

    // Save to cache
    fs::create_dir_all(CACHE_DIR).ok();
    let entry = CacheEntry {
        prompt,
        model: model.to_string(),
        response: text_output.clone(),
    };
    fs::write(&cache_file, serde_json::to_string_pretty(&entry).unwrap())
        .map_err(|e| format!("Failed to write cache: {e}"))?;

    Ok(text_output)
}

pub async fn get_llm_terms<L: SynthLanguage>(
    client: &Client,
    terms: &Workload,
    limit: usize,
) -> Workload {
    let representative_terms = sample_terms(terms);
    // 1. Send the request to the LLM.
    let input_text = representative_terms.join("\n");

    let prompt_text = ENUMERATE_TERMS_PROMPT
        .replace("{input_text}", &input_text)
        .replace("{term_limit}", &limit.to_string())
        .replace("{operators}", &get_operator_description(&terms.force()));

    println!("PROMPT TEXT:\n{}", prompt_text);

    let response = send_openai_request(client, prompt_text).await.unwrap();

    // 2. Parse the response into a list of strings.
    println!("LLM TERMS RESPONSE:\n{}", response);

    let mut final_wkld = Workload::empty();
    for line in response.lines() {
        // Attempt to parse it as a RecExpr<Pred>.
        let recexpr: Result<RecExpr<L>, _> = line.parse();
        if let Ok(re) = recexpr {
            final_wkld = final_wkld.append(Workload::new(&[re.to_string()]));
        } else {
            println!("failed to parse term: {}", line);
        }
    }

    final_wkld
}

pub async fn get_llm_conditions<L: SynthLanguage>(
    client: &Client,
    cond_terms: &Workload,
    terms: &Workload,
    limit: usize,
) -> Workload {
    let representative_terms = sample_terms(terms);
    // 1. Send the request to the LLM.
    let input_text = representative_terms.join("\n");

    let prompt_text = ENUMERATE_TERMS_PROMPT
        .replace("{input_text}", &input_text)
        .replace("{cond_limit}", &limit.to_string())
        .replace(
            "{operators}",
            &get_operator_description(&cond_terms.force()),
        );

    println!("PROMPT TEXT:\n{}", prompt_text);

    let response = send_openai_request(client, prompt_text).await.unwrap();

    println!("LLM CONDITIONS RESPONSE:\n{}", response);

    let mut working_wkld = Workload::empty();
    for line in response.lines() {
        // Attempt to parse it as a RecExpr<Pred>.
        let recexpr: Result<RecExpr<L>, _> = line.parse();
        if let Ok(re) = recexpr {
            working_wkld = working_wkld.append(Workload::new(&[re.to_string()]));
        } else {
            println!("failed to parse term: {}", line);
        }
    }

    let mut final_wkld = Workload::empty();

    for sexp in working_wkld.force() {
        let calculated_type = get_type(&sexp, None);
        match calculated_type {
            Some(HalideType::BoolType) => {
                final_wkld = final_wkld.append(Workload::new(&[sexp.to_string()]));
            }
            _ => {
                println!("skipping non-bool condition: {}", sexp);
            }
        };
    }

    final_wkld
}

#[tokio::test]
async fn get_llm_ammo_test() {
    let wkld = Workload::new(&["(OP2 V V)", "V"])
        .plug("V", &Workload::new(&["a", "b", "c", "0", "1"]))
        .plug("OP2", &Workload::new(&["+", "-", "*", "/", "min", "max"]));

    let cond_wkld = Workload::new(&["(OP2 V V)", "V"])
        .plug("V", &Workload::new(&["a", "b", "c", "0", "1"]))
        .plug("OP2", &Workload::new(&["<", "<=", "==", "!="]));

    let client = Client::new();
    let terms = get_llm_terms::<Pred>(&client, &wkld, 50).await;
    let conds = get_llm_conditions::<Pred>(&client, &cond_wkld, &wkld, 50).await;

    println!("LLM TERMS:");
    for t in terms.force() {
        println!("{}", t);
    }

    println!("LLM CONDITIONS:");
    for c in conds.force() {
        println!("{}", c);
    }
}

fn parse_categorization_response<L: SynthLanguage>(response: String) -> CategorizedRuleset<L> {
    let mut result: CategorizedRuleset<L> = Default::default();
    let mut current_category: Option<String> = None;

    for line in response.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }

        if let Some(stripped) = line.strip_prefix("Category:") {
            current_category = Some(stripped.trim().to_string());
        } else if let Some(ref category) = current_category {
            let ruleset = result.entry(category.clone()).or_default();
            // Treat it as a rule
            match Rule::from_string(line) {
                Ok((fwd, bkwd)) => {
                    ruleset.add(fwd);
                    if let Some(bkwd) = bkwd {
                        ruleset.add(bkwd);
                    }
                }
                Err(e) => {
                    // Handle parsing error, could log warning
                    eprintln!("Error parsing rule '{line}': {e}");
                    continue; // Skip this line
                }
            }
        } else {
            // Line outside of a category, could log warning
            eprintln!("Warning: rule found outside of a category: {line}");
        }
    }
    result
}

pub async fn sort_rule_candidates<L: SynthLanguage>(
    client: &Client,
    candidates: Ruleset<L>,
    batch_size: usize,
) -> CategorizedRuleset<L> {
    let mut result: CategorizedRuleset<L> = Default::default();

    // Batch the candidates:
    let mut candidates = candidates.clone();
    while !candidates.is_empty() {
        // 1. Make a batch of up to `batch_size` candidates.
        let batch = candidates.iter().take(batch_size).collect::<Vec<_>>();
        let batch_ruleset: Ruleset<L> = {
            let mut rs = Ruleset::default();
            for rule in batch {
                rs.add(rule.clone());
            }
            rs
        };
        candidates.remove_all(batch_ruleset.clone());

        // 2. Send the batch to the LLM for categorization.
        let current_categorized = send_group_rules_request(client, &batch_ruleset)
            .await
            .map_err(|e| {
                eprintln!("Error sending request: {e}");
                e
            })
            .unwrap();

        // 3. Parse the response into a CategorizedRuleset.
        let categorized = parse_categorization_response(current_categorized);

        // 4. Merge the categorized rules into the result.
        for (category, ruleset) in categorized {
            let entry = result.entry(category).or_default();
            entry.extend(ruleset);
        }
    }
    // 5. Return the final categorized ruleset.
    result
}

pub async fn generate_alphabet_soup(
    term_recipe: &Recipe,
    cond_r: Option<&ConditionRecipe>,
) -> (Workload, Option<Workload>) {
    let client = Client::new();

    let soup = alphabet_soup(&client, term_recipe).await.unwrap();

    // Convert the generated soup into a workload
    let term_workload = soup_to_workload::<Pred>(
        soup.clone(),
        term_recipe.vars.clone(),
        term_recipe.vals.clone(),
    )
    .unwrap();

    println!("term workload:");
    for t in &term_workload.clone().force() {
        println!("{t}");
    }

    if let Some(cond_recipe) = cond_r {
        // If a condition recipe is provided, generate conditions based on the previous workload.
        let condition_workload = condition_soup(&client, &soup, &term_recipe.vars, cond_recipe)
            .await
            .unwrap();

        // Convert the generated conditions into a workload
        let cond_workload = soup_to_workload::<Pred>(
            condition_workload,
            term_recipe.vars.clone(),
            cond_recipe.vals.clone(),
        )
        .unwrap();

        println!("conditional workload:");
        for c in &cond_workload.clone().force() {
            println!("{c}");
        }

        (term_workload, Some(cond_workload))
    } else {
        (term_workload, None)
    }
}

pub async fn condition_soup(
    client: &Client,
    term_workload_as_vec: &[String],
    vars: &Vec<String>,
    r: &ConditionRecipe,
) -> Result<Vec<String>, reqwest::Error> {
    // TODO: @ninehusky -- check that term workload vars are superset of recipe vars.
    let content = ENUMERATE_CONDITIONS_PROMPT
        .replace(
            "{last_step_workload}",
            // This will be the workload from the previous step, which is a list of terms.
            &term_workload_as_vec.join("\n"),
        )
        .replace("{max_size}", &r.max_size.to_string())
        .replace("{vals}", format!("{:?}", r.vals).as_str())
        .replace("{vars}", format!("{vars:?}").as_str())
        .replace("{ops}", format!("{:?}", r.ops).as_str());

    // Define request payload for the Responses API
    let request_body = json!({
        "model": "gpt-4o",  // Correct model
        "messages": [
            {
                "role": "system",
                "content": content,
            },
        ],
        "seed": 0xbeef,
        "temperature": 0.0,
    });

    let response = client
        .post("https://api.openai.com/v1/chat/completions") // <-- Using Responses API
        .header(
            "Authorization",
            format!(
                "Bearer {}",
                std::env::var("OPENAI_API_KEY").expect("OPENAI_API_KEY not set")
            ),
        )
        .header("Content-Type", "application/json")
        .json(&request_body)
        .send()
        .await?;

    let response_json: serde_json::Value = response.json().await?;

    let result = response_json["choices"][0]["message"]["content"]
        .as_str()
        .unwrap()
        .lines()
        .map(|s| s.to_string())
        .collect();

    Ok(result)
}

// asks GPT to generate a list of terms which implement some bigass recipe.
pub async fn alphabet_soup(client: &Client, r: &Recipe) -> Result<Vec<String>, reqwest::Error> {
    let url = "https://api.openai.com/v1/chat/completions";
    let content = ENUMERATE_TERMS_PROMPT
        .replace("{max_size}", &r.max_size.to_string())
        .replace("{vals}", format!("{:?}", r.vals).as_str())
        .replace("{vars}", format!("{:?}", r.vars).as_str())
        .replace("{ops}", format!("{:?}", r.ops).as_str());

    // Define request payload for the Responses API
    let request_body = json!({
        "model": "gpt-4o",  // Correct model
        "messages": [
            {
                "role": "system",
                "content": content,
            },
        ],
        "seed": 0xbeef,
        "temperature": 0.0,
    });

    println!("SENDING REQUEST TO: {url}");

    let response = client
        .post("https://api.openai.com/v1/chat/completions") // <-- Using Responses API
        .header(
            "Authorization",
            format!(
                "Bearer {}",
                std::env::var("OPENAI_API_KEY").expect("OPENAI_API_KEY not set")
            ),
        )
        .header("Content-Type", "application/json")
        .json(&request_body)
        .send()
        .await?;

    println!("response status: {}", response.status());
    let response_json: serde_json::Value = response.json().await?;

    let result = response_json["choices"][0]["message"]["content"]
        .as_str()
        .unwrap()
        .lines()
        .map(|s| s.to_string())
        .collect();

    Ok(result)
}

pub fn soup_to_workload<L: SynthLanguage>(
    soup: Vec<String>,
    vars: Vec<String>,
    vals: Vec<String>,
) -> Result<Workload, Box<dyn std::error::Error>> {
    println!("soup:");
    for s in &soup {
        println!("{s}");
    }
    let mut good_expressions = vec![];
    for r in &soup {
        // if it has no parentheses, and it is not a variable/value, then skip it.
        println!("checking expression: {r}");
        let r = r.trim();
        println!("starts with )? {}", r.starts_with(')'));
        println!("ends with (? {}", r.ends_with(')'));
        println!("is a variable? {}", vars.contains(&r.to_string()));
        println!("is a value? {}", vals.contains(&r.to_string()));

        let starts_with_paren = r.starts_with('(');
        let ends_with_paren = r.ends_with(')');

        if starts_with_paren != ends_with_paren {
            println!("skipping expression: {r}");
            continue;
        }

        if (!starts_with_paren || !ends_with_paren)
            && !vals.contains(&r.to_string())
            && !vars.contains(&r.to_string())
        {
            println!("skipping expression: {r}");
            continue;
        }

        let t: Result<RecExpr<L>, _> = r.parse();
        match t {
            Ok(t) => {
                good_expressions.push(t.to_string());
            }
            Err(_) => {
                // If we can't parse the expression, skip it.
                println!("skipping expression: {r}");
                continue;
            }
        }
    }

    let soup_workload = Workload::new(good_expressions);

    Ok(soup_workload)
}

pub async fn send_group_rules_request<L: SynthLanguage>(
    client: &Client,
    candidate_rules: &Ruleset<L>,
) -> Result<String, String> {
    // Build the prompt with existing rules + candidates
    let candidates_text = candidate_rules.to_str_vec().join("\n");
    let prompt = GROUP_RULES_PROMPT.replace("candidates_text", &candidates_text);

    let model = "gpt-4o";
    let hash = hash_request(&prompt, model);
    let cache_path = format!("{}/{}.json", CACHE_DIR, hash);

    // Replay mode
    if std::env::var("FAKE_LLM").is_ok() {
        if Path::new(&cache_path).exists() {
            let cached = fs::read_to_string(&cache_path)
                .map_err(|e| format!("Failed to read cache: {e}"))?;
            let cached_json: serde_json::Value =
                serde_json::from_str(&cached).map_err(|e| format!("Bad cached JSON: {e}"))?;

            if let Some(resp) = cached_json["response"].as_str() {
                println!("(replay) Using cached group_rules response for {}", hash);
                return Ok(resp.to_string());
            } else {
                return Err(format!("Cached file missing 'response' field for {}", hash));
            }
        } else {
            println!("We have to make a new API call!");
            // return Err(format!("No cached response found for hash {}", hash));
        }
    }

    // Real request
    let request_body = json!({
        "model": model,
        "messages": [
            { "role": "system", "content": prompt }
        ],
        "temperature": 0.0,
        "max_tokens": 1500
    });

    let response = client
        .post("https://api.openai.com/v1/chat/completions")
        .header(
            "Authorization",
            format!(
                "Bearer {}",
                std::env::var("OPENAI_API_KEY").expect("OPENAI_API_KEY not set")
            ),
        )
        .header("Content-Type", "application/json")
        .json(&request_body)
        .send()
        .await
        .map_err(|e| format!("Failed: {e}"))?;

    let response_json: serde_json::Value = response
        .json()
        .await
        .map_err(|e| format!("Failed to parse response: {e}"))?;

    let text_output = response_json["choices"][0]["message"]["content"]
        .as_str()
        .unwrap_or("")
        .to_string();

    // Write cache
    let cached_obj = json!({
        "prompt": prompt,
        "model": model,
        "response": text_output,
    });
    fs::write(&cache_path, serde_json::to_string_pretty(&cached_obj).unwrap())
        .map_err(|e| format!("Failed to write cache: {e}"))?;

    Ok(text_output)
}

pub async fn send_score_rules_request<L: SynthLanguage>(
    client: &Client,
    prior_rules: &Ruleset<L>,
    candidate_rules: &Ruleset<L>,
) -> Result<String, String> {
    // Build the prompt with existing rules + candidates
    let prior_text = prior_rules.to_str_vec().join("\n");
    let candidates_text = candidate_rules.to_str_vec().join("\n");

    let prompt = SCORE_RULES_PROMPT
        .replace("prior_text", &prior_text)
        .replace("candidates_text", &candidates_text);

    // Build the request payload
    let request_body = json!({
        "model": "gpt-4o",
        "messages": [
            { "role": "system", "content": prompt }
        ],
        "temperature": 0.0,
        "max_tokens": 1500
    });

    // Send the request
    let response = client
        .post("https://api.openai.com/v1/chat/completions")
        .header(
            "Authorization",
            format!(
                "Bearer {}",
                std::env::var("OPENAI_API_KEY").expect("OPENAI_API_KEY not set")
            ),
        )
        .header("Content-Type", "application/json")
        .json(&request_body)
        .send()
        .await
        .map_err(|e| format!("Failed: {e}"))?;

    let response_json: serde_json::Value = response
        .json()
        .await
        .map_err(|e| format!("Failed to parse response: {e}"))?;

    // Return raw text content
    let text_output = response_json["choices"][0]["message"]["content"]
        .as_str()
        .unwrap_or("")
        .to_string();

    Ok(text_output)
}

pub async fn send_filter_rules_request<L: SynthLanguage>(
    client: &Client,
    prior_rules: &Ruleset<L>,
    candidate_rules: &[ScoredRule<L>],
    keep_max: usize,
) -> Result<String, String> {
    // Build the prompt with existing rules + candidates
    let prior_text = prior_rules.to_str_vec().join("\n");
    let candidates_text = candidate_rules
        .iter()
        .map(|r| r.to_string())
        .collect::<Vec<_>>()
        .join("\n");

    let prompt = FILTER_RULES_PROMPT
        .replace("prior_text", &prior_text)
        .replace("candidates_text", &candidates_text)
        .replace("keep_max", &keep_max.to_string());

    println!("Prompt: {prompt}");

    // Build the request payload
    let request_body = json!({
        "model": "gpt-4o",
        "messages": [
            { "role": "system", "content": prompt }
        ],
        "temperature": 0.0,
        "max_tokens": 1500
    });

    // Send the request
    let response = client
        .post("https://api.openai.com/v1/chat/completions")
        .header(
            "Authorization",
            format!(
                "Bearer {}",
                std::env::var("OPENAI_API_KEY").expect("OPENAI_API_KEY not set")
            ),
        )
        .header("Content-Type", "application/json")
        .json(&request_body)
        .send()
        .await
        .map_err(|e| format!("Failed: {e}"))?;

    let response_json: serde_json::Value = response
        .json()
        .await
        .map_err(|e| format!("Failed to parse response: {e}"))?;

    // Return raw text content
    let text_output = response_json["choices"][0]["message"]["content"]
        .as_str()
        .unwrap_or("")
        .to_string();

    Ok(text_output)
}

#[derive(Debug, Clone)]
pub struct ScoredRule<L: SynthLanguage> {
    pub rule: Rule<L>,  // your rule type
    pub core: u8,       // 0–5
    pub importance: u8, // 0–5
    pub novelty: u8,    // 0–5
}

impl<L: SynthLanguage> Display for ScoredRule<L> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} — CORE:{} — IMPORTANCE:{} — NOVELTY:{}",
            self.rule, self.core, self.importance, self.novelty
        )
    }
}

pub fn parse_scored_rules<L: SynthLanguage>(text: &str) -> Vec<ScoredRule<L>> {
    let mut results = Vec::new();

    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }

        // Split on the “—” delimiter
        let parts: Vec<&str> = line.split("—").map(|s| s.trim()).collect();
        if parts.len() < 4 {
            continue; // malformed line
        }

        let rule = Rule::from_string(parts[0]);
        let core_str = parts[1].strip_prefix("CORE:").unwrap_or("0");
        let importance_str = parts[2].strip_prefix("IMPORTANCE:").unwrap_or("0");
        let novelty_str = parts[3].strip_prefix("NOVELTY:").unwrap_or("0");

        if let (Ok(core), Ok(importance), Ok(novelty)) = (
            core_str.parse::<u8>(),
            importance_str.parse::<u8>(),
            novelty_str.parse::<u8>(),
        ) {
            if let Ok((rule, _)) = rule {
                results.push(ScoredRule {
                    rule,
                    core,
                    importance,
                    novelty,
                });
            }
        }
    }

    results
}

pub async fn filter_rules_llm<L: SynthLanguage>(
    client: &Client,
    prior: &Ruleset<L>,
    candidates: &Ruleset<L>,
    keep_max: usize,
    batch_size: usize,
) -> Ruleset<L> {
    let mut candidates = candidates.clone();
    let mut scored_rules = vec![];
    while !candidates.is_empty() {
        // 1. Make a batch of up to `batch_size` candidates.
        let batch = candidates.iter().take(batch_size).collect::<Vec<_>>();
        let batch_ruleset: Ruleset<L> = {
            let mut rs = Ruleset::default();
            for rule in batch {
                rs.add(rule.clone());
            }
            rs
        };
        candidates.remove_all(batch_ruleset.clone());

        // 2. Send the batch to the LLM for scoring.
        let response = send_score_rules_request(client, prior, &batch_ruleset).await;
        match response {
            Ok(text) => {
                // 3. Parse the response and filter rules.
                let local_scored_rules: Vec<ScoredRule<L>> = parse_scored_rules(&text);
                scored_rules.extend(local_scored_rules);

                for scored_rule in &scored_rules {
                    println!("Scored rule: {scored_rule:?}");
                }
            }
            Err(e) => {
                eprintln!("Error scoring rules: {e}");
            }
        }
    }

    println!("Scored rules: {}", scored_rules.len());

    // 3. Ask the LLM to filter the scored rules based on their scores.
    let filtered_response = send_filter_rules_request(client, prior, &scored_rules, keep_max).await;

    if let Ok(r) = filtered_response {
        println!("the filtered response: {r}");
    }

    Default::default()
}

// NOTE: @ninehusky here! I am going to comment out the tests for here until I can think of
//       a more rigorous way of testing.
// #[allow(unused_imports)]
// pub mod rule_filter_tests {
//     use super::*;
//     use crate::{
//         enumo::{Rule, Ruleset},
//         llm::{filter_rules_llm, sort_rule_candidates},
//     };

//     #[tokio::test]
//     async fn group_rules_request() {
//         let candidates_str: &str = r#"?a ==> (max ?a ?b) if (<= ?b ?a)
// (< (min ?z (+ ?y ?c0)) (min ?x ?y)) ==> (< (min ?z (+ ?y ?c0)) ?x) if (< ?c0 0)
// (< (+ ?b (+ ?a ?a)) (min ?a (+ ?a ?a))) <=> (< (+ ?a (+ ?b ?b)) (min ?b ?a))
// (< (min ?b (+ ?a ?a)) (+ ?a (+ ?a ?a))) <=> (< (min ?b ?a) (+ ?a (+ ?a ?a)))
// (< (min ?a (+ ?b ?b)) (+ ?a (min ?b ?a))) <=> (< (min ?b (+ ?b ?b)) (+ ?b ?a))
// (< (+ ?b (min ?b ?a)) (min ?c (+ ?b ?a))) <=> (< (+ ?b ?b) (min ?c (+ ?a ?a)))
// (< (+ ?b (+ ?a ?a)) (min ?c (+ ?b ?a))) <=> (< (+ ?b (+ ?a ?a)) (min ?b ?c))
// (< (+ ?b (min ?b ?c)) (+ ?a (min ?b ?a))) <=> (< (+ ?b (min ?c ?a)) (+ ?a ?a))
// (< (+ ?b (+ ?d ?c)) (+ ?b (min ?b ?a))) <=> (< (min ?b (+ ?d ?c)) (min ?b ?a))
// (< (min ?c (+ ?b ?b)) (+ ?a (min ?b ?a))) <=> (< (min ?c (+ ?b ?a)) (+ ?a ?a))
// (< (min ?c (+ ?b ?b)) (+ ?a (min ?b ?a))) <=> (< (min ?c (+ ?b ?b)) (+ ?a ?a))
// (< (+ ?b (min ?d ?c)) (+ ?c (min ?b ?a))) <=> (< (+ ?b ?d) (+ ?c (min ?b ?a)))
// (< (+ ?b (min ?a ?c)) (+ ?c (min ?b ?a))) <=> (< (+ ?b ?a) (+ ?c (min ?b ?a)))
// (< (+ ?c (min ?d ?b)) (+ ?c (min ?b ?a))) <=> (< (+ ?c ?d) (+ ?c (min ?b ?a)))
// (< (min ?c (+ ?d ?b)) (min ?c (+ ?b ?a))) <=> (< (+ ?d ?b) (min ?c (+ ?b ?a)))
// (< (min ?b (+ ?c ?b)) (min ?b (+ ?b ?a))) <=> (< (+ ?c ?b) (min ?b (+ ?b ?a)))
// (< (+ ?b (+ ?c ?c)) (+ ?b (min ?b ?a))) <=> (< (min ?b (+ ?c ?c)) (min ?b ?a))
// (< (+ ?b (min ?c ?b)) (+ ?a (min ?b ?a))) <=> (< (+ ?b (min ?c ?b)) (+ ?a ?a))
// (< (min ?c (min ?a ?b)) (min ?b (+ ?a ?a))) <=> (< (min ?c ?a) (min ?b (+ ?a ?a)))
// (< (min ?a (+ ?c ?b)) (min ?a (+ ?b ?a))) <=> (< (+ ?c ?b) (min ?a (+ ?b ?a)))
// (< (+ ?a (min ?c ?a)) (min ?b (+ ?a ?a))) <=> (< (+ ?c ?a) (min ?b (+ ?a ?a)))
// (max ?b ?a) ==> ?a if (== ?b ?a)"#;

//         let client = reqwest::Client::new();

//         let mut candidate_rules: Ruleset<Pred> = Default::default();

//         for line in candidates_str.lines() {
//             let rule_str = line.trim();
//             if !rule_str.is_empty() {
//                 match Rule::from_string(rule_str) {
//                     Ok((f, _)) => {
//                         println!("adding rule: {f}");
//                         candidate_rules.add(f);
//                     }
//                     Err(e) => {
//                         println!("Error parsing rule '{rule_str}': {e}");
//                     }
//                 };
//             }
//         }

//         let categorized_rules = sort_rule_candidates::<Pred>(&client, candidate_rules, 10).await;

//         println!("Here's the categorized rules:");
//         for key in categorized_rules.keys() {
//             println!("Category: {key}");
//             let ruleset = categorized_rules.get(key).unwrap();
//             for rule in ruleset.iter() {
//                 println!("  - {rule}");
//             }
//         }
//     }

//     #[tokio::test]
//     async fn score_rules_request_doesnt_filter_out_important_rules() {
//         let candidates_str: &str = r#"?a ==> (max ?a ?b) if (<= ?b ?a)
// (< (min ?z (+ ?y ?c0)) (min ?x ?y)) ==> (< (min ?z (+ ?y ?c0)) ?x) if (< ?c0 0)
// (< (+ ?b (+ ?a ?a)) (min ?a (+ ?a ?a))) <=> (< (+ ?a (+ ?b ?b)) (min ?b ?a))
// (< (min ?b (+ ?a ?a)) (+ ?a (+ ?a ?a))) <=> (< (min ?b ?a) (+ ?a (+ ?a ?a)))
// (< (min ?a (+ ?b ?b)) (+ ?a (min ?b ?a))) <=> (< (min ?b (+ ?b ?b)) (+ ?b ?a))
// (< (+ ?b (min ?b ?a)) (min ?c (+ ?b ?a))) <=> (< (+ ?b ?b) (min ?c (+ ?a ?a)))
// (< (+ ?b (+ ?a ?a)) (min ?c (+ ?b ?a))) <=> (< (+ ?b (+ ?a ?a)) (min ?b ?c))
// (< (+ ?b (min ?b ?c)) (+ ?a (min ?b ?a))) <=> (< (+ ?b (min ?c ?a)) (+ ?a ?a))
// (< (+ ?b (+ ?d ?c)) (+ ?b (min ?b ?a))) <=> (< (min ?b (+ ?d ?c)) (min ?b ?a))
// (< (min ?c (+ ?b ?b)) (+ ?a (min ?b ?a))) <=> (< (min ?c (+ ?b ?a)) (+ ?a ?a))
// (< (min ?c (+ ?b ?b)) (+ ?a (min ?b ?a))) <=> (< (min ?c (+ ?b ?b)) (+ ?a ?a))
// (< (+ ?b (min ?d ?c)) (+ ?c (min ?b ?a))) <=> (< (+ ?b ?d) (+ ?c (min ?b ?a)))
// (< (+ ?b (min ?a ?c)) (+ ?c (min ?b ?a))) <=> (< (+ ?b ?a) (+ ?c (min ?b ?a)))
// (< (+ ?c (min ?d ?b)) (+ ?c (min ?b ?a))) <=> (< (+ ?c ?d) (+ ?c (min ?b ?a)))
// (< (min ?c (+ ?d ?b)) (min ?c (+ ?b ?a))) <=> (< (+ ?d ?b) (min ?c (+ ?b ?a)))
// (< (min ?b (+ ?c ?b)) (min ?b (+ ?b ?a))) <=> (< (+ ?c ?b) (min ?b (+ ?b ?a)))
// (< (+ ?b (+ ?c ?c)) (+ ?b (min ?b ?a))) <=> (< (min ?b (+ ?c ?c)) (min ?b ?a))
// (< (+ ?b (min ?c ?b)) (+ ?a (min ?b ?a))) <=> (< (+ ?b (min ?c ?b)) (+ ?a ?a))
// (< (min ?c (min ?a ?b)) (min ?b (+ ?a ?a))) <=> (< (min ?c ?a) (min ?b (+ ?a ?a)))
// (< (min ?a (+ ?c ?b)) (min ?a (+ ?b ?a))) <=> (< (+ ?c ?b) (min ?a (+ ?b ?a)))
// (< (+ ?a (min ?c ?a)) (min ?b (+ ?a ?a))) <=> (< (+ ?c ?a) (min ?b (+ ?a ?a)))
// (max ?b ?a) ==> ?a if (== ?b ?a)"#;
//         let client = reqwest::Client::new();

//         let prior_rules: Ruleset<Pred> = Default::default();
//         let mut candidate_rules: Ruleset<Pred> = Default::default();

//         for line in candidates_str.lines() {
//             let rule_str = line.trim();
//             if !rule_str.is_empty() {
//                 match Rule::from_string(rule_str) {
//                     Ok((f, _)) => {
//                         println!("adding rule: {f}");
//                         candidate_rules.add(f);
//                     }
//                     Err(e) => {
//                         println!("Error parsing rule '{rule_str}': {e}");
//                     }
//                 };
//             }
//         }

//         let result = filter_rules_llm(&client, &prior_rules, &candidate_rules, 50, 10).await;
//     }

//     #[tokio::test]
//     async fn score_rules_request_ok() {
//         let candidates_str: &str = r#"(< (+ ?b (+ ?c ?a)) (min ?a (+ ?b ?a))) ==> (< (+ ?b (+ ?c ?c)) (min ?b ?c))
// (< (+ ?b ?a) (min ?c (+ ?b ?a))) <=> (< (+ ?b ?a) (+ ?a (min ?b ?c)))
// (< (+ ?b ?a) (+ ?b (min ?a ?c))) ==> (< (+ ?b ?a) (min ?b (+ ?b ?a)))
// (< (min ?b (+ ?c ?a)) (+ ?b (+ ?a ?a))) <=> (< (min ?b ?c) (+ ?b ?a))
// (< (min ?b (+ ?a ?a)) (+ ?b (+ ?a ?a))) <=> (< (min ?b ?a) (+ ?b ?a))
// (< (min ?b (+ ?b ?b)) (+ ?b (+ ?a ?a))) <=> (< (min ?b ?a) (+ ?a ?a))
// (< (min ?d (+ ?c ?b)) (+ ?c (min ?b ?a))) <=> (< ?d (+ ?c (min ?b ?a)))
// (< (min ?c (+ ?b ?a)) (+ ?b (+ ?a ?a))) <=> (< (min ?c ?b) (+ ?b (+ ?a ?a)))
// (< (min ?a (+ ?a ?b)) (+ ?b (+ ?a ?a))) <=> (< (min ?a ?b) (+ ?b (+ ?a ?a)))
// (< (+ ?b (+ ?c ?c)) (+ ?b (+ ?a ?a))) <=> (< (+ ?b (min ?c ?a)) (+ ?b ?a))
// (< (+ ?b (min ?d ?a)) (min ?c (+ ?b ?a))) <=> (< (+ ?b ?d) (min ?c (+ ?b ?a)))
// (< (+ ?c (+ ?b ?b)) (min ?c (+ ?b ?a))) <=> (< (min ?c (+ ?b ?c)) (min ?c ?a))
// (< (min ?b (+ ?b ?b)) (+ ?a (+ ?b ?b))) <=> (< (min ?b ?a) (+ ?b (+ ?a ?a)))
// (< (+ ?c (min ?c ?b)) (+ ?b (min ?c ?a))) <=> (< (+ ?c ?c) (+ ?b (min ?b ?a)))
// (< (+ ?b (+ ?a ?a)) (min ?a (+ ?a ?a))) <=> (< (+ ?a (+ ?b ?b)) (min ?b ?a))
// (< (min ?b (+ ?a ?a)) (+ ?a (+ ?a ?a))) <=> (< (min ?b ?a) (+ ?a (+ ?a ?a)))
// (< (min ?a (+ ?b ?b)) (+ ?a (min ?b ?a))) <=> (< (min ?b (+ ?b ?b)) (+ ?b ?a))
// (< (+ ?b (min ?b ?a)) (min ?c (+ ?b ?a))) <=> (< (+ ?b ?b) (min ?c (+ ?a ?a)))
// (< (+ ?b (+ ?a ?a)) (min ?c (+ ?b ?a))) <=> (< (+ ?b (+ ?a ?a)) (min ?b ?c))
// (< (+ ?b (min ?b ?c)) (+ ?a (min ?b ?a))) <=> (< (+ ?b (min ?c ?a)) (+ ?a ?a))
// (< (+ ?b (+ ?d ?c)) (+ ?b (min ?b ?a))) <=> (< (min ?b (+ ?d ?c)) (min ?b ?a))
// (< (min ?c (+ ?b ?b)) (+ ?a (min ?b ?a))) <=> (< (min ?c (+ ?b ?a)) (+ ?a ?a))
// (< (min ?c (+ ?b ?b)) (+ ?a (min ?b ?a))) <=> (< (min ?c (+ ?b ?b)) (+ ?a ?a))
// (< (+ ?b (min ?d ?c)) (+ ?c (min ?b ?a))) <=> (< (+ ?b ?d) (+ ?c (min ?b ?a)))
// (< (+ ?b (min ?a ?c)) (+ ?c (min ?b ?a))) <=> (< (+ ?b ?a) (+ ?c (min ?b ?a)))
// (< (+ ?c (min ?d ?b)) (+ ?c (min ?b ?a))) <=> (< (+ ?c ?d) (+ ?c (min ?b ?a)))
// (< (min ?c (+ ?d ?b)) (min ?c (+ ?b ?a))) <=> (< (+ ?d ?b) (min ?c (+ ?b ?a)))
// (< (min ?b (+ ?c ?b)) (min ?b (+ ?b ?a))) <=> (< (+ ?c ?b) (min ?b (+ ?b ?a)))
// (< (+ ?b (+ ?c ?c)) (+ ?b (min ?b ?a))) <=> (< (min ?b (+ ?c ?c)) (min ?b ?a))
// (< (+ ?b (min ?c ?b)) (+ ?a (min ?b ?a))) <=> (< (+ ?b (min ?c ?b)) (+ ?a ?a))
// (< (min ?c (min ?a ?b)) (min ?b (+ ?a ?a))) <=> (< (min ?c ?a) (min ?b (+ ?a ?a)))
// (< (min ?a (+ ?c ?b)) (min ?a (+ ?b ?a))) <=> (< (+ ?c ?b) (min ?a (+ ?b ?a)))
// (< (+ ?a (min ?c ?a)) (min ?b (+ ?a ?a))) <=> (< (+ ?c ?a) (min ?b (+ ?a ?a)))
// (< (min ?b (+ ?c ?b)) (min ?b (+ ?a ?a))) <=> (< (+ ?c ?b) (min ?b (+ ?a ?a)))
// (< (min ?c (+ ?d ?d)) (min ?c (+ ?b ?a))) <=> (< (+ ?d ?d) (min ?c (+ ?b ?a)))
// (< (min ?b (+ ?b ?b)) (min ?a (+ ?b ?a))) <=> (< (+ ?b (+ ?b ?b)) (+ ?a (+ ?a ?a)))
// (< (+ ?b (+ ?b ?b)) (+ ?a (+ ?a ?a))) <=> (< (min ?b (+ ?b ?a)) (min ?a (+ ?a ?a)))
// (< (min ?c (+ ?c ?b)) (min ?a (+ ?b ?a))) <=> (< (+ ?c (min ?c ?b)) (+ ?a (min ?b ?a)))
// (< (+ ?b (+ ?c ?c)) (+ ?b (+ ?a ?a))) <=> (< (+ ?c (min ?c ?b)) (+ ?a (min ?b ?a)))
// (< (min ?c (+ ?b ?a)) (+ ?b (min ?b ?a))) <=> (< (min ?c (+ ?b ?b)) (+ ?b (min ?b ?a)))
// (< (+ ?b (+ ?a ?a)) (min ?b (+ ?a ?a))) <=> (< (+ ?a (+ ?b ?b)) (min ?a (+ ?b ?b)))
// (< (+ ?c (+ ?b ?b)) (+ ?c (min ?b ?a))) <=> (< (+ ?c (+ ?b ?b)) (min ?c (+ ?c ?a)))
// (< (min ?b (+ ?b ?c)) (min ?b (+ ?b ?a))) <=> (< (+ ?b (min ?c ?a)) (min ?b (+ ?b ?a)))
// (< (min ?b (+ ?a ?a)) (+ ?b (+ ?a ?a))) <=> (< (min ?a (+ ?b ?b)) (+ ?a (+ ?b ?b)))
// (< (+ ?b (min ?c ?a)) (+ ?b (+ ?a ?a))) <=> (< (min ?b (+ ?b ?c)) (+ ?b (+ ?a ?a)))
// (< (min ?b (+ ?b ?c)) (+ ?c (min ?b ?a))) <=> (< (min ?b (+ ?c ?a)) (+ ?c (min ?b ?a)))
// (< (min ?c (+ ?b ?c)) (min ?c (+ ?b ?a))) <=> (< (+ ?b (min ?c ?a)) (min ?c (+ ?b ?a)))
// (< (+ ?b (min ?b ?a)) (min ?b (+ ?a ?a))) <=> (< (min ?a (+ ?b ?a)) (min ?a (+ ?a ?a)))
// (< (min ?b (+ ?b ?b)) (min ?b (+ ?a ?a))) <=> (< (min ?a (+ ?b ?a)) (min ?a (+ ?a ?a)))
// (< (min ?b (+ ?b ?a)) (+ ?b (min ?b ?a))) <=> (< (min ?b (+ ?b ?b)) (+ ?b (min ?b ?a)))
// (< (min ?b (+ ?c ?d)) (min ?c (min ?b ?a))) <=> (< (min ?c (+ ?c ?d)) (min ?c (min ?b ?a)))
// (< (+ ?a (+ ?b ?b)) (min ?a (+ ?a ?a))) <=> (< (+ ?a (+ ?b ?b)) (+ ?a (min ?a ?b)))
// (< (+ ?a (min ?b ?c)) (+ ?c (min ?b ?a))) <=> (< (+ ?b (min ?c ?a)) (+ ?c (min ?b ?a)))
// (< (min ?a (+ ?b ?b)) (+ ?b (min ?b ?a))) <=> (< (min ?a (+ ?b ?a)) (+ ?b (min ?b ?a)))
// (< (+ ?b (min ?c ?a)) (min ?a (+ ?b ?a))) <=> (< (min ?a (+ ?b ?c)) (min ?a (+ ?b ?a)))
// (< (+ ?a (min ?b ?a)) (min ?c (+ ?b ?a))) <=> (< (+ ?a (min ?b ?a)) (min ?c (+ ?b ?b)))
// (< (min ?b (+ ?c ?c)) (min ?b (+ ?a ?a))) <=> (< (min ?b (+ ?c ?c)) (min ?b (+ ?c ?a)))
// (< (+ ?c (min ?b ?c)) (+ ?b (min ?b ?a))) <=> (< (+ ?c (min ?b ?c)) (+ ?b (min ?c ?a)))
// (< (min ?b (+ ?c ?a)) (min ?b (+ ?a ?a))) <=> (< (+ ?a (min ?c ?a)) (min ?b (+ ?a ?a)))"#;

//         let client = reqwest::Client::new();

//         let prior_rules: Ruleset<Pred> = Default::default();

//         let mut candidate_rules: Ruleset<Pred> = Default::default();

//         for line in candidates_str.lines() {
//             let rule_str = line.trim();
//             if !rule_str.is_empty() {
//                 let rule: Rule<Pred> = Rule::from_string(rule_str).unwrap().0;
//                 println!("Adding rule: {rule}");
//                 candidate_rules.add(rule);
//             }
//         }

//         let result = send_score_rules_request(&client, &prior_rules, &candidate_rules).await;
//         assert!(result.is_ok());
//         let text = result.unwrap();
//         println!("Response: {text}");
//     }

//     #[test]
//     fn filter_rules_keeps_important_ones() {
//         todo!()
//     }
// }

pub mod tests {

    #[allow(unused_imports)]
    use super::*;

    #[test]
    fn soup_to_workload_throws_away_div() {
        let soup = vec![
            "/".to_string(),
            "/".to_string(),
            "/".to_string(),
            "/".to_string(),
            "/ a b".to_string(),
            "55".to_string(),
            "a".to_string(),
            "b".to_string(),
        ];

        let result = soup_to_workload::<Pred>(
            soup,
            vec!["a".to_string(), "b".to_string()],
            vec!["1".to_string()],
        );
        assert!(result.is_ok());

        let workload = result
            .unwrap()
            .force()
            .into_iter()
            .map(|x| x.to_string())
            .collect::<Vec<String>>();
        assert_eq!(workload.len(), 2);
        assert!(workload.contains(&"a".to_string()));
        assert!(workload.contains(&"b".to_string()));
    }

    #[test]
    fn soup_to_workload_throws_away_more_bad() {
        let soup = vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
            "(+ a)".to_string(),
            "(+ b)".to_string(),
            "(+ c)".to_string(),
            "(- a)".to_string(),
            "(- b)".to_string(),
            "(- c)".to_string(),
            "(* a)".to_string(),
            "(* b)".to_string(),
            "(* c)".to_string(),
            "/ a".to_string(),
            "/ b".to_string(),
            "/ c".to_string(),
            "(+ a b)".to_string(),
            "(+ a c)".to_string(),
            "(+ b a)".to_string(),
            "(+ b c)".to_string(),
            "(+ c a)".to_string(),
            "(+ c b)".to_string(),
            "(- a b)".to_string(),
            "(- a c)".to_string(),
            "(- b a)".to_string(),
            "(- b c)".to_string(),
            "(- c a)".to_string(),
            "(- c b)".to_string(),
            "(* a b)".to_string(),
            "(* a c)".to_string(),
            "(* b a)".to_string(),
            "(* b c)".to_string(),
            "(* c a)".to_string(),
            "(* c b)".to_string(),
            "/ a b".to_string(),
            "/ a c".to_string(),
            "/ b a".to_string(),
            "/ b c".to_string(),
            "/ c a".to_string(),
            "/ c b".to_string(),
            "(+ a (+ b c))".to_string(),
            "(+ a (- b c))".to_string(),
            "(+ a (* b c))".to_string(),
            "(+ a (/ b c))".to_string(),
            "(- a (+ b c))".to_string(),
            "(- a (- b c))".to_string(),
            "(- a (* b c))".to_string(),
            "(- a (/ b c))".to_string(),
            "(* a (+ b c))".to_string(),
            "(* a (- b c))".to_string(),
            "(* a (* b c))".to_string(),
            "(* a (/ b c))".to_string(),
            "/ a (+ b c)".to_string(),
            "/ a (- b c)".to_string(),
            "/ a (* b c)".to_string(),
            "/ a (/ b c)".to_string(),
        ];

        // remove the bad stuff, and add in variables.
        let expected_length = soup.len() - 22 + 3;

        let wkld = soup_to_workload::<Pred>(
            soup,
            vec!["a".to_string(), "b".to_string(), "c".to_string()],
            vec!["1".to_string()],
        )
        .unwrap();

        for t in &wkld.force() {
            println!("{t}");
        }

        assert_eq!(wkld.force().len(), expected_length);
    }
}
