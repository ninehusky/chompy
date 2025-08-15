use egg::RecExpr;
use reqwest::Client;
use serde_json::json;

use crate::enumo::Ruleset;
use crate::{enumo::Workload, halide::Pred, SynthLanguage};

use crate::{ConditionRecipe, Recipe};

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

const SELECT_RULES_PROMPT: &str = r#"
You are given a list of rewrite rules with scores for CORE, IMPORTANCE, and NOVELTY.

Your task:
- Compute a COMPOSITE score for each rule:
    COMPOSITE = (CORE × 2.0) + (IMPORTANCE × 1.5) + (NOVELTY × 1.0)
- Select exactly the TOP 200 rules by COMPOSITE score.
- Break ties by choosing the one with the higher CORE score, then IMPORTANCE score.
- Output only the selected rules, sorted from highest to lowest COMPOSITE score.

Format:
Rank:<n> — COMPOSITE:<score> — CORE:<score> — IMPORTANCE:<score> — NOVELTY:<score> — <rule> — <reason from Pass 1>
"#;

const FILTER_RULES_PROMPT: &str  = r#"
You are an expert in program optimization and algebraic reasoning.

You will be given:
- A set of existing rewrite rules already accepted.
- A batch of new candidate rewrite rules that are valid.

Your goal: select the most important and non-redundant rules, with *strong preference* for rules that capture core algebraic properties of operators, such as:
- Distributivity (e.g., f(x ∘ y) → f(x) ∘ f(y), with correct guards)
- Associativity (grouping changes that keep semantics the same)
- Commutativity (order changes without altering meaning)
- Idempotence (applying an operation twice has same effect as once)
- Absorption (one operator absorbs another)
- Homomorphism-like transformations (distributing a function into multiple arguments)

**Selection criteria**:
1. **Core property priority** — Rules expressing these core operator laws should be ranked *very high* and almost always KEPT unless redundant.
2. **Generality** — Works for many inputs and variable arrangements.
3. **Simplification potential** — Likely to reduce expression size or enable further simplifications.
4. **Novelty** — Not equivalent to or implied by existing rules.
5. **Compactness** — Prefer rules where the RHS is no more complex than LHS, unless enabling major simplification later.

**Redundancy definition**:
- Isomorphic to an existing rule under variable renaming.
- Achieves the same effect as a sequence of simpler existing rules.
- Overly narrow special case with little general use.

**Instructions**:
For each candidate, respond with:
KEEP — if important and not redundant.
DROP — if redundant or unimportant.

If the rule matches a core algebraic property, add "CORE" after KEEP.

**Format**:
<rule> — <KEEP/DROP> [CORE if applicable] — <reason>

Existing rules:
<insert existing rules here>

Candidate rules:
<insert candidate rules here>
"#;


const ENUMERATE_TERMS_PROMPT: &str = r#"
You are an expert in generating a list of terms for a given
programming language. The syntax of the programming language
is s-expressions. You will be given a list of variables,
constants, and operations. Your task is to generate a list
of interesting terms using the above variables, constants, and operations.
The operations will be a list of list of strings, where operations[i]
will be the list of strings representing arity-i operations.
The terms should be in the s-expression format.
You should try to generate 50 terms, and you must try to generate
terms at each size from 1 to max_size. Outside of single constants,
make sure each term has at least one variable in it.
Avoid generating terms that only involve constants unless they reduce to a single constant.
First generate all size-1 terms, then size-2 terms, then size-3, and continue up to size-{max_size}.


Your response should only be terms, one after another.
Do not include any other text in your response. Do not
include line numbers or any other formatting. Only
include the terms in your response.
Example:

Example Input:
max_size: 4,
vals: ["0", "1"],
vars: ["x", "y"],
ops: [[], ["abs"], ["+", "-", "*", "min", "max"]],

Some example output:
x

(abs x)

(+ x y)
(- x x)
(* x y)
(min x y)
(min y x)
(min 0 x)
(min x 0)

(min (abs x) y)
...

Input:
Here is the recipe for the terms you should generate:
max_size: {max_size}
vals: {vals},
vars: {vars},
ops: {ops},
"#;

const ENUMERATE_CONDITIONS_PROMPT: &str = r#"
Good job! Now let's do it again, but with conditions. Your input will be the same as before:
it will be a list of variables, constants, and operations. However, this time instead of generating
terms that will be useful in rewrite situations, you generate conditions which can be used to
generate equalities between the terms you generated in the previous step.

Like before, you will generate terms in the s-expression format, one after another, up to
max_size. You will also generate conditions which will be used to compare terms.

Your response should only be terms, one after another.
Do not include any other text in your response. Do not
include line numbers or any other formatting. Only
include the terms in your response.

Example Input:
Here are the terms from the last step:
a
(abs a)

Here is the recipe for the terms you should generate:
max_size: 4,
vals: ["0"],
vars: ["a"],
ops: [[], ["abs"], ["<", "<=", "!="]],

Example Output:
(< a 0)
(<= a 0)
(< a (abs a))
...


Input:
Here are the terms from the last step:
{last_step_workload}

Here is the recipe for the terms you should generate:
max_size: {max_size}
vals: {vals},
vars: {vars},
ops: {ops},
"#;

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


pub async fn send_score_rules_request<L: SynthLanguage>(
    client: &Client,
    prior_rules: &Ruleset<L>,
    candidate_rules: &Ruleset<L>,
) -> Result<String, String> {
    // Build the prompt with existing rules + candidates
    let prior_text = prior_rules.to_str_vec().join("\n");
    let candidates_text = candidate_rules.to_str_vec().join("\n");

    let prompt =
        SCORE_RULES_PROMPT.replace("prior_text", &prior_text).replace("candidates_text", &candidates_text);

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
        .await.map_err(|e| format!("Failed: {}", e))?;

    let response_json: serde_json::Value = response.json().await.map_err(|e| format!("Failed to parse response: {}", e))?;

    // Return raw text content
    let text_output = response_json["choices"][0]["message"]["content"]
        .as_str()
        .unwrap_or("")
        .to_string();

    Ok(text_output)
}


fn filter_rules_llm<L: SynthLanguage>(client: &Client, prior: &Ruleset<L>, max: usize) -> Ruleset<L> {
    Default::default()
}

pub mod rule_filter_tests {
    use crate::{enumo::{Rule, Ruleset}, halide::Pred, llm::send_score_rules_request};

    #[tokio::test]
    async fn score_rules_request_doesnt_filter_out_important_rules() {
        let candidates_str: &str = r#"?a ==> (max ?a ?b) if (<= ?b ?a)
?a ==> (max ?a ?b) if (<= ?b ?a)
?a ==> (max ?a ?b) if (< ?b ?a)
?a ==> (max ?a ?b) if (< ?b ?a)
?a ==> (max ?a ?b) if (== ?a ?b)
?a ==> (max ?a ?b) if (== ?a ?b)
?a ==> (min ?a ?b) if (<= ?a ?b)
?a ==> (min ?a ?b) if (<= ?a ?b)
?a ==> (min ?a ?b) if (< ?a ?b)
?a ==> (min ?a ?b) if (< ?a ?b)
?a ==> (min ?a ?b) if (== ?a ?b)
?a ==> (min ?a ?b) if (== ?a ?b)
?a ==> ?b if (== ?a ?b)
?a ==> (max ?a ?b) if (<= ?b ?a)
?a ==> (max ?a ?b) if (<= ?b ?a)
?a ==> (max ?a ?b) if (< ?b ?a)
?a ==> (max ?a ?b) if (< ?b ?a)
?a ==> (max ?a ?b) if (== ?a ?b)
?a ==> (max ?a ?b) if (== ?a ?b)
?a ==> (min ?a ?b) if (<= ?a ?b)
?a ==> (min ?a ?b) if (<= ?a ?b)
?a ==> (min ?a ?b) if (< ?a ?b)
?a ==> (min ?a ?b) if (< ?a ?b)
?a ==> (min ?a ?b) if (== ?a ?b)
?a ==> (min ?a ?b) if (== ?a ?b)
?a ==> ?b if (== ?a ?b)
(min ?b ?a) ==> (max ?b ?a) if (== ?b ?a)
(min ?b ?a) ==> (max ?b ?a) if (== ?b ?a)
(min ?b ?a) ==> (min ?c ?b) if (== ?c ?a)
(min ?b ?a) ==> ?a if (<= ?a ?b)
(min ?b ?a) ==> ?a if (<= ?a ?b)
(min ?b ?a) ==> ?a if (< ?a ?b)
(min ?b ?a) ==> ?a if (< ?a ?b)
(min ?b ?a) ==> ?a if (== ?b ?a)
(min ?b ?a) ==> ?a if (== ?b ?a)
(min ?b ?a) ==> (min ?c ?a) if (== ?c ?b)
(min ?b ?a) ==> ?b if (<= ?b ?a)
(min ?b ?a) ==> ?b if (<= ?b ?a)
(min ?b ?a) ==> ?b if (< ?b ?a)
(min ?b ?a) ==> ?b if (< ?b ?a)
(min ?b ?a) ==> ?b if (== ?b ?a)
(min ?b ?a) ==> ?b if (== ?b ?a)
(max ?b ?a) ==> (max ?c ?a) if (== ?c ?b)
(max ?b ?a) ==> ?a if (<= ?b ?a)
(max ?b ?a) ==> ?a if (<= ?b ?a)
(max ?b ?a) ==> ?a if (< ?b ?a)
(max ?b ?a) ==> ?a if (< ?b ?a)
(max ?b ?a) ==> ?a if (== ?b ?a)
(max ?b ?a) ==> ?a if (== ?b ?a)
(max ?b ?a) ==> (max ?c ?b) if (== ?c ?a)
(max ?b ?a) ==> ?b if (<= ?a ?b)
(max ?b ?a) ==> ?b if (<= ?a ?b)
(max ?b ?a) ==> ?b if (< ?a ?b)
(max ?b ?a) ==> ?b if (< ?a ?b)
(max ?b ?a) ==> ?b if (== ?b ?a)
(max ?b ?a) ==> ?b if (== ?b ?a)
(max ?b ?a) ==> ?a if (<= ?b ?a)
(max ?b ?a) ==> ?a if (<= ?b ?a)
(max ?b ?a) ==> ?a if (< ?b ?a)
(max ?b ?a) ==> ?a if (< ?b ?a)
(max ?b ?a) ==> ?a if (== ?b ?a)
(max ?b ?a) ==> ?a if (== ?b ?a)
(max ?b ?a) ==> (max ?b ?c) if (== ?c ?a)
(max ?b ?a) ==> (min ?b ?a) if (== ?b ?a)
(max ?b ?a) ==> (min ?b ?a) if (== ?b ?a)
(min ?b ?a) ==> (max ?b ?a) if (== ?b ?a)
(min ?b ?a) ==> (max ?b ?a) if (== ?b ?a)
(min ?b ?a) ==> (min ?b ?c) if (== ?a ?c)
(min ?b ?a) ==> ?a if (<= ?a ?b)
(min ?b ?a) ==> ?a if (<= ?a ?b)
(min ?b ?a) ==> ?a if (< ?a ?b)
(min ?b ?a) ==> ?a if (< ?a ?b)
(min ?b ?a) ==> ?a if (== ?b ?a)
(min ?b ?a) ==> ?a if (== ?b ?a)
?a ==> (min ?b ?a) if (<= ?a ?b)
?a ==> (min ?b ?a) if (<= ?a ?b)
?a ==> (min ?b ?a) if (< ?a ?b)
?a ==> (min ?b ?a) if (< ?a ?b)
?a ==> (min ?b ?a) if (== ?b ?a)
?a ==> (min ?b ?a) if (== ?b ?a)
?a ==> ?b if (== ?b ?a)
(max ?b ?a) ==> ?a if (<= ?b ?a)
(max ?b ?a) ==> ?a if (<= ?b ?a)
(max ?b ?a) ==> ?a if (< ?b ?a)
(max ?b ?a) ==> ?a if (< ?b ?a)
(max ?b ?a) ==> ?a if (== ?b ?a)
(max ?b ?a) ==> ?a if (== ?b ?a)"#;
        let client = reqwest::Client::new();

        let mut prior_rules: Ruleset<Pred> = Default::default();

        let mut candidate_rules: Ruleset<Pred> = Default::default();

        for line in candidates_str.lines() {
            let rule_str = line.trim();
            if !rule_str.is_empty() {
                println!("rule str: {}", rule_str);
                let blah = Rule::<Pred>::from_string(rule_str);
                println!("don");
                match Rule::from_string(rule_str) {
                    Ok((f, b)) => {
                        println!("adding rule: {}", f);
                        candidate_rules.add(f);
                    }
                    _ => ()
                };
            }
        }

        let result = send_score_rules_request(&client, &prior_rules, &candidate_rules).await;
        assert!(result.is_ok());
        let text = result.unwrap();
        println!("Response: {}", text);



    }

    #[tokio::test]
    async fn score_rules_request_ok() {
        let candidates_str: &str = r#"(< (+ ?b (+ ?c ?a)) (min ?a (+ ?b ?a))) ==> (< (+ ?b (+ ?c ?c)) (min ?b ?c))
(< (+ ?b ?a) (min ?c (+ ?b ?a))) <=> (< (+ ?b ?a) (+ ?a (min ?b ?c)))
(< (+ ?b ?a) (+ ?b (min ?a ?c))) ==> (< (+ ?b ?a) (min ?b (+ ?b ?a)))
(< (min ?b (+ ?c ?a)) (+ ?b (+ ?a ?a))) <=> (< (min ?b ?c) (+ ?b ?a))
(< (min ?b (+ ?a ?a)) (+ ?b (+ ?a ?a))) <=> (< (min ?b ?a) (+ ?b ?a))
(< (min ?b (+ ?b ?b)) (+ ?b (+ ?a ?a))) <=> (< (min ?b ?a) (+ ?a ?a))
(< (min ?d (+ ?c ?b)) (+ ?c (min ?b ?a))) <=> (< ?d (+ ?c (min ?b ?a)))
(< (min ?c (+ ?b ?a)) (+ ?b (+ ?a ?a))) <=> (< (min ?c ?b) (+ ?b (+ ?a ?a)))
(< (min ?a (+ ?a ?b)) (+ ?b (+ ?a ?a))) <=> (< (min ?a ?b) (+ ?b (+ ?a ?a)))
(< (+ ?b (+ ?c ?c)) (+ ?b (+ ?a ?a))) <=> (< (+ ?b (min ?c ?a)) (+ ?b ?a))
(< (+ ?b (min ?d ?a)) (min ?c (+ ?b ?a))) <=> (< (+ ?b ?d) (min ?c (+ ?b ?a)))
(< (+ ?c (+ ?b ?b)) (min ?c (+ ?b ?a))) <=> (< (min ?c (+ ?b ?c)) (min ?c ?a))
(< (min ?b (+ ?b ?b)) (+ ?a (+ ?b ?b))) <=> (< (min ?b ?a) (+ ?b (+ ?a ?a)))
(< (+ ?c (min ?c ?b)) (+ ?b (min ?c ?a))) <=> (< (+ ?c ?c) (+ ?b (min ?b ?a)))
(< (+ ?b (+ ?a ?a)) (min ?a (+ ?a ?a))) <=> (< (+ ?a (+ ?b ?b)) (min ?b ?a))
(< (min ?b (+ ?a ?a)) (+ ?a (+ ?a ?a))) <=> (< (min ?b ?a) (+ ?a (+ ?a ?a)))
(< (min ?a (+ ?b ?b)) (+ ?a (min ?b ?a))) <=> (< (min ?b (+ ?b ?b)) (+ ?b ?a))
(< (+ ?b (min ?b ?a)) (min ?c (+ ?b ?a))) <=> (< (+ ?b ?b) (min ?c (+ ?a ?a)))
(< (+ ?b (+ ?a ?a)) (min ?c (+ ?b ?a))) <=> (< (+ ?b (+ ?a ?a)) (min ?b ?c))
(< (+ ?b (min ?b ?c)) (+ ?a (min ?b ?a))) <=> (< (+ ?b (min ?c ?a)) (+ ?a ?a))
(< (+ ?b (+ ?d ?c)) (+ ?b (min ?b ?a))) <=> (< (min ?b (+ ?d ?c)) (min ?b ?a))
(< (min ?c (+ ?b ?b)) (+ ?a (min ?b ?a))) <=> (< (min ?c (+ ?b ?a)) (+ ?a ?a))
(< (min ?c (+ ?b ?b)) (+ ?a (min ?b ?a))) <=> (< (min ?c (+ ?b ?b)) (+ ?a ?a))
(< (+ ?b (min ?d ?c)) (+ ?c (min ?b ?a))) <=> (< (+ ?b ?d) (+ ?c (min ?b ?a)))
(< (+ ?b (min ?a ?c)) (+ ?c (min ?b ?a))) <=> (< (+ ?b ?a) (+ ?c (min ?b ?a)))
(< (+ ?c (min ?d ?b)) (+ ?c (min ?b ?a))) <=> (< (+ ?c ?d) (+ ?c (min ?b ?a)))
(< (min ?c (+ ?d ?b)) (min ?c (+ ?b ?a))) <=> (< (+ ?d ?b) (min ?c (+ ?b ?a)))
(< (min ?b (+ ?c ?b)) (min ?b (+ ?b ?a))) <=> (< (+ ?c ?b) (min ?b (+ ?b ?a)))
(< (+ ?b (+ ?c ?c)) (+ ?b (min ?b ?a))) <=> (< (min ?b (+ ?c ?c)) (min ?b ?a))
(< (+ ?b (min ?c ?b)) (+ ?a (min ?b ?a))) <=> (< (+ ?b (min ?c ?b)) (+ ?a ?a))
(< (min ?c (min ?a ?b)) (min ?b (+ ?a ?a))) <=> (< (min ?c ?a) (min ?b (+ ?a ?a)))
(< (min ?a (+ ?c ?b)) (min ?a (+ ?b ?a))) <=> (< (+ ?c ?b) (min ?a (+ ?b ?a)))
(< (+ ?a (min ?c ?a)) (min ?b (+ ?a ?a))) <=> (< (+ ?c ?a) (min ?b (+ ?a ?a)))
(< (min ?b (+ ?c ?b)) (min ?b (+ ?a ?a))) <=> (< (+ ?c ?b) (min ?b (+ ?a ?a)))
(< (min ?c (+ ?d ?d)) (min ?c (+ ?b ?a))) <=> (< (+ ?d ?d) (min ?c (+ ?b ?a)))
(< (min ?b (+ ?b ?b)) (min ?a (+ ?b ?a))) <=> (< (+ ?b (+ ?b ?b)) (+ ?a (+ ?a ?a)))
(< (+ ?b (+ ?b ?b)) (+ ?a (+ ?a ?a))) <=> (< (min ?b (+ ?b ?a)) (min ?a (+ ?a ?a)))
(< (min ?c (+ ?c ?b)) (min ?a (+ ?b ?a))) <=> (< (+ ?c (min ?c ?b)) (+ ?a (min ?b ?a)))
(< (+ ?b (+ ?c ?c)) (+ ?b (+ ?a ?a))) <=> (< (+ ?c (min ?c ?b)) (+ ?a (min ?b ?a)))
(< (min ?c (+ ?b ?a)) (+ ?b (min ?b ?a))) <=> (< (min ?c (+ ?b ?b)) (+ ?b (min ?b ?a)))
(< (+ ?b (+ ?a ?a)) (min ?b (+ ?a ?a))) <=> (< (+ ?a (+ ?b ?b)) (min ?a (+ ?b ?b)))
(< (+ ?c (+ ?b ?b)) (+ ?c (min ?b ?a))) <=> (< (+ ?c (+ ?b ?b)) (min ?c (+ ?c ?a)))
(< (min ?b (+ ?b ?c)) (min ?b (+ ?b ?a))) <=> (< (+ ?b (min ?c ?a)) (min ?b (+ ?b ?a)))
(< (min ?b (+ ?a ?a)) (+ ?b (+ ?a ?a))) <=> (< (min ?a (+ ?b ?b)) (+ ?a (+ ?b ?b)))
(< (+ ?b (min ?c ?a)) (+ ?b (+ ?a ?a))) <=> (< (min ?b (+ ?b ?c)) (+ ?b (+ ?a ?a)))
(< (min ?b (+ ?b ?c)) (+ ?c (min ?b ?a))) <=> (< (min ?b (+ ?c ?a)) (+ ?c (min ?b ?a)))
(< (min ?c (+ ?b ?c)) (min ?c (+ ?b ?a))) <=> (< (+ ?b (min ?c ?a)) (min ?c (+ ?b ?a)))
(< (+ ?b (min ?b ?a)) (min ?b (+ ?a ?a))) <=> (< (min ?a (+ ?b ?a)) (min ?a (+ ?a ?a)))
(< (min ?b (+ ?b ?b)) (min ?b (+ ?a ?a))) <=> (< (min ?a (+ ?b ?a)) (min ?a (+ ?a ?a)))
(< (min ?b (+ ?b ?a)) (+ ?b (min ?b ?a))) <=> (< (min ?b (+ ?b ?b)) (+ ?b (min ?b ?a)))
(< (min ?b (+ ?c ?d)) (min ?c (min ?b ?a))) <=> (< (min ?c (+ ?c ?d)) (min ?c (min ?b ?a)))
(< (+ ?a (+ ?b ?b)) (min ?a (+ ?a ?a))) <=> (< (+ ?a (+ ?b ?b)) (+ ?a (min ?a ?b)))
(< (+ ?a (min ?b ?c)) (+ ?c (min ?b ?a))) <=> (< (+ ?b (min ?c ?a)) (+ ?c (min ?b ?a)))
(< (min ?a (+ ?b ?b)) (+ ?b (min ?b ?a))) <=> (< (min ?a (+ ?b ?a)) (+ ?b (min ?b ?a)))
(< (+ ?b (min ?c ?a)) (min ?a (+ ?b ?a))) <=> (< (min ?a (+ ?b ?c)) (min ?a (+ ?b ?a)))
(< (+ ?a (min ?b ?a)) (min ?c (+ ?b ?a))) <=> (< (+ ?a (min ?b ?a)) (min ?c (+ ?b ?b)))
(< (min ?b (+ ?c ?c)) (min ?b (+ ?a ?a))) <=> (< (min ?b (+ ?c ?c)) (min ?b (+ ?c ?a)))
(< (+ ?c (min ?b ?c)) (+ ?b (min ?b ?a))) <=> (< (+ ?c (min ?b ?c)) (+ ?b (min ?c ?a)))
(< (min ?b (+ ?c ?a)) (min ?b (+ ?a ?a))) <=> (< (+ ?a (min ?c ?a)) (min ?b (+ ?a ?a)))"#;

        let client = reqwest::Client::new();

        let mut prior_rules: Ruleset<Pred> = Default::default();

        let mut candidate_rules: Ruleset<Pred> = Default::default();

        for line in candidates_str.lines() {
            let rule_str = line.trim();
            if !rule_str.is_empty() {
                let rule: Rule<Pred> = Rule::from_string(rule_str).unwrap().0;
                println!("Adding rule: {}", rule);
                candidate_rules.add(rule);
            }
        }

        let result = send_score_rules_request(&client, &prior_rules, &candidate_rules).await;
        assert!(result.is_ok());
        let text = result.unwrap();
        println!("Response: {}", text);

    }


    #[test]
    fn filter_rules_keeps_important_ones() {
        todo!()



    }
}


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
