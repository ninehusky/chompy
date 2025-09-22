import os
import json
import csv
from collections import defaultdict

RUN_TYPES = [
    "enum_only",
    "baseline_and_filter_1",
    "baseline_and_enum",
    "baseline_and_filter_5",
    "baseline_with_filter_5_and_enum",
    "baseline",
]

CSV_LABELS = {
    "enum_only": "enum_only",
    "baseline_and_filter_1": "filter_1",
    "baseline_and_enum": "with_enum",
    "baseline_and_filter_5": "filter_5",
    "baseline_with_filter_5_and_enum": "enum+filter",
    "baseline": "baseline",
}

ROW_ORDER = [
    "enum_only",
    "baseline_and_filter_1",
    "baseline_and_enum",
    "baseline_and_filter_5",
    "baseline_with_filter_5_and_enum",
    "baseline",
]

def parse_log_seconds(log_path):
    with open(log_path) as f:
        for line in f:
            if "finished recipe (seconds:" in line:
                return float(line.split("seconds:")[1].split(")")[0])
    return None

def count_rules(txt_path):
    with open(txt_path) as f:
        return sum(1 for _ in f)

def parse_json(json_path):
    with open(json_path) as f:
        data = json.load(f)
    results = {}
    for direction in ["forwards", "backwards"]:
        can = len(data[direction]["can"])
        cannot = len(data[direction]["cannot"])
        results[direction] = (can, can + cannot)
    return results

def main():
    # get from command line args
    import sys
    root = sys.argv[1]
    out_csv = sys.argv[2]

    stats = defaultdict(lambda: {"ruleset_lengths": [], "seconds": []})
    derivs = defaultdict(lambda: defaultdict(lambda: defaultdict(list)))

    for subdir in os.listdir(root):
        run_dir = os.path.join(root, subdir, "full")
        if not os.path.isdir(run_dir):
            continue
        for run_type in RUN_TYPES:
            run_path = os.path.join(run_dir, run_type)
            if not os.path.isdir(run_path):
                continue

            txt_file = os.path.join(run_path, f"full_{run_type}.txt")
            log_file = os.path.join(run_path, f"full_{run_type}.log")

            if os.path.exists(txt_file):
                rules = count_rules(txt_file)
                stats[run_type]["ruleset_lengths"].append(rules)

            if os.path.exists(log_file):
                secs = parse_log_seconds(log_file)
                if secs is not None:
                    stats[run_type]["seconds"].append(secs)

            for fname in os.listdir(run_path):
                if fname.endswith(".json") and "_against_" in fname:
                    derive_type = fname.split("_against_")[1].split(".")[0]  # halide / caviar
                    json_path = os.path.join(run_path, fname)
                    res = parse_json(json_path)
                    for direction, (num, den) in res.items():
                        derivs[run_type][derive_type][direction].append((num, den))

    # write CSV
    with open(out_csv, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["run_type", "num_rules", "caviar_derivability", "halide_derivability", "runtime_seconds"])

        for run_type in ROW_ORDER:
            if run_type not in stats or not stats[run_type]["seconds"]:
                continue

            avg_secs = sum(stats[run_type]["seconds"]) / len(stats[run_type]["seconds"])
            avg_len = sum(stats[run_type]["ruleset_lengths"]) / len(stats[run_type]["ruleset_lengths"])

            # Halide derivability: average numerators / fixed denominator 84
            halide = None
            if "halide" in derivs[run_type]:
                numerators = [num for num, _ in derivs[run_type]["halide"]["forwards"]]
                if numerators:
                    halide = round((sum(numerators) / len(numerators) / 84) * 100, 1)

            # Caviar derivability: average fractions normally
            caviar = None
            if "caviar" in derivs[run_type]:
                fracs = derivs[run_type]["caviar"]["forwards"]
                if fracs:
                    caviar = round(sum(num / den for num, den in fracs) / len(fracs) * 100, 1)

            writer.writerow([
                CSV_LABELS.get(run_type, run_type),
                round(avg_len, 1),
                None if caviar is None else caviar,
                None if halide is None else halide,
                round(avg_secs, 1),
            ])

    print(f"Wrote {out_csv}")

if __name__ == "__main__":
    main()
