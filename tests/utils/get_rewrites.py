#!/usr/bin/python3
"""
    This is essentially a wrapper script for Anjali's script which
    gets rewrites from the Halide source code.

    Needs CHOMPY_DIR to be set to the path of the chompy directory.
"""

import os, sys

if "CHOMPY_DIR" not in os.environ:
    print("Set CHOMPY_DIR to the path of the chompy directory.")
    sys.exit(1)

SCRIPT_DIR = f"{os.environ['CHOMPY_DIR']}/ruler/scripts"
HALIDE_DIR = f"{os.environ['CHOMPY_DIR']}/halide"

OUTPUT_DIR = f"{os.environ['CHOMPY_DIR']}/tests/utils/"

if __name__ == "__main__":
    if len(sys.argv) != 1:
        sys.exit(1)

    print(f"python3 {SCRIPT_DIR}/scrape_halide_rules.py")

    os.system(f"python3 {SCRIPT_DIR}/scrape_halide_rules.py")

    # at this point, there will be two files in the folder of Anjali's script:
    # - out-c.txt
    # - out-nc.txt

    # we need to move them to the current directory.

    os.system(f"mv {SCRIPT_DIR}/out-c.txt {OUTPUT_DIR}")
    os.system(f"mv {SCRIPT_DIR}/out-nc.txt {OUTPUT_DIR}")

    print("I'm done.")

