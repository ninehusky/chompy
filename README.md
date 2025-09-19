# Conditional Rewrite Rule Synthesis Using E-Graphs and LLMs

This is the artifact for our paper "Conditional Rewrite Rule Synthesis Using E-Graphs and LLMs".
In our paper, we discuss an extension to theory explorers that allow for (1) conditional
rewrite rule synthesis 

- Available: The artifact is available on Zenodo.
- Functional: Below we provide instructions for setting up the artifact. Then, we list the claims
  in the paper and provide instructions for how to recreate each claim.
- Reusable: Finally, we provide instructions for extending Chompy. These instructions describe
  how to set up Enumo on a different machine, modify the code, and extend it to
  find rewrites for new domains.

## Overview

Our paper makes three claims:

**How powerful are Chompy's rules?** 
- Without LLM assistance, Chompy's rules subsume up to 71.1% of handwritten rules, as seen in the
  `baseline` row of `Table 1`.

**How do LLMs impact ruleset quality?** 
- Using LLMs to guide Chompy's filtering mechanism, Chompy's ruleset size decreases by up to
  44.3%
  with a decrease in derivability of as little as 4.5%, as shown in the `filter_5` row of `Table 1`.

**How does our technique of implication propagation affect conditional rule synthesis?** 
- If Chompy does not use our technique of implication propagation, it runs for several hours --
  much longer than the baseline time. In this time, it discovers many more rules
  than the final output of Chompy, as described in `Section 4.3`.

