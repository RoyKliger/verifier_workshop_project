# Formal Verification Project for While Language

Project Overview
This project is a formal verification tool designed for a simple programming language that supports basic integer operations and control structures, specifically the while language. The tool verifies program correctness by checking Hoare triples: {P} c {Q}, where P is a precondition, c is a command or series of commands, and Q is a postcondition. Using the first-order logic and SMT solver Z3, this tool systematically verifies that a given program adheres to specified logical constraints.

Key Features
Supported Commands: The language includes assignment, sequence (; operator), while and for loops, and if/else blocks.

Verification Techniques

1. Weakest Liberal Precondition (wlp) Verification
The wlp approach is effective for loop-free code verification. It calculates the weakest precondition (the minimal condition on inputs) that guarantees a postcondition Q holds after executing the code.

Use Case: Works best for loop-free code.
Limitations: Applying wlp directly to loops requires iterating over all variable changes, which can be inefficient or even infeasible for complex loops. Loop invariants are required to address these limitations.

2. Hybrid Verification (wlp/VC)
The hybrid wlp/VC method combines the strengths of wlp and verification conditions (VCs):

Loop-free Segments: Verified with wlp, as it’s more efficient.
Loops: Verified using VCs and loop invariants.
Middle Annotations: Placed between sequential components, including before and after loops, to provide intermediary states for verification.
This approach is more flexible than wlp alone and can verify a wider range of programs, including those with loops, as long as strong enough invariants and middle annotations are provided.

3. Hoare Logic VC Verification
For the most detailed verification, Hoare Logic is used, generating verification conditions for each line or block in the program:

Mid Annotations: Necessary between every two lines of code.
Use Case: Ensures precise verification, especially for complex control flows with nested structures.
Advantages: Guarantees correctness if all annotations are accurate and strong enough.