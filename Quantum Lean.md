# Quantum Lean

Quantum Lean is a foundation for formalising quantum algorithms in Lean. I created Quantum Lean for my Bachelor's thesis in Computer Science, at the University of Amsterdam: "A Foundation to Formalise Quantum Algorithms in Lean".

Quantum Lean applies the mathematical theorems in `mathlib` to formalise quantum algorithms by creating a foundation of theorems and definitions which can be used for this purpose.

## Definitions and Theorems

Quantum Lean provides a set of definitions, theorems and abbreviations of types in the `Data/Circuits/` directory. This directory includes:

- `Types.lean`: The type abbreviations for Quantum Lean;
- `Reindex.lean`: The reindexing definitions used throughout Quantum Lean theorems;
- `TensorPower.lean`: The tensor power definition and theorems;
- `Qubits.lean`: The qubit definitions.

Each of these files contains theorems and definitions of their respective content. The file itself has a preamble that explains what can be found in the file and what it is used for.

## Gates and Equivalences

In the `Gates/` directory, one can find a file for each category of gates in Quantum Lean. There currently is files for the following gate categories.

- `Hadamard.lean`: The Hadamard gate;
- `Pauli.lean`: The Pauli X, Y and Z gates, with $H*X*H=Z$ and $H*Z*H=X$ equivalences;
- `Conditionals.lean`: The conditional CX and CZ gates, as well as a SWAP definition.

Each of these files contains the definition of the basic gate, an $n$-qubit tensor power of that gate and any identities they may have, such as $H * H = I$.

## Formalisations of Algorithms

In the `Algorithms/` directory, one will find a single file for each formalised algorithm. Each of these files contains the mathematical theory behind the algorithm and the Lean code that formalises the algorithm.

- `Deutsch.lean`: The Deutsch algorithm with a phase oracle;
- `BernsteinVazirani.lean`: The Bernstein–Vazirani algorithm with an arbitrary number of qubits;
- `OneFourGrover.lean`: The one-out-of-four Grover algorithm utilising controlled gates.

## Learning Lean

To start utilising Lean, it may be helpful to first learn its basics. Here is a small list of resources to learn Lean that I found helpful.

- The [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4) for Lean 4;
  - An introduction to the basic principles of Lean;
  - No previous knowledge required;
  - Does not provide deep Lean knowledge.
- The [Learning Lean 4](https://leanprover-community.github.io/learn.html) page;
  - Contains recommendations for different learning resources such as books and hands-on approaches;
  - Kept up to date by the Lean community.
- [Loogle](loogle.lean-lang.org), a Lean search engine for finding applicable theorems;
- Lean's [Zulip Chat](https://leanprover.zulipchat.com/), a place to ask questions and talk to Lean experts,
- The `mathlib` [GitHub page](https://github.com/leanprover-community/mathlib4);
  - Contains all theorems from `mathlib`;
  - More searchable than official documentation site;
  - Requires some time to find the right theorems at times;
  - Notable files:
    - `Mathlib/Data/Complex/Basic.lean`: The complex number definition;
    - `Mathlib/Data/Matrix/Basic.lean`: The matrix definitions such as `mul_apply`;
    - `Mathlib/Data/Matrix/Kronecker.lean`: The matrix kronecker product definition;
    - `Mathlib/Data/Matrix/Notation.lean`: The matrix notation macro `!![]`.
