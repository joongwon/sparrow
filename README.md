# Sparrow

Sparrow is a state-of-the-art static analyzer that aims to verify the absence
of fatal bugs in C source. Sparrow is designed based on the Abstract Interpretation
framework and the analysis is sound in design. Sparrow adopts a number of well-founded
static analysis techniques for scalability, precision, and user convenience.
This is the academic version of Sparrow that is different from the [commercial version][fasoo].

### How to Build
1. Initialize an Opam switch and install dependencies.
2. Build using Dune: `dune build`.
