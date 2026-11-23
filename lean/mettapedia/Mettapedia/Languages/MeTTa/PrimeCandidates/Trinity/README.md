# Operational, intensional and extensional program comparisons

The entry [Trinity.lean](../Trinity.lean) collects concrete programs with
separately constructed execution, typing and model maps. The common triangle
interfaces live in `Computability.ComputationalTrinity`; a commuting comparison
is weaker than an exact correspondence.

| Example | Mathematical content |
|---|---|
| Append | Authored recursion, admitted typing and set recursion agree on the same program; the comparison is not globally exact. |
| Binary arithmetic | Declared binary datatypes and equations have typed computations and a unary-valued interpretation. Native-oracle agreement remains an explicit backend premise. |
| Log2 | The written nonstructural equation is admitted through its set solution; the readout loses input distinctions. |
| Streams | Finite observations can terminate although the stream does not. Hyperset readout preserves branching while forgetting multiplicity and cycle length. |
| Reverse | Plain and accumulator reversal agree extensionally, with different operational costs. |
| Graded identity | Stored occurrences and charges preserve more than value support or total grade. |
| Demand | Eager, shared and resampled computations agree only under the stated bag, support or effect observer. |

Every joined theorem uses the same program and the stated maps. Set-model
agreement is not syntactic readback, and a specimen does not settle a global
foundation or execution policy. Additional examples should reuse these maps
and interfaces rather than introduce another notion of a three-face triangle.
