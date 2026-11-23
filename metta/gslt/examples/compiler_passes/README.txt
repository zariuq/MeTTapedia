Dataflow specialization with Datalog and ground CHR

program.metta contains pure Add, Constant, Input and Output data. It has a
shared subexpression, a repeated operand, duplicate work requests, an
unknown input and a disconnected cycle.

demand.dl computes the backward dependency closure of the requested outputs.
Cycles terminate and repeated derivations produce one Need fact. This is a
dataflow demand slice; the example has no effectful or control-flow operators.

constant_fold.pl states three ground CHR rules: fold an addition with one
repeated input, fold an addition with two distinct inputs, and record each
constant occurrence once. The showcase generator prepares their independent
typed IR, while the shared MeTTa CHR controller performs the actual execution.
This is a prepared-IR example; ordinary CHR source loading and the universal
controller correspondence are still C0 work.

The MeTTa adapter selects seeds by Need while preserving their order and
multiplicity. The result contains constant(out,15), two constant(copy,7)
occurrences, and the residual add(future,dynamic,a). The unknown input is a
ground node name with no supplied constant, not a CHR logical variable. The
dead cycle is excluded. Eight propagation-history entries account for the
eight constant occurrences, including the two equal copy results.

From the repository root:

  python3 metta/gslt/tools/test_compiler_pass_showcase.py OUTPUT \
    --cetta CETTA_BINARY --souffle SOUFFLE_BINARY

The tool builds the prepared matcher, runs both passes in one MeTTa program,
checks exact resumption, and compares the demand set with Souffle and the
final multiset with SWI-CHR. OUTPUT/run.metta is the runnable artifact; run
it from OUTPUT so that SourceFile resolves demand.dl. Runtime execution
does not launch Lean or either reference implementation.

Plain MeTTa can implement the same algorithms. The guest languages provide
the closure/deduplication policy and the ordered resource/history machinery
as reusable semantics, rather than requiring each program to reconstruct
those mechanisms. Native compilation is a separate realization of these
same contracts; no performance advantage is claimed by this example.
