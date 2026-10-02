# Lean 4 proof: occupancy and randomized LOCAL MIS lower bound

The occupancy proof and LOCAL reduction are complete in the stated uniform,
measurable synchronous LOCAL model. The main theorem is
`MISLocal.randomized_LOCAL_MIS_iid_not_littleO` in
`MISLocal/AsymptoticLocalLowerBound.lean`.

## The theorem in English

For every family of uniform LOCAL programs, suppose that:

- its worst-case number of communication rounds on size n is `rounds n`;
- every vertex has a unique identifier, and the program can know n;
- each vertex has a private tape drawn independently from a common probability
  distribution (the tape space and distribution may depend on n);
- its output events are measurable functions of the tapes;
- on every n-vertex simple graph it outputs an inclusion-maximal independent
  set with probability at least 2/3.

Then `rounds n` is **not** o(log n / log log n). This uses Mathlib's actual
`Asymptotics.IsLittleO` relation at `Filter.atTop`, rather than a new predicate
whose definition includes the desired lower bound. `localScale n` is exactly
`Real.log (n : Real) / Real.log (Real.log (n : Real))`.

There are no black-box conjectures. The occupancy proof is imported from the
other checked modules in the same project; its entire proof is included in
the standalone file and in the transitive axiom audit.

## Exact program interface and scope

`UniformLocalProtocol n Tape State` has one initialization, transition, and
output function used at every vertex. These functions receive the identifier,
private tape, local state, and neighbor identifiers/states. They receive no
underlying vertex name or full graph. Initialization is given neighbors' IDs
for free. States and messages are unrestricted, and each message reveals the
sender's full state. These conventions strengthen the usual LOCAL model.
The program and its state/tape spaces may depend on n, so this is also valid
for nonuniform families of known-size programs.

The legal input in the final theorem is a graph on `Fin n` with identity IDs.
A program correct for all distinct legal ID assignments must in particular
be correct on these assignments. Any conventional larger legal ID range may
be restricted to a legal set of n identifiers. Sorted neighbor IDs provide
a canonical port numbering. A conventional program correct for arbitrary
port numberings must be correct for this numbering; full-state communication
allows its per-port messages to be reconstructed. The project defines the
uniform full-information protocol directly. It does not formalize a separate
programming language or Turing-machine encoding of all conventional LOCAL
programs.

`MeasurableProgram` requires measurable candidate events for each finite graph
and tentative ID map. This includes the extension to repeated IDs used in the
simulation, even though correctness is required only on legal inputs. It
asserts no correctness, symmetry, probability estimate, or lower bound.
Ordinary finite computations reading random bits have such a measurable
extension. Infinite tape spaces are allowed; no finite support restriction on
tapes is assumed.

The main theorem assumes independent tapes through the actual product measure
`Measure.pi`. A stronger intermediate theorem,
`randomized_LOCAL_MIS_not_littleO`, permits any probability measure on the
ID-indexed tape table, fixed independently of the input graph.

The conclusion rules out a little-o worst-case round bound. The proof gives
an explicit lower bound on a sequence of graph sizes; it does not separately
claim an eventual Omega bound at every integer n, an expected-time lower
bound, or a lower bound for a relaxed success criterion.

## Reduction and parameter proof

1. **Actual blow-up.** `CliqueBlowup` replaces every skeleton vertex by a
   clique of k vertices. Each skeleton edge carries k by k independent fair
   bits specifying cross-clique edges.
2. **Jointly independent tentative IDs.** `DirectedIdentifiers` and
   `IdentifierBits` use two disjoint off-diagonal blocks in every matrix.
   Summing outgoing strings over all incident edges is a surjective additive
   map. The entire tentative-ID vector is proved uniform, including joint
   independence. No independence between IDs and the graph is assumed.
3. **Anonymous simulation.** Collision gating, concrete execution, and repair
   define an actual function on quotient local views. Renaming vertices and
   edges and transposing reversed matrices preserve the simulation. The
   radius is T+3. The outputs have pointwise zero conflict.
4. **Legal local realization.** `LocalGraphRealization` embeds the skeleton
   ball of radius T+2, including all its clique coordinates, into `Fin n`.
   It preserves locally unique tentative IDs. Unused IDs name isolated
   vertices. `EmbeddedLocalExecution` proves that the relevant executions,
   identifiers, and ID-indexed tapes agree. This construction depends on
   matrices and IDs, but not on the tape table. The skeleton can be much
   larger than n: only the required local neighborhood must fit.
5. **Finite skeleton construction.** `FiniteTreePermutations` constructs
   involutions on a finite ball of reduced words. They cancel an equal first
   letter or prepend a different letter, fixing unmatched boundary words.
   `FiniteRegularSkeleton` uses permutations of this word ball as vertices
   and left multiplication by the involutions as edges. The graph is finite
   and D-regular. Evaluation at the empty word embeds each required local
   neighborhood into an acyclic prefix tree. Connectivity proves that every
   required induced edge neighborhood is a tree. No high-girth existence
   theorem or finite-model hypothesis is supplied as a premise.
6. **Probability errors.** `ExtractedCollisions` proves
   delta <= L(L-1)/n, where L is the local clique-ball size. A fixed external
   choice of at most one vertex in each neighboring clique must hit every
   independent root row. `CliqueDomination` unions over all choices, proving
   gamma <= (k+1)^D exp(-k 2^(-D)); the chosen output may depend on the matrices.
7. **Explicit finite parameters.** Set D=2^s, m=2^(2D), k=2m, b=6D+1,
   and n=2^b. `PowerSizeParameters` proves matrix capacity, the required
   logarithm range, and gamma <= 1/8. `PowerBallEstimates` proves that if
   20000(T+3)(s+1) <= D, then the local ball fits, delta <= 1/8, and the
   occupancy upper bound is <= 1/4.
8. **Finite contradiction and asymptotics.** MIS correctness and the legal
   realization force repaired root occupancy with probability at least
   (2/3)(1-delta-gamma) >= 1/2. This contradicts the occupancy cap of 1/4.
   `finite_local_round_bound` therefore proves
   D < 20000(T+3)(s+1), for s >= 20. The final module proves the size sequence
   tends to infinity and log n/log log n <= 28D/(s+1). A hypothetical
   little-o round bound violates the finite inequality for sufficiently
   large s, with the additive three-round slack proved explicitly.

`ConcreteFiniteObstruction` retains the earlier whole-blow-up legalization.
The final theorem uses `LocalSizeObstruction`, which only needs the local ball
size. Earlier conditional scalar and probability-transfer lemmas are retained
as generic assembly lemmas; their hypotheses are discharged in the final proof.

## Occupancy theorem used in the reduction

`MISLocal.TreeGeometry.anonymous_graph_occupancy` proves

    p <= min(1, 5000 r log D / D).

Its inputs are an actual finite, nonempty, simple D-regular graph, induced
edge-centered tree neighborhoods of radius r, independent fair k by k edge
matrices, one anonymous local rule, and zero selected conflict at an edge.
The numerical conditions are D >= 1048576, k >= 1, and D <= log k <= D^2.

An anonymous rule is one function on rooted matrix-labeled views modulo
vertex/edge renaming and edge-orientation reversal. Skeleton names are erased;
matrix entries and the root remain observable. Locality and symmetry are
proved from this definition and constructed regular-tree-neighborhood
isomorphisms. No symmetry certificate is assumed in the public theorem.
Optional finite private root values are supported; the LOCAL reduction uses
Unit there and handles all algorithm tapes by fixing and averaging their table.

The entropy, truncation, ancestor, projection, and final-conflict estimates are
all proved. Conditioning on a null fiber has an explicit normalized fallback.
The independent-source entropy argument adapts Csoka, Harangi, and Virag,
*Entropy and expansion*, Theorem 2.5 (https://arxiv.org/abs/1811.09560).

The final LOCAL theorem is entirely finite. No equivalence with a separately
formalized infinite-tree probability space is needed or claimed.

## Build and inspect

Pinned compiler: **Lean 4.19.0**.
Pinned Mathlib commit: **c44e0c8ee63ca166450922a373c7409c5d26b00b**.
Transitive revisions are locked in `lake-manifest.json`.

With these dependencies installed:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Tests.lean
lake env lean -DwarningAsError=true Audit.lean
lake env lean -DwarningAsError=true mis_local.lean
```

`mis_local.lean` mechanically concatenates the source modules, audit and tests.
Do not import `MISLocal` as well when compiling it. The project archive contains
the split modules and build files; it does not vendor Lean or Mathlib caches.
`node tools/verify.mjs` regenerates the standalone file and runs six compiler
commands, stopping on any nonzero exit code. `verification/commands.json`
records the actual exit codes and output. `source-sha256.json` identifies the
checked source bytes.

## Audit and arithmetic safeguards

All delivered proof files compile with warnings treated as errors. There are
no admissions, user-declared axioms, `native_decide`, custom proof-producing
macros, or executable proof shortcuts. `Audit.lean` traverses the transitive
axiom dependencies of every theorem and non-internal definition in MISLocal,
plus explicitly listed structure roots, and checks that each is in Lean's
checked kernel environment. Only `propext`, `Classical.choice`, and `Quot.sound`
are allowed. The full final theorem types are printed as well.

The audit checks 1,432 theorem/definition roots, including 1,132 theorems.
The main theorem has only the three standard classical dependencies above.
Negative audit tests for a custom axiom and an admitted proof are retained in
`verification/audit-negative-tests.txt`.

Probability subtraction, logarithms and L(L-1)/n are real-valued. Natural
subtractions used for cardinalities or D-1 have their order/positivity guards
proved. No negative natural number is silently treated as a real difference.
Tests cover empty views, zero rounds, null fibers, subtraction, repair, and
support domination. The descending projection's final view is proved empty;
this does not assert that the original algorithm has empty support.

The official compiler and Mathlib sources are unmodified. This container
requires a narrow compatibility shim for self-executable readlink lookups.
It changes only `/proc/<own pid>/exe` to `/proc/self/exe`; it does not alter
proof terms or the kernel. Source: `verification/proc_self_compat.c`. Normal
installations do not need it.
