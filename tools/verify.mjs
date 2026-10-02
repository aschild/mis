import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { fileURLToPath } from 'node:url';
import path from 'node:path';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const files = [
  'MISLocal/FiniteProbability.lean', 'MISLocal/Repair.lean',
  'MISLocal/Identifiers.lean', 'MISLocal/Extraction.lean',
  'MISLocal/Collisions.lean', 'MISLocal/TapeAveraging.lean',
  'MISLocal/InfiniteTapes.lean', 'MISLocal/Obstruction.lean',
  'MISLocal/Numerics.lean', 'MISLocal/ConditionalMain.lean',
  'MISLocal/Entropy.lean', 'MISLocal/EntropyBudget.lean',
  'MISLocal/ConditionalEntropy.lean', 'MISLocal/EntropyCopying.lean',
  'MISLocal/RareEntropy.lean', 'MISLocal/Conditioning.lean',
  'MISLocal/Projection.lean', 'MISLocal/FirstFailure.lean',
  'MISLocal/ProjectedBudget.lean', 'MISLocal/OccupancyNumerics.lean',
  'MISLocal/Hellinger.lean', 'MISLocal/Locality.lean', 'MISLocal/ZeroRadius.lean',
  'MISLocal/TopLists.lean', 'MISLocal/IndependentEvents.lean',
  'MISLocal/DenseMatrix.lean', 'MISLocal/FrequentLabels.lean',
  'MISLocal/ListCapture.lean', 'MISLocal/BranchParameters.lean',
  'MISLocal/BranchTransfer.lean', 'MISLocal/EntropyProduct.lean',
  'MISLocal/RandomMatrix.lean', 'MISLocal/Truncation.lean',
  'MISLocal/ScalarEntropy.lean', 'MISLocal/TruncationNumerics.lean',
  'MISLocal/ProductSources.lean', 'MISLocal/RevealedEntropy.lean',
  'MISLocal/EntropyCharging.lean',
  'MISLocal/TreeParent.lean', 'MISLocal/ParentCharging.lean',
  'MISLocal/GeometricCharging.lean', 'MISLocal/SourceGrouping.lean',
  'MISLocal/ConditionalSources.lean', 'MISLocal/SharedViews.lean',
  'MISLocal/NestedGiven.lean', 'MISLocal/WeightedBranch.lean',
  'MISLocal/EndpointTails.lean', 'MISLocal/ListParameters.lean',
  'MISLocal/TableSampling.lean', 'MISLocal/AnySourceEntropy.lean',
  'MISLocal/PrivateSources.lean', 'MISLocal/StochasticEntropy.lean',
  'MISLocal/BernoulliRounding.lean', 'MISLocal/AncestorSequence.lean',
  'MISLocal/TruncationEstimate.lean',
  'MISLocal/SymmetryTransport.lean', 'MISLocal/FiniteKernels.lean',
  'MISLocal/ProjectedTails.lean', 'MISLocal/LocalScalarMoment.lean',
  'MISLocal/LocalHomogeneity.lean', 'MISLocal/InputGeometry.lean',
  'MISLocal/GeometricTruncation.lean', 'MISLocal/HomogeneousEntropy.lean',
  'MISLocal/ConditionalReadLocality.lean', 'MISLocal/ProjectionConflict.lean',
  'MISLocal/GeometricBudget.lean', 'MISLocal/FiniteOccupancy.lean',
  'MISLocal/GraphBalls.lean', 'MISLocal/GraphInputGeometry.lean',
  'MISLocal/PrivateGeometry.lean', 'MISLocal/GraphOccupancy.lean',
  'MISLocal/InputRelabeling.lean', 'MISLocal/GraphTapeReduction.lean',
  'MISLocal/GraphNeighborhoodIso.lean', 'MISLocal/GraphViewTransport.lean',
  'MISLocal/AnonymousRule.lean', 'MISLocal/AnonymousTransport.lean',
  'MISLocal/AnonymousOccupancy.lean', 'MISLocal/AnonymousTapeReduction.lean',
  'MISLocal/CliqueBlowup.lean',
  'MISLocal/UniformLocalProtocol.lean',
  'MISLocal/UniformExtraction.lean',
  'MISLocal/DirectedIdentifiers.lean',
  'MISLocal/IdentifierBits.lean',
  'MISLocal/ViewSimulation.lean',
  'MISLocal/AnonymousLocalReduction.lean',
  'MISLocal/SnapshotAgreement.lean',
  'MISLocal/LocalBallCounts.lean',
  'MISLocal/ExtractedCollisions.lean',
  'MISLocal/SnapshotLocality.lean',
  'MISLocal/BlowupIDCompletion.lean',
  'MISLocal/MatrixUnitProbability.lean',
  'MISLocal/ConcreteOccupancyReduction.lean',
  'MISLocal/FairBitProjection.lean',
  'MISLocal/FairRowDomination.lean',
  'MISLocal/CliqueDomination.lean',
  'MISLocal/ConcreteFiniteObstruction.lean',
  'MISLocal/PrefixTree.lean',
  'MISLocal/FiniteTreePermutations.lean',
  'MISLocal/FiniteRegularSkeleton.lean',
  'MISLocal/EmbeddedLocalExecution.lean',
  'MISLocal/LocalGraphRealization.lean',
  'MISLocal/SuccessObstruction.lean',
  'MISLocal/LocalSizeObstruction.lean',
  'MISLocal/PowerSizeParameters.lean',
  'MISLocal/PowerBallEstimates.lean',
  'MISLocal/FiniteLocalLowerBound.lean',
  'MISLocal/AsymptoticLocalLowerBound.lean',
  'Audit.lean', 'Tests.lean',
];
const imports = new Set();
const sections = files.map(file => {
  const body = readFileSync(path.join(root, file), 'utf8').split('\n').filter(line => {
    if (!line.startsWith('import ')) return true;
    if (!line.startsWith('import MISLocal')) imports.add(line);
    return false;
  }).join('\n');
  return `/- ===== Source: ${file} ===== -/\n${body}`;
});
const header = `/-!
ANONYMOUS OCCUPANCY AND ASYMPTOTIC RANDOMIZED LOCAL MIS LOWER BOUND PROVED.

MISLocal.randomized_LOCAL_MIS_iid_not_littleO proves that a measurable
uniform LOCAL program family, correct with probability at least 2/3 on
every n-vertex graph, cannot have o(log n / log log n) worst-case rounds.
The state and tape spaces and program may depend on n. Infinite private
tapes are allowed. The only algorithmic premises are measurability and
MIS correctness. No reduction, skeleton-existence, symmetry, probability
estimate or asymptotic numerical inequality is assumed.

MISLocal.TreeGeometry.anonymous_graph_occupancy proves
p <= min(1,5000*r*log D/D) for anonymous radius-r rules on finite D-regular
graphs with the displayed tree neighborhoods, independent fair edge matrices
and iid finite private vertex values. D >= 1048576 and D <= log k <= D^2
are explicit. An AnonymousRule is one function on rooted matrix-labeled views
modulo vertex/edge renaming and edge-orientation reversal. Skeleton names
cannot be inspected. Locality and ViewHomogeneous are proved from this
definition and constructed regular-tree-neighborhood isomorphisms.
The entropy, truncation, ancestor, projection-budget and final-conflict estimates
are proved, not assumed. InputRelabeling derives probability preservation
from coordinate weights. The original graph_occupancy remains a more general
internal theorem with an explicit symmetry premise. AnonymousTapeReduction
applies the anonymous bound inside the fixed-tape averaging and
finite obstruction. ConcreteFiniteObstruction now constructs the actual
clique blow-up, jointly uniform matrix-derived IDs, collision gate, anonymous
quotient rule, global repaired process, zero conflict, local legal-ID
completion, collision and external-domination estimates. LocalGraphRealization
preserves a local execution on a legal n-vertex input with isolated padding.
FiniteRegularSkeleton constructs actual finite regular graphs with arbitrary
tree neighborhood depth from involutions on bounded reduced words.
PowerSizeParameters and PowerBallEstimates discharge all finite inequalities.
AsymptoticLocalLowerBound concludes using the powers-of-two size subsequence.
The iid corollary uses the actual product measure of arbitrary private tapes.
See README.md in the accompanying project archive for the exact scope.

This file mechanically concatenates the project's modules, audit, and tests.
Do not import MISLocal as well: the declarations would then be duplicated.
-/\n`;
const bundle = [...imports].join('\n') + '\n\n' +
  'set_option autoImplicit false\nset_option warningAsError true\n\n' +
  header + '\n' + sections.join('\n\n');
writeFileSync(path.join(root, 'mis_local.lean'), bundle);

mkdirSync(path.join(root, 'verification'), { recursive: true });
const commands = [
  ['--version'], ['env', 'lean', '--version'], ['build', 'MISLocal'],
  ['env', 'lean', '-DwarningAsError=true', 'Tests.lean'],
  ['env', 'lean', '-DwarningAsError=true', 'Audit.lean'],
  ['env', 'lean', '-DwarningAsError=true', 'mis_local.lean'],
];
const results = [];
for (const args of commands) {
  const command = ['lake', ...args].join(' ');
  process.stdout.write(`Checking: ${command}\n`);
  const result = spawnSync('lake', args, {
    cwd: root, encoding: 'utf8', maxBuffer: 32 * 1024 * 1024,
  });
  results.push({ command, exitCode: result.status, signal: result.signal,
    stdout: result.stdout ?? '', stderr: result.stderr ?? '',
    launchError: result.error?.message ?? null });
  writeFileSync(path.join(root, 'verification', 'commands.json'),
    JSON.stringify(results, null, 2) + '\n');
  if (result.status !== 0) {
    process.stderr.write((result.stdout ?? '') + (result.stderr ?? ''));
    throw new Error(`Verification stopped: ${command}, exit ${result.status}`);
  }
}
const auditedFiles = [...files, 'MISLocal.lean', 'lakefile.toml', 'lean-toolchain',
  'lake-manifest.json', 'tools/verify.mjs', 'mis_local.lean', 'README.md',
  'verification/proc_self_compat.c', 'verification/audit-negative-tests.txt'];
const hashes = Object.fromEntries(auditedFiles.map(file => [file,
  createHash('sha256').update(readFileSync(path.join(root, file))).digest('hex')]));
writeFileSync(path.join(root, 'verification', 'source-sha256.json'),
  JSON.stringify(hashes, null, 2) + '\n');
process.stdout.write('All listed compiler commands exited with code 0.\n');
