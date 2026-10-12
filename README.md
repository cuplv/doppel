# Doppel: Symbolic Active Indistinguishability in F\*

This F\* development is the framework **Doppel**, and case studies, from the
paper *Real Ideals: Symbolic Verification of Simulation-Based Security*. It
formalizes **testing equivalence** — an indistinguishability notion for security
protocols modelled in the symbolic (Dolev–Yao) style — and uses it to verify
that concrete protocol *implementations* (the "real" world) are observationally
indistinguishable from *idealized* functionalities composed with a simulator
(the "ideal" world) in the presence of an active adversary (a "tester"). This is
the symbolic analogue of simulation-based (real/ideal) security: a protocol
*realizes* an ideal functionality when no tester can distinguish the two.

The core idea: a protocol is modelled as a **reactive labelled transition
system (RLTS)**, composed with a **tester** (adversary) that interacts with it
and accumulates knowledge. Two protocols are **testing equivalent** when, for
every interaction the tester can drive against one, it can drive a matching
interaction against the other with the same observable effects and ending in
*statically equivalent* knowledges — so the tester can never tell them apart.
Rather than reason about traces directly, the development establishes a
**sufficient condition**: exhibiting a **barrier bisimulation up to
right-movable partitions** between two systems implies they are testing
equivalent. Each example proves indistinguishability by constructing such a
bisimulation.

> **Naming note.** The paper standardizes on *barrier bisimulation*; the F\*
> module names and identifiers here (like the companion Lean development) retain
> the earlier name *observational (bi)simulation* (`ObservationalBisimulation`,
> `obs_bisim_up_to_partitions`, …). They denote the same notion.

The framework's two central metatheorems are mechanized in the companion
**Lean** development and axiomatized here (see [Metatheory mechanized in
Lean](#metatheory-mechanized-in-lean)). Code comments cite the paper by
section, definition and theorem number: the formal model lives in paper §3
("Formal model and definitions") and the two proof techniques (barrier
bisimulation and its Lipton-style right-moving partitioned relaxation) in
paper §4 ("Proving testing equivalence").

## Getting started

### Requirements

Doppel was developed and tested with exactly the following versions (on Ubuntu
26.04, x86_64). Other F\* versions may work, but F\*'s SMT encoding changes
between versions and SMT-heavy proofs like these can become unstable, so we
recommend the pinned versions.

| Tool | Version | Notes |
|---|---|---|
| F\* | release tag [`v2026.05.31`](https://github.com/FStarLang/FStar/releases/tag/v2026.05.31) (`fstar.exe --version` reports `2026.05.31~dev`, commit `097bda35`) | installed with opam |
| Z3 | 4.13.3 | the version F\* expects; must be on `PATH` as `z3` |
| OCaml | 5.4.1 | only needed to build F\* |
| opam | ≥ 2.1 (tested with 2.5.1) | |
| GNU make, Python 3 | any recent | Python ≥ 3.9 for the scripts in `scripts/` |

Verifying everything takes about 2 minutes of wall-clock time with `make -j8`
(about 8 minutes of CPU time in total, so roughly 8 minutes with plain `make`),
and needs about 2 GB of RAM per parallel job.

### Installation

```sh
# 1. Create an opam switch with the right OCaml (skip if you already have one)
opam init --bare -n            # only if opam has never been initialized
opam switch create doppel ocaml-base-compiler.5.4.1
eval $(opam env --switch=doppel)

# 2. Install Z3 4.13.3 and F* at the pinned release tag
#    (builds OCaml dependencies and F* from source: ~15 min on a multi-core machine)
opam install z3.4.13.3
opam pin add fstar "git+https://github.com/FStarLang/FStar#v2026.05.31"

# 3. Check the versions
fstar.exe --version   # F* 2026.05.31~dev ... commit=097bda35...
z3 --version          # Z3 version 4.13.3 - 64 bit
```

Alternatively, if you already have a build of F\* at that tag, set
`FSTAR_HOME` to its root: the Makefile then uses `$FSTAR_HOME/bin/fstar.exe`.

### Building and checking

All commands are run from the root of this repository.

```sh
make -j8                                   # verify everything (~2 min with -j8)
make output/StaticEquivalence.fst.checked  # verify one module (and its dependencies)
make audit                                 # list every admit/assume (see below)
make clean                                 # remove all verification results
```

Verification results (`.checked` files) are written to `output/`. Running
`make` again only re-verifies modules whose sources changed. Module names in
targets are dotted (`output/MA.Ideal.fst.checked`), not paths. After adding,
renaming or deleting a module, or changing its `open`s, run `make .depend`
first so that the dependency graph is regenerated.

A successful run ends with `Verified module: ...` / `All verification
conditions discharged successfully` lines for every module and no `Error`.
The following warnings are expected and harmless:

- `Warning 274: Implicitly opening namespace 'ma.' shadows module 'adversary'`
  (and the same for `smd.`): the example modules `MA.Adversary` and
  `SMD.Adversary` share their last name component with the library module
  `Adversary`.
- `Did not expect module FStar.... to be already checked`: F\*'s standard
  library is found pre-checked in the opam installation rather than in
  `output/`.

### Auditing escape hatches

`make audit` (equivalently `python3 scripts/audit_assumes.py` after `make`)
lists every escape hatch in the development. It combines a source scan for
`admit`, `assume`, `tadmit`, `magic`, `unsafe_coerce`, `--admit_smt_queries`
and `--lax` (ignoring comments and strings) with F\*'s own
`--report_assumes warn` report. It takes about a minute and fails if it finds
anything beyond the four expected escape hatches. Its output (the `code:`
line printed under each entry is omitted here) is:

```
Escape hatches found (file:line, what it is, found by):
  ObservationalBisimulation.fst:39     obs_bisim_up_to_partitions_implies_t_equivalence (paper Thm 4.7), proved in Lean [source scan, F* report]
  ObservationalBisimulation.fst:68     obs_bisim_up_to_partitions_implies_t_equivalence' (paper Thm 4.13), proved in Lean [source scan, F* report]
  helpers/FStar.PartialMap.Ext.fst:15  FStar.PartialMap.Ext.map: workaround for opaque FStar.PartialMap (SMD example only) [source scan, F* report]
  helpers/FStar.PartialMap.Ext.fst:19  FStar.PartialMap.Ext.sel_map: workaround for opaque FStar.PartialMap (SMD example only) [source scan, F* report]

AUDIT PASSED: the only escape hatches are the 4 expected ones.
```

See [Metatheory mechanized in Lean](#metatheory-mechanized-in-lean) and
[Example-specific helpers](#example-specific-helpers) for why these are
justified.

## Repository layout

```
.                 the reusable Doppel library (top-level modules, see below)
helpers/          general-purpose F* libraries used by the library and examples
examples/         the two case studies of the paper, as usage examples
  secure_message_delivery/     SMD.*  (paper §5.1)
  nsl_mutual_authentication/   MA.*   (paper §5.2)
scripts/          audit_assumes.py (escape-hatch audit), estimate_loc.py (Table 1)
Makefile          verification build; output/ holds the .checked results
```

### The Doppel library (reusable)

The **top-level modules** form the reusable library: they define the model
(protocols, adversaries, the composed tested system, static and testing
equivalence) and the proof technique (barrier bisimulation up to right-movable
partitions), independently of any particular protocol. Read the `.fsti`
interface of a module first; the `.fst` holds the proofs.

| Module | Contents |
|---|---|
| `SymbolicTypes` | Base symbolic types: `knowledge` (a `seq term`), channel ids, knowledge membership. |
| `Adversary` | The `adversary` typeclass: derivations, `derive`, the `indistinguishable` relation (required to be an equivalence relation), and helper fields. |
| `Protocol` | Protocols as RLTSs: transition labels (`Internal` / `Observable`), protocol state (`inputs` bag × internal state), and the `protocol` typeclass. |
| `StaticEquivalence` | `statically_equivalent`, plus the bijective-correspondence machinery (`bijective_correspondence_implies_static_equivalence`) used to discharge static equivalence. |
| `TestedSystem` | The composed tester ∥ protocol system: combined state, combined labels, the transition relation `transitions'`, the knowledge-validity predicates, and `system` (compose a protocol with an adversary). |
| `TestEquivalence` | `multi_transitions`, observable effect projection (`label_effects`), and the `t_preorder` / `t_equivalence` definitions. |
| `ObservationalBisimulation` | Partitions, right-movability (`right_movable`, `right_movable_mod_inv`), observational (= barrier) bisimulation up to partitions, and the two main metatheorems. |
| `SencTerms`, `AdversarySenc` | A term algebra and Dolev–Yao adversary for symmetric encryption (`derive`, `derivable`, indistinguishability, and lemmas about them). |
| `AencTerms`, `AdversaryAenc` | The same for asymmetric (public-key) encryption. |

The library uses three of the helper libraries in `helpers/`, which are
therefore part of it: `Bag` (multisets; the protocols' input bags), `Partition`
(the `partition` typeclass: an equivalence relation on labels) and
`FStar.Set.Properties` (lemmas about `FStar.Set`).

The library's **only** escape hatches are the two metatheorems in
`ObservationalBisimulation`, which are proved in the companion Lean development
(see below). Everything else is verified by F\*. `Main.fst` is an empty
placeholder module.

### Example-specific helpers

`helpers/FStar.Bijection.Ext` (extra lemmas about `FStar.Bijection`) and
`helpers/FStar.PartialMap.Ext` (extra operations on `FStar.PartialMap`) are
only used by the examples and are not part of the library.

`FStar.PartialMap.Ext` **admits** `map` (mapping a function over the values of
a `PartialMap`) and its specification `sel_map`
(`sel (map f m) k == mapTot f (sel m k)`), which the SMD example's state
machinery uses. These admits are a temporary workaround: `FStar.PartialMap`
keeps its definitions opaque behind its interface, which does not expose
enough to define `map` or prove `sel_map` from outside the module. Once these
definitions are upstreamed into `FStar.PartialMap` in F\*'s standard library
(where the representation is visible), the admits are no longer needed.

### Examples (`examples/`)

Two end-to-end indistinguishability proofs (the paper's case studies, paper §5),
each showing that a protocol implementation *realizes* an ideal functionality
composed with a simulator. They double as worked examples of how to use the
library.

- **`secure_message_delivery/` (SMD)**: concurrent two-party secure message
  delivery. The top-level theorem is
  `SMD.ObservationalBisimulation.Proof.smd_t_equivalence`. It uses the
  unconditioned partitioned theorem
  (`obs_bisim_up_to_partitions_implies_t_equivalence`, paper Thm. 4.7) with
  the partition by session `smd_partition`.
- **`nsl_mutual_authentication/` (MA)**: the Needham–Schroeder–Lowe protocol
  realizing ideal mutual authentication under statically corrupted
  participants. The top-level theorem is
  `MA.ObservationalBisimulation.Proof.ma_t_equivalence`. It uses the
  invariant-conditioned variant
  (`obs_bisim_up_to_partitions_implies_t_equivalence'`, paper Thm. 4.13) with
  the partition by session, participants and role
  (`MA.PartitioningRole.ma_partition_role`), since right-movability only
  holds at reachable states (`MA.IdealInvariants.ma_ideal_system_inv`).

## Using the library: proving a new protocol realizes a functionality

To prove that a protocol `P` is testing equivalent to an ideal functionality
composed with a simulator `Q`, follow the structure of the examples (module
prefix `SMD.` or `MA.`; the SMD example is the smaller one and the better
starting point):

1. **Terms and adversary.** Pick (or write) a term algebra and an `adversary`
   instance: reuse `SencTerms`/`AdversarySenc` or `AencTerms`/`AdversaryAenc`,
   or write a new instance of the `Adversary.adversary` class. Protocol-specific
   types (session ids, effects, label ids) go in `*.Types`; `*.Adversary` holds
   protocol-specific lemmas about the adversary.
2. **The two protocols.** Define each side as an instance of
   `Protocol.protocol` (`SMD.Implementation`/`MA.NSL` for the real world,
   `SMD.Ideal`/`MA.Ideal` for the ideal functionality plus simulator) and prove
   that its transitions only consume inputs (`*_valid_transitions`). Then
   compose each with the adversary using `TestedSystem.system`
   (`*.TestedProtocols`: `smd_impl_system`, `smd_ideal_system`).
3. **Partition and right-movability.** Define a `Partition.partition` on
   labels (usually by session; see `smd_partition` in
   `SMD.ObservationalBisimulation.Proof.fsti` and `MA.PartitioningRole`) and
   prove it is `right_movable` for both systems. If that only holds on
   reachable states, prove `right_movable_mod_inv` for an inductive invariant
   instead (`*.IdealInvariants`, `*.ImplementationInvariants`).
4. **Relation.** Define the candidate barrier bisimulation relation
   (`*.ObservationalBisimulation.Relation`: `smd_bisim_relation`,
   `ma_bisim_relation`) and prove that related states are statically
   equivalent. `StaticEquivalence.bijective_correspondence_implies_static_equivalence`
   reduces this to exhibiting a bijection between the two adversary knowledges
   that maps each term to an indistinguishable one (`SMD.Bijection`).
5. **Simulation in both directions.** Prove `obs_sim_up_to_partitions` from
   `P` to `Q` and back. The step lemmas (one per transition kind) are in
   `*.ObservationalBisimulation.Proof.*`, with existential witnesses for the
   matching transitions in `*.ObservationalBisimulation.Witnesses*`.
6. **Conclude.** Apply `obs_bisim_up_to_partitions_implies_t_equivalence` (or
   its primed, invariant-conditioned variant) to obtain `t_equivalence`, as in
   `smd_t_equivalence` and `ma_t_equivalence`.

Put new examples under `examples/<name>/`: the Makefile finds every `.fst` and
`.fsti` under `helpers/` and `examples/` automatically. Add the new directory to
`include_dirs` in `.fst.config.json` if you use an editor integration.

## Line counts (paper Table 1)

`scripts/estimate_loc.py` produces the line counts reported in the paper's
Table 1, split into trusted specification, auxiliary definitions, auxiliary
lemma statements, and proof. Its docstring (`python3 scripts/estimate_loc.py
--help`) explains the classification heuristic; the `TRUSTED` table in the
script lists the trusted modules and declarations.

```sh
python3 scripts/estimate_loc.py        # all examples (or: smd, ma)
```

It prints a per-file breakdown followed by a `SUMMARY` table and the list of
admitted declarations.

## Metatheory mechanized in Lean

The two central metatheorems in `ObservationalBisimulation.fst` are
**axiomatized here with `admit ()`**, because they are mechanically proven in
the companion Lean development
[Doppel Metatheory](https://github.com/cuplv/doppel-metatheory).
Each `admit ()` is an instance of the corresponding Lean theorem: the F\*
statements match the Lean ones in strength, so that the `admit ()`s are
genuinely justified by the Lean proofs (e.g. `t_preorder` is the effects-based
weak preorder, `indistinguishable` is an equivalence relation, and the axioms
carry the transition-validity hypotheses the Lean proofs rely on).

The F\* framework exposes only the two *partitioned* theorems (the ones the
case studies use); the paper's and Lean's unpartitioned barrier-bisimulation
theorem (paper Thm. 4.2) is subsumed and not
restated here. The two admitted axioms are:

- **`obs_bisim_up_to_partitions_implies_t_equivalence`** — a (barrier)
  bisimulation up to right-movable partitions implies testing equivalence
  (paper Thm. 4.7). Backed by
  Lean's
  `observational_bisimulation_up_to_partitions_is_sufficient_for_weak_test_equivalence`.
- **`obs_bisim_up_to_partitions_implies_t_equivalence'`** — the same, but with
  right-movability only required at states satisfying an inductive invariant
  `inv` (over-approximating the reachable states) (paper Thm. 4.13). Backed by
  Lean's
  `observational_bisimulation_up_to_partitions_is_sufficient_for_weak_test_equivalence_mod_inv`.

Everything else in the F\* framework (the static-equivalence machinery, the
tested-system transition relation, the example bisimulation constructions) is
proven in F\* without `admit ()`. The validity of the tested-system relation
derived from a protocol is itself proven in F\* as `transitions'_valid`.

The only other admits are `map` and `sel_map` in the example-only helper
`helpers/FStar.PartialMap.Ext` (see
[Example-specific helpers](#example-specific-helpers)).

### How the F\* and Lean developments relate

The two developments share the same structure but differ in surface
representation (F\* uses `seq`, `bag`, and decidable-equality `eqtype`s where
Lean uses `List`, `Multiset`, and bare `Type`s with `Setoid`/`DecidableRel`
instances). The correspondences below let a reader check that the F\* axioms
instantiate the Lean theorems. For the paper's definition and theorem
numbers, see the citations in each module's comments (paper §3 for the formal
model, §4 for the proof techniques); note that both the F\* and Lean identifiers
use *observational* where the paper says *barrier* bisimulation.

#### Naming correspondence

| F\* (this repo) | Lean (companion development) |
|---|---|
| `adversary` class | `Tester` class |
| `knowledge term` (= `seq term`) | `List Term` |
| `Protocol.label` `Internal`/`Observable` | `ObservableLabel` `.internal`/`.external` |
| `Protocol.state` (`inputs`, `internal`) | `ProtoState` (`inputs`, `internal`) |
| `id` (label identifier type param) | `Label` / `ProtoLabel` |
| `obs` | `Effect` |
| `TestedSystem.state` (`know`, `inputs`, `internal`) | `SystemState` (`knowledge`, `inputs`, `protocol_state`) |
| `TestedSystem.label` `Internal`/`Observable`/`Input` | `CombinedLabel` `.internal`/`.external`/`.tester_input` |
| `TestedSystem.transitions'` | `combined_transitions` |
| `TestedSystem.valid_observable_transition_relation` | `validObservableTransitionRelation` |
| `TestedSystem.transitions'_valid` | (no direct counterpart; Lean takes transition validity as a hypothesis) |
| `multi_transitions` | `multi_transition` |
| `tested_effect` `Observable`/`Input` | `SystemEffect` `.protocol_effect`/`.derive` |
| `lbl_to_effect` | `effect_from_label` |
| `label_effects` | `effects` |
| `statically_equivalent` | `statically_equivalent` |
| `is_eventually_observable` | `EventuallyObservable` |
| `partition` class | `Setoid` + `DecidableRel` |
| `right_movable` | `rightMovablePartition` |
| `right_movable_mod_inv` | `rightMovablePartitionModInvariant` (+ per-state `rightMovableFrom`) |
| `obs_sim_up_to_partitions` | `observationalSimulationUpToPartitions` |
| `obs_bisim_up_to_partitions` | `observationalBisimulationUpToPartitions` |
| `t_preorder` | `weak_test_preorder` |
| `t_equivalence` | `weak_test_equivalence` |
| `obs_bisim_up_to_partitions_implies_t_equivalence` | `observational_bisimulation_up_to_partitions_is_sufficient_for_weak_test_equivalence` |
| `obs_bisim_up_to_partitions_implies_t_equivalence'` | `observational_bisimulation_up_to_partitions_is_sufficient_for_weak_test_equivalence_mod_inv` |

#### How key definitions and lemmas line up

- **Adversary / tester.** F\*'s `adversary` typeclass and Lean's `Tester` both
  bundle a derivation type, a `derive : Derivation -> knowledge -> option term`
  function, and a term-indistinguishability relation. Both require
  indistinguishability to be an *equivalence relation* — F\* via the
  `indistinguishable_equiv` field, Lean via modelling it as a `Setoid`. F\*'s
  `derivation` is an `eqtype` (so `derive`-equality is decidable) while Lean's
  `Derivation` is a bare `Type` with propositional `Option Term` equality;
  these are equivalent in content. F\* additionally carries `derivable` and
  `append_preserves_derive` fields, used only by the example protocols and with
  no Lean counterpart.

- **Static equivalence.** `StaticEquivalence.statically_equivalent` and Lean's
  `statically_equivalent` are the same two-part definition: (i) every
  derivation produces indistinguishable terms in both knowledges, and (ii) two
  derivations agree on whether they produce equal terms. Equal knowledges are
  statically equivalent in both (`statically_equivalent_if_knowledge_equal` in
  Lean), and the relation is symmetric (`statically_equivalent_symmetric`).

- **Tested system & transition validity.** `TestedSystem.transitions'` is the
  three-case combined relation (internal step preserves knowledge; observable
  step appends the emitted term; tester input applies a derivation into the
  input bag), matching Lean's inductive `combined_transitions`.
  `valid_observable_transition_relation` mirrors
  `validObservableTransitionRelation` (internal transitions preserve
  knowledge, others only extend it). The Lean metatheorems take this validity
  as a hypothesis; the F\* axioms instead build their two systems with
  `TestedSystem.system`, so validity holds by construction (the F\*-proven
  `transitions'_valid`) and is not restated as a `requires`.

- **Observable effects & the preorder.** `label_effects` projects a label
  sequence to its observable subsequence exactly as Lean's `effects` does
  (dropping internal labels, keeping observable effects and tester
  derivations). `t_preorder` / `t_equivalence` are the *weak* (effects-based)
  preorder and equivalence: the matching trace need only agree on
  `label_effects`, not on the literal label list — corresponding to Lean's
  `weak_test_preorder` / `weak_test_equivalence` and the paper's weak
  multi-step arrow.

- **Partitions & right-movability.** F\*'s `partition` typeclass (an
  equivalence relation `in_same_partition`) corresponds to a Lean `Setoid`
  together with a `DecidableRel` instance. `right_movable` matches
  `rightMovablePartition`: across distinct parts, an internal label commutes
  to the right past any other label. `right_movable_mod_inv` matches
  `rightMovablePartitionModInvariant`, which only requires that commutation
  from states satisfying an inductive invariant `inv` (Lean factors the
  per-state obligation into the helper `rightMovableFrom`).

- **The two metatheorems.** `obs_bisim_up_to_partitions` (a relation that is an
  observational simulation up to partitions in both directions) corresponds to
  Lean's `observationalBisimulationUpToPartitions`. The admitted F\* lemma
  `obs_bisim_up_to_partitions_implies_t_equivalence` is exactly Lean's
  `observational_bisimulation_up_to_partitions_is_sufficient_for_weak_test_equivalence`,
  and the invariant-conditioned `…'` variant is Lean's `…_mod_inv` theorem.
  Both F\* lemmas — like the Lean and paper theorems — give sufficient conditions
  for a *protocol composed with an adversary*: they take two protocols
  `proto_p`/`proto_q` and the tester `adv` and compose them with
  `TestedSystem.system` (the analogue of Lean's `combined_transitions proto`),
  rather than quantifying over arbitrary tested systems. The remaining
  hypotheses line up field-for-field: initial relatedness, "`rel` implies static
  equivalence", the bisimulation itself, and right-movability (unconditioned, or
  conditioned on initial-plus-inductive invariants for the primed/`_mod_inv`
  versions). Transition validity — taken as an explicit hypothesis in Lean — is
  *automatic* here because the systems are built by `TestedSystem.system`
  (discharged by the F\*-proven `transitions'_valid`), so it is not restated as a
  `requires`.

## License

Apache License 2.0; see [LICENSE](LICENSE).
