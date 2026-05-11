<!-- @created: 2026-05-12 -->
<!-- @scope: real-limits audit (Wave M) — meta-theory / discovery tooling / proof-cert chains -->
<!-- @authority: applies LATTICE_POLICY.md §1.2 taxonomy verbatim -->
---
type: limit-breakthrough-audit
wave: M
session: 2026-05-12
parent_policy: LATTICE_POLICY.md §1.2
applies_to: hexa-meta — meta-theorems, discovery tooling, proof-cert chains, cross-repo linking
---

# LIMIT_BREAKTHROUGH.md — hexa-meta real-limits audit (Wave M)

> **Question**: hexa-meta is the *meta* layer over the entire HEXA family.
> Its limits are not silicon; they are **graph-theoretic, computability,
> and discovery-engine** limits. Which of those can be broken?

This doc applies the LATTICE_POLICY.md §1.2 real-limits taxonomy. See
companion hexa-chip exemplar for the full method.

---

## §1 Domain identification

hexa-meta hosts:

| Layer | Verbs (representative) | Concern |
|-------|------------------------|---------|
| Proofs | `proofs/` (11) — attractor-meta-theorem, ouroboros-α universality, the-number-24, theorem-r1-uniqueness, honest-limitations | Meta-theory: are the n=6 claims internally consistent and externally non-overclaim? |
| Papers | `papers/` (24) — n6-arch-*, n6-cross-dse-matrix-112, M10star-21-unified-theorem | Cross-cutting synthesis across hexa-* siblings |
| Tools | `tools/` (15) — discovery-engine, deep-miner, formula-miner, universal-dse, hypothesis-grader, lens-coverage | Domain-agnostic discovery / DSE / verification engines |
| Predictions / Flow / Formal | `predictions/`, `flow/`, `formal/` | Forward-looking forecasts; formal-verification scaffolds |

hexa-meta is **not** about a physical artifact. It is about the
*self-organisation* and *cross-link integrity* of the HEXA repo family.
Its limits are accordingly **information-theoretic and computability-class**.

---

## §2 Real limits applicable to hexa-meta

### 2.1 Halting problem / Rice's theorem (MATHEMATICAL)

The `tools/discovery-engine`, `tools/deep-miner`, and
`tools/formula-miner` perform **automated search over program/formula
space**. Any non-trivial *semantic* property of submitted candidates
is undecidable in general (Rice 1953). The engines can only inspect
**syntactic** features + run-time samples.

### 2.2 Kolmogorov complexity lower bound (MATHEMATICAL)

`tools/formula-miner` and `papers/n6-cross-dse-matrix-112` claim
compact closed-form expressions for cross-domain regularities. K(x)
is **uncomputable**; the engine can only produce *upper bounds*
(shortest description found, not shortest description existing).

### 2.3 PAC-learning sample-complexity bound (MATHEMATICAL)

`tools/hypothesis-grader` evaluates discovery candidates against
empirical sets. PAC bounds (Vapnik 1995) require:
```
m  ≥  (1/ε) · ( ln |H| + ln(1/δ) )
```
for finite hypothesis class H. For the n=6 corpus (~80 domains,
~112 cross-DSE cells), reliable separation at ε=0.05, δ=0.05 needs
~100-200 *independent* empirical signals per cell — most cells in
the current corpus are below that.

### 2.4 Transitive-closure cost on cross-repo graph (MATHEMATICAL / ENGINEERING)

hexa-meta links 6+ sibling repos (hexa-chip / -lang / -sscb / -rtsc /
-codex / -fusion / -ufo / -cern / -bio). Naive transitive closure of
a sparse-DAG with N nodes is O(N²) edges. At current ~12 repos, the
cost is trivial; **growth past ~100 repos** would hit storage /
freshness cliffs.

### 2.5 Statistical-power floor on cross-domain claims (MATHEMATICAL)

`papers/n=6-convergence-80-domains` claims convergence across 80
domains. Power analysis: detecting a true effect-size d=0.3 at α=0.05
with 80% power requires N=176 per condition (Cohen 1988). The
80-domain corpus often has N=1-3 published replications per cell —
**statistically underpowered for negative claims**.

### 2.6 Computability of consistency checks (MATHEMATICAL)

`proofs/proof-certification-chain` claims a closure verdict across the
proof set. Hilbert-Gödel: any formal system rich enough to express
arithmetic is either incomplete or inconsistent. **Consistency of the
n=6 axiom set is not internally provable.** External proof assistants
(Lean 4, Coq) provide *relative* consistency only.

### 2.7 Discovery-engine compute envelope (ENGINEERING)

`tools/universal-dse` and `tools/cross-dse-calc` enumerate design-space
points. A 112-cell × 6-knob DSE = 6¹¹² ≈ 10⁸⁷ raw points — only
sampling is tractable. Concrete budget: ~10⁹ candidate evaluations on
a workstation/day; ~10¹² on a 1k-node cluster/day. **Sub-1-ppm of
the full space.**

### 2.8 Link-rot half-life on external citations (ENGINEERING)

Academic URL link-rot half-life ≈ 7 yr (Klein et al. 2014). hexa-meta
`papers/` cite hundreds of external resources. Without active
archival (Wayback / Zenodo DOI), citation integrity decays
~exponentially.

---

## §3 Per-limit breakthrough assessment

### 3.1 Halting / Rice → **HARD_WALL**

Cannot be broken under classical computability. Mitigation is
*restriction*: confine discovery engines to **decidable fragments**
(e.g., Presburger arithmetic, polynomial-bounded loops, total
functional languages like Agda). Trigger for partial break: a
typed-DSL frontend on `tools/formula-miner` that *refuses* to enumerate
candidates outside a decidable fragment. **Status: not implemented.**

### 3.2 Kolmogorov K(x) uncomputability → **HARD_WALL** (catalog-only)

K(x) is uncomputable from above; any "shortest formula found" is a
proof of an upper bound on K, never of K itself. Cannot break.
Practically: the formula-miner outputs are *upper-bound certificates*,
not optimality claims.

### 3.3 PAC sample-complexity → **SOFT_WALL** (active learning breaks it)

Active / query-based learning (Settles 2009) can cut sample
complexity by O(log) factors when the learner chooses queries.
For hexa-meta: instead of passively grading existing cross-domain
claims, the `hypothesis-grader` could *request specific experiments*
(e.g., "test cell (47,12) in hexa-fusion"). **Status: not designed
into the tool today.** Trigger: hypothesis-grader v2 with
information-gain-ranked query API.

### 3.4 Transitive closure → **BREAKABLE_WITH_TECH**

Engineering, not math. Incremental graph maintenance (Demetrescu &
Italiano 2003) keeps amortised O(N log N) updates. Trigger: when
hexa-* repo count crosses ~50, ship `tools/repo-graph-cache/`. Until
then, naive recomputation is fine.

### 3.5 Statistical power → **SOFT_WALL** (meta-analysis breaks it)

Cross-domain meta-analysis pooling effect sizes across N=80 domains
gives effective N ≫ 1000 *if domain-specific confounds are modelled*.
Trigger: `tools/meta-analysis-engine` adding fixed/random-effects
pooling — a documented gap in the current toolset. **Doable in
weeks of work.**

### 3.6 Gödel incompleteness → **HARD_WALL**

Cannot break. **Practical mitigation**: external consistency in
Lean 4 / Coq (already cited in `proofs/proof-certification-chain`).
This is the right honest move; no breakthrough exists.

### 3.7 Discovery-engine compute envelope → **BREAKABLE_WITH_TECH**

Two paths:
1. **Bayesian / surrogate-model DSE** — Gaussian-process surrogates
   prune ~99% of candidates without full evaluation.
2. **GPU-accelerated formula enumeration** — `tools/formula-miner`
   on H100/MI300 = ~100× speed-up.

Trigger: `tools/universal-dse-gpu/` shipping with surrogate-pruning.
**On the §1.2 BREAKABLE side.**

### 3.8 Link-rot → **BREAKABLE_WITH_TECH**

Trivially mitigated: enforce Zenodo DOI for every external citation
in `papers/`. Trigger: pre-commit hook that rejects non-DOI external
links. Engineering, not research.

---

## §4 Top-3 breakthrough opportunities

### #1 — Surrogate-pruned `universal-dse-gpu` (§3.7)

Pulls the largest practical lever: from 10⁹/day to ~10¹²/day on
single-node GPU + surrogate model. Concretely unlocks the
`n6-cross-dse-matrix-112` to be run at *cell-level* exhaustion
rather than sampled. Time-to-deliver: ~2 engineer-months.

### #2 — Active-learning hypothesis-grader v2 (§3.3)

Closes the PAC sample-complexity gap that today makes most
cross-domain claims rest on N=1-3 published replications. Active
querying flips the relationship between sibling repos and meta:
**meta requests the experiment instead of waiting for it**. Time:
~3 months.

### #3 — Lean 4 consistency relativisation for `proofs/` (§3.6)

Cannot escape Gödel, but *can* document the precise external
theory the n=6 corpus is relatively consistent against (ZFC + large
cardinals? PA? CIC?). This is honest, deliverable, and decisively
upgrades `proofs/honest-limitations` from prose to formal artefact.
Time: ~6 months with a Lean-capable contributor.

---

## §5 Honest caveats

1. **No empirical experiments in hexa-meta itself.** All limits here
   apply to the *engines and graphs*, not to physical phenomena.
   This is by design.

2. **PAC and statistical-power bounds presume IID-ish samples.**
   Cross-domain pooling violates IID; the honest move is hierarchical
   models with explicit domain-level random effects, not flat pooling.

3. **HARD_WALL for §3.1, §3.2, §3.6.** These are foundational
   mathematics. **No imaginable tech breaks them.** Mitigation is
   scoping, not breakthrough.

4. **n=6 lattice does NOT appear as a "limit"** per LATTICE_POLICY.md.
   The lattice is hexa-meta's organising vocabulary — limits are the
   *external* math/physics/engineering walls cataloged above.

5. **The discovery-engine output is upper-bound, never tight.**
   `formula-miner` produces shortest-found, not shortest-existing.
   Consumers should never treat its output as optimality certificate.

---

## §6 References

- `LATTICE_POLICY.md` §1.2 — taxonomy this audit applies
- `proofs/honest-limitations` — hexa-meta's own self-criticism document
- `proofs/proof-certification-chain` — relative-consistency framing
- `papers/n6-cross-dse-matrix-112` — 112-cell DSE that needs §3.7 to scale
- `papers/n=6-convergence-80-domains` — claim that needs §3.5 power-fix
- `tools/discovery-engine`, `tools/deep-miner`, `tools/formula-miner` — primary engines
- `tools/hypothesis-grader` — PAC/active-learning interface
- External: Rice (1953), Cohen (1988) *Statistical Power*, Klein et al. (2014) *Scholarly Context Adrift*,
  Settles (2009) *Active Learning Literature Survey*, Demetrescu & Italiano (2003) *Fully Dynamic Transitive Closure*.

---

*End of LIMIT_BREAKTHROUGH.md (hexa-meta, Wave M).*
