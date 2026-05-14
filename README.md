<p align="center">
  <img src="docs/logo.svg" width="140" alt="hexa-meta">
</p>

<h1 align="center">🌀 hexa-meta</h1>

<p align="center"><strong>HEXA-Meta family</strong> — meta-theoretic · self-architecture · proof-cert · discovery tooling</p>

<p align="center">
  <a href="LICENSE"><img alt="License" src="https://img.shields.io/badge/license-MIT-blue"></a>
  <a href=".github/workflows/lint.yml"><img alt="CI" src="https://github.com/dancinlab/hexa-meta/actions/workflows/lint.yml/badge.svg"></a>
  <img alt="Spec" src="https://img.shields.io/badge/spec-v0.1-success">
  <img alt="Bundle" src="https://img.shields.io/badge/bundle-24%20papers%20·%2011%20proofs%20·%2015%20tools-informational">
  <img alt="Verify" src="https://img.shields.io/badge/verify-105%2F105-informational">
  <img alt="DOI" src="https://zenodo.org/badge/DOI/10.5281/zenodo.20114998.svg">
  <img alt="Sibling" src="https://img.shields.io/badge/sibling-hexa--grid%20·%20hexa--millennium%20·%20hexa--mobility-blueviolet">
</p>

<p align="center">meta-theorem · self-organizing-architecture · proof-cert-chain · discovery-engine · DSE · universal-tooling</p>

---

> The n=6 framework reflecting on itself: meta-theorems, self-organizing
> architecture papers, proof-certification chains, and the domain-agnostic
> discovery / DSE / verification tooling that powers every other `hexa-*` repo.

---

## Install

```bash
# 1. Install hexa-lang (ships `hexa` + `hx` package manager)
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/dancinlab/hexa-lang/main/install.sh)"

# 2. Install hexa-meta
hx install hexa-meta          # global, pulls latest from registry
```

---

## Why

`hexa-meta` is the **meta** member of the HEXA family. Everything here is about
n=6 *itself* rather than a particular application domain:

- **`proofs/`** (11) — meta-theorems & certification: `attractor-meta-theorem`,
  `ouroboros-alpha-universality`, `mk4-trident-final-verdict`, `physics-math-certification`,
  `proof-certification-chain`, `the-number-24`, `theorem-r1-uniqueness`, `honest-limitations`, …
- **`papers/`** (24) — self-organizing architecture & cross-cutting synthesis:
  `n6-arch-*` (adaptive-evolution / homeostasis / ouroboros / quantum-design / selforg-*),
  `n6-mk3-synthesis`, `n6-cross-dse-matrix-112`, `n6-cross-paradigm-ai`,
  `n6-66-techniques-integrated`, `n=6-convergence-80-domains`, `M10star-21-unified-theorem`, …
- **`tools/`** (15) — domain-agnostic engines every `hexa-*` consumes:
  `discovery-engine`, `deep-miner`, `formula-miner`, `universal-dse`, `dse-calc`,
  `cross-dse-calc`, `hypothesis-grader`, `bt-extension-verifier`, `lens-coverage`,
  `hexa-sim`, `hexa-ssh`, `nobel-calc`, `ready-absorber`, `vendor-compare-calc`, `legacy`.

---

## Repo layout

```
hexa-meta/
├── README.md
├── LICENSE                       MIT
├── AGENTS.tape                   identity + governance (.tape v1.2)
├── hexa.toml                     package manifest
├── proofs/                       11 meta-theory proof docs        (← canon theory/proofs/)
├── papers/                       24 self-architecture papers       (← canon papers/)
├── tools/                        15 domain-agnostic calc/DSE tools (← canon bridge/origins/)
├── breakthroughs/                breakthrough records (7)
├── constants/                    physical / math constants (5)
├── flow/                         flow systems (4)
├── formal/                       formal / Lean4 stub layer
├── predictions/                  105 verify_*.hexa prediction sweep
├── preprints/                    pre-print drafts
├── proofs/                       proof artifacts
├── roadmap-v2/  roadmap-v3/      roadmap snapshots
├── study/                        study notes
├── verify/                       run_all.hexa + closure scripts
├── state/                        runtime state (gitignored)
├── docs/logo.svg                 repo logo
├── LATTICE_POLICY.md             real-limits policy
└── LIMIT_BREAKTHROUGH.md         HARD/SOFT wall audit
```

## Run

```bash
# Tier 1 — aggregate sweep of all 105 prediction verify scripts (rc=0 → PASS)
hexa run verify/run_all.hexa

# Tier 2 — Lean 4 formal layer (external toolchain; stub-marked per policy)
cd formal/lean4 && lake build

# Tier 4 — sample tool runs (some hit 768 MB mem-cap; raise with HEXA_MEM_UNLIMITED=1)
hexa run tools/discovery-engine/main.hexa
hexa run tools/dse-calc/main.hexa
hexa run tools/universal-dse/main.hexa
```

---

## Closure

hexa-meta uses a **4-tier closure model** (no single N/N reduction; see `hexa.toml [closure]`):

| Tier | Layer | Count | Status |
|------|-------|------:|--------|
| 1 | `predictions/verify_*.hexa` (orchestrator: `verify/run_all.hexa`) | 105 | **PASS** (105/105 rc=0; 2 marked STUB-port-pending) |
| 2 | `formal/lean4/N6/` (Lean 4 stub layer; 5/7 files `sorry`-marked) | 7 | **STUB_LAYER** (honest, per `raw_91` C3) |
| 3 | `proofs/` + `papers/` + `breakthroughs/` (theorems + citations) | 41 | **DOCUMENT_TIER** (not measurement-reducible) |
| 4 | `tools/` (domain-agnostic DSE / discovery / verify engines) | 15 dirs | **SMOKE_OK** (env-bounded by 768 MB hexa-runtime mem-cap) |

**Honest caveat** (`LATTICE_POLICY.md` §1.2 / `LIMIT_BREAKTHROUGH.md` §3.6):
hexa-meta's closure is **structural + executional**, not empirical. Gödel HARD_WALL
forbids internal consistency proof; relative consistency against Lean 4 / Mathlib is
the honest ceiling. Tier 1 sweep is the executional anchor.

---

## Status

`v0.1.0` — **BUNDLE_FIRST + META_CLOSURE_4TIER**. Bundle ships as material moved out
of `canon` (MOVE pattern). The 4-tier closure model above is now wired (Tier 1
orchestrator under `verify/`). Full n=6 HEXA-template authoring of the meta verbs
remains future work. See [`IMPORTED_FROM_CANON.md`](IMPORTED_FROM_CANON.md).

## Provenance

Moved from `canon/{theory/proofs,papers,bridge/origins}` at canon SHA `a86ca143` on 2026-05-10.

## License

[MIT](LICENSE).
