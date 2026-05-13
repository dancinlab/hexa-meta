# 🌀 hexa-meta — n=6 meta-theory · self-architecture · proof-cert · discovery tooling

> The n=6 framework reflecting on itself: meta-theorems, self-organizing
> architecture papers, proof-certification chains, and the domain-agnostic
> discovery / DSE / verification tooling that powers every other `hexa-*` repo.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20114998.svg)](https://doi.org/10.5281/zenodo.20114998)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
[![Version](https://img.shields.io/badge/version-0.1.0-informational.svg)](hexa.toml)
[![Bundle](https://img.shields.io/badge/bundle-24_papers_+_11_proofs_+_15_tools-blue.svg)](#layout)
[![Verify](https://img.shields.io/badge/verify-105%2F105_rc%3D0-brightgreen.svg)](verify/run_all.hexa)
[![Closure](https://img.shields.io/badge/closure-META__4TIER-blueviolet.svg)](#closure)
[![Status](https://img.shields.io/badge/status-bundle--first-orange.svg)](#status)

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

## Layout

```
hexa-meta/
├── proofs/   11 meta-theory proof docs        (← canon theory/proofs/)
├── papers/   24 self-architecture papers       (← canon papers/)
└── tools/    15 domain-agnostic calc/DSE tools  (← canon bridge/origins/)
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
