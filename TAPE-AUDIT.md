# TAPE-AUDIT — hexa-meta

**Date:** 2026-05-14 · **Lens:** `.tape` (typed events + provenance) — heaviest atom-promotion candidate in this audit set.

## A. Audit-class ledgers

`state/markers/*.marker` — **rich** marker set vs siblings: `verify_oeis_offline_match_f7_*`, `verify_big_b5_5bt_meganode_*`, `verify_big_d5_pvnp_schaefer_barrier_*`, `verify_SIG-UNIV-302_*`, `verify_SIG-CLM-303_*`, `verify_SIG-CONS-302_*`, `verify_bernoulli17_bb6_*`, `verify_millennium_g_f_bsd_pc_*`, `verify_killerapp_tp_*`, `verify_sigma_sopfr_7_bsd_*`, `verify_appl_honeycomb_hales_*`, `verify_appl_transformer_ffn_*`, `verify_appl_sr_calibration_*`, `verify_dfs27_ym_betafn_*`, `verify_dfs27_ym_cft_*`, `absorber_*`, … — still **CARGO** (rc-touch only, no payload), but the marker namespace is richer (verify-per-prediction). `roadmap-v2/phase-08-meta-audit-philosophy.md` exists (philosophy of audit — not a ledger). `study/p2/n6-p2-4-honesty-audit.md` (meta-audit doc).

## B. Identity surface

`hexa.toml` no `[identity]`. Meta-substrate ("n=6 reflecting on itself") — not per-agent.

## C. Domain.md files

**Zero** UPPERCASE.md at root. Heavy spec lives under `proofs/` (11), `papers/` (24), `predictions/` (117), `roadmap-v2/` (63), `roadmap-v3/`, `formal/`, `breakthroughs/` (with `_hypotheses_index.json`, `bt-1389-cube-octahedron-duality-2026-04-12.md`, etc.) — convention is `lowercase-with-hyphen-dated.md`, not the root UPPERCASE convention. `_theory_index.json` exists (machine-readable index — meta-spec).

## D. Per-run / per-event history

`predictions/_catalog.json` (4 KB) + 117 `.hexa` verify scripts + `falsification-experiments.md` + `pre-registered-predictions.md` + `predictions-unmeasured.md` + `testable-predictions.md` — strong **pre-registered-prediction → falsification** event-shape (the textbook `.tape` `@?` question · `@H` measurement · `@R` falsified/confirmed shape). `breakthroughs/` has `_hypotheses_index.json` (machine-readable hypothesis catalog). The `proofs/proof-certification-chain.md` + `physics-math-certification.md` describe a provenance-chain semantics directly mirroring `.tape` provenance-edge model (7 edges).

## E. Promotion candidates

- **n6 atoms** (HIGHEST — per spec "atom-promotion possibly HEAVY"). `predictions/_catalog.json` + `proofs/the-number-24.md` + `theorem-r1-uniqueness.md` + `n6-boundary-metatheory-2026-04-14.md` are the canonical atom inventory. Every entry in the 117-file predictions/ is a candidate atom.
- **`.tape` `@P` provenance-chain** (HIGH): `proofs/proof-certification-chain.md` + `physics-math-certification.md` are literally a description of `.tape`'s provenance-edge model — the semantic match is exact.
- **`<META>.tape`** (MEDIUM): a `META.tape` could carry the prediction-falsification event stream (`@? → @H → @R`) — currently spread across `_catalog.json` + per-prediction `.hexa` + result markers.
- **hxc / n12**: meta-substrate may use both as promotion vehicles.

## Verdict

**HEAVY** — strongest atom-promotion source in the audit set per spec ("50-doc meta-theory, possibly HEAVY for atom-promotion"). 117 predictions + 11 proofs + provenance-chain doc semantically matches `.tape` 7-edge model. `_catalog.json` is the atom-index seed. Most active ledger-shape semantics outside hexa-os.
