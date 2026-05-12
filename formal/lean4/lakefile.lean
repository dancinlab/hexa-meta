-- formal/lean4/lakefile.lean
--
-- Stub-layer build for the consumer-contract theorems consumed by hexa-bio
-- (lean4_mechanical_layer_v0.scaffold.md). Separate from the older
-- `lean4-n6/` package so the n=6 number-theory work and the formal-axis
-- consumer stubs evolve independently.

import Lake
open Lake DSL

package «n6-formal-stub» where
  -- Consumer-contract layer for axes F-CL-FORMAL-1..4. All four theorem
  -- proof bodies are kernel-checked against (richer-than-original-stub)
  -- WEAVE semantics (2026-05-12 cycle-30 upgrade). raw_91 honest C3:
  -- semantics still a v1 model, not the full WEAVE composition algebra.

lean_lib «N6» where
  roots := #[`N6.InvariantLattice.Sigma,
             `N6.InvariantLattice.SigmaLatticeCard,
             `N6.Weave.Strategy,
             `N6.Weave.LandauerMonotonic,
             `N6.Weave.PiP2Verifier,
             `N6.Weave.PiP2Termination,
             `N6.Weave.ClosureCert]

-- Mathlib re-added 2026-05-12 (cycle-30++, Axis 4 v2 promotion start):
-- F-CL-FORMAL-4 v2 (ClosureCert merge-idempotence with caveat-bag + signer-set
-- invariants) needs Mathlib for `Multiset` / `Finset.union` / `Multiset.dedup`
-- machinery. The `master` pin is provisional — `lake update` resolves to a
-- specific commit recorded in `lake-manifest.json`; that SHA is the
-- reproducibility anchor. The mathlib4-cache (~828 MB on this host at
-- ~/.cache/mathlib) provides precompiled oleans, so `lake exe cache get`
-- after `lake update` avoids a cold Mathlib build.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"
