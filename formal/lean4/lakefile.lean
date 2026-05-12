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

-- Mathlib is NOT required by the current proof bodies. The 4-axis proofs
-- use only Lean 4 core tactics (`rfl`, `simp [...]`, `omega`, structural
-- case-splits). The earlier forward-looking `require mathlib` was removed
-- 2026-05-12 because (a) no proof body currently consumes a Mathlib lemma,
-- and (b) the `master` pin made `lake build` clone the entire mathlib4
-- repo (~minutes) on every fresh build, which is wasted work as long as
-- no proof imports it. Re-add (with a SHA pin, not `master`) when the
-- first real proof body needs a Mathlib lemma.
