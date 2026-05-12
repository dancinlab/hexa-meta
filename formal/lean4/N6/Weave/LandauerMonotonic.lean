-- N6.Weave.LandauerMonotonic
--
-- Axis F-CL-FORMAL-2 — Landauer floor monotonicity under composition.
-- Consumer contract (hexa-bio): theorem `landauer_monotonic` at this
-- module path. PROMOTED v1 → v2 on 2026-05-12 (cycle-30+++) — see
-- `N6.Weave.Strategy` for the v2 ℝ-valued semantics with reversible-merge.
--
-- Pairs with: hexa-bio/weave/spec/lean4_mechanical_layer_v0.scaffold.md §2.2
-- Pairs with: .roadmap.weave §Falsifier preregister F-CL-FORMAL-2
-- Pairs with: .roadmap.lean4_formal §3 (v2 promotion work-order, Axis 2)
--
-- raw_91 honest C3 disclosure (2026-05-12 cycle-30+++):
--   Kernel-checked on lean4 4.30.0-rc2 + Mathlib (SHA pinned in
--   `lake-manifest.json`), sorry_count = 0. Monotonicity now follows from
--   real-valued heat additivity (compose .seq) + the heat-nonneg lemma
--   derivable from LandauerPass + landauerFloorPerBit > 0.
--   The consumer-contract statement is unchanged from v1; the underlying
--   semantics is upgraded. The merge-mode counterpart (heat is sub-additive
--   under reversible merge, NOT monotonic in `max`) is captured by
--   `landauer_pass_merge` in `N6.Weave.Strategy` — separate theorem because
--   the monotonicity claim only holds for sequential composition. This
--   matches the real WEAVE algebra: a merged strategy may have lower total
--   heat than either component, but it still respects the Landauer floor
--   on its (reduced) effective bit count.

import N6.Weave.Strategy

namespace N6
namespace Weave

/-- **Axis F-CL-FORMAL-2** (consumer contract, v2-PROVEN):
    composing two strategies sequentially cannot reduce heat consumed
    below the maximum of the component costs. Proof:
      heatConsumed (compose s₁ s₂) = s₁.heat + s₂.heat
    and `max a b ≤ a + b` holds when both summands are nonneg. The nonneg
    condition on each heat follows from `LandauerPass` (which posits
    heat ≥ bits · floor, and the RHS is nonneg since bits is a Nat and
    floor = kT·ln 2 > 0).

    The `LandauerPass` hypotheses are load-bearing in v2 (they pin down
    `0 ≤ heat`); v1's `omega`-discharged version had them as `_h₁`/`_h₂`
    only because Nat heat was nonneg by typing. -/
theorem landauer_monotonic
    (s₁ s₂ : Strategy) (h₁ : LandauerPass s₁) (h₂ : LandauerPass s₂) :
    heatConsumed (compose s₁ s₂) ≥ max (heatConsumed s₁) (heatConsumed s₂) := by
  unfold heatConsumed compose composeWith
  have h₁' : 0 ≤ s₁.heat := landauer_pass_heat_nonneg s₁ h₁
  have h₂' : 0 ≤ s₂.heat := landauer_pass_heat_nonneg s₂ h₂
  simp only [ge_iff_le, max_le_iff]
  refine ⟨?_, ?_⟩
  · linarith
  · linarith

end Weave
end N6
