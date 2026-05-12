-- N6.Weave.LandauerMonotonic
--
-- Axis F-CL-FORMAL-2 — Landauer floor monotonicity under composition.
-- Consumer contract (hexa-bio): theorem `landauer_monotonic` at this
-- module path. PROMOTED v2 → v3 on 2026-05-12 (cycle-30++++) — see
-- `N6.Weave.Strategy` for the v3 ℝ-valued semantics with an opaque
-- positive-real temperature parameter kT (section variable +
-- `[Fact (0 < kT)]`). Previous v2 commit: hexa-meta 2c68bea.
--
-- Pairs with: hexa-bio/weave/spec/lean4_mechanical_layer_v0.scaffold.md §2.2
-- Pairs with: .roadmap.weave §Falsifier preregister F-CL-FORMAL-2
-- Pairs with: .roadmap.lean4_formal §3 (v3 promotion work-order, Axis 2)
--
-- raw_91 honest C3 disclosure (2026-05-12 cycle-30++++):
--   Kernel-checked on lean4 4.30.0-rc2 + Mathlib (SHA pinned in
--   `lake-manifest.json`), sorry_count = 0. Monotonicity follows from
--   real-valued heat additivity (compose .seq) + the heat-nonneg lemma
--   derivable from LandauerPass + landauerFloorPerBit kT > 0 (under
--   `[Fact (0 < kT)]`).
--   The consumer-contract statement is externally unchanged from v2: kT is
--   an implicit-via-section parameter, so the binder list at the call site
--   sees only the existing `LandauerPass` hypotheses plus a `[Fact (0 < kT)]`
--   instance, with the conclusion shape unchanged. The merge-mode counterpart
--   is captured by `landauer_pass_merge` in `N6.Weave.Strategy`.
--   v3 caveats: energy is still ℝ; a v4 stretch could parametrise the entire
--   energy substrate (e.g. arbitrary `[OrderedAddCommGroup E]` instead of ℝ).
--   Out of scope for v3 promotion.

import N6.Weave.Strategy

namespace N6
namespace Weave

section LandauerParam

variable (kT : ℝ) [hkT : Fact (0 < kT)]

/-- **Axis F-CL-FORMAL-2** (consumer contract, v3-PROVEN):
    composing two strategies sequentially cannot reduce heat consumed
    below the maximum of the component costs. Proof:
      heatConsumed (compose kT s₁ s₂) = s₁.heat + s₂.heat
    and `max a b ≤ a + b` holds when both summands are nonneg. The nonneg
    condition on each heat follows from `LandauerPass kT` (which posits
    heat ≥ bits · floor, and the RHS is nonneg since bits is a Nat and
    floor = kT·ln 2 > 0 under `[Fact (0 < kT)]`).

    The `LandauerPass` hypotheses are load-bearing in v2/v3 (they pin down
    `0 ≤ heat`); v1's `omega`-discharged version had them as `_h₁`/`_h₂`
    only because Nat heat was nonneg by typing.

    v3 promotion: kT is implicit via section variable; externally the
    theorem signature still takes only `s₁ s₂ : Strategy` and two
    `LandauerPass _ s_i` hypotheses, with the conclusion shape unchanged. -/
theorem landauer_monotonic
    (s₁ s₂ : Strategy) (h₁ : LandauerPass kT s₁) (h₂ : LandauerPass kT s₂) :
    heatConsumed (compose kT s₁ s₂) ≥
      max (heatConsumed s₁) (heatConsumed s₂) := by
  unfold heatConsumed compose composeWith
  have h₁' : 0 ≤ s₁.heat := landauer_pass_heat_nonneg kT s₁ h₁
  have h₂' : 0 ≤ s₂.heat := landauer_pass_heat_nonneg kT s₂ h₂
  simp only [ge_iff_le, max_le_iff]
  refine ⟨?_, ?_⟩
  · linarith
  · linarith

end LandauerParam

end Weave
end N6
