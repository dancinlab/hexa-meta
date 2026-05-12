-- N6.Weave.LandauerMonotonic
--
-- Axis F-CL-FORMAL-2 — Landauer floor monotonicity under composition.
-- Consumer contract (hexa-bio): theorem `landauer_monotonic` at this
-- module path. PROMOTED v3 → v4 on 2026-05-12 (cycle-30++++++) — see
-- `N6.Weave.Strategy` for the v4 substrate-polymorphic semantics with an
-- arbitrary linearly-ordered additive commutative group `E` and an opaque
-- positive Landauer floor element `floor : E` (section variable +
-- `[Fact (0 < floor)]`). Previous v3 commit: hexa-meta 9e44e75.
--
-- Pairs with: hexa-bio/weave/spec/lean4_mechanical_layer_v0.scaffold.md §2.2
-- Pairs with: .roadmap.weave §Falsifier preregister F-CL-FORMAL-2
-- Pairs with: .roadmap.lean4_formal §3 (v4 promotion work-order, Axis 2)
--
-- raw_91 honest C3 disclosure (2026-05-12 cycle-30++++++):
--   Kernel-checked on lean4 4.30.0-rc2 + Mathlib (SHA pinned in
--   `lake-manifest.json`), sorry_count = 0. Monotonicity follows from
--   additivity of `compose .seq` on the `heat` field plus heat-nonneg
--   (derivable from `LandauerPass` + `nsmul_nonneg` on the positive floor).
--   Substrate-polymorphic: works for `E := ℝ`, `E := ℚ`, `E := ℤ`, or any
--   linearly-ordered additive commutative group; the v3-specific factor
--   `kT · Real.log 2` is recoverable only by instantiating `E := ℝ` and
--   `floor := kT * Real.log 2` at the consumer site.
--   The consumer-contract statement is externally unchanged from v3: `floor`
--   is an implicit-via-section parameter, so the binder list at the call site
--   sees only the existing `LandauerPass` hypotheses plus a `[Fact (0 < floor)]`
--   instance, with the conclusion shape unchanged. The merge-mode counterpart
--   is captured by `landauer_pass_merge` in `N6.Weave.Strategy`.
--   v4 caveats:
--     - The `kT · Real.log 2` calculation is no longer in the kernel-checked
--       statement; that's a consumer-instantiation concern at `E := ℝ`.
--     - v5 stretch: parametrise the ring/module structure (e.g. equip `E`
--       with a scalar action over a richer commutative semiring). Out of
--       scope for v4 promotion.

import N6.Weave.Strategy

namespace N6
namespace Weave

section LandauerParam

variable {E : Type*}
  [AddCommGroup E] [LinearOrder E] [IsOrderedAddMonoid E]
  (floor : E) [hfloor : Fact (0 < floor)]

/-- **Axis F-CL-FORMAL-2** (consumer contract, v4-PROVEN):
    composing two strategies sequentially cannot reduce heat consumed
    below the maximum of the component costs. Proof:
      heatConsumed (compose floor s₁ s₂) = s₁.heat + s₂.heat
    and `max a b ≤ a + b` holds when both summands are nonneg. The nonneg
    condition on each heat follows from `LandauerPass floor` (which posits
    `heat ≥ bits • floor`, and the RHS is nonneg by `nsmul_nonneg` since
    `floor > 0` under `[Fact (0 < floor)]`).

    The `LandauerPass` hypotheses are load-bearing in v2/v3/v4 (they pin down
    `0 ≤ heat`); v1's `omega`-discharged version had them as `_h₁`/`_h₂`
    only because Nat heat was nonneg by typing.

    v4 promotion: `floor` (and the substrate `E`) is implicit via section
    variable; externally the theorem signature still takes only `s₁ s₂ :
    Strategy E` and two `LandauerPass floor s_i` hypotheses, with the
    conclusion shape unchanged. -/
theorem landauer_monotonic
    (s₁ s₂ : Strategy E) (h₁ : LandauerPass floor s₁) (h₂ : LandauerPass floor s₂) :
    heatConsumed (compose floor s₁ s₂) ≥
      max (heatConsumed s₁) (heatConsumed s₂) := by
  unfold heatConsumed compose composeWith
  have h₁' : (0 : E) ≤ s₁.heat := landauer_pass_heat_nonneg floor s₁ h₁
  have h₂' : (0 : E) ≤ s₂.heat := landauer_pass_heat_nonneg floor s₂ h₂
  simp only [ge_iff_le, max_le_iff]
  refine ⟨?_, ?_⟩
  · -- s₁.heat ≤ s₁.heat + s₂.heat  (since 0 ≤ s₂.heat)
    exact le_add_of_nonneg_right h₂'
  · -- s₂.heat ≤ s₁.heat + s₂.heat  (since 0 ≤ s₁.heat)
    exact le_add_of_nonneg_left h₁'

end LandauerParam

end Weave
end N6
