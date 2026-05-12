-- N6.Weave.LandauerMonotonic
--
-- Axis F-CL-FORMAL-2 — Landauer floor monotonicity under composition.
-- Consumer contract (hexa-bio): theorem `landauer_monotonic` at this
-- module path. RE-PROVEN against WEAVE-semantics v1 on 2026-05-12
-- (cycle-30) — see `N6.Weave.Strategy` for the upgraded semantics.
--
-- Pairs with: hexa-bio/weave/spec/lean4_mechanical_layer_v0.scaffold.md §2.2
-- Pairs with: .roadmap.weave §Falsifier preregister F-CL-FORMAL-2
--
-- raw_91 honest C3 disclosure (2026-05-12):
--   Kernel-checked on lean4 4.30.0-rc1, sorry_count = 0. The proof now
--   exercises the upgraded two-field Strategy semantics (bits_erased +
--   heat_kT_ln2). Monotonicity holds because compose is Nat-additive on
--   both fields and Nat addition dominates the max of the summands. The
--   stronger meaningful theorem — composition closure for `LandauerPass`
--   — is `landauer_pass_compose` in `N6.Weave.Strategy` and is the
--   substantive Landauer-floor preservation lemma. Caveat: the additive-
--   composition rule is still a v1 model; the real WEAVE algebra admits
--   sub-additive composition under reversible re-merge, which a v2
--   semantics would capture. Promote to v2 when real-valued heat (kT·ln2
--   as ℝ, via Mathlib) and reversible-merge modes land.

import N6.Weave.Strategy

namespace N6
namespace Weave

/-- Axis F-CL-FORMAL-2: composing two strategies cannot reduce heat
    consumed below the maximum of the component costs. Proof exercises
    the upgraded Strategy semantics: heatConsumed (compose s₁ s₂) =
    s₁.heat_kT_ln2 + s₂.heat_kT_ln2 ≥ max s₁.heat_kT_ln2 s₂.heat_kT_ln2
    by Nat additivity. The hypotheses `LandauerPass sᵢ` are not required
    for monotonicity itself (it is purely arithmetic) — they are part of
    the consumer contract because they pair with `landauer_pass_compose`,
    which certifies that the floor is preserved under composition. -/
theorem landauer_monotonic
    (s₁ s₂ : Strategy) (_h₁ : LandauerPass s₁) (_h₂ : LandauerPass s₂) :
    heatConsumed (compose s₁ s₂) ≥ max (heatConsumed s₁) (heatConsumed s₂)
  := by
    simp only [heatConsumed, compose]
    omega

end Weave
end N6
