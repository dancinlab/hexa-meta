-- N6.Weave.Strategy
--
-- WEAVE-semantics v1 vocabulary for axis F-CL-FORMAL-2 (Landauer floor
-- monotonicity). Upgraded 2026-05-12 (cycle-30) from the heat-only
-- placeholder to a two-field record carrying both the erasure count
-- (`bits_erased`) and the integer heat budget in kT·ln2 quanta
-- (`heat_kT_ln2`). raw_91 honest C3: still a v1 model — the real WEAVE
-- composition algebra has interference / sub-additive composition modes
-- this Nat-additive form does not capture. But it is no longer a single-
-- field identity: `LandauerPass` now relates the two fields by the actual
-- Landauer floor inequality, and `compose` is non-trivial on both fields.

namespace N6
namespace Weave

/-- A sub-strategy carrying (a) the number of irreversible bit-erasures it
    performs and (b) its heat dissipation expressed in integer kT·ln2
    quanta. One quantum = the Landauer floor of one irreversible bit
    erasure. The integer model captures the floor inequality; a continuous
    refinement is a future v2 (real-valued, Mathlib-backed) work item. -/
structure Strategy where
  bits_erased : Nat
  heat_kT_ln2 : Nat
  deriving Repr

/-- Heat consumed by a strategy, in units of kT·ln2. -/
def heatConsumed (s : Strategy) : Nat := s.heat_kT_ln2

/-- Landauer-floor predicate: the strategy's heat budget covers at least
    one kT·ln2 quantum per irreversibly-erased bit. This is the integer
    form of the Landauer inequality (Q ≥ N·kT·ln2). -/
def LandauerPass (s : Strategy) : Prop := s.heat_kT_ln2 ≥ s.bits_erased

/-- Sequential composition: bit erasures and heat budgets add. This is
    the worst-case (additive) composition rule — the real WEAVE algebra
    permits cancellation under reversible re-merge, which a v2 semantics
    would model. -/
def compose (s₁ s₂ : Strategy) : Strategy :=
  { bits_erased := s₁.bits_erased + s₂.bits_erased,
    heat_kT_ln2 := s₁.heat_kT_ln2 + s₂.heat_kT_ln2 }

/-- Composition closure for `LandauerPass`: composing two passing
    strategies yields a passing strategy. This is the substantive
    counterpart of `landauer_monotonic` — it certifies that the integer
    Landauer floor is closed under additive composition. -/
theorem landauer_pass_compose
    (s₁ s₂ : Strategy) (h₁ : LandauerPass s₁) (h₂ : LandauerPass s₂) :
    LandauerPass (compose s₁ s₂)
  := by
    simp only [LandauerPass, compose] at *
    omega

end Weave
end N6
