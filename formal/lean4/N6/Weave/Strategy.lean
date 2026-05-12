-- N6.Weave.Strategy
--
-- WEAVE-semantics v3 vocabulary for axis F-CL-FORMAL-2 (Landauer floor
-- monotonicity). PROMOTED v2 → v3 on 2026-05-12 (cycle-30++++) from a
-- normalised-unit `kT := 1` model to an opaque positive-real temperature
-- parameter threaded via section variable + `[Fact (0 < kT)]` instance.
-- Previous v2 commit: hexa-meta 2c68bea (2026-05-12 cycle-30+++).
--
-- raw_91 honest C3 disclosure (2026-05-12 cycle-30++++):
--   v1 model: Strategy { bits_erased, heat_kT_ln2 : Nat }; compose Nat-additive
--   on both fields; LandauerPass s = (heat_kT_ln2 ≥ bits_erased).
--   v2 model: heat is ℝ in joules (or normalised units); kT was hard-coded
--   to 1; LandauerPass s = (heat ≥ bits_erased · kT · ln 2), the real
--   Landauer floor (commit 2c68bea).
--   v3 model: kT is an opaque positive real, introduced via a section
--   variable with `[Fact (0 < kT)]`; `landauerFloorPerBit kT = kT · ln 2`
--   is now parametric. `LandauerPass`, `composeWith`, `compose`,
--   `heatConsumed`, and both bonus theorems thread kT through. The
--   consumer-contract statement (`landauer_monotonic` in
--   `N6.Weave.LandauerMonotonic`) keeps its external shape because kT is
--   implicit-via-section: only `[Fact (0 < kT)]` shows up in the binder
--   list, and the hypothesis/conclusion shape is unchanged.
--   v3 caveats: energy is still ℝ; the reversible-merge cancellation is
--   still taken as input (not computed from the strategy structure); a v4
--   stretch could parametrise the entire energy substrate (e.g. arbitrary
--   `[OrderedAddCommGroup E]` with a positive `floor : E` instead of `ℝ`).
--   Intentionally out of scope for v3 promotion.

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Logic.Basic

namespace N6
namespace Weave

section LandauerParam

-- Opaque Boltzmann-temperature product kT (positive real, joules).
-- v3 promotion: this is a section variable parametrising the entire
-- Landauer-floor stack; instantiate it at consumer sites (e.g. kT = 1
-- for normalised units, kT = k_B · T for SI).
variable (kT : ℝ) [hkT : Fact (0 < kT)]

/-- Landauer floor energy per bit-erasure: kT · ln 2 (joules per bit).
    Lower bound on the heat dissipation required for one irreversible bit
    erasure (Landauer 1961). v3: parametric in kT. -/
noncomputable def landauerFloorPerBit : ℝ := kT * Real.log 2

/-- The Landauer floor energy is strictly positive (kT > 0, ln 2 > 0). -/
lemma landauerFloorPerBit_pos : 0 < landauerFloorPerBit kT := by
  unfold landauerFloorPerBit
  have hkT_pos : (0 : ℝ) < kT := hkT.out
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  exact mul_pos hkT_pos h2

/-- The Landauer floor energy is nonnegative. -/
lemma landauerFloorPerBit_nonneg : 0 ≤ landauerFloorPerBit kT :=
  le_of_lt (landauerFloorPerBit_pos kT)

end LandauerParam

/-- A sub-strategy carrying (a) the number of irreversible bit-erasures it
    performs and (b) its real-valued heat dissipation budget (joules).
    Strategy is kT-agnostic; kT only appears in the `LandauerPass`
    predicate and the composition operators. -/
structure Strategy where
  bits_erased : Nat
  heat        : ℝ

/-- Heat consumed by a strategy (real-valued, joules). -/
def heatConsumed (s : Strategy) : ℝ := s.heat

section LandauerParam

variable (kT : ℝ) [hkT : Fact (0 < kT)]

/-- Landauer-pass predicate: heat budget covers the real Landauer floor
    `bits_erased · kT · ln 2`. v3: parametric in kT. -/
def LandauerPass (s : Strategy) : Prop :=
  s.heat ≥ (s.bits_erased : ℝ) * landauerFloorPerBit kT

/-- A LandauerPass strategy has nonneg heat (since the Landauer floor is
    nonneg and bits_erased is a Nat). Used downstream to prove the
    sequential-monotonicity theorem. -/
lemma landauer_pass_heat_nonneg (s : Strategy) (h : LandauerPass kT s) :
    0 ≤ s.heat := by
  have hbits : (0 : ℝ) ≤ (s.bits_erased : ℝ) := Nat.cast_nonneg _
  have hprod : (0 : ℝ) ≤ (s.bits_erased : ℝ) * landauerFloorPerBit kT :=
    mul_nonneg hbits (landauerFloorPerBit_nonneg kT)
  unfold LandauerPass at h
  linarith

end LandauerParam

/-- Composition mode: sequential (heat-additive, bit-additive) vs
    reversible-merge (sub-additive heat under cancellation). The real WEAVE
    composition algebra distinguishes these: sequential composition has the
    worst-case additive cost; reversible-merge can free up bit-erasures
    (and their Landauer floor) when re-composed. -/
inductive ComposeMode | seq | merge
  deriving DecidableEq

section LandauerParam

variable (kT : ℝ) [hkT : Fact (0 < kT)]

/-- Compose two strategies in a given mode.
    - `.seq`:   bits add, heat adds (classical Landauer).
    - `.merge`: bits subtract by `cancel` (Nat-saturating); heat subtracts by
                `cancel · floor` (real). Pre-condition `cancel ≤ b₁ + b₂` is
                tracked by the user (Nat subtraction saturates at 0 anyway).
    v3: parametric in kT (via the `landauerFloorPerBit kT` factor in `.merge`). -/
noncomputable def composeWith (m : ComposeMode) (s₁ s₂ : Strategy)
    (cancel : Nat := 0) : Strategy :=
  match m with
  | .seq =>
    { bits_erased := s₁.bits_erased + s₂.bits_erased,
      heat := s₁.heat + s₂.heat }
  | .merge =>
    { bits_erased := (s₁.bits_erased + s₂.bits_erased) - cancel,
      heat := s₁.heat + s₂.heat - (cancel : ℝ) * landauerFloorPerBit kT }

/-- Sequential composition (consumer-contract default; backward-compatible
    with the v1/v2 signature `compose : Strategy → Strategy → Strategy`).
    v3: kT threads through via the (vacuous-for-`.seq`) `composeWith` call;
    semantically `compose` does not depend on kT, but we keep the parameter
    for uniformity with the bonus theorems. -/
noncomputable def compose (s₁ s₂ : Strategy) : Strategy :=
  composeWith kT .seq s₁ s₂

-- Composition closure for `LandauerPass` (sequential): composing two
-- passing strategies yields a passing strategy. v3: parametric in kT.
-- `omit hkT`: the proof manipulates `landauerFloorPerBit kT` as an
-- opaque real factor; positivity of `kT` is not needed.
omit hkT in
theorem landauer_pass_compose
    (s₁ s₂ : Strategy) (h₁ : LandauerPass kT s₁) (h₂ : LandauerPass kT s₂) :
    LandauerPass kT (compose kT s₁ s₂) := by
  unfold LandauerPass compose composeWith at *
  show s₁.heat + s₂.heat ≥
        ((s₁.bits_erased + s₂.bits_erased : ℕ) : ℝ) * landauerFloorPerBit kT
  push_cast
  have : s₁.heat + s₂.heat ≥
           (s₁.bits_erased : ℝ) * landauerFloorPerBit kT +
           (s₂.bits_erased : ℝ) * landauerFloorPerBit kT := by linarith
  linarith [this,
    add_mul (s₁.bits_erased : ℝ) (s₂.bits_erased : ℝ) (landauerFloorPerBit kT)]

-- Composition closure for `LandauerPass` under reversible merge.
-- Assumes `cancel ≤ b₁ + b₂` (which Nat subtraction enforces by
-- saturation; we still need it explicitly for the real-valued heat side).
-- The floor is preserved: merging two passing strategies and re-using
-- `cancel` bit-erasures cannot drop heat below the resulting bit count's
-- Landauer floor. v3: parametric in kT.
-- `omit hkT`: same as `landauer_pass_compose` — positivity not used in
-- the linarith/ring chain over the opaque `landauerFloorPerBit kT` factor.
omit hkT in
theorem landauer_pass_merge
    (s₁ s₂ : Strategy) (cancel : Nat)
    (h_cancel : cancel ≤ s₁.bits_erased + s₂.bits_erased)
    (h₁ : LandauerPass kT s₁) (h₂ : LandauerPass kT s₂) :
    LandauerPass kT (composeWith kT .merge s₁ s₂ cancel) := by
  unfold LandauerPass composeWith at *
  -- Goal: s₁.heat + s₂.heat - cancel·floor
  --       ≥ ((s₁.bits + s₂.bits) - cancel : ℕ) · floor
  -- Nat subtraction → ℝ cast: ((a + b) - c : ℕ) : ℝ = ((a + b) : ℝ) - (c : ℝ) when c ≤ a + b.
  have hcast :
      (((s₁.bits_erased + s₂.bits_erased) - cancel : ℕ) : ℝ) =
        ((s₁.bits_erased + s₂.bits_erased : ℕ) : ℝ) - (cancel : ℝ) :=
    Nat.cast_sub (R := ℝ) h_cancel
  rw [hcast]
  push_cast
  have h_sub :
      ((s₁.bits_erased : ℝ) + (s₂.bits_erased : ℝ) - (cancel : ℝ))
          * landauerFloorPerBit kT
        = (s₁.bits_erased : ℝ) * landauerFloorPerBit kT
          + (s₂.bits_erased : ℝ) * landauerFloorPerBit kT
          - (cancel : ℝ) * landauerFloorPerBit kT := by
    ring
  rw [h_sub]
  linarith [h₁, h₂]

end LandauerParam

end Weave
end N6
