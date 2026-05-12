-- N6.Weave.Strategy
--
-- WEAVE-semantics v2 vocabulary for axis F-CL-FORMAL-2 (Landauer floor
-- monotonicity). PROMOTED 2026-05-12 (cycle-30+++) from the v1 integer-kT·ln2
-- model to a real-valued heat budget with explicit `kT · ln 2` floor and
-- a reversible-merge composition mode.
--
-- raw_91 honest C3 disclosure (2026-05-12 cycle-30+++):
--   v1 model: Strategy { bits_erased, heat_kT_ln2 : Nat }; compose Nat-additive
--   on both fields; LandauerPass s = (heat_kT_ln2 ≥ bits_erased).
--   v2 model: heat is ℝ in joules (or normalised units; kT is parametrised);
--   LandauerPass s = (heat ≥ bits_erased · kT · ln 2), the real Landauer floor.
--   `compose` defaults to sequential (`composeWith .seq`) for backward compat;
--   `composeWith .merge` models reversible-merge with a cancellation count
--   (number of irreversibly-erased bits that cancel out when two strategies
--   are composed in reverse, freeing their Landauer-floor heat budget).
--   Bonus theorems kernel-checked: `landauer_pass_compose` (closure under
--   sequential composition; v1 carried over, signature unchanged) and
--   `landauer_pass_merge` (closure under reversible-merge, bounded by
--   cancellation ≤ b₁ + b₂; the floor is preserved as long as cancellation
--   does not exceed total bit count).
--   v3 caveats: kT is fixed at 1 (normalised units) here; production semantics
--   would parametrise `[Fact (0 < kT)]` over an opaque temperature; the
--   reversible-merge cancellation is taken as input (not computed from the
--   strategy structure) — a v4 would derive it from the underlying WEAVE
--   composition algebra. Intentionally out of scope for v2 promotion.

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace N6
namespace Weave

/-- Boltzmann-temperature product kT (positive real, joules). Normalised
    to 1 here; v3 will parametrise over an opaque `[Fact (0 < kT)]`. -/
noncomputable def kT : ℝ := 1

/-- Landauer floor energy per bit-erasure: kT · ln 2 (joules per bit).
    Lower bound on the heat dissipation required for one irreversible bit
    erasure (Landauer 1961). -/
noncomputable def landauerFloorPerBit : ℝ := kT * Real.log 2

/-- The Landauer floor energy is strictly positive (kT > 0, ln 2 > 0). -/
lemma landauerFloorPerBit_pos : 0 < landauerFloorPerBit := by
  unfold landauerFloorPerBit kT
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-- The Landauer floor energy is nonnegative. -/
lemma landauerFloorPerBit_nonneg : 0 ≤ landauerFloorPerBit :=
  le_of_lt landauerFloorPerBit_pos

/-- A sub-strategy carrying (a) the number of irreversible bit-erasures it
    performs and (b) its real-valued heat dissipation budget (joules).
    v2 promotion: heat is ℝ, not the v1 integer kT·ln2 count. -/
structure Strategy where
  bits_erased : Nat
  heat        : ℝ

/-- Heat consumed by a strategy (real-valued, joules). -/
def heatConsumed (s : Strategy) : ℝ := s.heat

/-- Landauer-pass predicate: heat budget covers the real Landauer floor
    `bits_erased · kT · ln 2`. Promotion from v1 integer inequality
    (heat_kT_ln2 ≥ bits_erased) to the actual continuous-energy inequality. -/
def LandauerPass (s : Strategy) : Prop :=
  s.heat ≥ (s.bits_erased : ℝ) * landauerFloorPerBit

/-- A LandauerPass strategy has nonneg heat (since the Landauer floor is
    nonneg and bits_erased is a Nat). Used downstream to prove the
    sequential-monotonicity theorem. -/
lemma landauer_pass_heat_nonneg (s : Strategy) (h : LandauerPass s) :
    0 ≤ s.heat := by
  have hbits : (0 : ℝ) ≤ (s.bits_erased : ℝ) := Nat.cast_nonneg _
  have hprod : (0 : ℝ) ≤ (s.bits_erased : ℝ) * landauerFloorPerBit :=
    mul_nonneg hbits landauerFloorPerBit_nonneg
  unfold LandauerPass at h
  linarith

/-- Composition mode: sequential (heat-additive, bit-additive) vs
    reversible-merge (sub-additive heat under cancellation). The real WEAVE
    composition algebra distinguishes these: sequential composition has the
    worst-case additive cost; reversible-merge can free up bit-erasures
    (and their Landauer floor) when re-composed. -/
inductive ComposeMode | seq | merge
  deriving DecidableEq

/-- Compose two strategies in a given mode.
    - `.seq`:   bits add, heat adds (classical Landauer).
    - `.merge`: bits subtract by `cancel` (Nat-saturating); heat subtracts by
                `cancel · floor` (real). Pre-condition `cancel ≤ b₁ + b₂` is
                tracked by the user (Nat subtraction saturates at 0 anyway). -/
noncomputable def composeWith (m : ComposeMode) (s₁ s₂ : Strategy)
    (cancel : Nat := 0) : Strategy :=
  match m with
  | .seq =>
    { bits_erased := s₁.bits_erased + s₂.bits_erased,
      heat := s₁.heat + s₂.heat }
  | .merge =>
    { bits_erased := (s₁.bits_erased + s₂.bits_erased) - cancel,
      heat := s₁.heat + s₂.heat - (cancel : ℝ) * landauerFloorPerBit }

/-- Sequential composition (consumer-contract default; backward-compatible
    with the v1 signature `compose : Strategy → Strategy → Strategy`). -/
noncomputable def compose (s₁ s₂ : Strategy) : Strategy :=
  composeWith .seq s₁ s₂

/-- Composition closure for `LandauerPass` (sequential): composing two
    passing strategies yields a passing strategy. Real-valued analogue of
    the v1 `omega`-discharged version. -/
theorem landauer_pass_compose
    (s₁ s₂ : Strategy) (h₁ : LandauerPass s₁) (h₂ : LandauerPass s₂) :
    LandauerPass (compose s₁ s₂) := by
  unfold LandauerPass compose composeWith at *
  show s₁.heat + s₂.heat ≥ ((s₁.bits_erased + s₂.bits_erased : ℕ) : ℝ) * landauerFloorPerBit
  push_cast
  have : s₁.heat + s₂.heat ≥
           (s₁.bits_erased : ℝ) * landauerFloorPerBit +
           (s₂.bits_erased : ℝ) * landauerFloorPerBit := by linarith
  linarith [this, add_mul (s₁.bits_erased : ℝ) (s₂.bits_erased : ℝ) landauerFloorPerBit]

/-- Composition closure for `LandauerPass` under reversible merge.
    Assumes `cancel ≤ b₁ + b₂` (which Nat subtraction enforces by
    saturation; we still need it explicitly for the real-valued heat side).
    The floor is preserved: merging two passing strategies and re-using
    `cancel` bit-erasures cannot drop heat below the resulting bit count's
    Landauer floor. -/
theorem landauer_pass_merge
    (s₁ s₂ : Strategy) (cancel : Nat)
    (h_cancel : cancel ≤ s₁.bits_erased + s₂.bits_erased)
    (h₁ : LandauerPass s₁) (h₂ : LandauerPass s₂) :
    LandauerPass (composeWith .merge s₁ s₂ cancel) := by
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
  have h_add :
      ((s₁.bits_erased : ℝ) + (s₂.bits_erased : ℝ)) * landauerFloorPerBit
        = (s₁.bits_erased : ℝ) * landauerFloorPerBit
          + (s₂.bits_erased : ℝ) * landauerFloorPerBit := by
    ring
  have h_sub :
      ((s₁.bits_erased : ℝ) + (s₂.bits_erased : ℝ) - (cancel : ℝ)) * landauerFloorPerBit
        = (s₁.bits_erased : ℝ) * landauerFloorPerBit
          + (s₂.bits_erased : ℝ) * landauerFloorPerBit
          - (cancel : ℝ) * landauerFloorPerBit := by
    ring
  rw [h_sub]
  linarith [h₁, h₂]

end Weave
end N6
