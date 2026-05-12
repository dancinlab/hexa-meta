-- N6.Weave.Strategy
--
-- WEAVE-semantics v4 vocabulary for axis F-CL-FORMAL-2 (Landauer floor
-- monotonicity). PROMOTED v3 → v4 on 2026-05-12 (cycle-30++++++) from a
-- ℝ-valued heat model with kT·ln 2 baked-in to a substrate-polymorphic
-- model: heat lives in an arbitrary linearly-ordered additive commutative
-- group `E`, with the Landauer floor an opaque positive element `floor : E`.
-- Previous v3 commit: hexa-meta 9e44e75 (2026-05-12 cycle-30++++).
--
-- raw_91 honest C3 disclosure (2026-05-12 cycle-30++++++):
--   v1 model: Strategy { bits_erased, heat_kT_ln2 : Nat }; compose Nat-additive
--   on both fields; LandauerPass s = (heat_kT_ln2 ≥ bits_erased).
--   v2 model: heat is ℝ in joules (or normalised units); kT was hard-coded
--   to 1; LandauerPass s = (heat ≥ bits_erased · ln 2), the Landauer floor
--   (commit 2c68bea).
--   v3 model: kT an opaque positive real via section variable + `[Fact (0 < kT)]`;
--   `landauerFloorPerBit kT = kT · ln 2`; consumer contract unchanged shape
--   (commit 9e44e75).
--   v4 model: energy substrate fully abstracted. `Strategy E` is parametric
--   over `E` with `[AddCommGroup E] [LinearOrder E] [IsOrderedAddMonoid E]`
--   (modern Mathlib unbundled spelling of "linearly ordered abelian group";
--   `LinearOrder` is needed for `max` in the consumer contract). The floor
--   is an opaque positive `floor : E` (no longer `kT · Real.log 2` — that
--   specific factorisation is ℝ-only and is lost at the substrate level;
--   consumers can recover it by instantiating `E := ℝ` and `floor := kT * Real.log 2`).
--   `LandauerPass floor s := s.heat ≥ s.bits_erased • floor` using the
--   Nat-smul from `AddCommGroup` (every additive commutative monoid has a
--   canonical Nat-smul; an ordered group inherits the monotonicity we need).
--   v4 caveats:
--     - The `kT · Real.log 2` calculation is no longer in the kernel-checked
--       statement; it's a consumer-instantiation concern.
--     - The reversible-merge cancellation is still taken as input (not
--       derived from a finer composition algebra).
--     - v5 stretch: parametrise the ring/module structure (e.g. equip `E`
--       with a scalar action over a richer commutative semiring for entropic
--       weights, free-energy decompositions, etc.). Intentionally out of
--       scope for v4 promotion.

import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Logic.Basic

namespace N6
namespace Weave

section LandauerParam

-- Substrate-polymorphic energy type `E` together with an opaque positive
-- Landauer floor element. v4 promotion: this is a section-variable block
-- parametrising the entire Landauer-floor stack; instantiate at consumer
-- sites (e.g. `E := ℝ`, `floor := kT * Real.log 2` recovers v3).
--
-- We use the modern unbundled spelling of "linearly ordered abelian group"
-- since `OrderedAddCommGroup` / `LinearOrderedAddCommGroup` are no longer
-- single classes in current Mathlib (see `Mathlib.Algebra.Order.Group.Defs`
-- header comment). `LinearOrder` is needed for `max` in `landauer_monotonic`.
variable {E : Type*}
  [AddCommGroup E] [LinearOrder E] [IsOrderedAddMonoid E]
  (floor : E) [hfloor : Fact (0 < floor)]

/-- The Landauer floor energy is strictly positive (consumer-provided via
    the `[Fact (0 < floor)]` instance). v4: opaque substrate-level positivity. -/
lemma landauerFloor_pos : (0 : E) < floor := hfloor.out

/-- The Landauer floor energy is nonnegative. -/
lemma landauerFloor_nonneg : (0 : E) ≤ floor :=
  le_of_lt (landauerFloor_pos floor)

end LandauerParam

/-- A sub-strategy carrying (a) the number of irreversible bit-erasures it
    performs and (b) its energy-substrate heat dissipation budget.
    v4: parametric over the energy type `E`; the floor only appears in the
    `LandauerPass` predicate and the composition operators. -/
structure Strategy (E : Type*) where
  bits_erased : Nat
  heat        : E

/-- Heat consumed by a strategy (substrate-typed). -/
def heatConsumed {E : Type*} (s : Strategy E) : E := s.heat

section LandauerParam

variable {E : Type*}
  [AddCommGroup E] [LinearOrder E] [IsOrderedAddMonoid E]
  (floor : E) [hfloor : Fact (0 < floor)]

/-- Landauer-pass predicate: heat budget covers the substrate-level
    Landauer floor `bits_erased • floor` (Nat-smul in `E`).
    v4: parametric over `E` and the opaque positive floor. -/
def LandauerPass (s : Strategy E) : Prop :=
  s.heat ≥ s.bits_erased • floor

/-- A LandauerPass strategy has nonneg heat (since the Landauer floor is
    positive and `bits_erased • floor ≥ 0` follows from `nsmul_nonneg`).
    Used downstream to prove the sequential-monotonicity theorem. -/
lemma landauer_pass_heat_nonneg (s : Strategy E) (h : LandauerPass floor s) :
    (0 : E) ≤ s.heat := by
  have hfloor_nn : (0 : E) ≤ floor := landauerFloor_nonneg floor
  have hsmul_nn : (0 : E) ≤ s.bits_erased • floor :=
    nsmul_nonneg hfloor_nn s.bits_erased
  -- h : LandauerPass floor s, i.e. s.heat ≥ s.bits_erased • floor.
  -- Transitivity: 0 ≤ s.bits_erased • floor ≤ s.heat.
  exact le_trans hsmul_nn h

end LandauerParam

/-- Composition mode: sequential (heat-additive, bit-additive) vs
    reversible-merge (sub-additive heat under cancellation). The real WEAVE
    composition algebra distinguishes these: sequential composition has the
    worst-case additive cost; reversible-merge can free up bit-erasures
    (and their Landauer floor) when re-composed. -/
inductive ComposeMode | seq | merge
  deriving DecidableEq

section LandauerParam

variable {E : Type*}
  [AddCommGroup E] [LinearOrder E] [IsOrderedAddMonoid E]
  (floor : E) [hfloor : Fact (0 < floor)]

/-- Compose two strategies in a given mode.
    - `.seq`:   bits add, heat adds (classical Landauer).
    - `.merge`: bits subtract by `cancel` (Nat-saturating); heat subtracts by
                `cancel • floor` in `E`. Pre-condition `cancel ≤ b₁ + b₂` is
                tracked by the user (Nat subtraction saturates at 0 anyway).
    v4: parametric over `E` and the opaque positive floor. -/
def composeWith (m : ComposeMode) (s₁ s₂ : Strategy E)
    (cancel : Nat := 0) : Strategy E :=
  match m with
  | .seq =>
    { bits_erased := s₁.bits_erased + s₂.bits_erased,
      heat := s₁.heat + s₂.heat }
  | .merge =>
    { bits_erased := (s₁.bits_erased + s₂.bits_erased) - cancel,
      heat := s₁.heat + s₂.heat - cancel • floor }

/-- Sequential composition (consumer-contract default; backward-compatible
    with the v1/v2/v3 signature pattern `compose : Strategy → Strategy → Strategy`).
    v4: floor threads through via the (vacuous-for-`.seq`) `composeWith` call;
    semantically `compose` does not depend on the floor for `.seq`, but we
    keep the parameter for uniformity with the bonus theorems. -/
def compose (s₁ s₂ : Strategy E) : Strategy E :=
  composeWith floor .seq s₁ s₂

-- Composition closure for `LandauerPass` (sequential): composing two
-- passing strategies yields a passing strategy. v4: parametric over `E`.
-- `omit hfloor`: the proof manipulates `n • floor` algebraically;
-- positivity of `floor` is not needed here.
omit hfloor in
theorem landauer_pass_compose
    (s₁ s₂ : Strategy E) (h₁ : LandauerPass floor s₁) (h₂ : LandauerPass floor s₂) :
    LandauerPass floor (compose floor s₁ s₂) := by
  -- Show form: goal reduces to the seq branch of `composeWith` via defeq.
  show s₁.heat + s₂.heat ≥ (s₁.bits_erased + s₂.bits_erased) • floor
  rw [add_nsmul]
  -- h₁ : s₁.bits_erased • floor ≤ s₁.heat (≥ is sugar)
  -- h₂ : s₂.bits_erased • floor ≤ s₂.heat
  -- add_le_add gives sum-of-LHS ≤ sum-of-RHS, exactly the goal in LE form.
  exact add_le_add h₁ h₂

-- Composition closure for `LandauerPass` under reversible merge.
-- Assumes `cancel ≤ b₁ + b₂` (which Nat subtraction enforces by
-- saturation; we still need it explicitly to bridge the smul side).
-- The floor is preserved: merging two passing strategies and re-using
-- `cancel` bit-erasures cannot drop heat below the resulting bit count's
-- Landauer floor. v4: parametric over `E`.
-- `omit hfloor`: positivity not used in the linarith chain over opaque smul.
omit hfloor in
theorem landauer_pass_merge
    (s₁ s₂ : Strategy E) (cancel : Nat)
    (h_cancel : cancel ≤ s₁.bits_erased + s₂.bits_erased)
    (h₁ : LandauerPass floor s₁) (h₂ : LandauerPass floor s₂) :
    LandauerPass floor (composeWith floor .merge s₁ s₂ cancel) := by
  -- Reduce goal to the merge branch via defeq.
  show s₁.heat + s₂.heat - cancel • floor ≥
       ((s₁.bits_erased + s₂.bits_erased) - cancel) • floor
  -- Build h_sum_ge : s₁.heat + s₂.heat ≥ (s₁.bits + s₂.bits) • floor.
  have h_sum_ge : s₁.heat + s₂.heat ≥
      (s₁.bits_erased + s₂.bits_erased) • floor := by
    rw [add_nsmul]
    exact add_le_add h₁ h₂
  -- Subtract cancel • floor on both sides.
  have h_sub_ge : s₁.heat + s₂.heat - cancel • floor ≥
      (s₁.bits_erased + s₂.bits_erased) • floor - cancel • floor :=
    sub_le_sub_right h_sum_ge _
  -- Rewrite RHS: ((s₁.bits + s₂.bits) - cancel) • floor
  --   = (s₁.bits + s₂.bits) • floor - cancel • floor  (since cancel ≤ total).
  have h_recover : (s₁.bits_erased + s₂.bits_erased) - cancel + cancel =
      s₁.bits_erased + s₂.bits_erased :=
    Nat.sub_add_cancel h_cancel
  have h_split : ((s₁.bits_erased + s₂.bits_erased) - cancel) • floor + cancel • floor =
      (s₁.bits_erased + s₂.bits_erased) • floor := by
    rw [← add_nsmul, h_recover]
  have h_eq : (s₁.bits_erased + s₂.bits_erased) • floor - cancel • floor =
      ((s₁.bits_erased + s₂.bits_erased) - cancel) • floor := by
    rw [← h_split]; abel
  rw [h_eq] at h_sub_ge
  exact h_sub_ge

end LandauerParam

end Weave
end N6
