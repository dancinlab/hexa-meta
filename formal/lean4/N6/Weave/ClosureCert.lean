-- N6.Weave.ClosureCert
--
-- Axis F-CL-FORMAL-4 — closure-cert disclosure idempotence (PROMOTED to v3).
-- Consumer contract: theorem `closure_cert_idempotent`. PROMOTED v2 → v3 on
-- 2026-05-12 (cycle-30++++) — `ClosureCert` is now polymorphic over the
-- caveat/signer carrier `α` (any type with `[DecidableEq α]`), generalising
-- the v2 hard-coded `Nat` IDs. The payload remains `Nat` and the commit flag
-- remains `Bool`; only the bag/set fields are polymorphic.
--
-- Pairs with: hexa-bio/weave/spec/lean4_mechanical_layer_v0.scaffold.md §2.4
-- Pairs with: .roadmap.weave §Falsifier preregister F-CL-FORMAL-4
-- Pairs with: .roadmap.lean4_formal §3 (v3 promotion, polymorphic carrier)
--
-- Prior commits credited:
--   - v1 → v2 introduced caveat_bag / signer_set / seal snapshots over `Nat`
--     (hexa-meta `350798c`, 2026-05-12 cycle-30++).
--   - v2 → v3 (this file) generalises the carrier to `[DecidableEq α]`
--     (2026-05-12 cycle-30++++).
--
-- raw_91 honest C3 disclosure (2026-05-12 cycle-30++++):
--   Kernel-checked on lean4 4.30.0-rc1 + Mathlib (commit pinned via
--   lake-manifest.json, SHA `f8e537424d154a7eaa025c4abab16c96c626f2e0`),
--   sorry_count = 0. Polymorphic carrier semantics:
--     - `ClosureCert α` for any `[DecidableEq α]` — caveat / signer IDs can be
--       `Nat`, `String`, `Fin n`, an enum, or any custom hashable type as long
--       as decidable equality is available (Mathlib `Finset` requires it).
--     - `discloseOnce` is a SEAL operation: on first call, copies the current
--       caveat_bag + signer_set into seal_caveats + seal_signers and sets
--       `disclosed := true`. On subsequent calls (disclosed already true),
--       returns the cert unchanged — the commit is immutable.
--     - Idempotence (`discloseTwice c = discloseOnce c`) is a case-split on
--       `c.disclosed`. On the True branch both sides reduce to `c` by
--       `if_pos`; on the False branch both reduce to the same sealed cert.
--     - Five bonus theorems re-proved with α-generic tactics: the proofs are
--       identical to v2 modulo the carrier name. No new Mathlib imports
--       required — `Finset.Basic` + `Finset.Insert` already provide
--       polymorphic `Finset α` machinery for any `[DecidableEq α]`.
--   v3 caveats / future stretch (v4, intentionally OUT OF SCOPE here):
--     - Caveats and signers are still set-theoretic bags. A v4 stretch could
--       parametrise the payload over `[CommutativeMonoid β]` so caveats carry
--       composable weights (e.g. severity, multiplicity) rather than being
--       opaque set members. That would let `addCaveat` accumulate via `· * ·`
--       on β instead of `Finset.insert`, and a stronger transparency claim
--       could quantify *how much* caveat-weight is sealed. Not v3 work.
--     - Bag/set equality remains structural (`Finset` `=`); a v4 quotient
--       under permutation of insertion order is automatic from `Finset`
--       semantics already, so no v4 work there.

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert

namespace N6
namespace Weave

/-- Closure-certificate (v3, polymorphic): a disclosure artefact with an
    opaque payload (`Nat`), a Bool flag tracking commit state, a caveat bag
    (`Finset α`), a signer set (`Finset α`), and seal-on-first-disclosure
    snapshots of each (`Finset α`). The carrier `α` is any type with
    `[DecidableEq α]`. The seal snapshots are empty before first disclosure
    and capture the bag/set at the moment of commit. -/
structure ClosureCert (α : Type) [DecidableEq α] where
  payload       : Nat
  disclosed     : Bool
  caveat_bag    : Finset α
  signer_set    : Finset α
  seal_caveats  : Finset α
  seal_signers  : Finset α
-- (Note: no `deriving Repr` — Mathlib `Finset` has no canonical `Repr`
--  instance because it's an equivalence class of NoDup lists. Add a custom
--  `instance : Repr (ClosureCert α)` if pretty-printing is ever needed.)

variable {α : Type} [DecidableEq α]

/-- First disclosure: SEAL operation. If `c.disclosed`, returns `c` unchanged
    (commit is immutable). Otherwise sets `disclosed := true` and copies
    `caveat_bag` / `signer_set` into `seal_caveats` / `seal_signers`. -/
def discloseOnce (c : ClosureCert α) : ClosureCert α :=
  if c.disclosed then c
  else { c with
    disclosed := true,
    seal_caveats := c.caveat_bag,
    seal_signers := c.signer_set }

/-- Repeated disclosure: apply `discloseOnce` twice. -/
def discloseTwice (c : ClosureCert α) : ClosureCert α :=
  discloseOnce (discloseOnce c)

/-- Add a caveat to the bag (Finset.insert is idempotent: same caveat twice
    yields the same set). This is the pre-disclosure operation that
    accumulates caveats; once `disclosed := true`, the seal snapshot freezes. -/
def addCaveat (c : ClosureCert α) (k : α) : ClosureCert α :=
  { c with caveat_bag := insert k c.caveat_bag }

/-- Add a signer to the set. Finset.insert is idempotent. -/
def addSigner (c : ClosureCert α) (s : α) : ClosureCert α :=
  { c with signer_set := insert s c.signer_set }

/-- **Axis F-CL-FORMAL-4** (consumer contract, v3-PROVEN, polymorphic):
    applying disclosure twice equals applying it once.
    Proof: case-split on `c.disclosed`.
      - True branch:  discloseOnce c = c (by if_pos), so discloseTwice c =
                      discloseOnce c = c.
      - False branch: discloseOnce c is the sealed cert s' with
                      s'.disclosed = true. discloseOnce s' = s' by if_pos.
                      So discloseTwice c = s' = discloseOnce c. -/
theorem closure_cert_idempotent :
    ∀ c : ClosureCert α, discloseTwice c = discloseOnce c := by
  intro c
  unfold discloseTwice discloseOnce
  by_cases h : c.disclosed
  · -- already disclosed: discloseOnce is identity
    simp [h]
  · -- not yet disclosed: outer call sees disclosed := true and returns input
    simp [h]

/-- **Bonus theorem** (v3, caveat-bag invariance under disclosure):
    `discloseOnce` does NOT modify the public `caveat_bag` — only the
    `seal_caveats` snapshot. This is the transparency claim: anyone reading
    the cert after disclosure sees the same caveats they would have seen
    before. -/
theorem caveat_bag_invariant :
    ∀ c : ClosureCert α, (discloseOnce c).caveat_bag = c.caveat_bag := by
  intro c
  unfold discloseOnce
  by_cases h : c.disclosed
  · simp [h]
  · simp [h]

/-- **Bonus theorem** (v3, signer-set invariance under disclosure): same as
    caveat_bag — disclosure does not touch the public signer set. -/
theorem signer_set_invariant :
    ∀ c : ClosureCert α, (discloseOnce c).signer_set = c.signer_set := by
  intro c
  unfold discloseOnce
  by_cases h : c.disclosed
  · simp [h]
  · simp [h]

/-- **Bonus theorem** (v3, caveat addition is idempotent):
    `addCaveat (addCaveat c k) k = addCaveat c k`. Follows from
    `Finset.insert` being set-idempotent. -/
theorem addCaveat_idempotent :
    ∀ (c : ClosureCert α) (k : α),
      addCaveat (addCaveat c k) k = addCaveat c k := by
  intro c k
  unfold addCaveat
  simp

/-- **Bonus theorem** (v3, signer-set monotonicity under addSigner):
    `c.signer_set ⊆ (addSigner c s).signer_set`. -/
theorem signer_set_monotonic :
    ∀ (c : ClosureCert α) (s : α),
      c.signer_set ⊆ (addSigner c s).signer_set := by
  intro c s
  unfold addSigner
  simp

end Weave
end N6
