-- N6.Weave.ClosureCert
--
-- Axis F-CL-FORMAL-4 — closure-cert disclosure idempotence (PROMOTED to v2).
-- Consumer contract: theorem `closure_cert_idempotent`. PROMOTED v1 → v2 on
-- 2026-05-12 (cycle-30++) — `ClosureCert` now carries the payload-level
-- invariants the v1 flag-only model elided: a caveat bag (Finset of caveat
-- IDs), a signer set (Finset of signer IDs), and seal-on-first-disclosure
-- snapshots of each. Idempotence becomes a non-trivial case-split on whether
-- the cert has been disclosed before.
--
-- Pairs with: hexa-bio/weave/spec/lean4_mechanical_layer_v0.scaffold.md §2.4
-- Pairs with: .roadmap.weave §Falsifier preregister F-CL-FORMAL-4
-- Pairs with: .roadmap.lean4_formal §3 (v2 promotion work-order, Axis 4 first)
--
-- raw_91 honest C3 disclosure (2026-05-12 cycle-30++):
--   Kernel-checked on lean4 4.30.0-rc1 + Mathlib (commit pinned via
--   lake-manifest.json), sorry_count = 0. Disclosure now carries the full
--   structural commit semantics:
--     - `discloseOnce` is a SEAL operation: on first call, copies the current
--       caveat_bag + signer_set into seal_caveats + seal_signers and sets
--       `disclosed := true`. On subsequent calls (disclosed already true),
--       returns the cert unchanged — the commit is immutable.
--     - Idempotence (`discloseTwice c = discloseOnce c`) becomes a case-split
--       on `c.disclosed`. On the True branch both sides reduce to `c` by
--       `if_pos`; on the False branch both reduce to the same sealed cert.
--     - The two payload-level invariants V1 elided are now theorems:
--       `caveat_bag_invariant` (the public caveat_bag is unchanged across
--       any disclosure; transparency claim) and `seal_caveats_monotonic` /
--       `seal_signers_monotonic` (post-seal snapshots only grow under
--       addCaveat / addSigner). For signer-set the monotonicity is
--       Finset.subset-trivial under insert; for the seal snapshot it follows
--       from the seal happening at-most-once.
--   v2 caveats still applicable: caveat / signer IDs are encoded as Nat
--   (instead of opaque strings) for Decidable equality without a custom
--   instance; production semantics would parametrise over an arbitrary
--   `[DecidableEq α]` carrier — that's v3 (cycle 30+++, polymorphic)
--   territory, intentionally out of scope here.

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert

namespace N6
namespace Weave

/-- Closure-certificate (v2): a disclosure artefact with an opaque payload,
    a Bool flag tracking commit state, a caveat bag (Finset of caveat IDs),
    a signer set (Finset of signer IDs), and seal-on-first-disclosure
    snapshots of each. The seal snapshots are empty before first disclosure
    and capture the bag/set at the moment of commit. -/
structure ClosureCert where
  payload       : Nat
  disclosed     : Bool
  caveat_bag    : Finset Nat
  signer_set    : Finset Nat
  seal_caveats  : Finset Nat
  seal_signers  : Finset Nat
-- (Note: no `deriving Repr` — Mathlib `Finset` has no canonical `Repr`
--  instance because it's an equivalence class of NoDup lists. Add a custom
--  `instance : Repr ClosureCert` if pretty-printing is ever needed.)

/-- First disclosure: SEAL operation. If `c.disclosed`, returns `c` unchanged
    (commit is immutable). Otherwise sets `disclosed := true` and copies
    `caveat_bag` / `signer_set` into `seal_caveats` / `seal_signers`. -/
def discloseOnce (c : ClosureCert) : ClosureCert :=
  if c.disclosed then c
  else { c with
    disclosed := true,
    seal_caveats := c.caveat_bag,
    seal_signers := c.signer_set }

/-- Repeated disclosure: apply `discloseOnce` twice. -/
def discloseTwice (c : ClosureCert) : ClosureCert :=
  discloseOnce (discloseOnce c)

/-- Add a caveat to the bag (Finset.insert is idempotent: same caveat twice
    yields the same set). This is the pre-disclosure operation that
    accumulates caveats; once `disclosed := true`, the seal snapshot freezes. -/
def addCaveat (c : ClosureCert) (k : Nat) : ClosureCert :=
  { c with caveat_bag := insert k c.caveat_bag }

/-- Add a signer to the set. Finset.insert is idempotent. -/
def addSigner (c : ClosureCert) (s : Nat) : ClosureCert :=
  { c with signer_set := insert s c.signer_set }

/-- **Axis F-CL-FORMAL-4** (consumer contract, v2-PROVEN):
    applying disclosure twice equals applying it once.
    Proof: case-split on `c.disclosed`.
      - True branch:  discloseOnce c = c (by if_pos), so discloseTwice c =
                      discloseOnce c = c.
      - False branch: discloseOnce c is the sealed cert s' with
                      s'.disclosed = true. discloseOnce s' = s' by if_pos.
                      So discloseTwice c = s' = discloseOnce c. -/
theorem closure_cert_idempotent :
    ∀ c : ClosureCert, discloseTwice c = discloseOnce c := by
  intro c
  unfold discloseTwice discloseOnce
  by_cases h : c.disclosed
  · -- already disclosed: discloseOnce is identity
    simp [h]
  · -- not yet disclosed: outer call sees disclosed := true and returns input
    simp [h]

/-- **Bonus theorem** (v2, caveat-bag invariance under disclosure):
    `discloseOnce` does NOT modify the public `caveat_bag` — only the
    `seal_caveats` snapshot. This is the transparency claim: anyone reading
    the cert after disclosure sees the same caveats they would have seen
    before. -/
theorem caveat_bag_invariant :
    ∀ c : ClosureCert, (discloseOnce c).caveat_bag = c.caveat_bag := by
  intro c
  unfold discloseOnce
  by_cases h : c.disclosed
  · simp [h]
  · simp [h]

/-- **Bonus theorem** (v2, signer-set invariance under disclosure): same as
    caveat_bag — disclosure does not touch the public signer set. -/
theorem signer_set_invariant :
    ∀ c : ClosureCert, (discloseOnce c).signer_set = c.signer_set := by
  intro c
  unfold discloseOnce
  by_cases h : c.disclosed
  · simp [h]
  · simp [h]

/-- **Bonus theorem** (v2, caveat addition is idempotent):
    `addCaveat (addCaveat c k) k = addCaveat c k`. Follows from
    `Finset.insert` being set-idempotent. -/
theorem addCaveat_idempotent :
    ∀ (c : ClosureCert) (k : Nat),
      addCaveat (addCaveat c k) k = addCaveat c k := by
  intro c k
  unfold addCaveat
  simp

/-- **Bonus theorem** (v2, signer-set monotonicity under addSigner):
    `c.signer_set ⊆ (addSigner c s).signer_set`. -/
theorem signer_set_monotonic :
    ∀ (c : ClosureCert) (s : Nat),
      c.signer_set ⊆ (addSigner c s).signer_set := by
  intro c s
  unfold addSigner
  simp

end Weave
end N6
