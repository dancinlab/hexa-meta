-- N6.Weave.ClosureCert
--
-- Axis F-CL-FORMAL-4 — closure-cert disclosure idempotence (PROMOTED to v4).
-- Consumer contract: theorem `closure_cert_idempotent`. PROMOTED v3 → v4 on
-- 2026-05-12 (cycle-30++++++) — caveats are now first-class data with
-- `[CommMonoid β]` payloads, generalising v3's opaque set-membership
-- semantics. Each caveat entry is a pair `(k : α, v : β)` where `α` is the
-- caveat-ID carrier and `β` is the payload (severity, count, weight, etc.).
-- The signer set is unchanged (signers carry no payload — they are identities).
--
-- Pairs with: hexa-bio/weave/spec/lean4_mechanical_layer_v0.scaffold.md §2.4
-- Pairs with: .roadmap.weave §Falsifier preregister F-CL-FORMAL-4
-- Pairs with: .roadmap.lean4_formal §3 (v4 promotion, monoid payload carrier)
--
-- Prior commits credited:
--   - v1 → v2 introduced caveat_bag / signer_set / seal snapshots over `Nat`
--     (hexa-meta `350798c`, 2026-05-12 cycle-30++).
--   - v2 → v3 generalised the carrier to `[DecidableEq α]`
--     (hexa-meta `9e44e75`, 2026-05-12 cycle-30++++).
--   - v3 → v4 (this file) generalises caveat payloads to `[CommMonoid β]`
--     (2026-05-12 cycle-30++++++).
--
-- raw_91 honest C3 disclosure (2026-05-12 cycle-30++++++):
--   Kernel-checked on lean4 4.30.0-rc1 + Mathlib (commit pinned via
--   lake-manifest.json, SHA `f8e537424d154a7eaa025c4abab16c96c626f2e0`),
--   sorry_count = 0. v4 polymorphic payload semantics:
--     - `ClosureCert α β` for any `[DecidableEq α] [CommMonoid β]`.
--       Caveat IDs (α) can be `Nat`, `String`, `Fin n`, etc.; payload values
--       (β) can be `Nat` (with `+`/`0` … wait, `CommMonoid` is `*`/`1`,
--       so for additive `Nat` counts use `Multiplicative Nat` or commute via
--       `[AddCommMonoid]` adapter), `WithTop ℕ` (severity grades), `Multiset α'`
--       (bag unions), `Finset α'` under union (idempotent commutative monoid),
--       or any custom domain-specific weight type.
--     - **Payload-carrier choice: `Finset (α × β)`.** Each caveat entry is a
--       pair (caveat ID, payload). This was preferred over `α → β` because:
--         (a) `Finset.prod` aggregation is automatic without needing a finite-
--             support witness (a `Finsupp` would be cleaner but adds bigger
--             Mathlib dependency surface);
--         (b) the v3 → v4 diff stays structurally close — `Finset α` becomes
--             `Finset (α × β)`, all proof tactics generalise mechanically;
--         (c) multiple entries with the same key are *allowed* (different
--             severities for the same caveat ID), and `totalCaveatPayload`
--             aggregates correctly under `CommMonoid` semantics.
--       Downside acknowledged: `addCaveat c k v₁` then `addCaveat c k v₂` does
--       NOT collapse into a single entry with payload `v₁ * v₂`; instead two
--       entries `(k, v₁)` and `(k, v₂)` coexist. The aggregate
--       `totalCaveatPayload` still gives `v₁ * v₂` (modulo other entries) so
--       downstream consumers see the right composed weight. A `Finsupp`-based
--       v5 would collapse keys structurally.
--     - `discloseOnce` SEAL: on first call (disclosed = false), copies the
--       current `caveat_bag : Finset (α × β)` and `signer_set : Finset α` into
--       `seal_caveats` / `seal_signers` and sets `disclosed := true`. On
--       subsequent calls, returns the cert unchanged.
--     - Idempotence (`discloseTwice c = discloseOnce c`) proof is structurally
--       identical to v3 — case-split on `c.disclosed`, both branches close by
--       `simp [h]`. The β payload does not enter the proof at all.
--     - `totalCaveatPayload : ClosureCert α β → β` aggregates via
--       `Finset.prod (fun p => p.2)` over the caveat bag. New in v4.
--   v4 caveat — `addCaveat_idempotent` REPLACED, not dropped:
--     - In v3, `addCaveat (addCaveat c k) k = addCaveat c k` followed from
--       `Finset.insert` set-idempotence. In v4, the v3 statement is still TRUE
--       structurally on `Finset (α × β)` if we insert the SAME pair `(k, v)`
--       twice — `Finset.insert` dedups on structural equality of pairs. So the
--       theorem survives in a slightly weaker form: same key AND same payload
--       collapse. We KEEP this as `addCaveat_idempotent` (now over `(k, v)`).
--     - Additionally, we ADD `addCaveat_commutative` as the v4-spirit theorem:
--       order of caveat insertion does not matter (independent of monoid).
--       This is the honest v4 generalisation — the monoid axioms guarantee
--       composition order-independence at the aggregate level.
--     - We intentionally DO NOT require `[IdempotentMonoid β]` or
--       `[SemilatticeSup β]` — that's v5 territory (lattice-grade severity
--       merging). v4 stays at the bare `[CommMonoid β]` floor.
--   v4 caveats / future stretch (v5, intentionally OUT OF SCOPE here):
--     - Promote `Finset (α × β)` to `α →₀ β` (`Finsupp`) so same-key inserts
--       collapse into a single entry combined via `·*·`. Requires
--       `Mathlib.Data.Finsupp.Basic`. Would change `addCaveat` to update
--       `caveats k := caveats k * v` and reduce ambiguity.
--     - Add `[SemilatticeSup β]` overload so caveats can also be merged by
--       max (severity grades) rather than only multiplied. Useful for
--       "highest severity wins" disclosure policies.
--     - Quantify *partial-disclosure* transparency: prove that
--       `totalCaveatPayload (discloseOnce c) = totalCaveatPayload c`, which
--       would be a strict generalisation of the v3/v4 `caveat_bag_invariant`.

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace N6
namespace Weave

/-- Closure-certificate (v4, polymorphic carrier + monoid payload):
    a disclosure artefact with an opaque `Nat` payload, a Bool commit flag, a
    caveat bag `Finset (α × β)` (each caveat = ID × monoid-valued weight), a
    signer set `Finset α` (signers carry no payload), and seal-on-first-
    disclosure snapshots of each. `α` is any type with `[DecidableEq α]`; `β`
    is any type with `[DecidableEq β]` (needed for `Finset (α × β)`) and
    `[CommMonoid β]` (needed for `totalCaveatPayload` aggregation). -/
structure ClosureCert (α : Type) [DecidableEq α]
    (β : Type) [DecidableEq β] [CommMonoid β] where
  payload       : Nat
  disclosed     : Bool
  caveat_bag    : Finset (α × β)
  signer_set    : Finset α
  seal_caveats  : Finset (α × β)
  seal_signers  : Finset α
-- (Note: no `deriving Repr` — Mathlib `Finset` has no canonical `Repr`
--  instance because it's an equivalence class of NoDup lists. Add a custom
--  `instance : Repr (ClosureCert α β)` if pretty-printing is ever needed.)

variable {α : Type} [DecidableEq α]
variable {β : Type} [DecidableEq β] [CommMonoid β]

/-- First disclosure: SEAL operation. If `c.disclosed`, returns `c` unchanged
    (commit is immutable). Otherwise sets `disclosed := true` and copies
    `caveat_bag` / `signer_set` into `seal_caveats` / `seal_signers`. -/
def discloseOnce (c : ClosureCert α β) : ClosureCert α β :=
  if c.disclosed then c
  else { c with
    disclosed := true,
    seal_caveats := c.caveat_bag,
    seal_signers := c.signer_set }

/-- Repeated disclosure: apply `discloseOnce` twice. -/
def discloseTwice (c : ClosureCert α β) : ClosureCert α β :=
  discloseOnce (discloseOnce c)

/-- Add a caveat (key + monoid-valued payload) to the bag. `Finset.insert`
    dedups structural equality of pairs, so `(k, v)` inserted twice yields the
    same set. Same key with different payload (e.g. `(k, v₁)` then `(k, v₂)`)
    creates two coexisting entries — aggregation via `totalCaveatPayload`
    combines them through the `CommMonoid` `·*·`. -/
def addCaveat (c : ClosureCert α β) (k : α) (v : β) : ClosureCert α β :=
  { c with caveat_bag := insert (k, v) c.caveat_bag }

/-- Add a signer to the set. Finset.insert is idempotent. Signers carry no
    payload (β plays no role here). -/
def addSigner (c : ClosureCert α β) (s : α) : ClosureCert α β :=
  { c with signer_set := insert s c.signer_set }

/-- Aggregate caveat payload via `CommMonoid` `·*·` over the bag.
    Returns `1 : β` for the empty bag. New in v4 — this is the consumer-side
    way to ask "how much caveat weight does this cert carry?" without
    introspecting individual entries. -/
def totalCaveatPayload (c : ClosureCert α β) : β :=
  c.caveat_bag.prod (fun p => p.2)

/-- **Axis F-CL-FORMAL-4** (consumer contract, v4-PROVEN, polymorphic carrier +
    monoid payload): applying disclosure twice equals applying it once.
    Proof: case-split on `c.disclosed`. The β payload does NOT enter the
    proof — the structure of `discloseOnce` is identical to v3.
      - True branch:  discloseOnce c = c (by if_pos), so discloseTwice c =
                      discloseOnce c = c.
      - False branch: discloseOnce c is the sealed cert s' with
                      s'.disclosed = true. discloseOnce s' = s' by if_pos.
                      So discloseTwice c = s' = discloseOnce c. -/
theorem closure_cert_idempotent :
    ∀ c : ClosureCert α β, discloseTwice c = discloseOnce c := by
  intro c
  unfold discloseTwice discloseOnce
  by_cases h : c.disclosed
  · -- already disclosed: discloseOnce is identity
    simp [h]
  · -- not yet disclosed: outer call sees disclosed := true and returns input
    simp [h]

/-- **Bonus theorem** (v4, caveat-bag invariance under disclosure):
    `discloseOnce` does NOT modify the public `caveat_bag` — only the
    `seal_caveats` snapshot. Transparency claim: anyone reading the cert
    after disclosure sees the same caveats they would have seen before. -/
theorem caveat_bag_invariant :
    ∀ c : ClosureCert α β, (discloseOnce c).caveat_bag = c.caveat_bag := by
  intro c
  unfold discloseOnce
  by_cases h : c.disclosed
  · simp [h]
  · simp [h]

/-- **Bonus theorem** (v4, signer-set invariance under disclosure): same as
    `caveat_bag_invariant` — disclosure does not touch the public signer set. -/
theorem signer_set_invariant :
    ∀ c : ClosureCert α β, (discloseOnce c).signer_set = c.signer_set := by
  intro c
  unfold discloseOnce
  by_cases h : c.disclosed
  · simp [h]
  · simp [h]

/-- **Bonus theorem** (v4, caveat addition is idempotent on identical entries):
    `addCaveat (addCaveat c k v) k v = addCaveat c k v`. Follows from
    `Finset.insert` being set-idempotent on structurally-equal pairs `(k, v)`.
    NOTE: this is *narrower* than v3's claim — inserting the SAME (k, v) twice
    is idempotent, but inserting `(k, v₁)` then `(k, v₂)` (different payloads)
    creates two coexisting entries. The v4-spirit replacement is
    `addCaveat_commutative` below. -/
theorem addCaveat_idempotent :
    ∀ (c : ClosureCert α β) (k : α) (v : β),
      addCaveat (addCaveat c k v) k v = addCaveat c k v := by
  intro c k v
  unfold addCaveat
  simp

/-- **Bonus theorem** (v4, caveat addition is commutative, NEW in v4):
    order of caveat insertion does not matter. This is the v4-spirit
    generalisation — the `CommMonoid` structure of `β` guarantees that
    composition is order-independent at the aggregate level, and at the
    structural level `Finset.insert` already commutes. Honest scope: the
    monoid axioms are not actually USED in this proof (Finset.insert commutes
    regardless), but the theorem makes the v4 semantic intent explicit. -/
theorem addCaveat_commutative :
    ∀ (c : ClosureCert α β) (k₁ k₂ : α) (v₁ v₂ : β),
      (addCaveat (addCaveat c k₁ v₁) k₂ v₂).caveat_bag =
        (addCaveat (addCaveat c k₂ v₂) k₁ v₁).caveat_bag := by
  intro c k₁ k₂ v₁ v₂
  unfold addCaveat
  simp [Finset.insert_comm]

/-- **Bonus theorem** (v4, signer-set monotonicity under addSigner):
    `c.signer_set ⊆ (addSigner c s).signer_set`. -/
theorem signer_set_monotonic :
    ∀ (c : ClosureCert α β) (s : α),
      c.signer_set ⊆ (addSigner c s).signer_set := by
  intro c s
  unfold addSigner
  simp

end Weave
end N6
