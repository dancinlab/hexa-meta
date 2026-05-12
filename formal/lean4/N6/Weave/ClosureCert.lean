-- N6.Weave.ClosureCert
--
-- Axis F-CL-FORMAL-4 — closure-cert disclosure idempotence. Consumer
-- contract: theorem `closure_cert_idempotent`. RE-PROVEN against
-- WEAVE-semantics v1 on 2026-05-12 (cycle-30) — `discloseOnce` is no
-- longer the identity; it is a structural field-overwrite that sets the
-- `disclosed` flag.
--
-- Pairs with: hexa-bio/weave/spec/lean4_mechanical_layer_v0.scaffold.md §2.4
-- Pairs with: .roadmap.weave §Falsifier preregister F-CL-FORMAL-4 (PARTIAL)
--
-- raw_91 honest C3 disclosure (2026-05-12):
--   Kernel-checked on lean4 4.30.0-rc1, sorry_count = 0. Idempotence now
--   reduces by the record-overwrite identity: re-setting a field to the
--   same value yields a definitionally-equal record, so `discloseTwice c
--   = discloseOnce c` discharges by `rfl` over the upgraded semantics.
--   This is structurally the real disclosure idempotence at the integer-
--   flag level. Caveat: the full WEAVE disclosure semantics
--   (`raw_91_c3_disclose:MVP_caveat`) carries payload-level conditions
--   (caveat-bag invariance, signer-set monotonicity) that this v1 model
--   does not encode. The wider F-CL-FORMAL-4 PARTIAL annotation in
--   `.roadmap.weave` therefore still applies; only the flag-level fragment
--   is mechanised here.

namespace N6
namespace Weave

/-- Closure-certificate: a disclosure artefact with an opaque payload
    plus a Bool flag tracking whether `discloseOnce` has been applied.
    This is the flag-level v1 model of the
    `raw_91_c3_disclose:MVP_caveat` semantics. -/
structure ClosureCert where
  payload   : Nat
  disclosed : Bool
  deriving Repr

/-- First disclosure: sets the `disclosed` flag to `true`. Idempotent by
    construction (record-overwrite). -/
def discloseOnce (c : ClosureCert) : ClosureCert :=
  { c with disclosed := true }

/-- Repeated disclosure: apply `discloseOnce` twice. -/
def discloseTwice (c : ClosureCert) : ClosureCert :=
  discloseOnce (discloseOnce c)

/-- Axis F-CL-FORMAL-4: applying disclosure twice equals applying it once.
    Proof: under the field-overwrite semantics,
      discloseTwice c
        = { (discloseOnce c) with disclosed := true }
        = { { c with disclosed := true } with disclosed := true }
        = { c with disclosed := true }     -- record-overwrite identity
        = discloseOnce c
    by definitional unfolding. -/
theorem closure_cert_idempotent :
    ∀ c : ClosureCert, discloseTwice c = discloseOnce c
  := fun _ => rfl

end Weave
end N6
