-- N6.Weave.PiP2Termination
--
-- Axis F-CL-FORMAL-3 — Π^p_2 verifier termination on the canonical
-- 12-strand catalogue. Consumer contract: theorem
-- `pi_p2_verifier_terminates`. PROMOTED v3 → v4 on 2026-05-12
-- (cycle-30++++++) — see `N6.Weave.PiP2Verifier` for the v4
-- lex-measure recursive `verifierSteps`.
--
-- Pairs with: hexa-bio/weave/spec/lean4_mechanical_layer_v0.scaffold.md §2.3
-- Pairs with: .roadmap.weave §Falsifier preregister F-CL-FORMAL-3
-- Pairs with: hexa-bio _python_bridge/module/weave_pi_p2_verifier_v3_exhaustive.py
-- Pairs with: .roadmap.lean4_formal §3 (v4 promotion work-order, Axis 3 — last)
--
-- raw_91 honest C3 disclosure (2026-05-12 cycle-30++++++):
--   Kernel-checked on lean4 4.30.0-rc2 + Mathlib (SHA pinned), sorry_count = 0.
--   The v4 witness is `2 ^ q.depth * (12 + q.payload)` — equal to the
--   lex-measure recursive `verifierStepsLex 12 q.depth q.payload` by the
--   closed-form characterisation `verifierStepsLex_closed_form`.
--   Numerically identical to v3's witness (the v3 ↔ v4 equivalence is
--   captured by `verifierStepsLex_eq_v3` in `N6.Weave.PiP2Verifier`), but
--   the underlying recursion is structurally distinct: v3 recurses on a
--   single Nat (`depth`); v4 recurses on a `Prod.lex` tuple
--   `(depth, catalogue_size)` over `Nat × Nat`, with Mathlib's
--   `WellFoundedRelation` instance for `Prod.lex` discharging termination.
--   v4 supersedes v3: v3's termination was an implicit appeal to
--   `Nat.rec` structural well-foundedness; v4's termination uses an
--   *explicit* `WellFoundedRelation` (lex on `Nat × Nat`) via
--   `termination_by (depth, sz)` + `decreasing_by` invoking
--   `Prod.Lex.left` / `Prod.Lex.right` constructors. This captures
--   verifiers whose decreasing argument is not depth alone (e.g.
--   catalogue-scan bookkeeping interleaved with alternation branching).
--   v5 stretch (cycle-30+++++++): parametrise the verifier strategy as a
--   typeclass — `class VerifierStrategy` carrying both the recursion
--   shape and the decreasing measure as data, so the consumer contract
--   `pi_p2_verifier_terminates` quantifies over *any* strategy. Out of
--   scope for v4.

import N6.Weave.PiP2Verifier

namespace N6
namespace Weave

/-- **Axis F-CL-FORMAL-3** (consumer contract, v4-PROVEN):
    every Π^p_2 query against the canonical 12-strand catalogue has an
    explicit step bound. Proof exhibits `n = 2 ^ q.depth * (12 + q.payload)`
    and discharges by rewriting `verifierSteps` through
    `verifierStepsLex_closed_form` and the catalogue-size hypothesis `h`.

    The lex-measure recursive `verifierStepsLex` (in `N6.Weave.PiP2Verifier`)
    is what the witness counts; the closed-form `2^d · (sz + p)` is the
    kernel-checked characterisation of that recursion. Numerically equal
    to the v3 fallback `verifierStepsRec` (see `verifierStepsLex_eq_v3`),
    but with `WellFoundedRelation` over `Prod.lex (Nat × Nat)` rather
    than `Nat.rec` discharging termination. -/
theorem pi_p2_verifier_terminates
    (cat : StrandCatalogue) (h : cat.size = 12) (q : Pi_p_2_Query cat) :
    ∃ (n : Nat), verifierSteps q ≤ n :=
  ⟨2 ^ q.depth * (12 + q.payload), by
      unfold verifierSteps
      rw [verifierStepsLex_closed_form, h]⟩

end Weave
end N6
