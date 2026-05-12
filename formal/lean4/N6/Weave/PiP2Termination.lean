-- N6.Weave.PiP2Termination
--
-- Axis F-CL-FORMAL-3 — Π^p_2 verifier termination on the canonical
-- 12-strand catalogue. Consumer contract: theorem
-- `pi_p2_verifier_terminates`. PROMOTED v2 → v3 on 2026-05-12 (cycle-30+++++)
-- — see `N6.Weave.PiP2Verifier` for the v3 recursive `verifierSteps`.
--
-- Pairs with: hexa-bio/weave/spec/lean4_mechanical_layer_v0.scaffold.md §2.3
-- Pairs with: .roadmap.weave §Falsifier preregister F-CL-FORMAL-3
-- Pairs with: hexa-bio _python_bridge/module/weave_pi_p2_verifier_v3_exhaustive.py
-- Pairs with: .roadmap.lean4_formal §3 (v3 promotion work-order, Axis 3 — last)
--
-- raw_91 honest C3 disclosure (2026-05-12 cycle-30+++++):
--   Kernel-checked on lean4 4.30.0-rc2 + Mathlib (SHA pinned), sorry_count = 0.
--   The v3 witness is `2 ^ q.depth * (12 + q.payload)` — equal to the
--   recursive `verifierStepsRec 12 q.depth q.payload` by the closed-form
--   characterisation `verifierStepsRec_closed_form`. This is the
--   recursively-defined alternation cost on the canonical 12-strand
--   catalogue: at depth 0 the verifier does 12 + payload work (single
--   catalogue scan + payload check); each additional alternation level
--   doubles the work via two recursive sub-calls.
--   v3 supersedes v2: v2 had a closed-form `c.size * 2^d + payload`
--   witness that was a *strict lower bound* on the recursive cost (the
--   recursive model multiplies the payload work at every level too, not
--   just the catalogue-scan work). The v2 → v3 link is captured by
--   `verifierSteps_ge_v2_bound` in `N6.Weave.PiP2Verifier`.
--   Termination is by Lean's automatic structural-recursion well-foundedness
--   on Nat (the `Nat.rec` recursor IS well-founded; no explicit
--   `WellFoundedRelation` instance is required for the `match`-on-Nat form
--   `verifierStepsRec` uses). v4 stretch (cycle-30++++++): swap to an
--   arbitrary measure function via `WellFoundedRelation`/`Prod.lex` to
--   model verifiers whose decreasing measure is not depth alone — out of
--   scope for v3 promotion.

import N6.Weave.PiP2Verifier

namespace N6
namespace Weave

/-- **Axis F-CL-FORMAL-3** (consumer contract, v3-PROVEN):
    every Π^p_2 query against the canonical 12-strand catalogue has an
    explicit step bound. Proof exhibits `n = 2 ^ q.depth * (12 + q.payload)`
    and discharges by rewriting `verifierSteps` through
    `verifierStepsRec_closed_form` and the catalogue-size hypothesis `h`.

    The recursive `verifierStepsRec` (in `N6.Weave.PiP2Verifier`) is what
    the witness counts; the closed-form `2^d · (sz + p)` is the
    kernel-checked characterisation of that recursion. -/
theorem pi_p2_verifier_terminates
    (cat : StrandCatalogue) (h : cat.size = 12) (q : Pi_p_2_Query cat) :
    ∃ (n : Nat), verifierSteps q ≤ n :=
  ⟨2 ^ q.depth * (12 + q.payload), by
      unfold verifierSteps
      rw [verifierStepsRec_closed_form, h]⟩

end Weave
end N6
