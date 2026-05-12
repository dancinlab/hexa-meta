-- N6.Weave.PiP2Verifier
--
-- WEAVE-semantics v3 vocabulary for axis F-CL-FORMAL-3 (Π^p_2 verifier
-- termination). PROMOTED v2 → v3 on 2026-05-12 (cycle-30+++++) from the
-- v2 closed-form `c.size * 2 ^ q.depth + q.payload` upper bound to a
-- *recursive* verifier function `verifierStepsRec` that models the
-- alternation cascade structurally on `depth`. Termination is then a
-- consequence of Lean's structural-recursion well-foundedness on `Nat`
-- (no explicit `WellFoundedRelation` instance needed).
-- Previous v2 commit: hexa-meta `2c68bea`.
--
-- raw_91 honest C3 disclosure (2026-05-12 cycle-30+++++):
--   v2 model: verifierSteps q := c.size * 2^q.depth + q.payload (closed-form
--   upper bound).
--   v3 model: verifierSteps q := verifierStepsRec c.size q.depth q.payload,
--   where verifierStepsRec is a recursive function structurally decreasing
--   on the depth argument (base case: depth = 0 returns sz + payload as a
--   leaf-level catalogue scan; inductive case: depth = d+1 doubles the
--   recursive call at depth d, modelling the ∃/∀ alternation branching).
--   Closed-form characterisation: verifierStepsRec sz d p = 2^d * (sz + p)
--   — kernel-checked as `verifierStepsRec_closed_form`. This is *stricter*
--   than v2 (v2 = sz·2^d + p; v3 = 2^d·(sz + p) = sz·2^d + p·2^d ≥ v2 when
--   2^d ≥ 1), but in the same exponential complexity class.
--   v3 termination is by Lean's automatic structural-recursion on Nat
--   (well-foundedness of `Nat.rec`), not an explicit WellFoundedRelation
--   instance — that is intentional: the standard `Nat.rec` IS the
--   well-founded recursor on Nat. A v4 stretch could use `WellFoundedRelation`
--   over an arbitrary measure function (e.g. `(catalogue_size, query_depth)`
--   lex-order via `Prod.lex`) to model verifiers whose recursion is not on
--   depth alone — intentionally out of scope for v3.

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace N6
namespace Weave

/-- Strand catalogue: a list of strand identifiers. Canonical n=6 case is
    a 12-element list (the 12-strand cube/oct duality catalogue). -/
structure StrandCatalogue where
  strands : List Nat
  deriving Repr

/-- Catalogue size. -/
def StrandCatalogue.size (c : StrandCatalogue) : Nat := c.strands.length

/-- A Π^p_2 query against a catalogue: carries (a) the alternation depth
    (existential-then-universal nesting count) and (b) an opaque payload
    representing the encoded predicate. -/
structure Pi_p_2_Query (_c : StrandCatalogue) where
  depth   : Nat
  payload : Nat
  deriving Repr

/-- Recursive verifier step counter (v3: structural recursion on alternation
    depth). Terminates by Lean's automatic well-founded recursion on Nat.
    - base (depth = 0): a single catalogue scan + payload check.
    - step (depth = d+1): two recursive sub-calls at depth d (modelling the
      ∃/∀ alternation branching at this level). -/
def verifierStepsRec (sz : Nat) (depth : Nat) (payload : Nat) : Nat :=
  match depth with
  | 0     => sz + payload
  | d + 1 => 2 * verifierStepsRec sz d payload

/-- Step count of the verifier on a query (v3: recursive). The closed-form
    is `2^q.depth * (c.size + q.payload)` — see `verifierStepsRec_closed_form`. -/
def verifierSteps {c : StrandCatalogue} (q : Pi_p_2_Query c) : Nat :=
  verifierStepsRec c.size q.depth q.payload

/-- The exponential factor is at least 1 for any depth. -/
theorem two_pow_pos (d : Nat) : 1 ≤ 2 ^ d := by
  induction d with
  | zero => simp
  | succ n ih =>
    have hstep : 2 ^ n ≤ 2 ^ (n + 1) := by
      rw [Nat.pow_succ]; omega
    exact Nat.le_trans ih hstep

/-- **Closed-form characterisation of `verifierStepsRec`** (v3 ↔ exponential
    bound link). Proved by induction on `d` using `Nat.pow_succ` and `ring`.
    This is the kernel-checked statement that the recursive verifier's cost
    is *exactly* `2^d · (sz + p)` — confirming the v2 exponential complexity
    class while now backed by a real recursion. -/
theorem verifierStepsRec_closed_form (sz d p : Nat) :
    verifierStepsRec sz d p = 2 ^ d * (sz + p) := by
  induction d with
  | zero =>
    simp [verifierStepsRec]
  | succ n ih =>
    show verifierStepsRec sz (n + 1) p = 2 ^ (n + 1) * (sz + p)
    unfold verifierStepsRec
    rw [ih, Nat.pow_succ]
    ring

/-- Monotonicity in depth + payload: deeper/heavier queries take at least
    as many recursive steps. Proof goes through the closed-form. -/
theorem verifierSteps_mono_depth
    {c : StrandCatalogue} (q q' : Pi_p_2_Query c)
    (hd : q.depth ≤ q'.depth) (hp : q.payload ≤ q'.payload) :
    verifierSteps q ≤ verifierSteps q' := by
  unfold verifierSteps
  rw [verifierStepsRec_closed_form, verifierStepsRec_closed_form]
  have h12 : (1 : Nat) ≤ 2 := by omega
  have hpow : 2 ^ q.depth ≤ 2 ^ q'.depth := Nat.pow_le_pow_right h12 hd
  have hsum : c.size + q.payload ≤ c.size + q'.payload :=
    Nat.add_le_add_left hp _
  exact Nat.mul_le_mul hpow hsum

/-- **Bonus theorem** (v3 ≥ v2-bound link): the v3 recursive verifier cost
    is at least the v2 closed-form upper bound `c.size * 2^q.depth +
    q.payload`. Confirms the v2 → v3 promotion is *stricter* (the recursive
    model is more pessimistic than the v2 closed-form because every
    alternation level multiplies the payload work too, not just the
    catalogue-scan work). -/
theorem verifierSteps_ge_v2_bound
    {c : StrandCatalogue} (q : Pi_p_2_Query c) :
    c.size * 2 ^ q.depth + q.payload ≤ verifierSteps q := by
  unfold verifierSteps
  rw [verifierStepsRec_closed_form]
  -- Goal: c.size * 2^d + payload ≤ 2^d * (c.size + payload)
  --     = 2^d * c.size + 2^d * payload
  -- Need: payload ≤ 2^d * payload (since 2^d ≥ 1)
  have h1 : 1 ≤ 2 ^ q.depth := two_pow_pos q.depth
  have hp : q.payload ≤ 2 ^ q.depth * q.payload := by
    have : 1 * q.payload ≤ 2 ^ q.depth * q.payload :=
      Nat.mul_le_mul_right q.payload h1
    linarith
  nlinarith [hp]

end Weave
end N6
