-- N6.Weave.PiP2Verifier
--
-- WEAVE-semantics v2 vocabulary for axis F-CL-FORMAL-3 (Π^p_2 verifier
-- termination). PROMOTED 2026-05-12 (cycle-30+++) from the v1 polynomial
-- bounded-instance encoding (`c.size * (q.depth + 1) + q.payload`) to the
-- v2 exponential-in-depth worst case (`c.size * 2 ^ q.depth + q.payload`),
-- matching the literature-standard Π^p_2 complexity bound (the second
-- level of the polynomial hierarchy is QBF-complete with alternation
-- count d → 2^d quantifier-elimination work at worst).
--
-- raw_91 honest C3 disclosure (2026-05-12 cycle-30+++):
--   The v2 exponential-in-depth bound is the worst-case Π^p_2 verifier
--   cost in symbolic-alternation-elimination terms. Tighter sub-exponential
--   bounds may apply to specific instance families (e.g. the v1 polynomial
--   bound is correct for the bounded-instance v3 exhaustive verifier on the
--   12-strand catalogue, where payload structure constrains the search).
--   v2 is the *worst-case* claim; v3 (cycle-30+++) could parametrise over
--   verifier strategies (with the bound switching by query family). The
--   exponential 2^depth uses Nat.pow which is decidable; no Mathlib import
--   needed here (Strategy.lean already pulls Mathlib for ℝ, so the package
--   is loaded — we just don't use Mathlib lemmas in this file).

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

/-- Step count of the verifier on a query (v2: exponential-in-depth).
    `verifierSteps q = c.size * 2 ^ q.depth + q.payload`. The exponential
    factor captures the Π^p_2 alternation cost (2^d nested ∀-elimination
    branches in the worst case). For the bounded-instance v3 verifier on
    the 12-strand catalogue the actual cost is sub-exponential (see v1
    comment); this v2 definition is the *worst-case* bound. -/
def verifierSteps {c : StrandCatalogue} (q : Pi_p_2_Query c) : Nat :=
  c.size * 2 ^ q.depth + q.payload

/-- The exponential factor is at least 1 for any depth. -/
theorem two_pow_pos (d : Nat) : 1 ≤ 2 ^ d := by
  induction d with
  | zero => simp
  | succ n ih =>
    have hstep : 2 ^ n ≤ 2 ^ (n + 1) := by
      rw [Nat.pow_succ]; omega
    exact Nat.le_trans ih hstep

/-- Monotonicity in depth: deeper queries take at least as many steps. -/
theorem verifierSteps_mono_depth
    {c : StrandCatalogue} (q q' : Pi_p_2_Query c)
    (hd : q.depth ≤ q'.depth) (hp : q.payload ≤ q'.payload) :
    verifierSteps q ≤ verifierSteps q' := by
  unfold verifierSteps
  have h12 : 1 ≤ 2 := by omega
  have hpow : 2 ^ q.depth ≤ 2 ^ q'.depth := Nat.pow_le_pow_right h12 hd
  have hmul : c.size * 2 ^ q.depth ≤ c.size * 2 ^ q'.depth :=
    Nat.mul_le_mul_left c.size hpow
  exact Nat.add_le_add hmul hp

end Weave
end N6
