-- N6.Weave.PiP2Verifier
--
-- WEAVE-semantics v4 vocabulary for axis F-CL-FORMAL-3 (Π^p_2 verifier
-- termination). PROMOTED v3 → v4 on 2026-05-12 (cycle-30++++++) from the
-- v3 single-Nat structural recursion `verifierStepsRec` to a *lex-measure*
-- recursive verifier `verifierStepsLex` whose decreasing argument is a
-- `Prod.lex` tuple `(depth, catalogue_size)` on `(Nat × Nat)`. Termination
-- is now an *explicit* `WellFoundedRelation` (the lex order on `Nat × Nat`,
-- supplied by Mathlib's `Prod.Lex.instWellFoundedRelation`), no longer a
-- bare appeal to `Nat.rec` structural well-foundedness.
-- Previous v3 commit: hexa-meta `2680f88`.
--
-- raw_91 honest C3 disclosure (2026-05-12 cycle-30++++++):
--   v3 model: verifierStepsRec sz d p — structural recursion on `d : Nat`
--   with base case `sz + p` (single catalogue scan) and doubling step
--   `2 * verifierStepsRec sz d p`. Termination automatic via `Nat.rec`.
--   v4 model: verifierStepsLex sz d p — three-way branching recursion
--   whose decreasing measure is the lex tuple `(d, sz)` on `Nat × Nat`:
--     • base    (d = 0, sz = 0)     : return `p`  (no catalogue, no
--                                     alternation — bare payload check).
--     • scan    (d = 0, sz = sz'+1) : `1 + verifierStepsLex sz' 0 p`
--                                     (catalogue scan step: second
--                                     component of the lex tuple
--                                     decreases from `sz` to `sz'`
--                                     while the first stays 0).
--     • branch  (d = d'+1)          : `2 * verifierStepsLex sz d' p`
--                                     (alternation doubling: first
--                                     component of the lex tuple
--                                     decreases from `d` to `d'`).
--   v4 termination is therefore *not* on a single Nat — it is on
--   `Prod.lex` over `(Nat × Nat)` (Mathlib's `WellFoundedRelation`
--   instance), captured via `termination_by (d, sz)` and discharged by
--   `decreasing_by` with `Prod.Lex` constructors. This models verifiers
--   whose decreasing argument is not depth alone (e.g. catalogue-scan
--   bookkeeping interleaved with alternation branching).
--   Closed-form characterisation: verifierStepsLex sz d p = 2^d * (sz + p)
--   — kernel-checked as `verifierStepsLex_closed_form` by lex induction
--   (depth induction outer, catalogue-size induction inner at the d=0
--   base layer). Same exponential complexity class as v3; numerically
--   *equal* to v3's `verifierStepsRec`. The v3 ↔ v4 link is captured by
--   `verifierStepsLex_eq_v3` below.
--   v5 stretch could parametrise the verifier strategy as a class /
--   typeclass — e.g. `class VerifierStrategy` carrying the recursion
--   shape + the decreasing measure as data — letting the consumer
--   contract `pi_p2_verifier_terminates` quantify over *any* strategy.
--   Intentionally out of scope for v4.

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Order.WellFounded
import Mathlib.Order.Lex
import Mathlib.Data.Prod.Lex

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

/-- **v3 fallback** recursive verifier step counter (kept for the v3 ↔ v4
    equivalence theorem `verifierStepsLex_eq_v3` below; consumer code uses
    `verifierStepsLex`). Structural recursion on alternation depth. -/
def verifierStepsRec (sz : Nat) (depth : Nat) (payload : Nat) : Nat :=
  match depth with
  | 0     => sz + payload
  | d + 1 => 2 * verifierStepsRec sz d payload

/-- **v4 recursive verifier step counter.** Three-way branching with the
    decreasing measure being the lex tuple `(depth, sz)` on `Nat × Nat`:
    - base   `(d = 0, sz = 0)`     : return `payload` (bare payload check).
    - scan   `(d = 0, sz = sz'+1)` : `1 + verifierStepsLex sz' 0 payload`
      (catalogue scan: lex second component decreases).
    - branch `(d = d'+1)`          : `2 * verifierStepsLex sz d' payload`
      (alternation doubling: lex first component decreases).

    Termination is via `Prod.lex` well-foundedness on `Nat × Nat`
    (Mathlib `WellFoundedRelation` instance). -/
def verifierStepsLex (sz : Nat) (depth : Nat) (payload : Nat) : Nat :=
  match depth, sz with
  | 0,     0      => payload
  | 0,     sz' + 1 => 1 + verifierStepsLex sz' 0 payload
  | d' + 1, sz    => 2 * verifierStepsLex sz d' payload
  termination_by (depth, sz)
  decreasing_by
    · -- scan branch: lex tuple (0, sz') < (0, sz' + 1)
      -- (first component equal, second component strictly decreases)
      simp_wf
      exact Prod.Lex.right 0 (Nat.lt_succ_self sz')
    · -- branch branch: lex tuple (d', sz) < (d' + 1, sz)
      -- (first component strictly decreases, second component irrelevant)
      simp_wf
      exact Prod.Lex.left _ _ (Nat.lt_succ_self d')

/-- Step count of the verifier on a query (v4: lex-measure recursive). The
    closed-form is `2^q.depth * (c.size + q.payload)` — see
    `verifierStepsLex_closed_form`. -/
def verifierSteps {c : StrandCatalogue} (q : Pi_p_2_Query c) : Nat :=
  verifierStepsLex c.size q.depth q.payload

/-- The exponential factor is at least 1 for any depth. -/
theorem two_pow_pos (d : Nat) : 1 ≤ 2 ^ d := by
  induction d with
  | zero => simp
  | succ n ih =>
    have hstep : 2 ^ n ≤ 2 ^ (n + 1) := by
      rw [Nat.pow_succ]; omega
    exact Nat.le_trans ih hstep

/-- Equation lemma for the v4 verifier's **scan branch**:
    `verifierStepsLex (sz' + 1) 0 p = 1 + verifierStepsLex sz' 0 p`.
    Stated as a standalone lemma because well-founded recursion does not
    unfold by `rfl` — we use the auto-generated equation compiler lemma
    via `simp [verifierStepsLex]`. -/
theorem verifierStepsLex_scan (sz' p : Nat) :
    verifierStepsLex (sz' + 1) 0 p = 1 + verifierStepsLex sz' 0 p := by
  simp [verifierStepsLex]

/-- Equation lemma for the v4 verifier's **branch (alternation) branch**:
    `verifierStepsLex sz (d' + 1) p = 2 * verifierStepsLex sz d' p`. -/
theorem verifierStepsLex_branch (sz d' p : Nat) :
    verifierStepsLex sz (d' + 1) p = 2 * verifierStepsLex sz d' p := by
  simp [verifierStepsLex]

/-- Closed form at depth 0: `verifierStepsLex sz 0 p = sz + p`. Proved by
    induction on the catalogue size `sz` (the inner lex component). -/
theorem verifierStepsLex_depth_zero (sz p : Nat) :
    verifierStepsLex sz 0 p = sz + p := by
  induction sz with
  | zero => simp [verifierStepsLex]
  | succ n ih =>
    rw [verifierStepsLex_scan, ih]
    omega

/-- **Closed-form characterisation of `verifierStepsLex`** (v4 ↔ exponential
    bound link). Same numeric value as v3's `verifierStepsRec`: namely
    `2^d · (sz + p)`. Proof: induction on the outer lex component `d`,
    invoking `verifierStepsLex_depth_zero` at the base. -/
theorem verifierStepsLex_closed_form (sz d p : Nat) :
    verifierStepsLex sz d p = 2 ^ d * (sz + p) := by
  induction d with
  | zero =>
    rw [verifierStepsLex_depth_zero]
    simp
  | succ n ih =>
    rw [verifierStepsLex_branch, ih, Nat.pow_succ]
    ring

/-- **v3 fallback** closed form (kept for the v3 ↔ v4 link). -/
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

/-- **v3 ↔ v4 numerical equivalence.** The v4 lex-measure verifier and
    the v3 structural-Nat verifier produce identical step counts on every
    input. The two recursions are *structurally distinct* (v3 recurses on
    `depth` only, v4 recurses on the lex tuple `(depth, sz)`), but their
    closed forms coincide — confirming v4 is a measure-refinement, not a
    cost-class change. -/
theorem verifierStepsLex_eq_v3 (sz d p : Nat) :
    verifierStepsLex sz d p = verifierStepsRec sz d p := by
  rw [verifierStepsLex_closed_form, verifierStepsRec_closed_form]

/-- Monotonicity in depth + payload: deeper/heavier queries take at least
    as many recursive steps. Proof goes through the closed-form. -/
theorem verifierSteps_mono_depth
    {c : StrandCatalogue} (q q' : Pi_p_2_Query c)
    (hd : q.depth ≤ q'.depth) (hp : q.payload ≤ q'.payload) :
    verifierSteps q ≤ verifierSteps q' := by
  unfold verifierSteps
  rw [verifierStepsLex_closed_form, verifierStepsLex_closed_form]
  have h12 : (1 : Nat) ≤ 2 := by omega
  have hpow : 2 ^ q.depth ≤ 2 ^ q'.depth := Nat.pow_le_pow_right h12 hd
  have hsum : c.size + q.payload ≤ c.size + q'.payload :=
    Nat.add_le_add_left hp _
  exact Nat.mul_le_mul hpow hsum

/-- **Bonus theorem** (v4 ≥ v2-bound link): the v4 lex-measure verifier
    cost is at least the v2 closed-form upper bound `c.size * 2^q.depth +
    q.payload`. Same statement as v3's `verifierSteps_ge_v2_bound`
    (because v4 and v3 are numerically equal) — re-proved against the
    v4 closed form for cleanliness. -/
theorem verifierSteps_ge_v2_bound
    {c : StrandCatalogue} (q : Pi_p_2_Query c) :
    c.size * 2 ^ q.depth + q.payload ≤ verifierSteps q := by
  unfold verifierSteps
  rw [verifierStepsLex_closed_form]
  have h1 : 1 ≤ 2 ^ q.depth := two_pow_pos q.depth
  have hp : q.payload ≤ 2 ^ q.depth * q.payload := by
    have : 1 * q.payload ≤ 2 ^ q.depth * q.payload :=
      Nat.mul_le_mul_right q.payload h1
    linarith
  nlinarith [hp]

end Weave
end N6
