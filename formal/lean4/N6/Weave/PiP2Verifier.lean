-- N6.Weave.PiP2Verifier
--
-- WEAVE-semantics v1 vocabulary for axis F-CL-FORMAL-3 (Π^p_2 verifier
-- termination). Upgraded 2026-05-12 (cycle-30) from the constant-zero
-- placeholder: `verifierSteps` is now a real polynomial bound in
-- catalogue size, query depth, and query payload, so the termination
-- theorem's witness `n` is no longer trivially zero.
--
-- raw_91 honest C3: still a v1 model. The real Π^p_2 verifier decision
-- procedure has worst-case complexity exponential in the alternation
-- depth (Π^p_2 is the second level of the polynomial hierarchy). The
-- polynomial-bound encoding here corresponds to the *amortised* /
-- bounded-instance behaviour observed on the 12-strand catalogue
-- (see `weave_pi_p2_verifier_v3_exhaustive.py` on the consumer side),
-- not the unrestricted Π^p_2 worst case. Cycle 30++ may swap this for
-- an explicit exponential-in-depth bound.

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
    representing the encoded predicate. Real queries also fix the
    catalogue indices they range over; this is captured by the type-level
    parameter `_c`. -/
structure Pi_p_2_Query (_c : StrandCatalogue) where
  depth   : Nat
  payload : Nat
  deriving Repr

/-- Step count of the verifier on a query. Polynomial bound:
    `size * (depth + 1) + payload`. The `+1` ensures depth-0 queries
    still incur the catalogue-scan cost. This is the bounded-instance
    encoding; the unrestricted Π^p_2 bound is exponential in `depth`. -/
def verifierSteps {c : StrandCatalogue} (q : Pi_p_2_Query c) : Nat :=
  c.size * (q.depth + 1) + q.payload

end Weave
end N6
