/-!
# Whitelist of Mathlib-internal choice sites (for human review)

`#check_explicit` fails on every choice operator occurring in the non-proof dependency closure
of a construction, except:
* `SymplecticPacking.Explicit.the` (definite description, needs a proof of `∃!`);
* decidability instances `Classical.propDecidable`, `Classical.dec*` (an `if` on a Prop has a
  definite value);
* occurrences *inside the Mathlib definitions listed below*, each of which denotes a definite
  object (or one whose value does not depend on the choice made).

Occurrences in project code (`SymplecticPacking.*`) or in the vendored OAI library are never
whitelisted. Each entry: (Mathlib declaration containing the choice, reason,
status). Status `source` = justified by reading the Mathlib source at the pinned commit
(v4.34.1, d13f23b7); `standard` = justified by a standard mathematical fact about the
construction, without a source reading. The entries are the choice sites in the closure of
`packingHamiltonian`.
-/

namespace SymplecticPacking.Explicit

/-- `(declaration name or generated module-local prefix, reason, status)`. -/
def mathlibWhitelist : List (String × String × String) :=
  [("CauSeq.lim", "limit of a Cauchy sequence; limits are unique", "source"),
   ("Real.instSupSet", "supremum of a bounded nonempty set of reals; unique", "standard"),
   ("Real.pi", "π = 2·(the unique zero of cos in [1,2])", "standard"),
   ("NNReal.instConditionallyCompleteLinearOrderBot",
     "order/lattice structure on ℝ≥0 (sSup, sInf are unique)", "standard"),
   ("Nonneg.conditionallyCompleteLinearOrder", "same, for nonnegative subtypes", "standard"),
   ("WellFounded.min", "minimum of a nonempty set for a well-founded linear order (ℕ); unique",
     "standard"),
   ("Equiv.ofInjective", "inverse of an injective map on its range; unique", "source"),
   ("Equiv.ofBijective", "inverse of a bijection; unique", "standard"),
   ("ContinuousLinearMap.inverse",
     "unique continuous two-sided inverse when invertible, zero otherwise; \
      Mathlib Topology/Algebra/Module/ContinuousLinearMap/Invertible.lean \
      inverse_equiv and inverse_of_not_isInvertible", "source"),
   ("Function.extend",
     "extension along a map; used in Mathlib's construction of the Bochner integral by \
      density, where the extended function factors through the map, so the value is \
      independent of the preimage chosen", "standard"),
   ("Quot.out", "representative of a quotient class; used only inside quotient lifts whose \
      value does not depend on the representative", "standard"),
   ("MeasureTheory.AEEqFun.cast", "representative of an a.e.-class; integrals are independent \
      of the representative", "standard"),
   ("MeasureTheory.AEStronglyMeasurable.mk", "strongly measurable representative; integrals are \
      independent of it", "standard"),
   ("MeasureTheory.Lp.simpleFunc.toSimpleFunc", "representative of a simple L¹ class; the \
      integral is independent of it", "standard"),
   ("MeasureTheory.Measure.haar.addCHaar", "Haar measure normalisation; the volume on \
      Euclidean space is the one normalised by the unit cube (orthonormal basis), independent \
      of the choices", "standard"),
   ("definition._@.Mathlib.Analysis.InnerProductSpace.PiL2.",
     "`stdOrthonormalBasis`; it only enters through the volume on EuclideanSpace, which is the \
      same for every orthonormal basis", "standard"),
   ("Set.Finite.fintype", "a Fintype instance on a finite set; finite sums/products do not \
      depend on it", "standard"),
   ("Filter.lim", "limit along a filter in a Hausdorff space; unique when it exists", "standard"),
   ("definition._@.Mathlib.Topology.Algebra.InfiniteSum.Defs.",
     "`tsum`: the sum of a summable family in a Hausdorff group; unique", "standard"),
   ("definition._@.Mathlib.Analysis.Calculus.FDeriv.Defs.",
     "`fderivWithin`: a derivative; project code only uses `fderiv`/`deriv` (within `univ`), \
      where the derivative is unique (checked by `scripts/check_explicit.sh`)", "source"),
   ("MeasureTheory.definition._@.Mathlib.MeasureTheory.Integral.Bochner.Basic.",
     "Bochner integral (decidability of integrability only)", "standard"),
   ("MeasureTheory.eLpNorm", "decidability only", "standard"),
   ("LinearEquiv.ofInjective", "inverse of an injective linear map on its range; unique \
      (reached through the matrix of a linear map, `Matrix.toEuclideanCLM.symm`)", "standard"),
   ("IsUnit.unit", "the unit witnessing `IsUnit a`; unique since inverses in a monoid are \
      unique (reached through the matrix inverse `a⁻¹` of the explicit `Sp(4)` path)", "standard"),
   ("FloorRing.ofBounded", "the floor function of an Archimedean ordered field (here ℝ); the \
      greatest integer ≤ x is unique (reached through `Int.fract` in the periodic extensions \
      of §2's base data)", "standard")]

end SymplecticPacking.Explicit
