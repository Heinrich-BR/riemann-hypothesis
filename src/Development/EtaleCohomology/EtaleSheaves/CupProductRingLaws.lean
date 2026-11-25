module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.CupProductRingLaws

def LeafTwPairExists : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ),
  ∃ μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j))), IsTwPair μ

end LateralTheory.E.CupProductRingLaws
