module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace Formalism.FourierDecayAlt.E

open Real Polynomial MeasureTheory

def CauchyTheta : Prop :=
  ∀ (σ ε : ℝ), 4 ≤ σ → 0 < ε → ∀ (p : ℕ) (u : ℝ),
    |iteratedDeriv p (fun v : ℝ => (1 + ε * Real.exp (-v)) ^ (-σ)) u| ≤
      Real.exp 1 * p.factorial * (4 * σ) ^ p * (1 + ε * Real.exp (-u)) ^ (-σ)

def AMarkov : Prop :=
  ∀ (p : ℝ[X]) (d : ℕ) (M : ℝ), p.natDegree ≤ d → (∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M) →
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.derivative.eval x| ≤ (d : ℝ) ^ 2 * M

def MarkovVector : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] (d : ℕ) (a : Fin (d + 1) → H)
    (t₀ L M : ℝ), 0 < L →
    (∀ t ∈ Set.Icc t₀ (t₀ + L), ‖∑ k : Fin (d + 1), t ^ (k : ℕ) • a k‖ ≤ M) →
    ∀ (q : ℕ), ∀ t ∈ Set.Icc t₀ (t₀ + L),
      ‖iteratedDeriv q (fun s : ℝ => ∑ k : Fin (d + 1), s ^ (k : ℕ) • a k) t‖ ≤ (2 * (d : ℝ) ^ 2 / L) ^ q * M

def Bdd {Λ : Type} (f : Λ → ℂ) : Prop := ∃ B : ℝ, ∀ x, ‖f x‖ ≤ B

def HerglotzLSC : Prop :=
  ∀ (d : ℕ) (N : (Fin d → ℝ) → ℝ) (A : (Fin d → ℤ) → ℂ),
    (∀ z, 0 ≤ N z) → LowerSemicontinuous N → Integrable N →
    (∀ (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ),
        0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, A (σ - σ') * c σ * starRingEnd ℂ (c σ')).re) →
    Summable (fun σ : Fin d → ℤ =>
      ‖(∫ z, (N z : ℂ) * Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (z j : ℂ))) + A σ‖) →
    ∀ (z₀ : Fin d → ℝ) (S : Finset (Fin d → ℤ)),
      ∑ m ∈ S, N (fun j => z₀ j + (m j : ℝ)) ≤
        ∑' σ : Fin d → ℤ,
          ‖(∫ z, (N z : ℂ) * Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (z j : ℂ))) + A σ‖

end Formalism.FourierDecayAlt.E
