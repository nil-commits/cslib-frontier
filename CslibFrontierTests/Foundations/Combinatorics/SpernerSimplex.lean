/-
Copyright (c) 2026 Nick L. Leppelmeier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick L. Leppelmeier
-/

module

public import CslibFrontier.Foundations.Combinatorics.Sperner.Simplex
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Classical `d`-simplex Sperner lemma: checked instances and boundary sharpness

Exercises `Cslib.Sperner.Simplex.odd_card_isRainbow` and `Cslib.Sperner.Simplex.exists_isRainbow`
on concrete barycentric subdivisions in dimensions `0` to `2`, checks simplex invariants
(`vertex_sum`, `vertex_diff_le_one`), and verifies a boundary counterexample showing why
`IsSpernerColoring` cannot be dropped.
-/

public section

namespace CslibFrontierTests.Foundations.Combinatorics.SpernerSimplex

open Cslib.Sperner.Simplex

/-- Dimension `1`, `N = 2` Sperner coloring: left vertex `[0, 2]` gets `1`, interior `[1, 1]` gets
`0`, right vertex `[2, 0]` gets `0`. -/
@[expose] def c1 (v : Fin 2 → ℕ) : Fin 2 :=
  if v 0 = 0 then 1 else 0

theorem c1_isSperner : IsSpernerColoring 1 2 c1 := by
  intro v hsum
  have hv : v 0 + v 1 = 2 := by
    change ∑ i : Fin 2, v i = 2 at hsum
    rwa [Fin.sum_univ_two] at hsum
  have hv0 : v 0 ≤ 2 := by omega
  interval_cases h0 : v 0 <;> simp [c1, h0]
  omega

example :
    open Classical in
    Odd ((allKuhnSimplices 1 2).filter (KuhnSimplex.IsRainbow c1)).card :=
  odd_card_isRainbow 1 (by norm_num) c1 c1_isSperner

example : ∃ σ : KuhnSimplex 1 2, σ.IsRainbow c1 :=
  exists_isRainbow 1 (by norm_num) c1 c1_isSperner

/-- Dimension `2`, `N = 2` classical Sperner coloring: chooses the least coordinate index `i` with
`v i ≠ 0` (when `∑ i, v i = 2`), so every vertex receives a nonzero coordinate. -/
@[expose] def c2 (v : Fin 3 → ℕ) : Fin 3 :=
  if v 0 ≠ 0 then 0 else if v 1 ≠ 0 then 1 else 2

theorem c2_isSperner : IsSpernerColoring 2 2 c2 := by
  intro v hsum
  have hv : v 0 + v 1 + v 2 = 2 := by
    change ∑ i : Fin 3, v i = 2 at hsum
    rw [Fin.sum_univ_three] at hsum
    omega
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · have h2 : v 2 ≠ 0 := by omega
      simp [c2, h0, h1, h2]
    · simp [c2, h0, h1]
  · simp [c2, h0]

example :
    open Classical in
    Odd ((allKuhnSimplices 2 2).filter (KuhnSimplex.IsRainbow c2)).card :=
  odd_card_isRainbow 2 (by norm_num) c2 c2_isSperner

example : ∃ σ : KuhnSimplex 2 2, σ.IsRainbow c2 :=
  exists_isRainbow 2 (by norm_num) c2 c2_isSperner

/-- Non-Sperner boundary coloring fails `IsSpernerColoring` (`v = ![0, 2]` colored `0` where
`v 0 = 0`), and indeed admits zero rainbow `1`-simplices. -/
@[expose] def cBad (_v : Fin 2 → ℕ) : Fin 2 := 0

example : ¬ IsSpernerColoring 1 2 cBad := by
  intro h
  have := h ![0, 2] (by simp)
  simp [cBad] at this

example :
    open Classical in
    ((allKuhnSimplices 1 2).filter (KuhnSimplex.IsRainbow cBad)).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro σ _ hrb
  obtain ⟨k, hk⟩ := hrb.2 1
  simp [cBad] at hk

/-- Every vertex of every simplex in `allKuhnSimplices 2 2` has barycentric sum `2`, and adjacent
vertices differ by at most `1` per coordinate. -/
example (σ : KuhnSimplex 2 2) (k₁ k₂ i : Fin 3) :
    ∑ j, σ.vertex k₁ j = 2 ∧ |((σ.vertex k₁ i : ℤ) - (σ.vertex k₂ i : ℤ))| ≤ 1 :=
  ⟨σ.vertex_sum k₁, σ.vertex_diff_le_one k₁ k₂ i⟩

end CslibFrontierTests.Foundations.Combinatorics.SpernerSimplex
