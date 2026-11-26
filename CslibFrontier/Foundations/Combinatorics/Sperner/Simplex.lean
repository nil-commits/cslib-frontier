/-
Copyright (c) 2026 Nick L. Leppelmeier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick L. Leppelmeier
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.Linarith

/-!
# Sperner's lemma on the Kuhn-triangulated standard simplex

This file proves the classical `d`-dimensional Sperner lemma in its parity form [Sperner1928] on
the Freudenthal / Kuhn triangulation of the `N`-subdivided standard `d`-simplex `Δ_d(N)`,
represented in cumulative order-simplex coordinates `0 ≤ y 0 ≤ y 1 ≤ ... ≤ y (d - 1) ≤ N`
converted to barycentric lattice coordinates `Fin (d + 1) → ℕ` summing to `N`.

For the Kuhn triangulation of the hypergrid `∏ i, [0, N i]`, see
`CslibFrontier/Foundations/Combinatorics/Sperner/Kuhn.lean`. Note that `IsSpernerColoring` here
enforces the classical simplex boundary condition (`∑ i, v i = N → v (c v) ≠ 0`, i.e., `v i = 0`
forbids colour `i`), whereas `Cslib.Sperner.IsHypergridSperner` enforces the cube boundary
condition.

## Main definitions

* `Cslib.Sperner.Simplex.KuhnSimplex`: Kuhn `d`-simplices in cumulative order-simplex coordinates.
* `Cslib.Sperner.Simplex.allKuhnSimplices`: finite set of all Kuhn `d`-simplices in `Δ_d(N)`.
* `Cslib.Sperner.Simplex.cumToBary`, `Cslib.Sperner.Simplex.KuhnSimplex.vertex`: barycentric
  lattice coordinates summing to `N`.
* `Cslib.Sperner.Simplex.IsSpernerColoring`: classical simplex Sperner boundary condition.
* `Cslib.Sperner.Simplex.KuhnSimplex.IsRainbow`: panchromaticity (`Function.Bijective` coloring
  on the `d + 1` vertices).

## Main results

* `Cslib.Sperner.Simplex.odd_card_isRainbow`: **Sperner's lemma**, parity form (`Odd` count of
  rainbow simplices for every `d : ℕ` and `N ≥ 1`).
* `Cslib.Sperner.Simplex.exists_isRainbow`: **Sperner's lemma**, existence of a rainbow simplex.

## References

* [Sperner1928]
-/

public section

namespace Cslib.Sperner.Simplex

open Finset
open scoped BigOperators

/-! ### Finite parity involution principle -/

section ParityInvolution

private lemma even_card_of_involution {α : Type*} {S : Finset α}
    (ι : α → α) (hmaps : ∀ x ∈ S, ι x ∈ S) (hinv : ∀ x ∈ S, ι (ι x) = x)
    (hfp : ∀ x ∈ S, ι x ≠ x) :
    Even S.card := by
  classical
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | ind n ih =>
    rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · rw [Finset.card_empty] at hn
      rw [← hn]
      exact ⟨0, rfl⟩
    · let b := ι a
      have hb : b ∈ S := hmaps a ha
      have hab : b ≠ a := hfp a ha
      let S' := (S.erase a).erase b
      have hb_in : b ∈ S.erase a := Finset.mem_erase.mpr ⟨hab, hb⟩
      have hcard' : S'.card + 2 = S.card := by
        have h1 := Finset.card_erase_add_one hb_in
        have h2 := Finset.card_erase_add_one ha
        dsimp only [S']
        omega
      have hmaps' : ∀ x ∈ S', ι x ∈ S' := by
        intro x hx
        have hxb : x ≠ b := (Finset.mem_erase.mp hx).1
        have hxa : x ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
        have hxS : x ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hmaps x hxS⟩⟩
        · intro hEq
          exact hxa (by rw [← hinv x hxS, hEq, hinv a ha])
        · intro hEq
          exact hxb (by rw [← hinv x hxS, hEq])
      have hinv' : ∀ x ∈ S', ι (ι x) = x := fun x hx =>
        hinv x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
      have hfp' : ∀ x ∈ S', ι x ≠ x := fun x hx =>
        hfp x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
      have heven' : Even S'.card := ih S'.card (by omega) hmaps' hinv' hfp' rfl
      rcases heven' with ⟨k, hk⟩
      exact ⟨k + 1, by omega⟩

private lemma sum_mod_two_eq {α : Type*} {S : Finset α} {f g : α → ℕ}
    (h : ∀ x ∈ S, f x % 2 = g x % 2) :
    (∑ x ∈ S, f x) % 2 = (∑ x ∈ S, g x) % 2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
    omega

end ParityInvolution

/-! ### Kuhn simplices in cumulative and barycentric coordinates -/

section Simplices

/-- A `d`-simplex in the Kuhn / Freudenthal triangulation of the `N`-subdivided
standard `d`-simplex `Δ_d(N)`, represented in cumulative order-simplex coordinates
`0 ≤ y 0 ≤ y 1 ≤ ... ≤ y (d - 1) ≤ N`:
- `base : Fin d → ℕ` is monotone with `∀ j, base j < N`;
- `perm : Equiv.Perm (Fin d)` records the coordinate-increment order, with tie-breaking
  `base j = base (j + 1) → perm.symm (j + 1) < perm.symm j` so that every intermediate
  vertex stays monotone. -/
structure KuhnSimplex (d N : ℕ) where
  /-- Cumulative lower-corner coordinates `0 ≤ base 0 ≤ ... ≤ base (d - 1) < N`. -/
  base : Fin d → ℕ
  /-- Coordinate-increment order permutation. -/
  perm : Equiv.Perm (Fin d)
  /-- Monotonicity of cumulative base coordinates. -/
  mono : Monotone base
  /-- Strict upper bound on cumulative base coordinates. -/
  lt_N : ∀ j : Fin d, base j < N
  /-- Tie-breaking rule ensuring all simplex vertices remain monotone. -/
  tie : ∀ (j : ℕ) (hj : j + 1 < d),
    base ⟨j, Nat.lt_of_succ_lt hj⟩ = base ⟨j + 1, hj⟩ →
    perm.symm ⟨j + 1, hj⟩ < perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩

instance {d N : ℕ} : DecidableEq (KuhnSimplex d N) := fun s t =>
  if h : s.base = t.base ∧ s.perm = t.perm then
    isTrue (by cases s; cases t; simp only at h; rcases h with ⟨rfl, rfl⟩; rfl)
  else
    isFalse (by rintro rfl; exact h ⟨rfl, rfl⟩)

@[ext]
theorem KuhnSimplex.ext {d N : ℕ} {s t : KuhnSimplex d N}
    (hb : s.base = t.base) (hp : s.perm = t.perm) : s = t := by
  cases s; cases t; cases hb; cases hp; rfl

/-- The `Finset` of all Kuhn `d`-simplices in `Δ_d(N)`. -/
noncomputable def allKuhnSimplices (d N : ℕ) : Finset (KuhnSimplex d N) := by
  classical
  let raw := (Finset.univ : Finset ((Fin d → Fin N) × Equiv.Perm (Fin d)))
  let valid := raw.filter fun p =>
    (∀ a b : Fin d, a ≤ b → (p.1 a).val ≤ (p.1 b).val) ∧
    ∀ (j : ℕ) (hj : j + 1 < d),
      (p.1 ⟨j, Nat.lt_of_succ_lt hj⟩).val = (p.1 ⟨j + 1, hj⟩).val →
      p.2.symm ⟨j + 1, hj⟩ < p.2.symm ⟨j, Nat.lt_of_succ_lt hj⟩
  exact valid.attach.image fun ⟨p, hp⟩ =>
    let h := (Finset.mem_filter.mp hp).2
    ⟨fun j => (p.1 j).val, p.2, fun _ _ hab => h.1 _ _ hab, fun j => (p.1 j).isLt, h.2⟩

theorem mem_allKuhnSimplices {d N : ℕ} (σ : KuhnSimplex d N) :
    σ ∈ allKuhnSimplices d N := by
  classical
  unfold allKuhnSimplices
  refine Finset.mem_image.mpr ?_
  let p : (Fin d → Fin N) × Equiv.Perm (Fin d) := (fun j => ⟨σ.base j, σ.lt_N j⟩, σ.perm)
  have hp : p ∈ (Finset.univ.filter fun q : (Fin d → Fin N) × Equiv.Perm (Fin d) =>
      (∀ a b : Fin d, a ≤ b → (q.1 a).val ≤ (q.1 b).val) ∧
      ∀ (j : ℕ) (hj : j + 1 < d),
        (q.1 ⟨j, Nat.lt_of_succ_lt hj⟩).val = (q.1 ⟨j + 1, hj⟩).val →
        q.2.symm ⟨j + 1, hj⟩ < q.2.symm ⟨j, Nat.lt_of_succ_lt hj⟩) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ _ hab => σ.mono hab, σ.tie⟩
  exact ⟨⟨p, hp⟩, Finset.mem_attach _ _, KuhnSimplex.ext rfl rfl⟩

/-- The `k`-th vertex (`k : Fin (d + 1)`) of `σ : KuhnSimplex d N` in cumulative
order-simplex coordinates `Fin d → ℕ`: `y j = base j + 1` if `perm.symm j < k`, else `base j`. -/
def KuhnSimplex.cumVertex {d N : ℕ} (σ : KuhnSimplex d N) (k : Fin (d + 1)) (j : Fin d) : ℕ :=
  σ.base j + if (σ.perm.symm j).val < k.val then 1 else 0

theorem KuhnSimplex.cumVertex_mono {d N : ℕ} (σ : KuhnSimplex d N) (k : Fin (d + 1)) :
    Monotone (σ.cumVertex k) := by
  intro j₁ j₂ hle
  suffices ∀ (m : ℕ) (hm : m + 1 < d),
      σ.cumVertex k ⟨m, Nat.lt_of_succ_lt hm⟩ ≤ σ.cumVertex k ⟨m + 1, hm⟩ by
    have hstep : ∀ (a b : ℕ) (ha : a < d) (hb : b < d), a ≤ b →
        σ.cumVertex k ⟨a, ha⟩ ≤ σ.cumVertex k ⟨b, hb⟩ := by
      intro a b ha hb hab
      induction b with
      | zero =>
        have : a = 0 := Nat.eq_zero_of_le_zero hab
        subst this
        exact le_rfl
      | succ m ih =>
        rcases eq_or_lt_of_le hab with rfl | hlt
        · exact le_rfl
        · exact le_trans (ih (Nat.lt_of_succ_lt hb) (Nat.le_of_lt_succ hlt)) (this m hb)
    exact hstep j₁.val j₂.val j₁.isLt j₂.isLt hle
  intro m hm
  unfold KuhnSimplex.cumVertex
  have hble : σ.base ⟨m, Nat.lt_of_succ_lt hm⟩ ≤ σ.base ⟨m + 1, hm⟩ :=
    σ.mono (show (⟨m, Nat.lt_of_succ_lt hm⟩ : Fin d) ≤ ⟨m + 1, hm⟩ by
      change m ≤ m + 1; omega)
  rcases eq_or_lt_of_le hble with hEq | hlt
  · have htie := σ.tie m hm hEq
    rw [hEq]
    by_cases h1 : (σ.perm.symm ⟨m, Nat.lt_of_succ_lt hm⟩).val < k.val
    · have h2 : (σ.perm.symm ⟨m + 1, hm⟩).val < k.val := lt_trans htie h1
      simp [h1, h2]
    · simp only [h1, ↓reduceIte, add_zero]
      exact Nat.le_add_right _ _
  · split_ifs <;> omega

theorem KuhnSimplex.cumVertex_le_N {d N : ℕ} (σ : KuhnSimplex d N) (k : Fin (d + 1)) (j : Fin d) :
    σ.cumVertex k j ≤ N := by
  unfold KuhnSimplex.cumVertex
  have := σ.lt_N j
  split_ifs <;> omega

/-- Convert cumulative coordinates `y : Fin d → ℕ` (`0 ≤ y 0 ≤ ... ≤ y (d - 1) ≤ N`) to
barycentric lattice coordinates `v : Fin (d + 1) → ℕ` summing to `N`:
`v 0 = y 0`, `v (j + 1) = y (j + 1) - y j`, `v d = N - y (d - 1)` (and `v 0 = N` when `d = 0`). -/
def cumToBary {d : ℕ} (N : ℕ) (y : Fin d → ℕ) (i : Fin (d + 1)) : ℕ :=
  if h0 : i.val = 0 then
    if hd : 0 < d then y ⟨0, hd⟩ else N
  else if hlt : i.val < d then
    y ⟨i.val, hlt⟩ - y ⟨i.val - 1, by omega⟩
  else
    N - y ⟨d - 1, by omega⟩

theorem sum_cumToBary {d N : ℕ} {y : Fin d → ℕ}
    (hmono : Monotone y) (hle : ∀ j, y j ≤ N) :
    ∑ i : Fin (d + 1), cumToBary N y i = N := by
  cases d with
  | zero => simp [cumToBary]
  | succ m =>
    have hprefix : ∀ (r : ℕ) (hr : r ≤ m),
        ∑ i ∈ Finset.univ.filter (fun i : Fin (m + 2) => i.val ≤ r),
          cumToBary N y i = y ⟨r, by omega⟩ := by
      intro r hr
      induction r with
      | zero =>
        have hfilt : Finset.univ.filter (fun i : Fin (m + 2) => i.val ≤ 0) =
            {(0 : Fin (m + 2))} := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          rw [Fin.ext_iff]
          exact Nat.le_zero
        rw [hfilt, Finset.sum_singleton]
        simp [cumToBary]
      | succ k ih =>
        have hsplit : Finset.univ.filter (fun i : Fin (m + 2) => i.val ≤ k + 1) =
            insert ⟨k + 1, by omega⟩
              (Finset.univ.filter (fun i : Fin (m + 2) => i.val ≤ k)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
          omega
        have hnotmem : (⟨k + 1, by omega⟩ : Fin (m + 2)) ∉
            Finset.univ.filter (fun i : Fin (m + 2) => i.val ≤ k) := by
          simp
        rw [hsplit, Finset.sum_insert hnotmem, ih (by omega)]
        have hval : cumToBary N y ⟨k + 1, by omega⟩ =
            y ⟨k + 1, by omega⟩ - y ⟨k, by omega⟩ := by
          unfold cumToBary
          have h2 : k + 1 < m + 1 := by omega
          simp [h2]
        rw [hval]
        have hle_k : y ⟨k, by omega⟩ ≤ y ⟨k + 1, by omega⟩ :=
          hmono (show (⟨k, by omega⟩ : Fin (m + 1)) ≤ ⟨k + 1, by omega⟩ by
            change k ≤ k + 1; omega)
        omega
    have huniv : (Finset.univ : Finset (Fin (m + 2))) =
        insert ⟨m + 1, by omega⟩ (Finset.univ.filter (fun i : Fin (m + 2) => i.val ≤ m)) := by
      ext i
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_filter, true_and,
        Fin.ext_iff, true_iff]
      have := i.isLt
      omega
    have hnotmem : (⟨m + 1, by omega⟩ : Fin (m + 2)) ∉
        Finset.univ.filter (fun i : Fin (m + 2) => i.val ≤ m) := by simp
    rw [huniv, Finset.sum_insert hnotmem, hprefix m le_rfl]
    have hlast : cumToBary N y ⟨m + 1, by omega⟩ = N - y ⟨m, by omega⟩ := by
      unfold cumToBary
      simp
    rw [hlast]
    have hle_m := hle ⟨m, by omega⟩
    omega

/-- The `k`-th vertex of `σ : KuhnSimplex d N` in barycentric lattice coordinates
`Fin (d + 1) → ℕ` summing to `N`. -/
def KuhnSimplex.vertex {d N : ℕ} (σ : KuhnSimplex d N) (k : Fin (d + 1)) : Fin (d + 1) → ℕ :=
  cumToBary N (σ.cumVertex k)

theorem KuhnSimplex.vertex_sum {d N : ℕ} (σ : KuhnSimplex d N) (k : Fin (d + 1)) :
    ∑ i : Fin (d + 1), σ.vertex k i = N :=
  sum_cumToBary (σ.cumVertex_mono k) (σ.cumVertex_le_N k)

/-- Any two vertices of the same Kuhn simplex differ by at most `1` in every barycentric
coordinate. -/
theorem KuhnSimplex.vertex_diff_le_one {d N : ℕ} (σ : KuhnSimplex d N)
    (k₁ k₂ : Fin (d + 1)) (i : Fin (d + 1)) :
    |((σ.vertex k₁ i : ℤ) - (σ.vertex k₂ i : ℤ))| ≤ 1 := by
  have hcum : ∀ j : Fin d, σ.base j ≤ σ.cumVertex k₁ j ∧ σ.cumVertex k₁ j ≤ σ.base j + 1 ∧
      σ.base j ≤ σ.cumVertex k₂ j ∧ σ.cumVertex k₂ j ≤ σ.base j + 1 := by
    intro j
    unfold KuhnSimplex.cumVertex
    split_ifs <;> omega
  unfold KuhnSimplex.vertex cumToBary
  split_ifs with h0 hd hlt
  · have h1 := hcum ⟨0, hd⟩
    rw [abs_le]
    omega
  · simp
  · have hj1 := hcum ⟨i.val, hlt⟩
    have hj0 := hcum ⟨i.val - 1, by omega⟩
    have hle1 : σ.cumVertex k₁ ⟨i.val - 1, by omega⟩ ≤ σ.cumVertex k₁ ⟨i.val, hlt⟩ :=
      σ.cumVertex_mono k₁ (show (⟨i.val - 1, by omega⟩ : Fin d) ≤ ⟨i.val, hlt⟩ by
        change i.val - 1 ≤ i.val; omega)
    have hle2 : σ.cumVertex k₂ ⟨i.val - 1, by omega⟩ ≤ σ.cumVertex k₂ ⟨i.val, hlt⟩ :=
      σ.cumVertex_mono k₂ (show (⟨i.val - 1, by omega⟩ : Fin d) ≤ ⟨i.val, hlt⟩ by
        change i.val - 1 ≤ i.val; omega)
    have hno_opp : ¬ (σ.cumVertex k₁ ⟨i.val, hlt⟩ = σ.base ⟨i.val, hlt⟩ + 1 ∧
        σ.cumVertex k₁ ⟨i.val - 1, by omega⟩ = σ.base ⟨i.val - 1, by omega⟩ ∧
        σ.cumVertex k₂ ⟨i.val, hlt⟩ = σ.base ⟨i.val, hlt⟩ ∧
        σ.cumVertex k₂ ⟨i.val - 1, by omega⟩ = σ.base ⟨i.val - 1, by omega⟩ + 1) := by
      unfold KuhnSimplex.cumVertex
      rintro ⟨h1, h2, h3, h4⟩
      have ha : (σ.perm.symm ⟨i.val, hlt⟩).val < k₁.val := by by_contra hc; simp [hc] at h1
      have hb : ¬ (σ.perm.symm ⟨i.val - 1, by omega⟩).val < k₁.val := by
        by_contra hc; simp [hc] at h2
      have hc' : ¬ (σ.perm.symm ⟨i.val, hlt⟩).val < k₂.val := by by_contra hc2; simp [hc2] at h3
      have hd' : (σ.perm.symm ⟨i.val - 1, by omega⟩).val < k₂.val := by
        by_contra hc2; simp [hc2] at h4
      omega
    have hno_opp' : ¬ (σ.cumVertex k₂ ⟨i.val, hlt⟩ = σ.base ⟨i.val, hlt⟩ + 1 ∧
        σ.cumVertex k₂ ⟨i.val - 1, by omega⟩ = σ.base ⟨i.val - 1, by omega⟩ ∧
        σ.cumVertex k₁ ⟨i.val, hlt⟩ = σ.base ⟨i.val, hlt⟩ ∧
        σ.cumVertex k₁ ⟨i.val - 1, by omega⟩ = σ.base ⟨i.val - 1, by omega⟩ + 1) := by
      unfold KuhnSimplex.cumVertex
      rintro ⟨h1, h2, h3, h4⟩
      have ha : (σ.perm.symm ⟨i.val, hlt⟩).val < k₂.val := by by_contra hc; simp [hc] at h1
      have hb : ¬ (σ.perm.symm ⟨i.val - 1, by omega⟩).val < k₂.val := by
        by_contra hc; simp [hc] at h2
      have hc' : ¬ (σ.perm.symm ⟨i.val, hlt⟩).val < k₁.val := by by_contra hc2; simp [hc2] at h3
      have hd' : (σ.perm.symm ⟨i.val - 1, by omega⟩).val < k₁.val := by
        by_contra hc2; simp [hc2] at h4
      omega
    have hnat1 : σ.cumVertex k₁ ⟨i.val, hlt⟩ - σ.cumVertex k₁ ⟨i.val - 1, by omega⟩ ≤
        (σ.cumVertex k₂ ⟨i.val, hlt⟩ - σ.cumVertex k₂ ⟨i.val - 1, by omega⟩) + 1 := by omega
    have hnat2 : σ.cumVertex k₂ ⟨i.val, hlt⟩ - σ.cumVertex k₂ ⟨i.val - 1, by omega⟩ ≤
        (σ.cumVertex k₁ ⟨i.val, hlt⟩ - σ.cumVertex k₁ ⟨i.val - 1, by omega⟩) + 1 := by omega
    rw [abs_le]
    omega
  · have hd_pos : 0 < d := by have := i.isLt; omega
    have h1 := hcum ⟨d - 1, by omega⟩
    have hle1 := σ.cumVertex_le_N k₁ ⟨d - 1, by omega⟩
    have hle2 := σ.cumVertex_le_N k₂ ⟨d - 1, by omega⟩
    have hnat1 : N - σ.cumVertex k₁ ⟨d - 1, by omega⟩ ≤
        (N - σ.cumVertex k₂ ⟨d - 1, by omega⟩) + 1 := by omega
    have hnat2 : N - σ.cumVertex k₂ ⟨d - 1, by omega⟩ ≤
        (N - σ.cumVertex k₁ ⟨d - 1, by omega⟩) + 1 := by omega
    rw [abs_le]
    omega

/-- A coloring `c : (Fin (d + 1) → ℕ) → Fin (d + 1)` satisfies the **classical Sperner boundary
condition** on `Δ_d(N)` if every vertex `v` with `∑ i, v i = N` receives a colour `c v` whose
barycentric coordinate `v (c v)` is nonzero (equivalently, `v i = 0 → c v ≠ i`). -/
@[expose] def IsSpernerColoring (d N : ℕ) (c : (Fin (d + 1) → ℕ) → Fin (d + 1)) : Prop :=
  ∀ v : Fin (d + 1) → ℕ, (∑ i, v i = N) → v (c v) ≠ 0

/-- A Kuhn simplex `σ` is **rainbow** (panchromatic) under `c` if its `d + 1` vertices
receive all `d + 1` distinct colours `Fin (d + 1)`. -/
@[expose] def KuhnSimplex.IsRainbow {d N : ℕ} (c : (Fin (d + 1) → ℕ) → Fin (d + 1))
    (σ : KuhnSimplex d N) : Prop :=
  Function.Bijective (fun k : Fin (d + 1) => c (σ.vertex k))

end Simplices

/-! ### Local facet parity and door-involution proof of Sperner's lemma -/

section ParityProof

private lemma local_sperner_facet_parity {d : ℕ} (f : Fin (d + 1) → Fin (d + 1)) :
    ((Finset.univ : Finset (Fin (d + 1))).filter (fun k =>
      ∀ r : Fin d, ∃ j : Fin (d + 1), j ≠ k ∧ f j = r.castSucc)).card % 2 =
    if Function.Bijective f then 1 else 0 := by
  let good := (Finset.univ : Finset (Fin (d + 1))).filter (fun k =>
    ∀ r : Fin d, ∃ j : Fin (d + 1), j ≠ k ∧ f j = r.castSucc)
  by_cases hbij : Function.Bijective f
  · simp only [hbij, ↓reduceIte]
    obtain ⟨k₀, hk₀⟩ := hbij.2 (Fin.last d)
    have hgood_eq : good = {k₀} := by
      ext k
      simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hk
        by_contra hne
        have hnotlt : ∀ r : Fin d, f k ≠ r.castSucc := by
          intro r hEq
          obtain ⟨j, hjk, hjr⟩ := hk r
          exact hjk (hbij.1 (hjr.trans hEq.symm))
        have hlast : f k = Fin.last d := by
          ext
          change (f k).val = d
          have hlt := (f k).isLt
          by_contra hne'
          exact hnotlt ⟨(f k).val, by omega⟩ (Fin.ext rfl)
        exact hne (hbij.1 (hlast.trans hk₀.symm))
      · rintro rfl r
        obtain ⟨j, hj⟩ := hbij.2 r.castSucc
        refine ⟨j, ?_, hj⟩
        rintro rfl
        have : r.castSucc = Fin.last d := hj.symm.trans hk₀
        have := congrArg Fin.val this
        simp at this
        omega
    change good.card % 2 = 1
    rw [hgood_eq, Finset.card_singleton]
  · simp only [hbij, ↓reduceIte]
    have hnsurj : ¬ Function.Surjective f := fun h =>
      hbij ⟨Finite.injective_iff_surjective.mpr h, h⟩
    by_cases hmiss : ∃ r : Fin d, ∀ j : Fin (d + 1), f j ≠ r.castSucc
    · obtain ⟨r₀, hr₀⟩ := hmiss
      have hgood_eq : good = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro k hk
        obtain ⟨j, _, hj⟩ := (Finset.mem_filter.mp hk).2 r₀
        exact hr₀ j hj
      change good.card % 2 = 0
      rw [hgood_eq]
      simp
    · push Not at hmiss
      have hno_last : ∀ j : Fin (d + 1), f j ≠ Fin.last d := by
        intro j hj
        apply hnsurj
        intro y
        by_cases hy : y.val < d
        · obtain ⟨x, hx⟩ := hmiss ⟨y.val, hy⟩
          exact ⟨x, hx.trans (Fin.ext rfl)⟩
        · have : y = Fin.last d := Fin.ext (by change y.val = d; have := y.isLt; omega)
          exact ⟨j, hj.trans this.symm⟩
      have hfib_sum : ∑ r : Fin d,
          (Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)).card = d + 1 := by
        have hpart : (Finset.univ : Finset (Fin (d + 1))) =
            Finset.univ.biUnion (fun r : Fin d =>
              Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)) := by
          ext j
          simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_filter, true_and, true_iff]
          have hlt : (f j).val < d := by
            have := (f j).isLt
            by_contra hc
            exact hno_last j (Fin.ext (by change (f j).val = d; omega))
          exact ⟨⟨(f j).val, hlt⟩, Fin.ext rfl⟩
        have hdisj : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin d)) : Set (Fin d))
            (fun r : Fin d => Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)) := by
          intro r₁ _ r₂ _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro j h1 h2
          have e1 := (Finset.mem_filter.mp h1).2
          have e2 := (Finset.mem_filter.mp h2).2
          exact hne (Fin.ext (by simpa using congrArg Fin.val (e1.symm.trans e2)))
        have hc := congrArg Finset.card hpart
        rw [Finset.card_univ, Fintype.card_fin, Finset.card_biUnion hdisj] at hc
        exact hc.symm
      have hfib_ge1 : ∀ r : Fin d,
          1 ≤ (Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)).card := by
        intro r
        obtain ⟨j, hj⟩ := hmiss r
        exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
      have hex_ge2 : ∃ r₀ : Fin d,
          2 ≤ (Finset.univ.filter (fun j : Fin (d + 1) => f j = r₀.castSucc)).card := by
        by_contra hall
        push Not at hall
        have hle : ∑ r : Fin d,
            (Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)).card ≤ d := by
          calc ∑ r : Fin d, (Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)).card
              ≤ ∑ _r : Fin d, 1 := Finset.sum_le_sum fun r _ => by have := hall r; omega
            _ = d := by simp
        omega
      obtain ⟨r₀, hr₀_ge2⟩ := hex_ge2
      have hr₀_eq2 : (Finset.univ.filter (fun j : Fin (d + 1) => f j = r₀.castSucc)).card = 2 ∧
          ∀ r : Fin d, r ≠ r₀ →
            (Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)).card = 1 := by
        have hsum_rest : ∑ r ∈ Finset.univ.erase r₀,
            (Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)).card ≥ d - 1 := by
          calc ∑ r ∈ Finset.univ.erase r₀,
                (Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)).card
              ≥ ∑ _r ∈ Finset.univ.erase r₀, 1 := Finset.sum_le_sum fun r _ => hfib_ge1 r
            _ = d - 1 := by simp
        have hsplit := Finset.add_sum_erase Finset.univ
          (fun r : Fin d => (Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)).card)
          (Finset.mem_univ r₀)
        have hd_pos : 1 ≤ d := Nat.pos_of_ne_zero (fun h => by subst h; exact Fin.elim0 r₀)
        have h2 : (Finset.univ.filter (fun j : Fin (d + 1) => f j = r₀.castSucc)).card = 2 := by
          omega
        refine ⟨h2, fun r hr => ?_⟩
        by_contra hne1
        have hge2' :
            2 ≤ (Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)).card := by
          have := hfib_ge1 r
          omega
        have hrest_ge : ∑ r' ∈ Finset.univ.erase r₀,
            (Finset.univ.filter (fun j : Fin (d + 1) => f j = r'.castSucc)).card ≥ d := by
          have hsp := Finset.add_sum_erase (Finset.univ.erase r₀)
            (fun r' : Fin d => (Finset.univ.filter (fun j : Fin (d + 1) => f j = r'.castSucc)).card)
            (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ _⟩)
          have hrem : ∑ r' ∈ (Finset.univ.erase r₀).erase r,
              (Finset.univ.filter (fun j : Fin (d + 1) => f j = r'.castSucc)).card ≥ d - 2 := by
            calc ∑ r' ∈ (Finset.univ.erase r₀).erase r,
                  (Finset.univ.filter (fun j : Fin (d + 1) => f j = r'.castSucc)).card
                ≥ ∑ _r' ∈ (Finset.univ.erase r₀).erase r, 1 :=
                  Finset.sum_le_sum fun r' _ => hfib_ge1 r'
              _ = ((Finset.univ.erase r₀).erase r).card := by simp
              _ = d - 2 := by
                rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ _⟩),
                  Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
                omega
          omega
        omega
      have hgood_eq :
          good = Finset.univ.filter (fun j : Fin (d + 1) => f j = r₀.castSucc) := by
        ext k
        simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hk
          by_contra hne
          have hlt : (f k).val < d := by
            have := (f k).isLt
            by_contra hc
            exact hno_last k (Fin.ext (by change (f k).val = d; omega))
          let rk : Fin d := ⟨(f k).val, hlt⟩
          have hrk_ne : rk ≠ r₀ := fun h => hne (by rw [← h]; exact Fin.ext rfl)
          obtain ⟨j, hjk, hj⟩ := hk rk
          have hfib1 := hr₀_eq2.2 rk hrk_ne
          have h2le : 2 ≤ (Finset.univ.filter (fun x : Fin (d + 1) => f x = rk.castSucc)).card := by
            have hsub : ({k, j} : Finset (Fin (d + 1))) ⊆
                Finset.univ.filter (fun x : Fin (d + 1) => f x = rk.castSucc) := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl
              · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.ext rfl⟩
              · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
            have hc2 : ({k, j} : Finset (Fin (d + 1))).card = 2 := Finset.card_pair hjk.symm
            exact hc2 ▸ Finset.card_le_card hsub
          omega
        · intro hk r
          by_cases hr : r = r₀
          · subst hr
            obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega :
              1 < (Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)).card)
            by_cases hka : a = k
            · exact ⟨b, by rw [← hka]; exact hab.symm, (Finset.mem_filter.mp hb).2⟩
            · exact ⟨a, hka, (Finset.mem_filter.mp ha).2⟩
          · obtain ⟨j, hj⟩ := hmiss r
            refine ⟨j, ?_, hj⟩
            rintro rfl
            exact hr (Fin.ext (by simpa using congrArg Fin.val (hj.symm.trans hk)))
      change good.card % 2 = 0
      rw [hgood_eq, hr₀_eq2.1]

/-- Cyclic left shift on `Fin (d + 1)`: `0 → 1 → ... → d → 0`. -/
private def cycShift (d : ℕ) : Equiv.Perm (Fin (d + 1)) where
  toFun i := if h : i.val + 1 < d + 1 then ⟨i.val + 1, h⟩ else ⟨0, Nat.succ_pos d⟩
  invFun i := if h : 0 < i.val then ⟨i.val - 1, by omega⟩ else ⟨d, Nat.lt_succ_self d⟩
  left_inv i := by
    ext
    dsimp only
    by_cases h : i.val + 1 < d + 1
    · simp [h]
    · have hi : i.val = d := by have := i.isLt; omega
      simp [hi]
  right_inv i := by
    ext
    dsimp only
    by_cases h : 0 < i.val
    · have hlt : i.val - 1 + 1 < d + 1 := by have := i.isLt; omega
      simp [h, hlt]
      omega
    · have hi : i.val = 0 := by omega
      simp [hi]

private noncomputable def goodFacetPairs (m N : ℕ)
    (c : (Fin (m + 2) → ℕ) → Fin (m + 2)) : Finset (KuhnSimplex (m + 1) N × Fin (m + 2)) :=
  open Classical in
  ((allKuhnSimplices (m + 1) N) ×ˢ (Finset.univ : Finset (Fin (m + 2)))).filter fun p =>
    ∀ r : Fin (m + 1), ∃ j : Fin (m + 2), j ≠ p.2 ∧ c (p.1.vertex j) = r.castSucc

private lemma goodFacetPairs_mod_two (m N : ℕ)
    (c : (Fin (m + 2) → ℕ) → Fin (m + 2)) :
    (goodFacetPairs m N c).card % 2 =
      open Classical in
      ((allKuhnSimplices (m + 1) N).filter (KuhnSimplex.IsRainbow c)).card % 2 := by
  classical
  have hcard_eq : (goodFacetPairs m N c).card =
      ∑ σ ∈ allKuhnSimplices (m + 1) N,
        ((Finset.univ : Finset (Fin (m + 2))).filter (fun k =>
          ∀ r : Fin (m + 1), ∃ j : Fin (m + 2), j ≠ k ∧ c (σ.vertex j) = r.castSucc)).card := by
    unfold goodFacetPairs
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.card_filter]
  have hrb_eq : ((allKuhnSimplices (m + 1) N).filter (KuhnSimplex.IsRainbow c)).card =
      ∑ σ ∈ allKuhnSimplices (m + 1) N, if KuhnSimplex.IsRainbow c σ then 1 else 0 := by
    rw [Finset.card_filter]
  rw [hcard_eq, hrb_eq]
  refine sum_mod_two_eq fun σ _ => ?_
  have hloc := local_sperner_facet_parity (fun k => c (σ.vertex k))
  have hrb_iff : KuhnSimplex.IsRainbow c σ ↔ Function.Bijective (fun k => c (σ.vertex k)) :=
    Iff.rfl
  rw [hloc]
  by_cases hb : Function.Bijective (fun k => c (σ.vertex k))
  · simp only [hb, hrb_iff.mpr hb, ↓reduceIte]
  · simp only [hb, mt hrb_iff.mp hb, ↓reduceIte]

private lemma no_bdry_lt_of_good {m N : ℕ} {c : (Fin (m + 2) → ℕ) → Fin (m + 2)}
    (hc : IsSpernerColoring (m + 1) N c) {p : KuhnSimplex (m + 1) N × Fin (m + 2)}
    (hp : p ∈ goodFacetPairs m N c) :
    (p.2.val = 0 → p.1.base (p.1.perm 0) = N - 1 → p.1.perm 0 = Fin.last m) ∧
    (p.2.val = m + 1 → 0 < p.1.base (p.1.perm (Fin.last m))) ∧
    (∀ (h0 : 0 < p.2.val) (hD : p.2.val < m + 1),
      ∀ (j : ℕ) (hj : j + 1 < m + 1),
        p.1.perm ⟨p.2.val - 1, by omega⟩ = ⟨j + 1, hj⟩ →
        p.1.perm ⟨p.2.val, hD⟩ = ⟨j, Nat.lt_of_succ_lt hj⟩ →
        p.1.base ⟨j, Nat.lt_of_succ_lt hj⟩ ≠ p.1.base ⟨j + 1, hj⟩) := by
  rcases p with ⟨σ, k⟩
  dsimp only at *
  have hgood : ∀ r : Fin (m + 1), ∃ j : Fin (m + 2), j ≠ k ∧ c (σ.vertex j) = r.castSucc := by
    classical
    unfold goodFacetPairs at hp
    exact (Finset.mem_filter.mp hp).2
  refine ⟨?_, ?_, ?_⟩
  · intro _ hmax
    by_contra hne
    have hlt : (σ.perm 0).val < m := by
      have := (σ.perm 0).isLt
      have hvalne : (σ.perm 0).val ≠ m := fun h => hne (Fin.ext h)
      omega
    have hle1 : σ.base (σ.perm 0) ≤ σ.base ⟨(σ.perm 0).val + 1, by omega⟩ :=
      σ.mono (show σ.perm 0 ≤ ⟨(σ.perm 0).val + 1, by omega⟩ by
        change (σ.perm 0).val ≤ (σ.perm 0).val + 1; omega)
    have hltN := σ.lt_N ⟨(σ.perm 0).val + 1, by omega⟩
    have hEq : σ.base ⟨(σ.perm 0).val, by omega⟩ =
        σ.base ⟨(σ.perm 0).val + 1, by omega⟩ := by
      have : (⟨(σ.perm 0).val, by omega⟩ : Fin (m + 1)) = σ.perm 0 := Fin.ext rfl
      rw [this]
      omega
    have htie := σ.tie (σ.perm 0).val (by omega) hEq
    have h0eq : (⟨(σ.perm 0).val, by omega⟩ : Fin (m + 1)) = σ.perm 0 := Fin.ext rfl
    rw [h0eq, Equiv.symm_apply_apply] at htie
    exact Nat.not_lt_zero _ htie
  · intro hkD
    by_contra h0
    have hb0 : σ.base (σ.perm (Fin.last m)) = 0 := by omega
    have hlast0 : σ.perm (Fin.last m) = 0 := by
      by_contra hne
      have hpos : 0 < (σ.perm (Fin.last m)).val := by
        have hvalne : (σ.perm (Fin.last m)).val ≠ 0 := fun h => hne (Fin.ext h)
        omega
      have hle1 :
          σ.base ⟨(σ.perm (Fin.last m)).val - 1, by omega⟩ ≤ σ.base (σ.perm (Fin.last m)) :=
        σ.mono (show (⟨(σ.perm (Fin.last m)).val - 1, by omega⟩ : Fin (m + 1)) ≤
          σ.perm (Fin.last m) by
          change (σ.perm (Fin.last m)).val - 1 ≤ (σ.perm (Fin.last m)).val; omega)
      have hEq : σ.base ⟨(σ.perm (Fin.last m)).val - 1, by omega⟩ =
          σ.base ⟨(σ.perm (Fin.last m)).val - 1 + 1, by omega⟩ := by
        have : (⟨(σ.perm (Fin.last m)).val - 1 + 1, by omega⟩ : Fin (m + 1)) =
            σ.perm (Fin.last m) := Fin.ext (by dsimp only; omega)
        rw [this]
        omega
      have htie := σ.tie ((σ.perm (Fin.last m)).val - 1) (by omega) hEq
      have heq' : (⟨(σ.perm (Fin.last m)).val - 1 + 1, by omega⟩ : Fin (m + 1)) =
          σ.perm (Fin.last m) := Fin.ext (by dsimp only; omega)
      rw [heq', Equiv.symm_apply_apply] at htie
      have hlt' := (σ.perm.symm ⟨(σ.perm (Fin.last m)).val - 1, by omega⟩).isLt
      change m < _ at htie
      omega
    obtain ⟨j, hjk, hjc⟩ := hgood ⟨0, Nat.succ_pos m⟩
    have hjlt : j.val < m + 1 := by
      have := j.isLt
      have : j.val ≠ k.val := Fin.val_ne_of_ne hjk
      omega
    have hv0 : σ.vertex j 0 = 0 := by
      unfold KuhnSimplex.vertex cumToBary KuhnSimplex.cumVertex
      have hsymm0 : σ.perm.symm 0 = Fin.last m := by
        rw [← hlast0, Equiv.symm_apply_apply]
      have hnotlt : ¬ (σ.perm.symm 0).val < j.val := by
        rw [hsymm0]
        change ¬ m < j.val
        omega
      have hbase0 : σ.base 0 = 0 := by
        rw [← hlast0]
        exact hb0
      have h0eq : (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) = 0 := rfl
      simp only [Fin.val_zero, ↓reduceDIte, Nat.succ_pos m, h0eq, hbase0,
        hnotlt, ↓reduceIte, add_zero]
    have hsp := hc (σ.vertex j) (σ.vertex_sum j)
    rw [hjc] at hsp
    exact hsp hv0
  · intro h0 hD j hj hp1 hp2 hEq
    obtain ⟨r, hrk, hrc⟩ := hgood ⟨j + 1, hj⟩
    have hvr : σ.vertex r ⟨j + 1, by omega⟩ = 0 := by
      unfold KuhnSimplex.vertex cumToBary KuhnSimplex.cumVertex
      have h1 : ¬ (j + 1 = 0) := by omega
      simp only [h1, ↓reduceDIte, hj]
      have hs1 : σ.perm.symm ⟨j + 1, hj⟩ = ⟨k.val - 1, by omega⟩ := by
        rw [← hp1, Equiv.symm_apply_apply]
      have hs2 : σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩ = ⟨k.val, hD⟩ := by
        rw [← hp2, Equiv.symm_apply_apply]
      have hsub : (⟨j + 1 - 1, by omega⟩ : Fin (m + 1)) = ⟨j, Nat.lt_of_succ_lt hj⟩ :=
        Fin.ext (by simp)
      change σ.cumVertex r ⟨j + 1, hj⟩ - σ.cumVertex r ⟨j + 1 - 1, _⟩ = 0
      unfold KuhnSimplex.cumVertex
      rw [hsub, hs1, hs2, hEq]
      have hrne : r.val ≠ k.val := Fin.val_ne_of_ne hrk
      by_cases hlt : k.val - 1 < r.val
      · have hlt2 : k.val < r.val := by omega
        simp [hlt, hlt2]
      · have hlt2 : ¬ k.val < r.val := by omega
        simp [hlt, hlt2]
    have hsp := hc (σ.vertex r) (σ.vertex_sum r)
    rw [hrc] at hsp
    exact hsp hvr

private noncomputable def facetPivot (m N : ℕ) :
    KuhnSimplex (m + 1) N × Fin (m + 2) → KuhnSimplex (m + 1) N × Fin (m + 2) :=
  fun ⟨σ, k⟩ =>
  if h0 : k.val = 0 then
    if hlt : σ.base (σ.perm 0) + 1 < N then
      let i₀ := σ.perm 0
      let b' : Fin (m + 1) → ℕ := Function.update σ.base i₀ (σ.base i₀ + 1)
      let p' : Equiv.Perm (Fin (m + 1)) := (cycShift m).trans σ.perm
      have hmono' : Monotone b' := by
        intro a b hab
        by_cases ha : a = i₀
        · subst ha
          rcases eq_or_lt_of_le hab with rfl | hlt'
          · exact le_rfl
          · have hne_eq : σ.base i₀ ≠ σ.base ⟨i₀.val + 1, by omega⟩ := by
              intro hEq
              have htie := σ.tie i₀.val (by omega) hEq
              have hi0eq : (⟨i₀.val, by omega⟩ : Fin (m + 1)) = σ.perm 0 := Fin.ext rfl
              rw [hi0eq, Equiv.symm_apply_apply] at htie
              exact Nat.not_lt_zero _ htie
            have hle1 : σ.base i₀ ≤ σ.base ⟨i₀.val + 1, by omega⟩ :=
              σ.mono (show i₀ ≤ ⟨i₀.val + 1, by omega⟩ by change i₀.val ≤ i₀.val + 1; omega)
            have hle2 : σ.base ⟨i₀.val + 1, by omega⟩ ≤ σ.base b :=
              σ.mono (show (⟨i₀.val + 1, by omega⟩ : Fin (m + 1)) ≤ b by
                change i₀.val + 1 ≤ b.val; omega)
            have hne_b : b ≠ i₀ := ne_of_gt hlt'
            simp only [b', Function.update_self, Function.update_of_ne hne_b]
            omega
        · by_cases hb : b = i₀
          · subst hb
            simp only [b', Function.update_self, Function.update_of_ne ha]
            exact le_trans (σ.mono hab) (Nat.le_succ _)
          · simp only [b', Function.update_of_ne ha, Function.update_of_ne hb]
            exact σ.mono hab
      have hltN' : ∀ j, b' j < N := by
        intro j
        by_cases hj : j = i₀
        · subst hj; simpa [b'] using hlt
        · simp [b', hj, σ.lt_N j]
      have htie' : ∀ (j : ℕ) (hj : j + 1 < m + 1),
          b' ⟨j, Nat.lt_of_succ_lt hj⟩ = b' ⟨j + 1, hj⟩ →
          p'.symm ⟨j + 1, hj⟩ < p'.symm ⟨j, Nat.lt_of_succ_lt hj⟩ := by
        intro j hj hEq
        have hp'symm : ∀ x : Fin (m + 1), p'.symm x = (cycShift m).symm (σ.perm.symm x) :=
          fun _ => rfl
        rw [hp'symm, hp'symm]
        by_cases h1 : (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin (m + 1)) = i₀
        · have h2 : (⟨j + 1, hj⟩ : Fin (m + 1)) ≠ i₀ := fun h => by
            have := congrArg Fin.val (h.trans h1.symm); simp at this
          have hv1 : σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩ = 0 := by
            rw [h1]; exact Equiv.symm_apply_apply σ.perm 0
          have hv2_ne : σ.perm.symm ⟨j + 1, hj⟩ ≠ 0 := by
            intro h; exact h2 (by dsimp only [i₀]; rw [← h, Equiv.apply_symm_apply])
          rw [hv1]
          change ((cycShift m).symm (σ.perm.symm ⟨j + 1, hj⟩)).val < ((cycShift m).symm 0).val
          have hpos : 0 < (σ.perm.symm ⟨j + 1, hj⟩).val :=
            Nat.pos_of_ne_zero (Fin.val_ne_of_ne hv2_ne)
          have hltm := (σ.perm.symm ⟨j + 1, hj⟩).isLt
          have h0lt : ¬ (0 : ℕ) < (0 : Fin (m + 1)).val := by simp
          simp only [cycShift, Equiv.coe_fn_symm_mk, hpos, h0lt, ↓reduceDIte]
          omega
        · by_cases h2 : (⟨j + 1, hj⟩ : Fin (m + 1)) = i₀
          · simp only [b', Function.update_of_ne h1, h2, Function.update_self] at hEq
            have hle1 : σ.base ⟨j, Nat.lt_of_succ_lt hj⟩ ≤ σ.base i₀ :=
              σ.mono (show (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin (m + 1)) ≤ i₀ by
                rw [← h2]; change j ≤ j + 1; omega)
            omega
          · simp only [b', Function.update_of_ne h1, Function.update_of_ne h2] at hEq
            have htie0 := σ.tie j hj hEq
            have hpos1 : 0 < (σ.perm.symm ⟨j + 1, hj⟩).val := by
              by_contra hz
              have hz0 : σ.perm.symm ⟨j + 1, hj⟩ = 0 :=
                Fin.ext (by change (σ.perm.symm _).val = 0; omega)
              exact h2 (by dsimp only [i₀]; rw [← hz0, Equiv.apply_symm_apply])
            have hpos2 : 0 < (σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩).val := lt_trans hpos1 htie0
            change ((cycShift m).symm (σ.perm.symm ⟨j + 1, hj⟩)).val <
              ((cycShift m).symm (σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩)).val
            simp only [cycShift, Equiv.coe_fn_symm_mk, hpos1, hpos2, ↓reduceDIte]
            exact Nat.sub_lt_sub_right (by omega) htie0
      (⟨b', p', hmono', hltN', htie'⟩, Fin.last (m + 1))
    else (σ, k)
  else if hD : k.val = m + 1 then
    if hpos : 0 < σ.base (σ.perm (Fin.last m)) then
      let i₁ := σ.perm (Fin.last m)
      let b' : Fin (m + 1) → ℕ := Function.update σ.base i₁ (σ.base i₁ - 1)
      let p' : Equiv.Perm (Fin (m + 1)) := (cycShift m).symm.trans σ.perm
      have hmono' : Monotone b' := by
        intro a b hab
        by_cases hb : b = i₁
        · subst hb
          rcases eq_or_lt_of_le hab with rfl | hlt'
          · exact le_rfl
          · have hi1_pos : 0 < i₁.val := by omega
            have hne_eq : σ.base ⟨i₁.val - 1, by omega⟩ ≠ σ.base i₁ := by
              intro hEq
              have hEq' : σ.base ⟨i₁.val - 1, by omega⟩ =
                  σ.base ⟨i₁.val - 1 + 1, by omega⟩ := by
                have : (⟨i₁.val - 1 + 1, by omega⟩ : Fin (m + 1)) = i₁ :=
                  Fin.ext (by dsimp only; omega)
                rwa [this]
              have htie := σ.tie (i₁.val - 1) (by omega) hEq'
              have hi1eq : (⟨i₁.val - 1 + 1, by omega⟩ : Fin (m + 1)) = σ.perm (Fin.last m) :=
                Fin.ext (by dsimp only; omega)
              rw [hi1eq, Equiv.symm_apply_apply] at htie
              have hltm := (σ.perm.symm ⟨i₁.val - 1, by omega⟩).isLt
              change m < _ at htie
              omega
            have hle1 : σ.base a ≤ σ.base ⟨i₁.val - 1, by omega⟩ :=
              σ.mono (show a ≤ ⟨i₁.val - 1, by omega⟩ by change a.val ≤ i₁.val - 1; omega)
            have hle2 : σ.base ⟨i₁.val - 1, by omega⟩ ≤ σ.base i₁ :=
              σ.mono (show (⟨i₁.val - 1, by omega⟩ : Fin (m + 1)) ≤ i₁ by
                change i₁.val - 1 ≤ i₁.val; omega)
            have hne_a : a ≠ i₁ := ne_of_lt hlt'
            simp only [b', Function.update_self, Function.update_of_ne hne_a]
            omega
        · by_cases ha : a = i₁
          · subst ha
            simp only [b', Function.update_self, Function.update_of_ne hb]
            exact le_trans (Nat.sub_le _ _) (σ.mono hab)
          · simp only [b', Function.update_of_ne ha, Function.update_of_ne hb]
            exact σ.mono hab
      have hltN' : ∀ j, b' j < N := by
        intro j
        by_cases hj : j = i₁
        · subst hj; simp only [b', Function.update_self]; have := σ.lt_N i₁; omega
        · simp [b', hj, σ.lt_N j]
      have htie' : ∀ (j : ℕ) (hj : j + 1 < m + 1),
          b' ⟨j, Nat.lt_of_succ_lt hj⟩ = b' ⟨j + 1, hj⟩ →
          p'.symm ⟨j + 1, hj⟩ < p'.symm ⟨j, Nat.lt_of_succ_lt hj⟩ := by
        intro j hj hEq
        have hp'symm : ∀ x : Fin (m + 1), p'.symm x = (cycShift m) (σ.perm.symm x) := fun _ => rfl
        rw [hp'symm, hp'symm]
        by_cases h2 : (⟨j + 1, hj⟩ : Fin (m + 1)) = i₁
        · have h1 : (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin (m + 1)) ≠ i₁ := fun h => by
            have := congrArg Fin.val (h.trans h2.symm); simp at this
          have hv2 : σ.perm.symm ⟨j + 1, hj⟩ = Fin.last m := by
            rw [h2]; exact Equiv.symm_apply_apply σ.perm (Fin.last m)
          have hv1_ne : σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩ ≠ Fin.last m := by
            intro h; exact h1 (by dsimp only [i₁]; rw [← h, Equiv.apply_symm_apply])
          rw [hv2]
          change ((cycShift m) (Fin.last m)).val <
            ((cycShift m) (σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩)).val
          have hlt1 : (σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩).val + 1 < m + 1 := by
            have := (σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩).isLt
            have hne := Fin.val_ne_of_ne hv1_ne
            simp at hne
            omega
          have hnotlast : ¬ (Fin.last m).val + 1 < m + 1 := by simp
          simp only [cycShift, Equiv.coe_fn_mk, hlt1, hnotlast, ↓reduceDIte]
          exact Nat.succ_pos _
        · by_cases h1 : (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin (m + 1)) = i₁
          · simp only [b', h1, Function.update_self, Function.update_of_ne h2] at hEq
            have hle1 : σ.base i₁ ≤ σ.base ⟨j + 1, hj⟩ :=
              σ.mono (show i₁ ≤ ⟨j + 1, hj⟩ by rw [← h1]; change j ≤ j + 1; omega)
            dsimp only [i₁] at hEq hle1
            omega
          · simp only [b', Function.update_of_ne h1, Function.update_of_ne h2] at hEq
            have htie0 := σ.tie j hj hEq
            have hlt2 : (σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩).val + 1 < m + 1 := by
              have hlt' := (σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩).isLt
              have hne : σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩ ≠ Fin.last m := by
                intro h; exact h1 (by dsimp only [i₁]; rw [← h, Equiv.apply_symm_apply])
              have hvalne : (σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩).val ≠ m :=
                fun h => hne (Fin.ext h)
              omega
            have hlt1 : (σ.perm.symm ⟨j + 1, hj⟩).val + 1 < m + 1 := by
              have : (σ.perm.symm ⟨j + 1, hj⟩).val < (σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩).val :=
                htie0
              omega
            change ((cycShift m) (σ.perm.symm ⟨j + 1, hj⟩)).val <
              ((cycShift m) (σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩)).val
            simp only [cycShift, Equiv.coe_fn_mk, hlt1, hlt2, ↓reduceDIte]
            exact Nat.succ_lt_succ htie0
      (⟨b', p', hmono', hltN', htie'⟩, 0)
    else (σ, k)
  else
    have hklt : k.val < m + 1 := by have := k.isLt; omega
    let p' : Equiv.Perm (Fin (m + 1)) :=
      (Equiv.swap (⟨k.val - 1, by omega⟩ : Fin (m + 1)) ⟨k.val, hklt⟩).trans σ.perm
    open Classical in
    if hvalid : ∀ (j : ℕ) (hj : j + 1 < m + 1),
        σ.base ⟨j, Nat.lt_of_succ_lt hj⟩ = σ.base ⟨j + 1, hj⟩ →
        p'.symm ⟨j + 1, hj⟩ < p'.symm ⟨j, Nat.lt_of_succ_lt hj⟩ then
      (⟨σ.base, p', σ.mono, σ.lt_N, hvalid⟩, k)
    else (σ, k)

private lemma int_pairs_even (m N : ℕ) {c : (Fin (m + 2) → ℕ) → Fin (m + 2)}
    (hc : IsSpernerColoring (m + 1) N c) :
    Even (open Classical in
      ((goodFacetPairs m N c).filter (fun p =>
        ¬ (p.2.val = 0 ∧ p.1.base (p.1.perm 0) = N - 1)))).card := by
  classical
  let intPairs := (goodFacetPairs m N c).filter (fun p =>
    ¬ (p.2.val = 0 ∧ p.1.base (p.1.perm 0) = N - 1))
  have hpivot_props : ∀ p ∈ intPairs,
      facetPivot m N p ∈ intPairs ∧ facetPivot m N (facetPivot m N p) = p ∧
        facetPivot m N p ≠ p := by
    intro ⟨σ, k⟩ hp
    obtain ⟨hpG, hpNotB⟩ := Finset.mem_filter.mp hp
    have hgood : ∀ r : Fin (m + 1),
        ∃ j : Fin (m + 2), j ≠ k ∧ c (σ.vertex j) = r.castSucc :=
      (Finset.mem_filter.mp hpG).2
    have hnb := no_bdry_lt_of_good hc hpG
    dsimp only at hpNotB hgood hnb
    by_cases h0 : k.val = 0
    · have hlt : σ.base (σ.perm 0) + 1 < N := by
        have := σ.lt_N (σ.perm 0)
        by_contra hc'
        exact hpNotB ⟨h0, by omega⟩
      have hp_eq : (facetPivot m N (σ, k)).2 = Fin.last (m + 1) := by
        simp only [facetPivot, h0, hlt, ↓reduceDIte]
      have hσ'_base : (facetPivot m N (σ, k)).1.base =
          Function.update σ.base (σ.perm 0) (σ.base (σ.perm 0) + 1) := by
        simp only [facetPivot, h0, hlt, ↓reduceDIte]
      have hσ'_perm : (facetPivot m N (σ, k)).1.perm = (cycShift m).trans σ.perm := by
        simp only [facetPivot, h0, hlt, ↓reduceDIte]
      have hv_eq : ∀ (r : Fin (m + 2)) (hr : r.val < m + 1),
          (facetPivot m N (σ, k)).1.vertex r = σ.vertex ⟨r.val + 1, by omega⟩ := by
        intro r hr
        funext i
        unfold KuhnSimplex.vertex cumToBary
        suffices hcum : ∀ j : Fin (m + 1),
            (facetPivot m N (σ, k)).1.cumVertex r j = σ.cumVertex ⟨r.val + 1, by omega⟩ j by
          simp [hcum]
        intro j
        unfold KuhnSimplex.cumVertex
        rw [hσ'_base, hσ'_perm]
        have hsymm : ((cycShift m).trans σ.perm).symm j = (cycShift m).symm (σ.perm.symm j) := rfl
        rw [hsymm]
        by_cases hj : j = σ.perm 0
        · subst hj
          rw [Function.update_self, Equiv.symm_apply_apply]
          have hc0 : ((cycShift m).symm 0).val = m := by simp [cycShift]
          rw [hc0]
          have hnotlt : ¬ m < r.val := by omega
          have hlt1 : (0 : ℕ) < r.val + 1 := Nat.succ_pos _
          simp [hnotlt, hlt1]
        · rw [Function.update_of_ne hj]
          have hpos : 0 < (σ.perm.symm j).val := by
            by_contra hz
            have hz0 : σ.perm.symm j = 0 := Fin.ext (by change (σ.perm.symm j).val = 0; omega)
            exact hj (by rw [← hz0, Equiv.apply_symm_apply])
          have hcs : ((cycShift m).symm (σ.perm.symm j)).val = (σ.perm.symm j).val - 1 := by
            simp only [cycShift, Equiv.coe_fn_symm_mk, hpos, ↓reduceDIte]
          rw [hcs]
          by_cases hc' : (σ.perm.symm j).val < r.val + 1
          · have hsub : (σ.perm.symm j).val - 1 < r.val := by omega
            simp [hc', hsub]
          · have hsub : ¬ (σ.perm.symm j).val - 1 < r.val := by omega
            simp [hc', hsub]
      have hmem_int : facetPivot m N (σ, k) ∈ intPairs := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨mem_allKuhnSimplices _, Finset.mem_univ _⟩, ?_⟩, ?_⟩
        · intro r
          obtain ⟨j, hjk, hjc⟩ := hgood r
          have hjpos : 0 < j.val := by have := Fin.val_ne_of_ne hjk; omega
          refine ⟨⟨j.val - 1, by omega⟩, ?_, ?_⟩
          · rw [hp_eq]
            intro hEq
            have := congrArg Fin.val hEq
            simp at this
            omega
          · have hjlt' : j.val - 1 < m + 1 := by have := j.isLt; omega
            rw [hv_eq ⟨j.val - 1, by omega⟩ hjlt']
            have heq' : (⟨j.val - 1 + 1, by omega⟩ : Fin (m + 2)) = j :=
              Fin.ext (by dsimp only; omega)
            rw [heq']
            exact hjc
        · rw [hp_eq]
          rintro ⟨h, _⟩
          simp at h
      have hinv : facetPivot m N (facetPivot m N (σ, k)) = (σ, k) := by
        let σ' := (facetPivot m N (σ, k)).1
        have hk' : (facetPivot m N (σ, k)).2 = Fin.last (m + 1) := hp_eq
        have h0' : ¬ (Fin.last (m + 1)).val = 0 := by simp
        have hD' : (Fin.last (m + 1)).val = m + 1 := rfl
        have hp_last : σ'.perm (Fin.last m) = σ.perm 0 := by
          rw [hσ'_perm]
          change σ.perm ((cycShift m) (Fin.last m)) = σ.perm 0
          congr 1
          ext
          simp [cycShift]
        have hpos' : 0 < σ'.base (σ'.perm (Fin.last m)) := by
          rw [hp_last, hσ'_base, Function.update_self]
          omega
        have h1 : (facetPivot m N (σ', Fin.last (m + 1))).2 = k := by
          have : (facetPivot m N (σ', Fin.last (m + 1))).2 = 0 := by
            dsimp only [facetPivot]
            rw [dite_eq_right_of_eq_false (eq_false h0'), dite_eq_left_of_eq_true (eq_true hD'),
              dite_eq_left_of_eq_true (eq_true hpos')]
          rw [this]
          exact Fin.ext h0.symm
        have h2 : (facetPivot m N (σ', Fin.last (m + 1))).1 = σ := by
          apply KuhnSimplex.ext
          · funext j
            have hbase_eq : (facetPivot m N (σ', Fin.last (m + 1))).1.base =
                Function.update σ'.base (σ'.perm (Fin.last m))
                  (σ'.base (σ'.perm (Fin.last m)) - 1) := by
              dsimp only [facetPivot]
              rw [dite_eq_right_of_eq_false (eq_false h0'), dite_eq_left_of_eq_true (eq_true hD'),
                dite_eq_left_of_eq_true (eq_true hpos')]
            rw [hbase_eq, hp_last, hσ'_base]
            by_cases hj : j = σ.perm 0
            · subst hj; simp
            · simp [hj]
          · have hperm_eq :
                (facetPivot m N (σ', Fin.last (m + 1))).1.perm =
                  (cycShift m).symm.trans σ'.perm := by
              dsimp only [facetPivot]
              rw [dite_eq_right_of_eq_false (eq_false h0'), dite_eq_left_of_eq_true (eq_true hD'),
                dite_eq_left_of_eq_true (eq_true hpos')]
            rw [hperm_eq, hσ'_perm]
            ext j
            simp
        exact Prod.ext (by rw [← hk'] at h2; exact h2) (by rw [← hk'] at h1; exact h1)
      have hne : facetPivot m N (σ, k) ≠ (σ, k) := by
        intro hEq
        have := congrArg (fun q : KuhnSimplex (m + 1) N × Fin (m + 2) => q.2.val) hEq
        rw [hp_eq] at this
        simp at this
        omega
      exact ⟨hmem_int, hinv, hne⟩
    · by_cases hD : k.val = m + 1
      · have hpos : 0 < σ.base (σ.perm (Fin.last m)) := hnb.2.1 hD
        have hp_eq : (facetPivot m N (σ, k)).2 = 0 := by
          dsimp only [facetPivot]
          rw [dite_eq_right_of_eq_false (eq_false h0), dite_eq_left_of_eq_true (eq_true hD),
            dite_eq_left_of_eq_true (eq_true hpos)]
        have hσ'_base : (facetPivot m N (σ, k)).1.base =
            Function.update σ.base (σ.perm (Fin.last m))
              (σ.base (σ.perm (Fin.last m)) - 1) := by
          dsimp only [facetPivot]
          rw [dite_eq_right_of_eq_false (eq_false h0), dite_eq_left_of_eq_true (eq_true hD),
            dite_eq_left_of_eq_true (eq_true hpos)]
        have hσ'_perm : (facetPivot m N (σ, k)).1.perm = (cycShift m).symm.trans σ.perm := by
          dsimp only [facetPivot]
          rw [dite_eq_right_of_eq_false (eq_false h0), dite_eq_left_of_eq_true (eq_true hD),
            dite_eq_left_of_eq_true (eq_true hpos)]
        have hv_eq : ∀ (r : Fin (m + 2)) (hr : 0 < r.val),
            (facetPivot m N (σ, k)).1.vertex r = σ.vertex ⟨r.val - 1, by omega⟩ := by
          intro r hr
          funext i
          unfold KuhnSimplex.vertex cumToBary
          suffices hcum : ∀ j : Fin (m + 1),
              (facetPivot m N (σ, k)).1.cumVertex r j = σ.cumVertex ⟨r.val - 1, by omega⟩ j by
            simp [hcum]
          intro j
          unfold KuhnSimplex.cumVertex
          rw [hσ'_base, hσ'_perm]
          have hsymm : ((cycShift m).symm.trans σ.perm).symm j = (cycShift m) (σ.perm.symm j) := rfl
          rw [hsymm]
          by_cases hj : j = σ.perm (Fin.last m)
          · subst hj
            rw [Function.update_self, Equiv.symm_apply_apply]
            have hc' : ((cycShift m) (Fin.last m)).val = 0 := by simp [cycShift]
            rw [hc']
            have hnotlt : ¬ (Fin.last m).val < r.val - 1 := by simp; have := r.isLt; omega
            dsimp only
            simp only [hr, hnotlt, ↓reduceIte]
            omega
          · rw [Function.update_of_ne hj]
            have hlt : (σ.perm.symm j).val + 1 < m + 1 := by
              have := (σ.perm.symm j).isLt
              have hne : σ.perm.symm j ≠ Fin.last m := fun h =>
                hj (by rw [← h, Equiv.apply_symm_apply])
              have := Fin.val_ne_of_ne hne
              simp at this
              omega
            have hcs : ((cycShift m) (σ.perm.symm j)).val = (σ.perm.symm j).val + 1 := by
              simp only [cycShift, Equiv.coe_fn_mk, hlt, ↓reduceDIte]
            rw [hcs]
            by_cases hc' : (σ.perm.symm j).val < r.val - 1
            · have hadd : (σ.perm.symm j).val + 1 < r.val := by omega
              simp [hc', hadd]
            · have hadd : ¬ (σ.perm.symm j).val + 1 < r.val := by omega
              simp [hc', hadd]
        have hp0 : (facetPivot m N (σ, k)).1.perm 0 = σ.perm (Fin.last m) := by
          rw [hσ'_perm]
          exact congrArg σ.perm (Fin.ext (by simp [cycShift]))
        have hlt' : (facetPivot m N (σ, k)).1.base ((facetPivot m N (σ, k)).1.perm 0) + 1 < N := by
          rw [hp0, hσ'_base, Function.update_self]
          have := σ.lt_N (σ.perm (Fin.last m))
          omega
        have hmem_int : facetPivot m N (σ, k) ∈ intPairs := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
            ⟨mem_allKuhnSimplices _, Finset.mem_univ _⟩, ?_⟩, ?_⟩
          · intro r
            obtain ⟨j, hjk, hjc⟩ := hgood r
            have hjlt : j.val < m + 1 := by
              have := j.isLt
              have := Fin.val_ne_of_ne hjk
              omega
            refine ⟨⟨j.val + 1, by omega⟩, ?_, ?_⟩
            · rw [hp_eq]
              intro hEq
              have := congrArg Fin.val hEq
              simp at this
            · rw [hv_eq ⟨j.val + 1, by omega⟩ (Nat.succ_pos _)]
              have heq' : (⟨j.val + 1 - 1, by omega⟩ : Fin (m + 2)) = j := Fin.ext (by simp)
              rw [heq']
              exact hjc
          · rintro ⟨_, hmax⟩
            omega
        have hinv : facetPivot m N (facetPivot m N (σ, k)) = (σ, k) := by
          let σ' := (facetPivot m N (σ, k)).1
          have hk' : (facetPivot m N (σ, k)).2 = 0 := hp_eq
          have h0' : (0 : Fin (m + 2)).val = 0 := rfl
          have hlt'' : σ'.base (σ'.perm 0) + 1 < N := hlt'
          have h1 : (facetPivot m N (σ', 0)).2 = k := by
            have : (facetPivot m N (σ', 0)).2 = Fin.last (m + 1) := by
              simp only [facetPivot, h0', hlt'', ↓reduceDIte]
            rw [this]
            exact Fin.ext hD.symm
          have h2 : (facetPivot m N (σ', 0)).1 = σ := by
            apply KuhnSimplex.ext
            · funext j
              have hbase_eq : (facetPivot m N (σ', 0)).1.base =
                  Function.update σ'.base (σ'.perm 0) (σ'.base (σ'.perm 0) + 1) := by
                simp only [facetPivot, h0', hlt'', ↓reduceDIte]
              rw [hbase_eq, hp0, hσ'_base]
              by_cases hj : j = σ.perm (Fin.last m)
              · subst hj; simp; omega
              · simp [hj]
            · have hperm_eq : (facetPivot m N (σ', 0)).1.perm = (cycShift m).trans σ'.perm := by
                simp only [facetPivot, h0', hlt'', ↓reduceDIte]
              rw [hperm_eq, hσ'_perm]
              ext j
              simp
          exact Prod.ext (by rw [← hk'] at h2; exact h2) (by rw [← hk'] at h1; exact h1)
        have hne : facetPivot m N (σ, k) ≠ (σ, k) := by
          intro hEq
          have := congrArg (fun q : KuhnSimplex (m + 1) N × Fin (m + 2) => q.2.val) hEq
          rw [hp_eq] at this
          simp at this
          omega
        exact ⟨hmem_int, hinv, hne⟩
      · have hkpos : 0 < k.val := by omega
        have hklt : k.val < m + 1 := by have := k.isLt; omega
        let sw : Equiv.Perm (Fin (m + 1)) := Equiv.swap ⟨k.val - 1, by omega⟩ ⟨k.val, hklt⟩
        let p' : Equiv.Perm (Fin (m + 1)) := sw.trans σ.perm
        have hvalid : ∀ (j : ℕ) (hj : j + 1 < m + 1),
            σ.base ⟨j, Nat.lt_of_succ_lt hj⟩ = σ.base ⟨j + 1, hj⟩ →
            p'.symm ⟨j + 1, hj⟩ < p'.symm ⟨j, Nat.lt_of_succ_lt hj⟩ := by
          intro j hj hEq
          have htie0 := σ.tie j hj hEq
          have hp's : ∀ x : Fin (m + 1), p'.symm x = sw (σ.perm.symm x) := fun x => by
            change sw.symm (σ.perm.symm x) = sw (σ.perm.symm x)
            rw [Equiv.symm_swap]
          rw [hp's, hp's]
          let a := σ.perm.symm ⟨j + 1, hj⟩
          let b := σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩
          have hab : a.val < b.val := htie0
          by_cases h1 : a = ⟨k.val - 1, by omega⟩ ∧ b = ⟨k.val, hklt⟩
          · exfalso
            have hp1 : σ.perm ⟨k.val - 1, by omega⟩ = ⟨j + 1, hj⟩ := by
              rw [← h1.1]; exact Equiv.apply_symm_apply _ _
            have hp2 : σ.perm ⟨k.val, hklt⟩ = ⟨j, Nat.lt_of_succ_lt hj⟩ := by
              rw [← h1.2]; exact Equiv.apply_symm_apply _ _
            exact hnb.2.2 hkpos hklt j hj hp1 hp2 hEq
          · change (sw a).val < (sw b).val
            by_cases ha1 : a = ⟨k.val - 1, by omega⟩
            · have hb2 : b ≠ ⟨k.val, hklt⟩ := fun hb => h1 ⟨ha1, hb⟩
              have hb1 : b ≠ ⟨k.val - 1, by omega⟩ := fun hb => by
                rw [ha1, hb] at hab; exact lt_irrefl _ hab
              have hbv : k.val < b.val := by
                have hne := Fin.val_ne_of_ne hb2
                rw [ha1] at hab
                dsimp at hab hne
                omega
              rw [ha1, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hb1 hb2]
              exact hbv
            · by_cases ha2 : a = ⟨k.val, hklt⟩
              · have hb1 : b ≠ ⟨k.val - 1, by omega⟩ := fun hb => by
                  rw [ha2, hb] at hab; dsimp at hab; omega
                have hb2 : b ≠ ⟨k.val, hklt⟩ := fun hb => by
                  rw [ha2, hb] at hab; exact lt_irrefl _ hab
                rw [ha2, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hb1 hb2]
                rw [ha2] at hab
                dsimp at hab ⊢
                omega
              · rw [Equiv.swap_apply_of_ne_of_ne ha1 ha2]
                by_cases hb1 : b = ⟨k.val - 1, by omega⟩
                · rw [hb1, Equiv.swap_apply_left]
                  rw [hb1] at hab
                  dsimp at hab ⊢
                  omega
                · by_cases hb2 : b = ⟨k.val, hklt⟩
                  · rw [hb2, Equiv.swap_apply_right]
                    have hne1 := Fin.val_ne_of_ne ha1
                    rw [hb2] at hab
                    dsimp at hab hne1 ⊢
                    omega
                  · rw [Equiv.swap_apply_of_ne_of_ne hb1 hb2]
                    exact hab
        have hp_eq : facetPivot m N (σ, k) = (⟨σ.base, p', σ.mono, σ.lt_N, hvalid⟩, k) := by
          dsimp only [facetPivot]
          rw [dite_eq_right_of_eq_false (eq_false h0), dite_eq_right_of_eq_false (eq_false hD),
            dite_eq_left_of_eq_true (eq_true hvalid)]
        have hv_eq : ∀ r : Fin (m + 2), r ≠ k →
            (facetPivot m N (σ, k)).1.vertex r = σ.vertex r := by
          intro r hrk
          funext i
          unfold KuhnSimplex.vertex cumToBary
          suffices hcum : ∀ j : Fin (m + 1),
              (facetPivot m N (σ, k)).1.cumVertex r j = σ.cumVertex r j by
            simp [hcum]
          intro j
          unfold KuhnSimplex.cumVertex
          rw [hp_eq]
          dsimp only
          have hp's : p'.symm j = sw (σ.perm.symm j) := by
            change sw.symm (σ.perm.symm j) = sw (σ.perm.symm j)
            rw [Equiv.symm_swap]
          rw [hp's]
          have hrne : r.val ≠ k.val := Fin.val_ne_of_ne hrk
          have hiff : (sw (σ.perm.symm j)).val < r.val ↔ (σ.perm.symm j).val < r.val := by
            by_cases h1 : σ.perm.symm j = ⟨k.val - 1, by omega⟩
            · rw [h1, Equiv.swap_apply_left]; dsimp; omega
            · by_cases h2 : σ.perm.symm j = ⟨k.val, hklt⟩
              · rw [h2, Equiv.swap_apply_right]; dsimp; omega
              · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
          by_cases h : (σ.perm.symm j).val < r.val
          · simp [h, hiff.mpr h]
          · simp [h, mt hiff.mp h]
        have hmem_int : facetPivot m N (σ, k) ∈ intPairs := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
            ⟨mem_allKuhnSimplices _, Finset.mem_univ _⟩, ?_⟩, ?_⟩
          · intro r
            obtain ⟨j, hjk, hjc⟩ := hgood r
            rw [hp_eq] at *
            refine ⟨j, hjk, ?_⟩
            have := hv_eq j hjk
            rw [hp_eq] at this
            rw [this]
            exact hjc
          · rw [hp_eq]
            rintro ⟨h, _⟩
            exact h0 h
        have hinv : facetPivot m N (facetPivot m N (σ, k)) = (σ, k) := by
          rw [hp_eq]
          have hvalid2 : ∀ (j : ℕ) (hj : j + 1 < m + 1),
              σ.base ⟨j, Nat.lt_of_succ_lt hj⟩ = σ.base ⟨j + 1, hj⟩ →
              (sw.trans p').symm ⟨j + 1, hj⟩ < (sw.trans p').symm ⟨j, Nat.lt_of_succ_lt hj⟩ := by
            have hsw2 : sw.trans p' = σ.perm := by ext x; simp [p', sw]
            rw [hsw2]
            exact σ.tie
          have h2 : facetPivot m N (⟨σ.base, p', σ.mono, σ.lt_N, hvalid⟩, k) =
              (⟨σ.base, sw.trans p', σ.mono, σ.lt_N, hvalid2⟩, k) := by
            dsimp only [facetPivot]
            rw [dite_eq_right_of_eq_false (eq_false h0), dite_eq_right_of_eq_false (eq_false hD),
              dite_eq_left_of_eq_true (eq_true hvalid2)]
          rw [h2]
          refine Prod.ext (KuhnSimplex.ext rfl ?_) rfl
          ext x
          simp [p', sw]
        have hne : facetPivot m N (σ, k) ≠ (σ, k) := by
          intro hEq
          rw [hp_eq] at hEq
          have hpEq : p' = σ.perm :=
            congrArg (fun q : KuhnSimplex (m + 1) N × Fin (m + 2) => q.1.perm) hEq
          have hval := congrArg (fun e : Equiv.Perm (Fin (m + 1)) => e ⟨k.val, hklt⟩) hpEq
          simp [p', sw] at hval
          omega
        exact ⟨hmem_int, hinv, hne⟩
  exact even_card_of_involution (facetPivot m N)
    (fun p hp => (hpivot_props p hp).1)
    (fun p hp => (hpivot_props p hp).2.1)
    (fun p hp => (hpivot_props p hp).2.2)

private def embedBary (m : ℕ) (v : Fin (m + 1) → ℕ) (i : Fin (m + 2)) : ℕ :=
  if h : i.val < m + 1 then v ⟨i.val, h⟩ else 0

private def restrictColoring (m : ℕ) (c : (Fin (m + 2) → ℕ) → Fin (m + 2))
    (v : Fin (m + 1) → ℕ) : Fin (m + 1) :=
  let col := c (embedBary m v)
  if h : col.val < m + 1 then ⟨col.val, h⟩ else ⟨0, Nat.succ_pos m⟩

private lemma bdry_pairs_card_eq (m : ℕ) {N : ℕ} (hN : 1 ≤ N)
    {c : (Fin (m + 2) → ℕ) → Fin (m + 2)} (hc : IsSpernerColoring (m + 1) N c) :
    (open Classical in
      ((goodFacetPairs m N c).filter (fun p =>
        p.2.val = 0 ∧ p.1.base (p.1.perm 0) = N - 1)).card) =
    (open Classical in
      ((allKuhnSimplices m N).filter (KuhnSimplex.IsRainbow (restrictColoring m c))).card) ∧
      IsSpernerColoring m N (restrictColoring m c) := by
  classical
  have hembed_sum : ∀ v : Fin (m + 1) → ℕ,
      ∑ i : Fin (m + 2), embedBary m v i = ∑ j : Fin (m + 1), v j := by
    intro v
    rw [Fin.sum_univ_castSucc]
    have hlast : embedBary m v (Fin.last (m + 1)) = 0 := by simp [embedBary]
    rw [hlast, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [embedBary, j.isLt]
  have hc'_sp : IsSpernerColoring m N (restrictColoring m c) := by
    intro v hv
    have hsum : ∑ i : Fin (m + 2), embedBary m v i = N := by
      rw [hembed_sum]
      exact hv
    have hsp := hc (embedBary m v) hsum
    have hlt : (c (embedBary m v)).val < m + 1 := by
      by_contra hge
      have hlast : c (embedBary m v) = Fin.last (m + 1) := Fin.ext (by
        change (c (embedBary m v)).val = m + 1
        have := (c (embedBary m v)).isLt
        omega)
      rw [hlast] at hsp
      simp [embedBary] at hsp
    have hc'eq : (restrictColoring m c v).castSucc = c (embedBary m v) := by
      ext
      simp [restrictColoring, hlt]
    have hveq : embedBary m v (c (embedBary m v)) = v (restrictColoring m c v) := by
      rw [← hc'eq]
      simp [embedBary, (restrictColoring m c v).isLt]
    rwa [← hveq]
  let liftPerm : Equiv.Perm (Fin m) → Equiv.Perm (Fin (m + 1)) := fun π =>
    { toFun := fun i =>
        if h : 0 < i.val then (π ⟨i.val - 1, by omega⟩).castSucc else Fin.last m
      invFun := fun j =>
        if h : j.val < m then ⟨(π.symm ⟨j.val, h⟩).val + 1, by omega⟩ else 0
      left_inv := fun i => by
        ext
        dsimp only
        by_cases h : 0 < i.val
        · have hlt : (π ⟨i.val - 1, by omega⟩).val < m := (π _).isLt
          simp [h, hlt]
          omega
        · have hi : i.val = 0 := by omega
          simp [hi]
      right_inv := fun j => by
        ext
        dsimp only
        by_cases h : j.val < m
        · simp [h]
        · have hj : j.val = m := by have := j.isLt; omega
          simp [hj] }
  let lift : KuhnSimplex m N → KuhnSimplex (m + 1) N × Fin (m + 2) := fun τ =>
    let b : Fin (m + 1) → ℕ := fun j => if h : j.val < m then τ.base ⟨j.val, h⟩ else N - 1
    have hmono : Monotone b := by
      intro j₁ j₂ hle
      by_cases h2 : j₂.val < m
      · have h1 : j₁.val < m := lt_of_le_of_lt hle h2
        simp only [b, h1, h2, ↓reduceDIte]
        exact τ.mono (show (⟨j₁.val, h1⟩ : Fin m) ≤ ⟨j₂.val, h2⟩ from hle)
      · simp only [b, h2, ↓reduceDIte]
        by_cases h1 : j₁.val < m
        · simp only [h1, ↓reduceDIte]
          have := τ.lt_N ⟨j₁.val, h1⟩
          omega
        · simp [h1]
    have hltN : ∀ j, b j < N := by
      intro j
      by_cases h : j.val < m
      · simp [b, h, τ.lt_N]
      · simp [b, h]
        omega
    have htie : ∀ (j : ℕ) (hj : j + 1 < m + 1),
        b ⟨j, Nat.lt_of_succ_lt hj⟩ = b ⟨j + 1, hj⟩ →
        (liftPerm τ.perm).symm ⟨j + 1, hj⟩ <
          (liftPerm τ.perm).symm ⟨j, Nat.lt_of_succ_lt hj⟩ := by
      intro j hj hEq
      by_cases h2 : j + 1 < m
      · have h1 : j < m := by omega
        simp only [b, h1, h2, ↓reduceDIte] at hEq
        have htie0 := τ.tie j h2 hEq
        change ((liftPerm τ.perm).symm ⟨j + 1, hj⟩).val <
          ((liftPerm τ.perm).symm ⟨j, Nat.lt_of_succ_lt hj⟩).val
        simp only [liftPerm, Equiv.coe_fn_symm_mk, h1, h2, ↓reduceDIte]
        exact Nat.succ_lt_succ htie0
      · have h1 : j < m := by omega
        change ((liftPerm τ.perm).symm ⟨j + 1, hj⟩).val <
          ((liftPerm τ.perm).symm ⟨j, Nat.lt_of_succ_lt hj⟩).val
        simp [liftPerm, h1, h2]
    (⟨b, liftPerm τ.perm, hmono, hltN, htie⟩, 0)
  have hlift_vertex : ∀ (τ : KuhnSimplex m N) (r : Fin (m + 1)),
      (lift τ).1.vertex r.succ = embedBary m (τ.vertex r) := by
    intro τ r
    have hcum : ∀ j : Fin m, (lift τ).1.cumVertex r.succ j.castSucc = τ.cumVertex r j := by
      intro j
      unfold KuhnSimplex.cumVertex
      have hb : (lift τ).1.base j.castSucc = τ.base j := by simp [lift, j.isLt]
      have hp : ((lift τ).1.perm.symm j.castSucc).val = (τ.perm.symm j).val + 1 := by
        simp [lift, liftPerm, j.isLt]
      rw [hb, hp]
      change τ.base j + (if (τ.perm.symm j).val + 1 < r.val + 1 then 1 else 0) =
        τ.base j + (if (τ.perm.symm j).val < r.val then 1 else 0)
      simp
    have hcum_last : (lift τ).1.cumVertex r.succ (Fin.last m) = N := by
      unfold KuhnSimplex.cumVertex
      have hb : (lift τ).1.base (Fin.last m) = N - 1 := by simp [lift]
      have hp : ((lift τ).1.perm.symm (Fin.last m)).val = 0 := by simp [lift, liftPerm]
      rw [hb, hp]
      simp
      omega
    funext i
    unfold KuhnSimplex.vertex embedBary cumToBary
    by_cases hi : i.val < m + 1
    · simp only [hi, ↓reduceDIte]
      by_cases h0 : i.val = 0
      · simp only [h0, ↓reduceDIte]
        by_cases hm : 0 < m
        · simp only [Nat.succ_pos m, hm, ↓reduceDIte]
          exact hcum ⟨0, hm⟩
        · have hm0 : m = 0 := by omega
          subst hm0
          simp only [Nat.succ_pos 0, ↓reduceDIte]
          exact hcum_last
      · by_cases him : i.val < m
        · simp only [h0, ↓reduceDIte, him]
          exact congrArg₂ (· - ·) (hcum ⟨i.val, him⟩) (hcum ⟨i.val - 1, by omega⟩)
        · have him_eq : i.val = m := by omega
          simp only [h0, ↓reduceDIte, him]
          have h1 : (lift τ).1.cumVertex r.succ ⟨i.val, hi⟩ = N := by
            have hlast_eq : (⟨i.val, hi⟩ : Fin (m + 1)) = Fin.last m := Fin.ext him_eq
            rw [hlast_eq]
            exact hcum_last
          have h2 : (lift τ).1.cumVertex r.succ ⟨i.val - 1, by omega⟩ =
              τ.cumVertex r ⟨m - 1, by omega⟩ := by
            have hprev_eq : (⟨i.val - 1, by omega⟩ : Fin (m + 1)) =
                (⟨m - 1, by omega⟩ : Fin m).castSucc := Fin.ext (by dsimp; omega)
            rw [hprev_eq]
            exact hcum ⟨m - 1, by omega⟩
          rw [h1, h2]
    · simp only [hi, ↓reduceDIte]
      have h0 : ¬ i.val = 0 := by omega
      simp only [h0, ↓reduceDIte]
      have hlast_eq : (⟨m + 1 - 1, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
      rw [hlast_eq, hcum_last]
      omega
  have hinj :
      Set.InjOn lift
        ((allKuhnSimplices m N).filter (KuhnSimplex.IsRainbow (restrictColoring m c))) := by
    intro τ₁ _ τ₂ _ hEq
    have hσEq := congrArg Prod.fst hEq
    apply KuhnSimplex.ext
    · funext j
      have hb := congrFun (congrArg KuhnSimplex.base hσEq) j.castSucc
      simpa [lift, j.isLt] using hb
    · ext j
      have hp := congrArg (fun e : Equiv.Perm (Fin (m + 1)) => (e ⟨j.val + 1, by omega⟩).val)
        (congrArg KuhnSimplex.perm hσEq)
      simp only [lift, liftPerm, Equiv.coe_fn_mk, Nat.succ_pos, ↓reduceDIte,
        Fin.val_castSucc, Nat.add_sub_cancel, Fin.eta] at hp
      exact hp
  let bdryPairs := (goodFacetPairs m N c).filter (fun p =>
    p.2.val = 0 ∧ p.1.base (p.1.perm 0) = N - 1)
  have himg : ((allKuhnSimplices m N).filter
      (KuhnSimplex.IsRainbow (restrictColoring m c))).image lift = bdryPairs := by
    ext ⟨σ, k⟩
    simp only [bdryPairs, goodFacetPairs, Finset.mem_image, Finset.mem_filter,
      Finset.mem_product, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨τ, ⟨_, hrb⟩, hEq⟩
      have hσEq : (lift τ).1 = σ := congrArg Prod.fst hEq
      have hkEq : (lift τ).2 = k := congrArg Prod.snd hEq
      subst hσEq; subst hkEq
      refine ⟨⟨mem_allKuhnSimplices _, ?_⟩, rfl, ?_⟩
      · intro r
        obtain ⟨j, hj⟩ := hrb.2 r
        refine ⟨j.succ, Fin.succ_ne_zero j, ?_⟩
        rw [hlift_vertex τ j]
        have hsum : ∑ i, embedBary m (τ.vertex j) i = N := by
          rw [hembed_sum]
          exact τ.vertex_sum j
        have hsp := hc (embedBary m (τ.vertex j)) hsum
        have hlt : (c (embedBary m (τ.vertex j))).val < m + 1 := by
          by_contra hge
          have hlast : c (embedBary m (τ.vertex j)) = Fin.last (m + 1) := Fin.ext (by
            change (c (embedBary m (τ.vertex j))).val = m + 1
            have := (c (embedBary m (τ.vertex j))).isLt
            omega)
          rw [hlast] at hsp
          simp [embedBary] at hsp
        have hc'eq : (restrictColoring m c (τ.vertex j)).castSucc =
            c (embedBary m (τ.vertex j)) := by
          ext
          simp [restrictColoring, hlt]
        dsimp only at hj
        rw [← hc'eq, hj]
      · simp [lift, liftPerm]
    · rintro ⟨⟨hσ, hgood⟩, hk0, hmax⟩
      have hmem_good : (σ, k) ∈ goodFacetPairs m N c := by
        unfold goodFacetPairs
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hσ, Finset.mem_univ _⟩, hgood⟩
      have hperm0 : σ.perm 0 = Fin.last m := (no_bdry_lt_of_good hc hmem_good).1 hk0 hmax
      let b₀ : Fin m → ℕ := fun j => σ.base j.castSucc
      let p₀ : Equiv.Perm (Fin m) :=
        { toFun := fun j =>
            let y := σ.perm ⟨j.val + 1, by omega⟩
            have hy : y.val < m := by
              have hne : y ≠ Fin.last m := by
                rw [← hperm0]
                intro h
                have := congrArg Fin.val (σ.perm.injective h)
                simp at this
              have := y.isLt
              have := Fin.val_ne_of_ne hne
              simp at this
              omega
            ⟨y.val, hy⟩
          invFun := fun i =>
            let x := σ.perm.symm i.castSucc
            have hx : 0 < x.val := by
              have hne : x ≠ 0 := by
                intro h
                have := congrArg Fin.val
                  (show i.castSucc = σ.perm 0 by rw [← h, Equiv.apply_symm_apply])
                rw [hperm0] at this
                simp at this
                omega
              exact Nat.pos_of_ne_zero (Fin.val_ne_of_ne hne)
            ⟨x.val - 1, by have := x.isLt; omega⟩
          left_inv := fun j => by
            ext
            dsimp only
            have hcast : ∀ h : (σ.perm ⟨j.val + 1, by omega⟩).val < m,
                (⟨(σ.perm ⟨j.val + 1, by omega⟩).val, h⟩ : Fin m).castSucc =
                σ.perm ⟨j.val + 1, by omega⟩ := fun _ => Fin.ext rfl
            rw [hcast, Equiv.symm_apply_apply]
            simp
          right_inv := fun i => by
            ext
            dsimp only
            have hpos : 0 < (σ.perm.symm i.castSucc).val := by
              by_contra hz
              have h0 : σ.perm.symm i.castSucc = 0 :=
                Fin.ext (by change (σ.perm.symm _).val = 0; omega)
              have := congrArg Fin.val
                (show i.castSucc = σ.perm 0 by rw [← h0, Equiv.apply_symm_apply])
              rw [hperm0] at this
              simp at this
              omega
            have hmk : (⟨(σ.perm.symm i.castSucc).val - 1 + 1, by omega⟩ : Fin (m + 1)) =
                σ.perm.symm i.castSucc := Fin.ext (by dsimp; omega)
            rw [hmk, Equiv.apply_symm_apply]
            rfl }
      let τ : KuhnSimplex m N :=
        ⟨b₀, p₀, fun a b hab => σ.mono hab, fun j => σ.lt_N j.castSucc, fun j hj hEq => by
          have htie0 := σ.tie j (by omega) hEq
          have hpos1 : 0 < (σ.perm.symm ⟨j + 1, by omega⟩).val := by
            by_contra hz
            have h0 : σ.perm.symm ⟨j + 1, by omega⟩ = 0 :=
              Fin.ext (by change (σ.perm.symm _).val = 0; omega)
            have := congrArg Fin.val (show (⟨j + 1, by omega⟩ : Fin (m + 1)) = σ.perm 0 by
              rw [← h0, Equiv.apply_symm_apply])
            rw [hperm0] at this
            simp at this
            omega
          change (p₀.symm ⟨j + 1, hj⟩).val < (p₀.symm ⟨j, Nat.lt_of_succ_lt hj⟩).val
          dsimp only [p₀, Equiv.coe_fn_symm_mk]
          exact Nat.sub_lt_sub_right
            (show 1 ≤ (σ.perm.symm ⟨j + 1, by omega⟩).val from hpos1) htie0⟩
      have hlift_eq : lift τ = (σ, k) := by
        refine Prod.ext (KuhnSimplex.ext ?_ ?_) (Fin.ext hk0.symm)
        · funext j
          dsimp only [lift]
          by_cases hj : j.val < m
          · simp [hj, τ, b₀]
          · have hlast : j = Fin.last m := Fin.ext (by change j.val = m; have := j.isLt; omega)
            subst hlast
            rw [hperm0] at hmax
            simp only [Fin.val_last, lt_self_iff_false, ↓reduceDIte]
            exact hmax.symm
        · ext j
          dsimp only [lift, liftPerm]
          by_cases hj : 0 < j.val
          · simp only [hj, ↓reduceDIte, τ, p₀, Equiv.coe_fn_mk, Fin.val_castSucc]
            have hmk : (⟨j.val - 1 + 1, by omega⟩ : Fin (m + 1)) = j := Fin.ext (by dsimp; omega)
            rw [hmk]
          · have h0 : j = 0 := Fin.ext (by change j.val = 0; omega)
            subst h0
            simp [hperm0]
      have hrb : τ.IsRainbow (restrictColoring m c) := by
        have hsurj :
            Function.Surjective (fun j : Fin (m + 1) => restrictColoring m c (τ.vertex j)) := by
          intro r
          obtain ⟨j, hjk, hjc⟩ := hgood r
          have hjpos : 0 < j.val := by have := Fin.val_ne_of_ne hjk; omega
          let j' : Fin (m + 1) := ⟨j.val - 1, by have := j.isLt; omega⟩
          refine ⟨j', ?_⟩
          have hj_eq : j'.succ = j := Fin.ext (by dsimp [j']; omega)
          have hv := hlift_vertex τ j'
          rw [hlift_eq, hj_eq] at hv
          ext
          simp only [restrictColoring, ← hv, hjc, Fin.val_castSucc, r.isLt, ↓reduceDIte]
        exact ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
      exact ⟨τ, ⟨mem_allKuhnSimplices τ, hrb⟩, hlift_eq⟩
  exact ⟨by dsimp only [bdryPairs] at himg; exact himg ▸ (Finset.card_image_of_injOn hinj), hc'_sp⟩

/-- **Sperner's Lemma (Freudenthal / Kuhn Triangulation):**
For any dimension `d : ℕ`, subdivision `N ≥ 1`, and proper Sperner coloring
`c : (Fin (d + 1) → ℕ) → Fin (d + 1)` on `Δ_d(N)`, the number of rainbow Kuhn `d`-simplices
in `Δ_d(N)` is **odd**. -/
theorem odd_card_isRainbow (d : ℕ) {N : ℕ} (hN : 1 ≤ N)
    (c : (Fin (d + 1) → ℕ) → Fin (d + 1))
    (hc : IsSpernerColoring d N c) :
    open Classical in
    Odd ((allKuhnSimplices d N).filter (KuhnSimplex.IsRainbow c)).card := by
  classical
  induction d with
  | zero =>
    let σ₀ : KuhnSimplex 0 N :=
      ⟨Fin.elim0, Equiv.refl _, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun j hj => by omega⟩
    have hall : allKuhnSimplices 0 N = {σ₀} := by
      ext σ
      simp only [Finset.mem_singleton]
      constructor
      · intro _
        exact KuhnSimplex.ext (funext fun i => Fin.elim0 i) (Equiv.ext fun i => Fin.elim0 i)
      · rintro rfl
        exact mem_allKuhnSimplices σ₀
    have hrb : σ₀.IsRainbow c := by
      refine ⟨fun a b _ => Fin.ext (by have := a.isLt; have := b.isLt; omega),
        fun y => ⟨0, Fin.ext (by have := (c (σ₀.vertex 0)).isLt; have := y.isLt; omega)⟩⟩
    simp only [hall, Finset.filter_singleton, hrb, ↓reduceIte, Finset.card_singleton]
    exact odd_one
  | succ m ih =>
    let bdryPairs := (goodFacetPairs m N c).filter (fun p =>
      p.2.val = 0 ∧ p.1.base (p.1.perm 0) = N - 1)
    let intPairs := (goodFacetPairs m N c).filter (fun p =>
      ¬ (p.2.val = 0 ∧ p.1.base (p.1.perm 0) = N - 1))
    have hsplit_card : (goodFacetPairs m N c).card = bdryPairs.card + intPairs.card := by
      have hdisj : Disjoint bdryPairs intPairs := by
        rw [Finset.disjoint_left]
        intro p h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      have hunion : bdryPairs ∪ intPairs = goodFacetPairs m N c := by
        ext p
        simp only [bdryPairs, intPairs, Finset.mem_union, Finset.mem_filter]
        tauto
      rw [← hunion, Finset.card_union_of_disjoint hdisj]
    have hmod_rainbow := goodFacetPairs_mod_two m N c
    have hint_even := int_pairs_even m N hc
    have ⟨hbdry_card, hc'_sp⟩ := bdry_pairs_card_eq m hN hc
    have hIH := ih (restrictColoring m c) hc'_sp
    rcases hint_even with ⟨e, he⟩
    rcases hIH with ⟨q, hq⟩
    have hodd : ((allKuhnSimplices (m + 1) N).filter (KuhnSimplex.IsRainbow c)).card % 2 = 1 := by
      rw [← hmod_rainbow, hsplit_card, hbdry_card, he, hq]
      omega
    exact Nat.odd_iff.mpr hodd

/-- **Existence form of Sperner's Lemma:** every proper Sperner coloring of `Δ_d(N)` (`N ≥ 1`)
has at least one rainbow Kuhn simplex. -/
theorem exists_isRainbow (d : ℕ) {N : ℕ} (hN : 1 ≤ N)
    (c : (Fin (d + 1) → ℕ) → Fin (d + 1))
    (hc : IsSpernerColoring d N c) :
    ∃ σ : KuhnSimplex d N, σ.IsRainbow c := by
  classical
  have hodd := odd_card_isRainbow d hN c hc
  have hpos : 0 < ((allKuhnSimplices d N).filter (KuhnSimplex.IsRainbow c)).card := by
    rcases hodd with ⟨k, hk⟩
    omega
  obtain ⟨σ, hσ⟩ := Finset.card_pos.mp hpos
  exact ⟨σ, (Finset.mem_filter.mp hσ).2⟩

end ParityProof

end Cslib.Sperner.Simplex
