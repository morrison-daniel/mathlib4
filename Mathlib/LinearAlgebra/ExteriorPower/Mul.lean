/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Multiplication on exterior powers
-/

@[expose] public section

open BigOperators Module

namespace exteriorPower

section ring

variable {R M : Type*} {m n : ℕ} [CommRing R] [AddCommGroup M] [Module R M]

lemma degree_mul (x : ⋀[R]^m M) (y : ⋀[R]^n M) :
    (x : ExteriorAlgebra R M) * (y : ExteriorAlgebra R M) ∈ ⋀[R]^(m+n) M := by
  exact ExteriorAlgebra.degree_mul R x.val y.val x.prop y.prop

instance instHMul : HMul (⋀[R]^m M) (⋀[R]^n M) (⋀[R]^(m + n) M) where
  hMul x y := ⟨x.val * y.val, degree_mul x y⟩

@[simp]
lemma hmul_val (x : ⋀[R]^m M) (y : ⋀[R]^n M) : (x * y).val = x.val * y.val := rfl

@[simp]
lemma hmul_add (x : ⋀[R]^m M) (y z : ⋀[R]^n M) : x * (y + z) = x * y + x * z := by
  ext
  simp [mul_add]

@[simp]
lemma add_hmul (x y : ⋀[R]^m M) (z : ⋀[R]^n M) : (x + y) * z = x * z + y * z := by
  ext
  simp [add_mul]

@[simp]
lemma smul_hmul (r : R) (x : ⋀[R]^m M) (y : ⋀[R]^n M) : (r • x) * y = r • (x * y) := by
  ext
  simp

@[simp]
lemma hmul_smul (r : R) (x : ⋀[R]^m M) (y : ⋀[R]^n M) : x * (r • y) = r • (x * y) := by
  ext
  simp

lemma ιMulti_mul_ιMulti (a : Fin m → M) (b : Fin n → M) :
    (ιMulti R m a) * (ιMulti R n b) = ιMulti R (m + n) (Fin.append a b) := by
  ext
  rw [hmul_val]
  exact ExteriorAlgebra.ιMulti_mul_ιMulti a b

lemma ιMulti_family_mul_of_not_disjoint {m n : ℕ} {I : Type*} [LinearOrder I] (v : I → M)
    (s : {s : Finset I // Finset.card s = m}) (t : {s : Finset I // Finset.card s = n})
    (h : ¬Disjoint s.val t.val) :
    ιMulti_family R m v s * ιMulti_family R n v t = 0 := by
  ext
  rw [hmul_val]
  exact ExteriorAlgebra.ιMulti_family_mul_of_not_disjoint R v s t h

lemma ιMulti_family_mul_of_disjoint {m n : ℕ} {I : Type*} [LinearOrder I] (v : I → M)
    (s : {s : Finset I // Finset.card s = m}) (t : {s : Finset I // Finset.card s = n})
    (h : Disjoint s.val t.val) :
    ιMulti_family R m v s * ιMulti_family R n v t = ((ExteriorAlgebra.ιMulti_perm h).sign : R) •
    ιMulti_family R (m + n) v ⟨s ∪ t, by rw [Finset.card_union_of_disjoint h, s.prop, t.prop]⟩ := by
  ext
  rw [hmul_val]
  exact ExteriorAlgebra.ιMulti_family_mul_of_disjoint R v s t h

variable (x : ⋀[R]^m M) (y : ⋀[R]^n M)

lemma mul_eq_zero_of_degree_gt_finrank [StrongRankCondition R] [Module.Free R M] [Module.Finite R M]
    (h : m + n > finrank R M) : x * y = 0 :=
  zero_of_degree_gt_finrank _ _ h _

variable (R M m n) in
def mulLeft : (⋀[R]^m M) →ₗ[R] (⋀[R]^n M →ₗ[R] ⋀[R]^(m + n) M) where
  toFun x := {
    toFun y := x * y
    map_add' := by intros; rw [hmul_add]
    map_smul' := by intros; rw [RingHom.id_apply, hmul_smul] }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

lemma mulLeft_apply : mulLeft R M m n x y = x * y := rfl

lemma coe_mulLeft_eq_mulLeft :
    (mulLeft R M m n x y).val = LinearMap.mulLeft R x.val y.val := by rfl

variable (R M m n) in
def mulRight : (⋀[R]^n M) →ₗ[R] (⋀[R]^m M →ₗ[R] ⋀[R]^(m + n) M) where
  toFun y := {
    toFun x := x * y
    map_add' := by intros; rw [add_hmul]
    map_smul' := by intros; rw [RingHom.id_apply, smul_hmul] }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

lemma mulRight_apply : mulRight R M m n y x = x * y := rfl

lemma coe_mulRight_eq_mulRight :
    (mulRight R M m n y x).val = LinearMap.mulRight R y.val x.val := by rfl

end ring

section basis

variable {R M : Type*} {m n : ℕ}
  [CommRing R] [AddCommGroup M] [Module R M]
  {I : Type*} [LinearOrder I] (b : Basis I R M)
  (s : {s : Finset I // Finset.card s = m}) (t : {s : Finset I // Finset.card s = n})

lemma basis_mul_eq_ite :
    Basis.exteriorPower R m b s * Basis.exteriorPower R n b t =
    if h : Disjoint s.val t.val then (ExteriorAlgebra.ιMulti_perm h).sign •
    (Basis.exteriorPower R (m+n) b ⟨s.val ∪ t.val,
    by rw [Finset.card_union_of_disjoint h, s.prop, t.prop]⟩) else 0 := by
  by_cases h : Disjoint s.val t.val
  · simp only [basis_apply, h, ↓reduceDIte]
    exact ιMulti_family_mul_of_disjoint _ _ _ h
  · simp only [basis_apply, h, ↓reduceDIte]
    exact ιMulti_family_mul_of_not_disjoint _ _ _ h

lemma mulLeft_injective [Fintype I] [NoZeroDivisors R] [CharZero R] [StrongRankCondition R]
    (b : Basis I R M) (hmn : m + n ≤ finrank R M) :
    Function.Injective (mulLeft R M m n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rw [← Module.Basis.forall_coord_eq_zero_iff (Basis.exteriorPower R m b)]
  intro s
  obtain ⟨t, h⟩ : ∃ t : {a : Finset I // a.card = n}, Disjoint s.val t.val := by
    suffices n ≤ s.valᶜ.card by
      obtain ⟨t, t_sub, t_card⟩ := Finset.le_card_iff_exists_subset_card.mp this
      use ⟨t, t_card⟩
      rw [← Finset.subset_compl_iff_disjoint_left]
      exact t_sub
    rw [Finset.card_compl, ← finrank_eq_card_basis b, s.prop, Nat.le_sub_iff_add_le' (by linarith)]
    exact hmn
  rw [LinearMap.ext_iff] at hx
  specialize hx <| (Basis.exteriorPower R n b) t
  rw [mulLeft_apply, LinearMap.zero_apply, ← Module.Basis.sum_repr
    (Basis.exteriorPower R m b) x] at hx
  simp_rw [Subtype.ext_iff, hmul_val, Submodule.coe_sum, Finset.sum_mul, Submodule.coe_smul] at hx
  simp_rw [smul_mul_assoc, ← hmul_val, ← Submodule.coe_smul, ← Submodule.coe_sum,
    ← Subtype.ext_iff] at hx
  rw [← Module.Basis.forall_coord_eq_zero_iff (Basis.exteriorPower R (m+n) b)] at hx
  specialize hx ⟨s ∪ t, by rw [Finset.card_union_of_disjoint h, s.prop, t.prop]⟩
  simp_rw [map_sum, map_smul] at hx
  rw [Fintype.sum_eq_single s] at hx
  · rw [← Basis.coord_apply, basis_apply, basis_apply, ιMulti_family_mul_of_disjoint _ s t h] at hx
    simp only [Basis.coord_apply, map_smul, basis_repr_self, smul_eq_mul, mul_one,
      mul_eq_zero] at hx
    rcases hx with hx | hx
    · exact hx
    · rw [← Int.cast_zero, Int.cast_inj] at hx
      simp only [Units.ne_zero] at hx
  · intro s' hs'
    by_cases hs't : Disjoint s'.val t.val
    · rw [basis_apply, basis_apply, ιMulti_family_mul_of_disjoint _ s' t hs't, map_smul, ← mul_smul]
      apply smul_eq_zero_of_right
      rw [← basis_apply, Basis.coord_apply, Module.Basis.repr_self]
      apply Finsupp.single_eq_of_ne
      by_contra hss't
      rw [Subtype.mk.injEq, ← Finset.coe_inj, Finset.coe_union, Finset.coe_union] at hss't
      apply hs'
      rw [Subtype.ext_iff, ← Finset.subset_iff_eq_of_card_le (by simp [s.prop, s'.prop]),
        ← Finset.coe_subset]
      apply Disjoint.subset_left_of_subset_union (u := t.val)
      · simp only [hss't, Set.subset_union_left]
      · simp only [Finset.disjoint_coe, hs't]
    · rw [basis_apply, basis_apply, ιMulti_family_mul_of_not_disjoint _ s' t hs't]
      simp

lemma mulRight_injective [Fintype I] [NoZeroDivisors R] [CharZero R] [StrongRankCondition R]
    (b : Basis I R M) (hmn : m + n ≤ finrank R M) :
    Function.Injective (mulRight R M m n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rw [← Module.Basis.forall_coord_eq_zero_iff (Basis.exteriorPower R n b)]
  intro s
  obtain ⟨t, h⟩ : ∃ t : {a : Finset I // a.card = m}, Disjoint t.val s.val := by
    suffices m ≤ s.valᶜ.card by
      obtain ⟨t, t_sub, t_card⟩ := Finset.le_card_iff_exists_subset_card.mp this
      use ⟨t, t_card⟩
      rw [← Finset.subset_compl_iff_disjoint_right]
      exact t_sub
    rw [Finset.card_compl, ← finrank_eq_card_basis b, s.prop, Nat.le_sub_iff_add_le' (by linarith)]
    rw [add_comm]
    exact hmn
  rw [LinearMap.ext_iff] at hx
  specialize hx <| (Basis.exteriorPower R m b) t
  rw [mulRight_apply, LinearMap.zero_apply, ← Module.Basis.sum_repr
    (Basis.exteriorPower R n b) x] at hx
  simp_rw [Subtype.ext_iff, hmul_val, Submodule.coe_sum, Finset.mul_sum, Submodule.coe_smul] at hx
  simp_rw [mul_smul_comm, ← hmul_val, ← Submodule.coe_smul, ← Submodule.coe_sum,
    ← Subtype.ext_iff] at hx
  rw [← Module.Basis.forall_coord_eq_zero_iff (Basis.exteriorPower R (m+n) b)] at hx
  specialize hx ⟨t ∪ s, by rw [Finset.card_union_of_disjoint h, s.prop, t.prop, add_comm]⟩
  simp_rw [map_sum, map_smul] at hx
  rw [Fintype.sum_eq_single s] at hx
  · rw [← Basis.coord_apply, basis_apply, basis_apply, ιMulti_family_mul_of_disjoint _ t s h] at hx
    simp only [Basis.coord_apply, map_smul, basis_repr_self, smul_eq_mul, mul_one,
      mul_eq_zero] at hx
    rcases hx with hx | hx
    · exact hx
    · rw [← Int.cast_zero, Int.cast_inj] at hx
      simp only [Units.ne_zero] at hx
  · intro s' hs'
    by_cases hs't : Disjoint t.val s'.val
    · rw [basis_apply, basis_apply, ιMulti_family_mul_of_disjoint _ t s' hs't, map_smul, ← mul_smul]
      apply smul_eq_zero_of_right
      rw [← basis_apply, Basis.coord_apply, Module.Basis.repr_self]
      apply Finsupp.single_eq_of_ne
      by_contra hss't
      rw [Subtype.mk.injEq, ← Finset.coe_inj, Finset.coe_union, Finset.coe_union] at hss't
      apply hs'
      rw [Subtype.ext_iff, ← Finset.subset_iff_eq_of_card_le (by simp [s.prop, s'.prop]),
        ← Finset.coe_subset]
      apply Disjoint.subset_right_of_subset_union (t := t.val)
      · simp only [hss't, Set.subset_union_right]
      · simp only [Finset.disjoint_coe, disjoint_comm, hs't]
    · rw [basis_apply, basis_apply, ιMulti_family_mul_of_not_disjoint _ t s' hs't]
      simp

end basis

end exteriorPower
