/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.ExteriorPower.Mul
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Constructs the Hodge pairing on the exterior product
-/

@[expose] public section

open BigOperators Module

namespace exteriorPower

noncomputable section volume

variable {R M : Type*}
  [CommRing R] [StrongRankCondition R] [AddCommGroup M] [Module R M]
  {I : Type*} [LinearOrder I] [Fintype I] (b : Basis I R M)

abbrev _root_.Module.Basis.volSet : {a : Finset I // a.card = finrank R M} :=
    ⟨Finset.univ, by rw [finrank_eq_card_basis b, Finset.card_univ]⟩

/-- The induced element of maximal rank by the basis `b` on `M`. -/
abbrev _root_.Module.Basis.vol : ⋀[R]^(finrank R M) M :=
    ιMulti_family R (finrank R M) b b.volSet

@[simp]
lemma ιMulti_family_volSet_eq_vol :
    ιMulti_family R (finrank R M) b b.volSet = b.vol := rfl

lemma span_vol_eq_top : Submodule.span R {b.vol} = ⊤ := by
  rw [Submodule.eq_top_iff_forall_basis_mem (Basis.exteriorPower R (finrank R M) b)]
  rintro s
  suffices s = b.volSet by
    rw [this]
    apply Submodule.mem_span_of_mem
    rw [Set.mem_singleton_iff]
    exact basis_apply R (finrank R M) b b.volSet
  rw [Subtype.ext_iff]
  apply Finset.eq_of_subset_of_card_le (by simp)
  rw [s.2, b.volSet.2]

@[simp]
lemma volSet_repr_vol : ((Basis.exteriorPower R (finrank R M) b).repr b.vol) b.volSet = 1 := by
  simp only [basis_repr_self]

@[simp]
lemma volSet_repr (x : ⋀[R]^(finrank R M) M) :
    ((Basis.exteriorPower R (finrank R M) b).repr x) b.volSet • b.vol = x := by
  obtain ⟨r, rfl⟩ := (Submodule.span_singleton_eq_top_iff R b.vol).mp (span_vol_eq_top b) x
  simp

@[simp]
lemma volSet_coord (x : ⋀[R]^(finrank R M) M) :
    ((Basis.exteriorPower R (finrank R M) b).coord b.volSet x) • b.vol = x := by
  simp

def volEquiv : ⋀[R]^(finrank R M) M ≃ₗ[R] R where
  toFun := (Basis.exteriorPower R (finrank R M) b).coord b.volSet
  map_add' x y := by simp only [Basis.coord_apply, map_add]
  map_smul' r x := by simp only [map_smul, Basis.coord_apply, smul_eq_mul, RingHom.id_apply]
  invFun r := r • b.vol
  left_inv := by rw [Function.leftInverse_iff_comp]; ext; simp
  right_inv := by rw [Function.rightInverse_iff_comp]; ext; simp

variable (x : ⋀[R]^(finrank R M) M) (r : R)

lemma volEquiv_apply :
    volEquiv b x = (Basis.exteriorPower R (finrank R M) b).coord b.volSet x := rfl

@[simp]
lemma volEquiv_symm_apply : (volEquiv b).symm r = r • b.vol := rfl

@[simp]
lemma volEquiv_vol : volEquiv b b.vol = 1 := by
  rw [volEquiv_apply, Basis.coord_apply, basis_repr_self]

@[simp]
lemma volEquiv_smul : volEquiv b x • b.vol = x := by simp [volEquiv_apply]

lemma repr_volSet_eq_volEquiv :
    (Basis.exteriorPower R (finrank R M) b).repr x b.volSet = volEquiv b x := rfl

end volume

noncomputable section hodgePairing

variable {R M : Type*} {m n : ℕ}
  [Field R] [AddCommGroup M] [Module R M]
  {I : Type*} [LinearOrder I] [Fintype I]


variable (b : Basis I R M)

def hodgePairing (h : m + n = finrank R M) : ⋀[R]^m M →ₗ[R] ⋀[R]^n M →ₗ[R] R :=
  LinearMap.compr₂ (mulLeft R M m n) ((cast R h).trans (volEquiv b))

def hodgePairing_apply_apply (x : ⋀[R]^m M) (y : ⋀[R]^n M) (h : m + n = finrank R M) :
    hodgePairing b h x y = volEquiv b (cast R h (x * y)) := rfl

lemma hodgePairing_flip (h : m + n = finrank R M) : (hodgePairing b h).flip =
    LinearMap.compr₂ (mulRight R M m n) ((cast R h).trans (volEquiv b)) := by
  ext x y
  simp [hodgePairing_apply_apply, mulRight]

open LinearMap

lemma hodgePairing_injective [NoZeroDivisors R] [CharZero R] [StrongRankCondition R]
    (h : m + n = finrank R M) :
    Function.Injective (hodgePairing b h) := by
  rw [hodgePairing]
  apply LinearMap.injective_compr₂_of_injective
  · exact mulLeft_injective b (le_of_eq h)
  · exact ((cast R h).trans (volEquiv b)).injective

lemma hodgePairing_flip_injective [NoZeroDivisors R] [CharZero R] [StrongRankCondition R]
    (h : m + n = finrank R M) :
    Function.Injective (hodgePairing b h).flip := by
  rw [hodgePairing_flip]
  apply LinearMap.injective_compr₂_of_injective
  · exact mulRight_injective b (le_of_eq h)
  · exact ((cast R h).trans (volEquiv b)).injective

variable [FiniteDimensional R M] [NoZeroDivisors R] [CharZero R] [StrongRankCondition R]

instance instPerfPair (h : m + n = finrank R M) : IsPerfPair (hodgePairing b h) := by
  apply IsPerfPair.of_injective
  · exact hodgePairing_injective b h
  · exact hodgePairing_flip_injective b h

def hodgeStar (h : m + n = finrank R M) : ⋀[R]^m M ≃ₗ[R] ⋀[R]^n M :=
    (hodgePairing b h).toPerfPair.trans (Basis.exteriorPower R n b).toDualEquiv.symm

lemma hodgeStar_apply (h : m + n = finrank R M) (x : ⋀[R]^m M) :
    hodgeStar b h x = (Basis.exteriorPower R n b).toDualEquiv.symm (hodgePairing b h x) := rfl

lemma hodgeStar_eq (h : m + n = finrank R M) (x : ⋀[R]^m M) (y : ⋀[R]^n M) :
    hodgeStar b h x = y ↔ cast R h (x * y) = b.vol := by
  rw [hodgeStar_apply, hodgePairing]
  constructor
  · rintro rfl
    ext
    rw [val_cast, hmul_val]
    sorry
  · intro h
    rw [LinearEquiv.symm_apply_eq, Basis.toDualEquiv_apply]
    apply Module.Basis.ext (Basis.exteriorPower R n b)
    intro s
    rw [compr₂_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, Module.Basis.toDual_apply_left]
    rw [mulLeft_apply, ← LinearEquiv.eq_symm_apply, volEquiv_symm_apply, ← h, ← map_smul]
    congr
    sorry

end hodgePairing

end exteriorPower
