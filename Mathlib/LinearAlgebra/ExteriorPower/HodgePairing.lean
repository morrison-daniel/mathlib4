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

noncomputable section hodgePairing

variable {R M : Type*} {m n : ℕ} [Field R] [AddCommGroup M] [Module R M]
  {I : Type*} [LinearOrder I] [Fintype I] (b : Basis I R M)

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
