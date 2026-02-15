/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Basis for `ExteriorAlgebra`
-/

@[expose] public section

namespace ExteriorAlgebra

open Module Set Set.powersetCard exteriorPower

variable {R K M E : Type*} {n : ℕ} {I : Type*} [LinearOrder I] [CommRing R] [Field K]
  [AddCommGroup M] [Module R M] [AddCommGroup E] [Module K E] (b : Module.Basis I R M)

/-- If `b` is a basis of `M` (indexed by a linearly ordered type), the basis of the exterior
algebra of `M` formed by the `n`-fold exterior products of elements of `b` for each `n`. -/
noncomputable def _root_.Module.Basis.ExteriorAlgebra : Basis (Finset I) R (ExteriorAlgebra R M) :=
  Module.Basis.reindex (DirectSum.IsInternal.collectedBasis
  (DirectSum.Decomposition.isInternal (fun n => ⋀[R]^n M)) (fun n => b.exteriorPower n))
  Set.powersetCard.prodEquiv

lemma basis_apply (s : Finset I) :
    b.ExteriorAlgebra s = ιMulti_family R s.card b (prodEquiv.symm s).2 := by
  rw [Basis.ExteriorAlgebra]
  simp
  rfl

lemma basis_apply_ofCard {s : Finset I} (s_card : s.card = n) :
    b.ExteriorAlgebra s = ιMulti_family R n b (ofCard s_card) := by
  rw [basis_apply]
  subst s_card
  rfl

lemma basis_eq_coe_basis (s : powersetCard I n) :
    b.ExteriorAlgebra s = (b.exteriorPower n s : ExteriorAlgebra R M) := by
  rw [basis_apply_ofCard, exteriorPower.basis_apply, ιMulti_family_apply_coe]
  · rfl
  · exact card_eq s

end ExteriorAlgebra
