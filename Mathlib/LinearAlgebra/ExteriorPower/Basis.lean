/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Daniel Morrison
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import Mathlib.Order.Extension.Well
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.ExteriorPower.BasisIndex

/-!
# Constructs a basis for exterior powers
-/

@[expose] public section

variable {R K M E : Type*} {n : ℕ}
  [CommRing R] [Field K] [AddCommGroup M] [Module R M] [AddCommGroup E] [Module K E]

open BigOperators

namespace exteriorPower

/-! Finiteness of the exterior power. -/

/-- The `n`th exterior power of a finite module is a finite module. -/
instance instFinite [Module.Finite R M] : Module.Finite R (⋀[R]^n M) := by
  rw [Module.Finite.iff_fg, ExteriorAlgebra.exteriorPower, LinearMap.range_eq_map]
  exact Submodule.FG.pow (Submodule.FG.map _ Module.Finite.fg_top) n

/-! We construct a basis of `⋀[R]^n M` from a basis of `M`. -/

open Module

variable (R n)

/-- If `b` is a basis of `M` indexed by a linearly ordered type `I` and `s` is a finset of
`I` of cardinality `n`, then we get a linear form on the `n`th exterior power of `M` by
applying the `exteriorPower.linearForm` construction to the family of linear forms
given by the coordinates of `b` indexed by elements of `s` (ordered using the given order on
`I`). -/
noncomputable def ιMulti_dual {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : {a : Finset I // a.card = n}) : Module.Dual R (⋀[R]^n M) :=
  pairingDual R M n (ιMulti R n (fun i ↦ b.coord (Finset.orderIsoOfFin s.1 s.2 i)))

@[simp]
lemma ιMulti_dual_apply_ιMulti {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : {a : Finset I // a.card = n}) (v : Fin n → M) :
    ιMulti_dual R n b s (ιMulti R n v) =
    (Matrix.of fun i j => b.coord (Finset.orderIsoOfFin s.1 s.2 j) (v i)).det := by
  rw [ιMulti_dual, pairingDual_ιMulti_ιMulti]

/-- Let `b` be a basis of `M` indexed by a linearly ordered type `I` and `s` be a finset of `I`
of cardinality `n`. If we apply the linear form on `⋀[R]^n M` defined by `b` and `s`
to the exterior product of the `b i` for `i ∈ s`, then we get `1`. -/
lemma ιMulti_dual_apply_diag {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : {a : Finset I // a.card = n}) :
    ιMulti_dual R n b s (ιMulti_family R n b s) = 1 := by
  rw [ιMulti_family, ιMulti_dual_apply_ιMulti]
  suffices Matrix.of (fun i j => b.coord (Finset.orderIsoOfFin s.1 s.2 j)
    (b (Finset.orderIsoOfFin s.1 s.2 i))) = 1 by
    rw [this, Matrix.det_one]
  ext
  simp [Matrix.one_apply, Finsupp.single_apply]

lemma ιMulti_apply_nondiag_aux {I : Type*} [LinearOrder I]
    (s t : {a : Finset I // a.card = n}) (hst : s ≠ t) :
    ∃ (i : Fin n), ∀ (j : Fin n),
    (Finset.orderIsoOfFin s.1 s.2 i).1 ≠ (Finset.orderIsoOfFin t.1 t.2 j).1 := by
  by_contra! habs
  apply hst
  rw [Subtype.ext_iff]
  apply Finset.eq_of_subset_of_card_le _ (by rw [s.2, t.2])
  intro a has
  obtain ⟨b, hb⟩ := habs ((Finset.orderIsoOfFin s.1 s.2).symm ⟨a, has⟩)
  simp only [OrderIso.apply_symm_apply] at hb
  rw [hb]
  simp

/-- Let `b` be a basis of `M` indexed by a linearly ordered type `I` and `s` be a finset of `I`
of cardinality `n`. Let `t` be a finset of `I` of cardinality `n` such that `s ≠ t`. If we apply
the linear form on `⋀[R]^n M` defined by `b` and `s` to the exterior product of the
`b i` for `i ∈ t`, then we get `0`. -/
lemma ιMulti_dual_apply_nondiag {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s t : {a : Finset I // a.card = n}) (hst : s ≠ t) :
    ιMulti_dual R n b s (ιMulti_family R n b t) = 0 := by
  simp only [ιMulti_family]
  rw [ιMulti_dual_apply_ιMulti]
  obtain ⟨j, hi⟩ := ιMulti_apply_nondiag_aux n s t hst
  apply Matrix.det_eq_zero_of_column_eq_zero j
  intro j
  rw [Matrix.of_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne]
  exact hi j

/-- If `b` is a basis of `M` (indexed by a linearly ordered type), then the family
`exteriorPower.ιMulti R n b` of the `n`-fold exterior products of its elements is linearly
independent in the `n`th exterior power of `M`. -/
lemma ιMulti_family_linearIndependent_ofBasis {I : Type*} [LinearOrder I] (b : Basis I R M) :
    LinearIndependent R (ιMulti_family R n b) :=
  LinearIndependent.ofDualFamily _ (fun s ↦ ιMulti_dual R n b s)
    (fun _ _ h => ιMulti_dual_apply_nondiag R n b _ _ h)
    (fun _ => ιMulti_dual_apply_diag _ _ _ _)

/-- If `b` is a basis of `M` (indexed by a linearly ordered type), the basis of the `n`th
exterior power of `M` formed by the `n`-fold exterior products of elements of `b`. -/
noncomputable def _root_.Basis.exteriorPower {I : Type*} [LinearOrder I] (b : Basis I R M) :
    Basis (basisIndex I n) R (⋀[R]^n M) :=
  Basis.mk (ιMulti_family_linearIndependent_ofBasis _ _ _)
    (eq_top_iff.mp <| ιMulti_family_span_of_span R b.span_eq)

@[simp]
lemma coe_basis {I : Type*} [LinearOrder I] (b : Basis I R M) :
    DFunLike.coe (Basis.exteriorPower R n b) = ιMulti_family R n b :=
  Basis.coe_mk _ _

@[simp]
lemma basis_apply {I : Type*} [LinearOrder I] (b : Basis I R M) (s : basisIndex I n) :
    Basis.exteriorPower R n b s = ιMulti_family R n b s := by
  rw [coe_basis]

/-- If `b` is a basis of `M` indexed by a linearly ordered type `I` and `B` is the corresponding
basis of the `n`th exterior power of `M`, indexed by the set of finsets `s` of `I` of cardinality
`n`, then the coordinate function of `B` at `s` is the linear form on the `n`th exterior power
defined by `b` and `s` in `exteriorPower.ιMulti_dual`. -/
lemma basis_coord {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : basisIndex I n) :
    Basis.coord (Basis.exteriorPower R n b) s = ιMulti_dual R n b s := by
  apply LinearMap.ext_on (ιMulti_family_span_of_span R (Basis.span_eq b))
  rintro x ⟨t, rfl⟩
  rw [Basis.coord_apply]
  by_cases heq : s = t
  · rw [heq, ιMulti_dual_apply_diag, ← basis_apply, Basis.repr_self, Finsupp.single_eq_same]
  · rw [ιMulti_dual_apply_nondiag R n b s t heq, ← basis_apply,
      Basis.repr_self, Finsupp.single_eq_of_ne (by rw [ne_eq]; exact heq)]

lemma basis_repr_apply {I : Type*} [LinearOrder I] (b : Basis I R M) (x : ⋀[R]^n M)
    (s : basisIndex I n) :
    Basis.repr (Basis.exteriorPower R n b) x s = ιMulti_dual R n b s x := by
  rw [← Basis.coord_apply]
  congr
  exact basis_coord R n b s

@[simp]
lemma basis_repr_self {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : basisIndex I n) :
    Basis.repr (Basis.exteriorPower R n b) (ιMulti_family R n b s) s = 1 := by
  rw [basis_repr_apply]
  exact ιMulti_dual_apply_diag R n b s

@[simp]
lemma basis_repr_ne {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s t : basisIndex I n} (hst : s ≠ t) :
    Basis.repr (Basis.exteriorPower R n b) (ιMulti_family R n b s) t = 0 := by
  rw [basis_repr_apply]
  exact ιMulti_dual_apply_nondiag R n b t s (id (Ne.symm hst))

lemma basis_repr {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : basisIndex I n) :
    Basis.repr (Basis.exteriorPower R n b) (ιMulti_family R n b s) = Finsupp.single s 1 := by
  ext t
  by_cases hst : s = t <;> simp [hst]

lemma dualBasis_eq_ιMulti_dual {I : Type*} [Fintype I] [LinearOrder I] (b : Basis I R M)
    (s : basisIndex I n) :
    (Basis.exteriorPower R n b).dualBasis s = ιMulti_dual R n b s := by
  rw [Basis.coe_dualBasis, basis_coord]

lemma dualBasis_apply_eq_det {I : Type*} [Fintype I] [LinearOrder I] (b : Basis I R M)
    (s : basisIndex I n) (v : Fin n → M) :
    (Basis.exteriorPower R n b).dualBasis s (ιMulti R n v) =
    (Matrix.of fun i j => b.coord (Finset.orderIsoOfFin s.1 s.2 j) (v i)).det := by
  rw [dualBasis_eq_ιMulti_dual, ιMulti_dual_apply_ιMulti]

/-! ### The unique induced basis element of `⋀[R]^(finrank R V) M`. -/

noncomputable section volume

variable {R M : Type*}
  [CommRing R] [StrongRankCondition R] [AddCommGroup M] [Module R M]
  {I : Type*} [LinearOrder I] [Fintype I] (b : Basis I R M)

abbrev _root_.Module.Basis.volSet : basisIndex I (finrank R M) :=
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

/-! ### Linear equivalence with `AlternatingMap`. -/

noncomputable def toAlternatingMap {I : Type*} [Fintype I] [LinearOrder I] (b : Basis I R M) :
    ⋀[R]^n M ≃ₗ[R] (M [⋀^Fin n]→ₗ[R] R) :=
  (Basis.exteriorPower R n b).toDualEquiv.trans <| alternatingMapLinearEquiv.symm

lemma toAlternatingMap_basis {I : Type*} [Fintype I] [LinearOrder I] (b : Basis I R M)
    (s : basisIndex I n) :
    toAlternatingMap R n b (Basis.exteriorPower R n b s) =
    (((Basis.exteriorPower R n b).coord s).compAlternatingMap (ιMulti R n)) := by
  ext
  rw [toAlternatingMap, LinearEquiv.trans_apply, Basis.toDualEquiv_apply, Basis.coe_toDual_self,
    alternatingMapLinearEquiv_symm_apply]

lemma toAlternatingMap_basis_apply {I : Type*} [Fintype I] [LinearOrder I] (b : Basis I R M)
    (s : basisIndex I n) (a : Fin n → M) :
    toAlternatingMap R n b (Basis.exteriorPower R n b s) a =
    (Basis.exteriorPower R n b).coord s (ιMulti R n a) := by
  rw [toAlternatingMap_basis, LinearMap.compAlternatingMap_apply]

lemma toAlternatingMap_symm_coord {I : Type*} [Fintype I] [LinearOrder I] (b : Basis I R M)
    (s : basisIndex I n) (f : M [⋀^Fin n]→ₗ[R] R) :
    (Basis.exteriorPower R n b).coord s ((toAlternatingMap R n b).symm f) =
    f (fun i ↦ b (Finset.orderIsoOfFin s.1 s.2 i)) := by
  rw [toAlternatingMap, LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    Basis.coord_toDualEquiv_symm_apply, Basis.coord_apply, Basis.dualBasis_repr, basis_apply,
    ιMulti_family, alternatingMapLinearEquiv_apply_ιMulti]

/-! ### Freeness and dimension of `⋀[R]^n M. -/

/-- If `M` is a free module, then so is its `n`th exterior power. -/
instance instFree [hfree : Module.Free R M] : Module.Free R (⋀[R]^n M) :=
  have ⟨I, b⟩ := hfree.exists_basis
  letI : LinearOrder I := IsWellFounded.wellOrderExtension emptyWf.rel
  Module.Free.of_basis (Basis.exteriorPower R n b)

variable [StrongRankCondition R]

/-- If `R` satisfies the strong rank condition and `M` is finite free of rank `r`, then
the `n`th exterior power of `M` is of finrank `Nat.choose r n`. -/
lemma finrank_eq [hfree : Module.Free R M] [Module.Finite R M] :
    Module.finrank R (⋀[R]^n M) =
    Nat.choose (Module.finrank R M) n := by
  letI : LinearOrder hfree.ChooseBasisIndex := IsWellFounded.wellOrderExtension emptyWf.rel
  let B := Basis.exteriorPower R n hfree.chooseBasis
  rw [Module.finrank_eq_card_basis hfree.chooseBasis,
    Module.finrank_eq_card_basis B, Fintype.card_finset_len]

@[simp]
lemma bot_of_degree_gt_finrank [Module.Free R M] [Module.Finite R M] (hn : n > finrank R M) :
    ⋀[R]^n M = ⊥ := by
  rw [← Submodule.subsingleton_iff_eq_bot, ← Module.finrank_eq_zero_iff_of_free R, finrank_eq]
  exact Nat.choose_eq_zero_of_lt hn

@[simp]
lemma zero_of_degree_gt_finrank [Module.Free R M] [Module.Finite R M] (hn : n > finrank R M)
    (x : ⋀[R]^n M) : x = 0 := by
  rw [Subtype.ext_iff, ZeroMemClass.coe_zero, ← Submodule.mem_bot R,
    ← bot_of_degree_gt_finrank R n hn]
  exact Submodule.coe_mem x


/-! Results that only hold over a field. -/

/-- If `v` is a linearly independent family of vectors (indexed by a linearly ordered type),
then the family of its `n`-fold exterior products is also linearly independent. -/
lemma ιMulti_family_linearIndependent_field {I : Type*} [LinearOrder I] {v : I → E}
    (hv : LinearIndependent K v) : LinearIndependent K (ιMulti_family K n v) := by
  let W := Submodule.span K (Set.range v)
  let v' : I → W := fun i ↦ ⟨v i, Submodule.subset_span <| exists_apply_eq_apply _ _⟩
  have h : v = W.subtype ∘ v' := by
    ext x
    simp only [Submodule.coe_subtype, Function.comp_apply]
    rw [Subtype.val]
  rw [h, ← map_comp_ιMulti_family]
  refine LinearIndependent.map' ?_ (map n W.subtype)
    (LinearMap.ker_eq_bot.mpr (map_injective_field (Submodule.ker_subtype _)))
  have hv'span : ⊤ ≤ Submodule.span K (Set.range v') := by
    rintro x -
    rw [← Submodule.apply_mem_span_image_iff_mem_span (Submodule.injective_subtype W),
      ← Set.range_comp, ← h, Submodule.coe_subtype]
    exact SetLike.coe_mem _
  have heq : ιMulti_family K n v' =
      Basis.exteriorPower K n (Basis.mk (.of_comp W.subtype (h ▸ hv)) hv'span) := by
    rw [coe_basis, Basis.coe_mk]
  rw [heq]
  apply Basis.linearIndependent

instance instNonempty {I : Type*} [LinearOrder I] [Nonempty {v : I → E // LinearIndependent K v}] :
    Nonempty {v : {s : Finset I // Finset.card s = n} → (⋀[K]^n) E // LinearIndependent K v} :=
  Nonempty.map (fun v : {v : I → E // LinearIndependent K v} ↦
    ⟨ιMulti_family K n v, ιMulti_family_linearIndependent_field n v.2⟩) ‹_›

end exteriorPower
