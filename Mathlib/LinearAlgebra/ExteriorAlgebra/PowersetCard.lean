/-
Copyright (c) 2026 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
module

public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination

@[expose] public section

open Finset Function Set

namespace Set.powersetCard

section basic

variable {α β : Type*} {n : ℕ}

instance instFintype [Fintype α] : Fintype (powersetCard α n) :=
  inferInstanceAs (Fintype {a : Finset α // a.card = n})

lemma exists_mem_notMem_of_ne (s t : powersetCard α n) : s ≠ t ↔ ∃ a ∈ s, a ∉ t := by
  simp_rw [← SetLike.mem_coe, ← not_subset_iff_exists_mem_notMem]
  exact eq_iff_subset.not

def ofCard {s : Finset α} (hs : s.card = n) : powersetCard α n := ⟨s, hs⟩

@[simp]
lemma mem_ofCard_iff_mem {s : Finset α} (hs : s.card = n) (i : α) :
    i ∈ ofCard hs ↔ i ∈ s := by
  rfl

@[simp]
lemma coe_ofCard {s : Finset α} (hs : s.card = n) : SetLike.coe (ofCard hs) = ↑s := rfl

@[simp]
lemma val_ofCard {s : Finset α} (hs : s.card = n) : Subtype.val (ofCard hs) = s := rfl

variable (n)

def ofFin : powersetCard (Fin n) n :=
    ofCard (s := Finset.univ) (by rw [Finset.card_univ, Fintype.card_fin])

@[simp]
lemma mem_ofFin (i : Fin n) : i ∈ ofFin n := by
  rw [ofFin, mem_ofCard_iff_mem]
  exact Finset.mem_univ i

@[simp]
lemma coe_ofFin : SetLike.coe (ofFin n) = Set.univ := by
  ext
  simp [SetLike.mem_coe]

@[simp]
lemma val_ofFin : Subtype.val (ofFin n) = Finset.univ := rfl

def map (f : α ↪ β) (s : powersetCard α n) : powersetCard β n :=
    ⟨Finset.map f s, by rw [mem_iff, card_map, s.prop]⟩

lemma mem_map_iff_mem_range (f : α ↪ β) (s : powersetCard α n) (b : β) :
    b ∈ map n f s ↔ b ∈ f '' s := by
  simp [map]
  rfl

@[simp]
lemma coe_map (f : α ↪ β) (s : powersetCard α n) : SetLike.coe (map n f s) = f '' s := by
  ext
  simp [mem_map_iff_mem_range]

@[simp]
lemma val_map (f : α ↪ β) (s : powersetCard α n) : Subtype.val (map n f s) = s.val.map f := rfl

variable {n}

def ofFinEmb (f : Fin n ↪ β) : powersetCard β n := map n f (ofFin n)

lemma mem_ofFinEmb_iff_mem_range (f : Fin n ↪ β) (b : β) :
    b ∈ ofFinEmb f ↔ b ∈ Set.range f := by
  simp [ofFinEmb, mem_map_iff_mem_range]

lemma coe_ofFinEmb (f : Fin n ↪ β) : SetLike.coe (ofFinEmb f) = Set.range f := by
  ext
  simp [mem_ofFinEmb_iff_mem_range]

lemma val_ofFinEmb [DecidableEq β] (f : Fin n ↪ β) :
    Subtype.val (ofFinEmb f) = Finset.univ.image f := by
  simp [← coe_inj, coe_ofFinEmb]

end basic

section order

variable {I : Type*} [LinearOrder I] {n : ℕ}

def ofFinEmbEquiv : (Fin n ↪o I) ≃ powersetCard I n where
  toFun f := ofFinEmb f.toEmbedding
  invFun s := Finset.orderEmbOfFin s.val s.prop
  left_inv f := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro
    simp [mem_coe_iff, mem_ofFinEmb_iff_mem_range]
  right_inv s := by
    dsimp
    ext
    simp [mem_coe_iff, mem_ofFinEmb_iff_mem_range]

lemma ofFinEmbEquiv_apply (f : Fin n ↪o I) : ofFinEmbEquiv f = ofFinEmb f.toEmbedding := rfl

lemma mem_ofFinEmbEquiv_iff_mem (f : Fin n ↪o I) (i : I) :
    i ∈ ofFinEmbEquiv f ↔ i ∈ Set.range f := by
  rw [ofFinEmbEquiv_apply, mem_ofFinEmb_iff_mem_range, RelEmbedding.coe_toEmbedding]

lemma ofFinEmbEquiv_symm_apply (s : powersetCard I n) :
    ofFinEmbEquiv.symm s = Finset.orderEmbOfFin s.val s.prop := rfl

lemma mem_range_ofFinEmbEquiv_symm_iff_mem {s : powersetCard I n} {i : I} :
    i ∈ Set.range (ofFinEmbEquiv.symm s) ↔ i ∈ s := by
  simp [ofFinEmbEquiv_symm_apply, range_orderEmbOfFin]

end order

end Set.powersetCard
