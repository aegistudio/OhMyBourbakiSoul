import OhMyBourbakiSoul.MyBasic.MySet.Basic
import OhMyBourbakiSoul.MyBasic.MyOrd.Basic
import OhMyBourbakiSoul.MyBasic.MyOrd.Compat
import OhMyBourbakiSoul.MyBasic.MyOrd.Custom
import OhMyBourbakiSoul.MyBasic.MyOrd.Induced

universe u
variable {α : Type u}

namespace MySet

def subset (s₁ s₂ : MySet α) : Prop :=
  ∀ (a : α), (a ∈ s₁) → (a ∈ s₂)

instance instHasSubset : HasSubset (MySet α) where
  Subset := subset

theorem subset_def {s₁ s₂ : MySet α} :
  (s₁ ⊆ s₂) ↔ (∀ a ∈ s₁, a ∈ s₂) := by rfl

theorem empty_subset {s : MySet α} : ∅ ⊆ s := by
  rw [subset_def]
  intro a ha
  exfalso
  have : a ∉ ∅ := empty_def a
  contradiction

theorem subset_refl {s : MySet α} : s ⊆ s := by
  rw [subset_def]
  intro a ha
  exact ha

theorem subset_trans {s₁ s₂ s₃ : MySet α} :
  (s₁ ⊆ s₂) → (s₂ ⊆ s₃) → (s₁ ⊆ s₃) := by
  intro hs₁s₂ hs₂s₃
  rw [subset_def]
  rw [subset_def] at hs₁s₂ hs₂s₃
  intro a has₁
  have has₂ := (hs₁s₂ a) has₁
  have has₃ := (hs₂s₃ a) has₂
  exact has₃

theorem subset_antisymm {s₁ s₂ : MySet α} :
  (s₁ ⊆ s₂) → (s₂ ⊆ s₁) → (s₁ = s₂) := by
  intro hs₁s₂ hs₂s₁
  rw [eq_iff]
  rw [subset_def] at hs₁s₂ hs₂s₁
  intro a
  apply Iff.intro
  · intro has₁
    exact (hs₁s₂ a) has₁
  · intro has₂
    exact (hs₂s₁ a) has₂

section

open MyOrd
open MyOrd.MyCompatOrd
open MyOrd.MyCustomPartialOrd
open MyOrd.MyInduceStrict

instance instSubsetCustomOrd : MyCustomPartialOrd (MySet α) where
  op := subset
  op_refl := subset_refl
  op_trans := subset_trans
  op_antisymm := subset_antisymm

theorem subset_iff_lift_le (s₁ s₂ : MySet α) :
  (s₁ ⊆ s₂) ↔ ((lift_le s₁) ≤ (lift_le s₂)) := by
  rw [lift_le_iff]
  change (s₁ ⊆ s₂ ↔ subset s₁ s₂)
  rfl

def ssubset (s₁ s₂ : MySet α) : Prop := (s₁ ⊆ s₂) ∧ (s₁ ≠ s₂)

instance instHasSSubset : HasSSubset (MySet α) where
  SSubset := ssubset

theorem ssubset_def {s₁ s₂ : MySet α} :
  (s₁ ⊂ s₂) ↔ (s₁ ⊆ s₂) ∧ (s₁ ≠ s₂) := by rfl

instance instSubsetPartialOrd : MyPartialOrd (Lift (MySet α)) :=
  instLiftedPartialOrd

instance instInducedStrict : MyInduceStrict (Lift (MySet α)) where

theorem ssubset_iff_lift_lt (s₁ s₂ : MySet α) :
  (s₁ ⊂ s₂) ↔ ((lift_le s₁) < (lift_le s₂)) := by
  rw [ssubset_def]
  change s₁ ⊆ s₂ ∧ ¬(s₁ = s₂) ↔ lift_le s₁ < lift_le s₂
  rw [subset_iff_lift_le]
  rw [<-lift_eq_iff]
  rw [induced_lt_def]

theorem ssubset_irrefl {s : MySet α} : ¬(s ⊂ s) := by
  repeat rw [ssubset_iff_lift_lt]
  exact induced_lt_irrefl

theorem ssubset_trans {s₁ s₂ s₃ : MySet α} :
  (s₁ ⊂ s₂) → (s₂ ⊂ s₃) → (s₁ ⊂ s₃) := by
  repeat rw [ssubset_iff_lift_lt]
  exact induced_lt_trans

theorem ssubset_asymm {s₁ s₂ : MySet α} :
  (s₁ ⊂ s₂) → ¬(s₂ ⊂ s₁) := by
  repeat rw [ssubset_iff_lift_lt]
  exact induced_lt_asymm

theorem ssubset_of_ssubset_of_subset {s₁ s₂ s₃ : MySet α} :
  (s₁ ⊂ s₂) → (s₂ ⊆ s₃) → (s₁ ⊂ s₃) := by
  repeat rw [ssubset_iff_lift_lt]
  rw [subset_iff_lift_le]
  apply lt_of_lt_of_le

theorem ssubset_of_subset_of_ssubset {s₁ s₂ s₃ : MySet α} :
  (s₁ ⊆ s₂) → (s₂ ⊂ s₃) → (s₁ ⊂ s₃) := by
  repeat rw [ssubset_iff_lift_lt]
  rw [subset_iff_lift_le]
  apply lt_of_le_of_lt

end

end MySet

-- Theorems derivable from the definitions above.
namespace MySet

theorem eq_iff_subset_and_supset {s₁ s₂ : MySet α} :
  (s₁ = s₂) ↔ (s₁ ⊆ s₂) ∧ (s₁ ⊇ s₂) := by
  repeat rw [subset_iff_lift_le s₁ s₂]
  rw [Superset]
  repeat rw [subset_iff_lift_le s₂ s₁]
  rw [<-MyOrd.eq_iff_le_and_ge]
  repeat rw [MyOrd.MyCustomPartialOrd.lift_eq_iff]

end MySet
