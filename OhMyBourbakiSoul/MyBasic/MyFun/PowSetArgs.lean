import OhMyBourbakiSoul.MyBasic.MyFun.Basic
import OhMyBourbakiSoul.MyBasic.MyLogic.Propositional
import OhMyBourbakiSoul.MyBasic.MySet.OpsDef
import OhMyBourbakiSoul.MyBasic.MySet.Subtype

universe u v
variable {α : Type u}
variable {X : MySet α}

open MySet
open MyLogic

-- If f: X → 𝒫(X) were surjecive, consider the
-- preimage x' of { x ∈ X | x ∉ f(x) } ∈ 𝒫(X):
-- If x' ∈ f(x'), then x' ∉ f(x') by definition.
-- If x' ∉ f(x'), then x' ∈ f(x') by definition.
-- And x' ∈ f(x') ↔ x' ∉ f(x') leads to paradox.
theorem no_surjection_powerset :
  ∀ f : X -→ 𝒫 X, ¬(f.surj) := by
  intro f Sf
  generalize hs : unlift_subtype { x ∈ X | x.val ∉ (f x).val } = s
  have hs'X : s ⊆ X := by
    rw [<-hs]
    apply unlift_subset
  rw [<-powerset_def] at hs'X
  rw [mem_def] at hs'X
  generalize hs' : Subtype.mk s hs'X = s'
  have h := Sf.surj s'
  rcases h with ⟨x, hx⟩

  have h₀ : x.val ∈ s → x.val ∉ s := by
    intro hxs
    rw [<-hs] at hxs
    unfold unlift_subtype at hxs
    change ∃ (x' : X.type),
      (x.val = x'.val) ∧
      (¬x'.val ∈ (f.coe_fn x').val) at hxs
    rcases hxs with ⟨x', hx'⟩
    rcases hx' with ⟨hxx', hx's⟩
    rw [<-Subtype.eq_iff] at hxx'
    rw [<-hxx'] at hx's
    rw [hx] at hx's
    have hs' : s'.val = s := by
      rw [<-hs']
    rw [<-hs']
    exact hx's

  have h₁ : x.val ∉ s → x.val ∈ s := by
    intro hnxs
    rw [<-hs'] at hx
    rw [Subtype.eq_iff] at hx
    change (f x).val = s at hx
    unfold unlift_subtype at hs
    rw [mem_def]
    rw [<-hs]
    change ∃ (x' : X.type),
      (x.val = x'.val) ∧
      (¬x'.val ∈ (f.coe_fn x').val)
    exists x
    apply And.intro
    · rfl
    · rw [<-hx] at hnxs
      exact hnxs

  have h := Iff.intro h₀ h₁
  exact contra_with_iff_not h

theorem no_bijection_powerset :
  ∀ f : X -→ 𝒫 X, ¬(f.bij) := by
  intro f Bf
  exact no_surjection_powerset f Bf.toMySurj
