import OhMyBourbakiSoul.MyBasic.MyFun.Basic
import OhMyBourbakiSoul.MyBasic.MyLogic.Propositional
import OhMyBourbakiSoul.MyBasic.MySet.OpsDef
import OhMyBourbakiSoul.MyBasic.MySet.Restrict

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
  generalize hs : { x ∈ X | x.val ∉ (f x).val } = s
  have hs'X : s ⊆ X := by
    rw [<-hs]
    exact restrict_subset
  rw [<-powerset_def] at hs'X
  rw [mem_def] at hs'X
  generalize hs' : Subtype.mk s hs'X = s'
  have h := Sf.surj s'
  rcases h with ⟨x, hx⟩

  have h₀ : x.val ∈ s → x.val ∉ s := by
    intro hxs
    rw [<-hs] at hxs
    rw [restrict_def] at hxs
    change x.val ∉ (f x).val at hxs
    rw [hx] at hxs
    rw [<-hs'] at hxs
    change x.val ∉ s at hxs
    exact hxs

  have h₁ : x.val ∉ s → x.val ∈ s := by
    intro hnxs
    rw [<-hs'] at hx
    rw [Subtype.eq_iff] at hx
    change (f x).val = s at hx
    rw [<-hs]
    rw [restrict_def]
    change x.val ∉ (f x).val
    rw [hx]
    exact hnxs

  have h := Iff.intro h₀ h₁
  exact contra_with_iff_not h

theorem no_bijection_powerset :
  ∀ f : X -→ 𝒫 X, ¬(f.bij) := by
  intro f Bf
  exact no_surjection_powerset f Bf.toMySurj
