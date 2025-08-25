import OhMyBourbakiSoul.MyBasic.MySet.Basic
import OhMyBourbakiSoul.MyBasic.MyFun.Basic

open MySet

universe u v w
variable {α : Type u} {β : Type v}
variable {X : MySet α} {Y : MySet β}

namespace MyFun

def empty (X : MySet α) (Y : MySet β) (h₀ : X = ∅) : X -→ Y := by
  apply MyFun.mk
  intro x
  exfalso
  have h := x.membership
  subst h₀
  have := empty_def x.val
  contradiction

theorem empty_surj_if (g : X -→ Y) : (Y = ∅) → g.surj := by
  intro h₁
  apply MySurj.mk
  intro y
  exfalso
  have h := y.membership
  subst h₁
  have := empty_def y.val
  contradiction

theorem empty_domain_if_empty_codomain
  {f : X -→ Y} :
  (f.codomain = ∅) → (f.domain = ∅) := by
  intro h
  rw [<-empty_iff] at h
  rw [<-empty_iff]
  intro x hx
  have y := f ⟨x, hx⟩
  have := h y.val
  have := y.membership
  contradiction

theorem empty_range_iff_empty_domain
  {f : X -→ Y} :
  (f.range = ∅) ↔ (f.domain = ∅) := by
  repeat rw [<-empty_iff]
  apply Iff.intro
  · intro h x hx
    have x' : Subtype X := ⟨x, hx⟩
    have : (f x').val ∈ f.range := range_def x'
    have := h (f x').val
    contradiction
  · intro h y hy
    rw [range_mem] at hy
    rcases hy with ⟨x, hx⟩
    have := x.membership
    have := h x.val
    contradiction

end MyFun
