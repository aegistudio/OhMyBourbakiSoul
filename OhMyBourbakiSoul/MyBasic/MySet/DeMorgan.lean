import OhMyBourbakiSoul.MyBasic.MySet.OpsDef
import OhMyBourbakiSoul.MyBasic.MySet.Subtype
import OhMyBourbakiSoul.MyBasic.MySet.Exclusive
import OhMyBourbakiSoul.MyBasic.MyLogic.Quantifier

universe u
variable {α : Type u}

namespace MySet

open MyLogic

theorem elem_bigcap_complement_iff
  {A : MySet (MySet α)} {x : α} :
  (x ∈ ⋂ { aᶜ || a ∈ A }) ↔ (∀ a ∈ A, x ∉ a) := by
  rw [bigcap_def]
  apply Iff.intro
  · intro h a haA hxa
    have h' := h aᶜ
    rw [transform_def] at h'
    have ha'A : ∃ a', a' ∈ A ∧ aᶜ = a'ᶜ := by
      exists a
    have hxa' := h' ha'A
    rw [complement_def] at hxa'
    contradiction
  · intro h a' ha'
    rw [transform_def] at ha'
    rcases ha' with ⟨a, ha⟩
    rw [And.right ha]
    rw [complement_def]
    apply h a (And.left ha)

theorem demorgan_univ_bigcup {A : MySet (MySet α)}:
  (⋃ A)ᶜ = ⋂ { aᶜ || a ∈ A } := by
  rw [eq_iff]
  intro x
  rw [complement_def]
  rw [bigcup_def]
  rw [elem_bigcap_complement_iff]
  symm
  exact forall_in_not_iff_not_exists_in

-- WARN: if not inhabited, when B = ∅, and a ≠ univ,
-- there's lhs = a while the rhs = univ.
theorem demorgan_inhabited_bigcup
  {a b₀ : MySet α} {B : MySet (MySet α)} :
  (b₀ ∈ B) →
  (a \ (⋃ B)) = (⋂ { a \ b || b ∈ B }) := by
  intro hb₀
  rw [sdiff_eq_cap_complement]
  rw [intersect_comm]
  rw [demorgan_univ_bigcup]
  have hb₀' : b₀ᶜ ∈ { bᶜ || b ∈ B } := by
    rw [transform_def]
    exists b₀
  rw [bigcap_inhabited_intersect_distrib hb₀']
  rw [transform_compose]
  have hf : (λ x => xᶜ ∩ a) = (λ x => a \ x) := by
    funext x
    rw [intersect_comm]
    rw [sdiff_eq_cap_complement]
  rw [hf]

theorem demorgan_nonempty_bigcup
  {a : MySet α} {B : MySet (MySet α)}
  (h : B.nonempty) :
  (a \ (⋃ B)) = (⋂ { a \ b || b ∈ B }) := by
  rcases h with ⟨b₀, hb₀⟩
  rw [<-mem_def (s := B)] at hb₀
  exact demorgan_inhabited_bigcup hb₀

theorem elem_bigcup_complement_iff
  {A : MySet (MySet α)} {x : α} :
  (x ∈ ⋃ { aᶜ || a ∈ A }) ↔ (∃ a ∈ A, x ∉ a) := by
  rw [bigcup_def]
  apply Iff.intro
  · intro h
    rcases h with ⟨a', ha'⟩
    rcases ha' with ⟨ha'Ac, hxa'⟩
    rw [transform_def] at ha'Ac
    rcases ha'Ac with ⟨a, ha⟩
    exists a
    apply And.intro
    · exact And.left ha
    · rw [<-complement_def]
      rw [And.right ha] at hxa'
      exact hxa'
  · intro h
    rcases h with ⟨a, ha⟩
    exists aᶜ
    apply And.intro
    · apply transform_mem
      exact And.left ha
    · exact And.right ha

theorem demorgan_univ_bigcap_if_non_universal_witness
  {A : MySet (MySet α)} :
  (∀ (x : α), ¬(∀ a ∈ A, x ∈ a) → (∃ a ∈ A, x ∉ a)) →
  (⋂ A)ᶜ = ⋃ { aᶜ || a ∈ A } := by
  intro h₀
  rw [eq_iff]
  intro x
  rw [complement_def]
  rw [bigcap_def]
  rw [elem_bigcup_complement_iff]
  apply Iff.intro
  · exact h₀ x
  · exact not_forall_in_if_exists_in_not

theorem demorgan_bigcap_if_non_universal_witness
  {a : MySet α} {B : MySet (MySet α)} :
  (∀ (x : α), ¬(∀ b ∈ B, x ∈ b) → (∃ b ∈ B, x ∉ b)) →
  (a \ (⋂ B)) = (⋃ { a \ b || b ∈ B }) := by
  intro h₀
  rw [sdiff_eq_cap_complement]
  rw [intersect_comm]
  rw [demorgan_univ_bigcap_if_non_universal_witness h₀]
  rw [bigcup_intersect_distrib]
  rw [transform_compose]
  have hf : (λ b => bᶜ ∩ a) = (λ b => a \ b) := by
    funext b
    rw [intersect_comm]
    symm
    exact sdiff_eq_cap_complement
  rw [hf]

theorem subset_double_complement
  {s : MySet α} : (s ⊆ (sᶜ)ᶜ) := by
  rw [subset_def]
  intro x hxs
  rw [complement_def]
  intro hxs'
  rw [complement_def] at hxs'
  contradiction

-- This is again a LEM → DNE argument,
-- see also the DoYouKnowEverything.lean
-- for templates of such kind of arguments.
theorem double_complement_eq_self_if_exclusive_mem
  {s : MySet α} :
  (s.exclusive) → (s = (sᶜ)ᶜ) := by
  intro h
  rw [eq_iff]
  intro x
  apply Iff.intro
  · intro hxs
    intro hxs'
    contradiction
  · intro hxs'
    rw [complement_def] at hxs'
    apply (h x).by_contra
    intro hnxs
    rw [<-mem_def (s := s)] at hnxs
    exfalso
    rw [complement_def] at hxs'
    contradiction

theorem complement_exclusive_mem_if_exclusive_mem
  {s : MySet α} :
  (s.exclusive) → ((sᶜ).exclusive) := by
  intro h x
  apply Or.elim (h x)
  · intro hxs
    right
    intro hxs'
    rw [<-mem_def (s := sᶜ)] at hxs'
    rw [complement_def] at hxs'
    contradiction
  · intro hxs'
    left
    rw [<-mem_def (s := s)] at hxs'
    rw [<-complement_def] at hxs'
    exact hxs'

theorem bigcap_complement_exclusive_mem_if_bigcup_exclusive_mem
  {A : MySet (MySet α)} :
  ((⋃ A).exclusive) →
  ((⋂ { aᶜ || a ∈ A }).exclusive) := by
  intro h
  rw [<-demorgan_univ_bigcup]
  apply complement_exclusive_mem_if_exclusive_mem
  exact h

end MySet
