import OhMyBourbakiSoul.MyNat.Basic
import OhMyBourbakiSoul.MyNat.OrderDef
import OhMyBourbakiSoul.MyNat.SegDef
import OhMyBourbakiSoul.MyBasic.MySet.Basic
import OhMyBourbakiSoul.MyBasic.MySet.OpsDef
import OhMyBourbakiSoul.MyBasic.MySet.Exclusive
import OhMyBourbakiSoul.MyBasic.MyOrd.Cmp
import OhMyBourbakiSoul.MyBasic.MyLogic.Propositional

open MyOrd
open MySet
open MyLogic

namespace MyNat

-- This proof is very classical, you may find
-- it on textbooks like Munkres easily.
theorem _well_order_inner
  {s : MySet MyNat} (h : s.exclusive) (n : MyNat):
  ((s ∩ seg n).nonempty) → (∃ x ∈ s, ∀ y ∈ s, x ≤ y) := by
  revert n
  apply mathematical_induction
  · intro hsz
    exfalso
    rw [seg_zero_is_empty] at hsz
    rw [intersect_empty] at hsz
    exact empty_not_nonempty hsz
  · intro n hp hsn
    have hse : Exclusive (s ∩ seg n).nonempty :=
      seg_induced_exclusive_emptiness h
    apply Or.elim hse
    · intro h'
      have h'' := hp h'
      rcases h'' with ⟨x, hx⟩
      exists x
    · intro h'
      exists n
      rcases hsn with ⟨n', hn'⟩
      rw [<-mem_def] at hn'
      rcases hn' with ⟨hn's, hn'n⟩
      rw [mem_succ_seg_iff] at hn'n
      apply And.intro
      · have hnn' : n = n' := by
          match (cmp n n') with
            | MyCmp.lt hlt =>
              rw [<-MyComparableOrd.not_ge_iff_lt] at hlt
              rw [ge_iff_le] at hlt
              contradiction
            | MyCmp.eq heq =>
              exact heq
            | MyCmp.gt hgt =>
              have : (s ∩ seg n).nonempty := by
                exists n'
              contradiction
        rw [<-hnn'] at hn's
        exact hn's
      · intro y hy
        rw [<-MyComparableOrd.not_gt_iff_le]
        intro hyn
        rw [gt_iff_lt] at hyn
        have : (s ∩ seg n).nonempty := by
          exists y
        contradiction

theorem well_order
  {s : MySet MyNat} (h : s.exclusive) :
  (s.nonempty) → (∃ x ∈ s, ∀ y ∈ s, x ≤ y) := by
  intro h
  rcases h with ⟨n, hn⟩
  apply _well_order_inner h (succ n)
  exists n
  rw [<-mem_def]
  apply And.intro
  · exact hn
  · rw [mem_succ_seg_iff]
    exact le_refl

-- We need it to be decidable in order to
-- excavate the infimum, however.
def well_order_mu {s : MySet MyNat}
  [D : s.decidable] (h₁ : s.nonempty) :
  { x : MyNat // (x ∈ s) ∧ (∀ y ∈ s, x ≤ y) } := by
  have h₀ : s.exclusive := by
    intro x
    apply exclusive_if_decidable

  have hex : ∃ x, (x ∈ s) := by
    rcases h₁ with ⟨x, hx⟩
    exists x

  have m := MyNat.mu hex
  apply Subtype.mk m.val
  apply And.intro
  · exact m.sufficient
  · intro y hys
    have h := modus_tollens_neg (m.minimal y)
    rw [<-MyComparableOrd.not_gt_iff_le]
    exact h hys

end MyNat
