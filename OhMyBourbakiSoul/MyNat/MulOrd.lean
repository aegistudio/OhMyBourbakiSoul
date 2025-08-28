import OhMyBourbakiSoul.MyNat.MulDef
import OhMyBourbakiSoul.MyNat.OrderDef
import OhMyBourbakiSoul.MyNat.MonusDef

open MyLogic
open MyOrd

namespace MyNat

-- Note, we DON'T have
-- (a < b) → (a * c < b * d) → (c ≤ d)
-- an easy conterexample is
-- (1 < 2) → (1 * 3 < 2 * 2) → ¬(3 ≤ 2)
theorem lt_mul_combine {a b c d : MyNat} :
  (c ≠ zero) → (a < b) → (c ≤ d) → (a * c < b * d) := by
  intro hc hab hcd
  rw [<-MyComparableOrd.not_ge_iff_lt]
  intro h
  rw [lt_iff_succ_le] at hab
  rcases hab with ⟨k₁, hk₁⟩
  rcases hcd with ⟨k₂, hk₂⟩
  rcases h with ⟨k₃, hk₃⟩
  rw [<-hk₁, <-hk₂] at hk₃
  match c with
    | zero =>
      contradiction
    | succ c' =>
      rw [mul_distrib] at hk₃
      rw [mul_left_distrib] at hk₃
      rw [succ_mul] at hk₃
      rw (occs := [2]) [<-add_zero (a := a * (succ c'))] at hk₃
      rw [add_assoc] at hk₃
      rw [add_assoc] at hk₃
      rw [add_assoc] at hk₃
      rw [add_cancel_left] at hk₃
      have := add_eq_zero_cancel_left hk₃
      contradiction

theorem lt_mul_cancel {a b c : MyNat} :
  (c ≠ zero) → ((a * c < b * c) ↔ (a < b)) := by
  intro hc
  apply Iff.intro
  · intro h
    rw [<-MyComparableOrd.not_ge_iff_lt]
    intro hab
    rw [ge_iff_le] at hab
    rw [le_def] at hab
    rcases hab with ⟨d, hd⟩
    rw [lt_iff_succ_le] at h
    rw [le_def] at h
    rcases h with ⟨e, he⟩
    rw [succ_add_eq_add_succ] at he
    rw [<-hd] at he
    rw [mul_distrib] at he
    rw (occs := [2]) [<-add_zero (a := b * c)] at he
    rw [add_assoc] at he
    rw [add_cancel_left] at he
    have := add_eq_zero_cancel he
    have := succ_ne_zero (a := e)
    contradiction
  · intro hab
    apply lt_mul_combine hc hab le_refl

theorem lt_mul_cancel_left {a b c : MyNat} :
  (c ≠ zero) → ((c * a < c * b) ↔ (a < b)) := by
  intro h
  rw [mul_comm (a := c) (b := a)]
  rw [mul_comm (a := c) (b := b)]
  exact lt_mul_cancel h

theorem le_mul_cancel {a b c : MyNat} :
  (c ≠ zero) → ((a * c ≤ b * c) ↔ (a ≤ b)) := by
  intro hcnz
  apply Iff.intro
  · intro h
    repeat rw [MyComparableOrd.le_iff_lt_or_eq] at h
    apply Or.elim h
    · intro h'
      have hab := (lt_mul_cancel hcnz).mp h'
      exact And.left hab
    · intro h'
      have hab := mul_cancel_left hcnz h'
      rw [hab]
      exact MyPartialOrd.le_refl
  · intro h
    rcases h with ⟨d, hd⟩
    exists d * c
    rw [<-mul_distrib]
    rw [hd]

theorem le_mul_cancel_left {a b c : MyNat} :
  (c ≠ zero) → ((c * a ≤ c * b) ↔ (a ≤ b)) := by
  intro h
  rw [mul_comm (a := c) (b := a)]
  rw [mul_comm (a := c) (b := b)]
  exact le_mul_cancel h

theorem mul_monus_distrib {a b c : MyNat} :
  (a ⊖ b) * c = (a * c) ⊖ (b * c) := by
  have d : Decidable (a * c < b * c) := inferInstance
  match d with
    | Decidable.isTrue h =>
      rw [monus_cancel_unsafe h]
      match c with
        | zero =>
          rw [mul_zero]
        | succ c' =>
          rw [lt_mul_cancel succ_ne_zero] at h
          rw [monus_cancel_unsafe h]
          rw [zero_mul]
    | Decidable.isFalse h =>
      rw [MyComparableOrd.not_gt_iff_le] at h
      rw [<-add_cancel_left (c := b * c)]
      rw [monus_cancel_safe h]
      rw [<-mul_distrib]
      match c with
        | zero =>
          repeat rw [mul_zero]
        | succ c' =>
          rw [le_mul_cancel succ_ne_zero] at h
          rw [monus_cancel_safe h]

theorem mul_monus_left_distrib {a b c : MyNat} :
  c * (a ⊖ b) = (c * a) ⊖ (c * b) := by
  rw [mul_comm (b := (a ⊖ b))]
  rw [mul_comm (b := a)]
  rw [mul_comm (b := b)]
  exact mul_monus_distrib

end MyNat
