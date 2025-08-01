import OhMyBourbakiSoul.MyNat.Basic
import OhMyBourbakiSoul.MyNat.AddDef
import OhMyBourbakiSoul.MyNat.OrderDef
import OhMyBourbakiSoul.MyCompose.MyNatCompose

open MyCompose

namespace MyNat

-- While some people might argue that this function
-- should be named "pred", it's confusing since
-- zero has no predecessor, so I name it to
-- "monus_dec" i.e. "monus decrement", to
-- avoid such a confusion.
def monus_dec (a : MyNat) : MyNat := by
  match a with
    | zero => exact zero
    | succ a' => exact a'

def monus (a n : MyNat) := (monus_dec ^ n) a

-- I copy the precedence number of "-" from
-- lean4/src/Init/Notation.lean.
infixl:65 " ⊖ " => monus

theorem monus_def {a n : MyNat} :
  a ⊖ n = (monus_dec ^ n) a := by rfl

theorem monus_dec_zero :
  monus_dec zero = zero := by
  rfl

theorem monus_dec_succ {a : MyNat} :
  monus_dec (succ a) = a := by
  rfl

theorem monus_cancel {a b : MyNat} : (a + b) ⊖ a = b := by
  rw [monus_def]
  revert a
  apply mathematical_induction
  · rw [zero_add]
    rw [compose_nat_pow_zero]
    rw [id]
  · intro a hp
    rw [compose_nat_pow_inner]
    rw [compose_apply]
    rw [succ_add]
    rw [monus_dec_succ]
    exact hp

theorem monus_cancel_self {a : MyNat} : a ⊖ a = zero := by
  apply monus_cancel (b := zero)

theorem zero_monus {n : MyNat} : zero ⊖ n = zero := by
  rw [monus_def]
  revert n
  apply mathematical_induction
  · rw [compose_nat_pow_zero]
    rw [id]
  · intro n hp
    rw [compose_nat_pow_inner]
    rw [compose_apply]
    rw [monus_dec_zero]
    exact hp

theorem monus_cancel_safe {a n : MyNat} :
  (n ≤ a) → (n + (a ⊖ n) = a) := by
  intro hnlea
  rw [le_def] at hnlea
  rcases hnlea with ⟨c, hc⟩
  rw [<-hc]
  rw [monus_cancel]

theorem monus_cancel_unsafe {a n : MyNat} :
  (a < n) → (a ⊖ n = zero) := by
  intro haltn
  rw [lt_iff_succ_le] at haltn
  rcases haltn with ⟨c, hc⟩
  rw [succ_add] at hc
  rw [add_comm] at hc
  rw [<-succ_add] at hc
  rw [monus_def, <-hc]
  rw [<-compose_nat_pow_add_hom]
  rw [compose_apply]
  rw [<-monus_def (n := a)]
  rw [monus_cancel_self]
  rw [<-monus_def]
  rw [zero_monus]

theorem monus_eq_zero_iff {a n : MyNat} :
  (a ⊖ n = zero) ↔ (a ≤ n) := by
  apply Iff.intro
  · intro hanz
    match (cmp a n) with
      | Cmp.lt hlt =>
        rw [lt_def] at hlt
        exact And.left hlt
      | Cmp.eq heq =>
        rw [heq]
        exact le_refl
      | Cmp.gt hgt =>
        exfalso
        rw [lt_iff_succ_le] at hgt
        rcases hgt with ⟨b, hb⟩
        rw [succ_add_eq_add_succ] at hb
        rw [<-hb] at hanz
        rw [monus_cancel] at hanz
        apply succ_ne_zero hanz
  · intro h
    rw [le_iff_lt_or_eq] at h
    apply Or.elim h
    · intro h'
      apply monus_cancel_unsafe h'
    · intro h'
      rw [h']
      exact monus_cancel_self

end MyNat
