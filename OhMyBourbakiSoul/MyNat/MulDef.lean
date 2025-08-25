import OhMyBourbakiSoul.MyNat.Basic
import OhMyBourbakiSoul.MyNat.AddDef

namespace MyNat

-- a * 0 = 0
-- a * σ(b) = a + a * b
def mul (a b : MyNat) : MyNat := by
  match b with
    | zero => exact zero
    | succ b' => exact a + (mul a b')

instance instMul : Mul MyNat where
  mul := mul

@[simp] theorem mul_zero {a : MyNat} :
  a * zero = zero := by
  change zero = zero
  rfl

@[simp] theorem mul_succ {a b : MyNat} :
  a * succ b = a + (a * b) := by
  change a + (mul a b) = a + (a * b)
  rfl

@[simp] theorem mul_one {a : MyNat} :
  a * one = a := by
  rw [one_def]
  rw [mul_succ]
  rw [mul_zero]
  rw [add_zero]

theorem zero_mul {a : MyNat} :
  zero * a = zero := by
  apply mathematical_induction
    (λ a' => zero * a' = zero)
  · rw [mul_zero]
  · intro a' hp
    rw [mul_succ]
    rw [zero_add]
    exact hp

theorem succ_mul {a b : MyNat} :
  (succ a) * b = a * b + b := by
  apply mathematical_induction
    (λ b' => (succ a) * b' = a * b' + b')
  · rw [mul_zero]
    rw [mul_zero]
    rw [zero_add]
  · intro b' hp
    rw [mul_succ]
    rw [mul_succ]
    rw [succ_add]
    rw [add_succ]
    rw [succ_inj]
    rw [add_assoc]
    rw [add_cancel_left]
    exact hp

theorem mul_comm {a b : MyNat} :
  a * b = b * a := by
  apply mathematical_induction
    λ b' => a * b' = b' * a
  · rw [zero_mul]
    rw [mul_zero]
  · intro b' hp
    rw [mul_succ]
    rw [succ_mul]
    rw [add_comm]
    rw [add_cancel]
    exact hp

theorem one_mul {a : MyNat} :
  one * a = a := by
  rw [mul_comm]
  exact mul_one

theorem mul_distrib {a b c : MyNat} :
  (a + b) * c = a * c + b * c := by
  apply mathematical_induction
    λ c' => (a + b) * c' = (a * c') + (b * c')
  · repeat rw [mul_zero]
    rw [add_zero]
  · intro c' hp
    repeat rw [mul_succ]
    rw [add_comm (a := b) (b := b * c')]
    rw (occs := [2]) [add_assoc]
    rw [<-add_assoc (a := a * c')]
    rw [<-hp]
    rw [add_comm (a := (a + b) * c') (b := b)]
    rw [<-add_assoc]

theorem mul_left_distrib {a b c : MyNat} :
  c * (a + b) = c * a + c * b := by
  repeat rw [mul_comm (a := c)]
  exact mul_distrib

theorem mul_assoc {a b c : MyNat} :
  (a * b) * c = a * (b * c) := by
  apply mathematical_induction
    λ c' => (a * b) * c' = a * (b * c')
  · repeat rw [mul_zero]
  · intro c' hp
    repeat rw [mul_succ]
    rw [mul_left_distrib]
    rw [hp]

theorem mul_eq_zero_cancel {a b : MyNat} :
  (a ≠ zero) → (a * b = zero) → (b = zero) := by
  intro hanz habz
  rw [ne_zero_iff_succ] at hanz
  rcases hanz with ⟨a', ha'⟩
  rw [ha'] at habz
  rw [succ_mul] at habz
  apply add_eq_zero_cancel habz

theorem mul_eq_zero_cancel_left {a b : MyNat} :
  (b ≠ zero) → (a * b = zero) → (a = zero) := by
  intro hbnz habz
  rw [mul_comm] at habz
  apply mul_eq_zero_cancel hbnz habz

-- This proof is a bit complex, its mathematical induction
-- requires ranging over ∀ (b : MyNat), not just the
-- parameter b provided in the function argument.
theorem mul_cancel {a b c : MyNat} :
  (a ≠ zero) → (a * b = a * c) → (b = c) := by
  intro ha
  revert b
  apply mathematical_induction
    λ c' => ∀ (b : MyNat), (a * b = a * c') → (b = c')
  · intro b h
    rw [mul_zero] at h
    apply mul_eq_zero_cancel ha h
  · intro c' hp b h
    rw [mul_succ] at h
    cases b with
      | zero =>
        exfalso
        rw [mul_zero] at h
        symm at h
        have : a = zero := add_eq_zero_cancel_left h
        contradiction
      | succ b' =>
        rw [succ_inj]
        rw [mul_succ] at h
        rw [add_cancel_left] at h
        exact hp b' h

theorem mul_cancel_left {a b c : MyNat} :
  (a ≠ zero) → (b * a = c * a) → (b = c) := by
  intro ha
  intro h
  repeat rw [mul_comm (b := a)] at h
  exact mul_cancel ha h

end MyNat
