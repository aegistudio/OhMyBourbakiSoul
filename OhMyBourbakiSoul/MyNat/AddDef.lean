import OhMyBourbakiSoul.MyNat.Basic

namespace MyNat

-- a + 0 = a
-- a + σ(b) = σ(a + b)
def add (a b : MyNat) : MyNat := by
  match b with
    | zero => exact a
    | succ b' => exact succ (add a b')

-- enable us to write a + b := add a b
instance instHAdd : HAdd MyNat MyNat MyNat where
  hAdd := add

@[simp] theorem add_zero {a : MyNat} :
  a + zero = a := by
  change a = a
  rfl

@[simp] theorem add_succ {a b : MyNat} :
  a + succ b = succ (a + b) := by
  change succ (add a b) = succ (a + b)
  rfl

@[simp] theorem succ_eq_add_one {a : MyNat} :
  succ a = a + one := by
  change succ a = succ (a + zero)
  rw [add_zero]

-- Although it's trivial, we have to use
-- mathematical induction due to our way of
-- definition MyNat.add.
@[simp] theorem zero_add {a : MyNat} :
  zero + a = a := by
  apply mathematical_induction (λ a' => zero + a' = a')
  · rw [add_zero]
  · intro a' ha'
    rw [add_succ]
    rw [ha']

-- Well, again, mathematical induction.
@[simp] theorem succ_add {a b : MyNat} :
  (succ a) + b = succ (a + b) := by
  apply mathematical_induction
    (λ b' => (succ a) + b' = succ (a + b'))
  · repeat rw [add_zero]
  · intro b' hb'
    rw [add_succ]
    rw [hb']
    rw [add_succ]

@[simp] theorem succ_add_eq_add_succ {a b : MyNat} :
  (succ a) + b = a + (succ b) := by
  rw [succ_add]
  rw [add_succ]

-- Now we can see why mathematical induction
-- is important, it enables us to prove the
-- commutativity of addition.
@[simp] theorem add_comm {a b : MyNat} :
  a + b = b + a := by
  apply mathematical_induction
    (λ b' => a + b' = b' + a)
  · rw [zero_add]
    rw [add_zero]
  · intro b' hb'
    rw [add_succ]
    rw [hb']
    rw [succ_add]

@[simp] theorem add_assoc {a b c : MyNat} :
  (a + b) + c = a + (b + c) := by
  apply mathematical_induction
    (λ c' => (a + b) + c' = a + (b + c'))
  · repeat rw [add_zero]
  · intro c' hc'
    repeat rw [add_succ]
    rw [hc']

-- This establish MyNat as a cancel monoid.
@[simp] theorem add_cancel {a b c : MyNat} :
  (a + c) = (b + c) ↔ (a = b) := by
  apply Iff.intro
  · apply mathematical_induction
      (λ c' => (a + c') = (b + c') → (a = b))
    · intro h
      repeat rw [add_zero] at h
      exact h
    · intro c' hc' h
      repeat rw [add_succ] at h
      rw [succ_inj] at h
      exact hc' h
  · intro h
    rw [h]

@[simp] theorem add_cancel_left {a b c : MyNat} :
  (c + a) = (c + b) ↔ (a = b) := by
  rw [add_comm (a := c) (b := a)]
  rw [add_comm (a := c) (b := b)]
  apply add_cancel

-- While it seems absurd, please imagine when
-- will the premise be true first. Yes, it's
-- only the case of zero + zero = zero.
theorem add_eq_zero_cancel {a b : MyNat} :
  (a + b = zero) → (b = zero) := by
  intro h
  cases b with
    | zero => rfl
    | succ b' =>
      exfalso
      rw [add_succ] at h
      exact succ_ne_zero h

theorem add_eq_zero_cancel_left {a b : MyNat} :
  (a + b = zero) → (a = zero) := by
  intro h
  rw [add_comm] at h
  apply add_eq_zero_cancel (a := b)
  exact h

theorem add_eq_self_cancel {a b : MyNat} :
  (a + b = a) → (b = zero) := by
  intro h
  rw (occs := [2]) [<-add_zero (a := a)] at h
  rw [add_cancel_left] at h
  exact h

theorem add_eq_self_cancel_left {a b : MyNat} :
  (a + b = b) → (a = zero) := by
  intro h
  rw [add_comm] at h
  apply add_eq_self_cancel (a := b)
  exact h

theorem ne_succ {a : MyNat} : a ≠ (succ a) := by
  intro h
  rw [succ_eq_add_one] at h
  symm at h
  have hoz : one = zero := add_eq_self_cancel h
  rw [one_def] at hoz
  exact succ_ne_zero hoz

end MyNat
