import OhMyBourbakiSoul.MyNat.Basic
import OhMyBourbakiSoul.MyNat.AddDef
import OhMyBourbakiSoul.MyCompose.Basic

open MyCompose
open MyNat

universe u
variable {α : Type u}

namespace MyCompose

-- f: α → α
-- f⁰(x) := idₐ
-- fⁿ⁺¹(x) := f(fⁿ(x))
def compose_nat_pow (f : α → α) (n : MyNat) : α → α := by
  match n with
    | zero => exact id
    | succ n' => exact λ x => f ((compose_nat_pow f n') x)

instance instComposeNatPow : HPow (α → α) MyNat (α → α) where
  hPow := compose_nat_pow

theorem compose_nat_pow_def {f : α → α} {n : MyNat} :
  f ^ n = compose_nat_pow f n := by rfl

theorem compose_nat_pow_zero {f : α → α} : f ^ zero = id := by
  change id = id
  rfl

theorem compose_nat_pow_succ {f : α → α} {n : MyNat} :
  f ^ (succ n) = f ∘ (f ^ n) := by
  -- this extensional theorem is used to prove equality of functions
  funext x
  change (λ y => f ((compose_nat_pow f n) y)) x = f ((f ^ n) x)
  change f ((compose_nat_pow f n) x) = f ((f ^ n) x)
  rw [compose_nat_pow_def]

theorem compose_nat_pow_one {f : α → α} :
  f ^ one = f := by
  rw [one_def]
  rw [compose_nat_pow_succ]
  rw [compose_nat_pow_zero]
  rw [compose_id]

theorem compose_nat_pow_inner {f : α → α} {n : MyNat} :
  f ^ (succ n) = (f ^ n) ∘ f := by
  funext x
  apply mathematical_induction
    λ n' => (f ^ (succ n')) x = (f ^ n') (f x)
  · rw [<-one_def]
    rw [compose_nat_pow_one]
    rw [compose_nat_pow_zero]
    rw [id]
  · intro n' hp
    rw [compose_nat_pow_succ]
    rw [compose_nat_pow_succ] at hp
    rw [compose_nat_pow_succ]
    change f ((f ∘ (f ^ n')) x) = f ((f ^ n') (f x))
    rw [hp]

theorem compose_nat_pow_ids {n : MyNat} :
  id (α := α) ^ n = id (α := α) := by
  apply mathematical_induction (λ n' => id ^ n' = id)
  · rw [compose_nat_pow_zero]
  · intro n' hp
    rw [compose_nat_pow_succ]
    rw [hp]
    rw [compose_id]

theorem compose_nat_pow_add_hom {f : α → α} {m n : MyNat} :
  (f ^ m) ∘ (f ^ n) = f ^ (m + n) := by
  revert n
  apply mathematical_induction
  · rw [compose_nat_pow_zero]
    rw [compose_id]
    rw [add_zero]
  · intro n hp
    rw [compose_nat_pow_inner]
    rw [<-compose_assoc]
    rw [hp]
    rw [<-compose_nat_pow_inner]
    rw [add_succ]

def idempotent (f : α → α) : Prop :=
  f ^ (succ one) = f

theorem idempotent_pow {f : α → α} :
  (idempotent f) ↔ (∀ (n : MyNat), f ^ (succ n) = f) := by
  unfold idempotent
  apply Iff.intro
  · intro h
    apply mathematical_induction
    · rw [<-one_def]
      rw [compose_nat_pow_one]
    · intro n hp
      rw [compose_nat_pow_succ]
      rw [hp]
      rw (occs := [2]) [<-compose_nat_pow_one (f := f)]
      rw [<-compose_nat_pow_succ]
      exact h
  · intro h'
    exact h' one

def nilpotent (f : α → α) : Prop :=
  ∃ (n : MyNat), (n ≠ zero) ∧ (f ^ n = id)

theorem nilpotent_idempotent_then_identity {f : α → α} :
  (nilpotent f) → (idempotent f) → (f = id) := by
  intro h_nilpotent h_idempotent
  have h_idempotent' := idempotent_pow.mp h_idempotent
  unfold nilpotent at h_nilpotent
  unfold idempotent at h_idempotent
  rcases h_nilpotent with ⟨o, ho⟩
  rcases ho with ⟨honz, hfoi⟩
  rw [ne_zero_iff_succ] at honz
  rcases honz with ⟨b, hb⟩
  rw [hb] at hfoi
  rw [<-hfoi]
  symm
  exact h_idempotent' b

end MyCompose
