inductive MyNat where
  | zero
  | succ (a : MyNat)

namespace MyNat

def one := MyNat.succ zero

@[simp] theorem one_def : one = succ zero := by
  rfl

-- MyNat.succ is an injection.
--
-- This is due to the inductive type nature of Lean
-- that each inductive constructor maps the arguments
-- into disjoint partitions of the range.
@[simp] theorem succ_inj {a b : MyNat} :
  (succ a) = (succ b) ↔ (a = b) := by
  apply Iff.intro
  · intro h
    injection h
  · intro h
    rw [h]

-- again, disjoint partition of the range.
theorem succ_ne_zero {a : MyNat} :
  (succ a) ≠ zero := by
  intro h
  injection h

-- What makes Peano arithmetic (PA) different from
-- the Robbinson arithmetic (Q)?
-- Yes, the axiom schema of induction!
--
-- In lean, this is done by constructing proof by
-- recursively distructing a successor till zero.
def _construct_mathemetically_inductive_proof
  (a : MyNat) (p : MyNat -> Prop)
  (h₀: p zero) (h₁: ∀(a : MyNat), p a → p (succ a)) :
  p a := by
  match a with
    | zero =>
      exact h₀
    | succ a' =>
      apply h₁
      apply _construct_mathemetically_inductive_proof a' p h₀ h₁

-- Generally, we should use tactic 'induction',
-- but I just want to demonstrate how mathematical
-- induction is done definitionally.
theorem mathematical_induction (p : MyNat -> Prop)
  (h₀: p zero) (h₁: ∀(a : MyNat), p a → p (succ a)) :
  (∀ (a : MyNat), p a) := by
  intro a
  exact _construct_mathemetically_inductive_proof a p h₀ h₁

end MyNat

-- Other helpful theorems that depends ONLY on the
-- primary section of MyNat.Basic above.
namespace MyNat

-- I find this very helpful in the proofs later.
theorem ne_zero_iff_succ {a : MyNat} :
  (a ≠ zero) ↔ (∃ b : MyNat, a = succ b) := by
  apply Iff.intro
  · intro h
    match a with
      | zero => contradiction
      | succ a' => exists a'
  · intro h
    rcases h with ⟨b, hb⟩
    rw [hb]
    apply succ_ne_zero

end MyNat
