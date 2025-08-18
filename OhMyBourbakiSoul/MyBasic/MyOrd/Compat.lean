import OhMyBourbakiSoul.MyBasic.MyOrd.Basic
import OhMyBourbakiSoul.MyBasic.MyLogic.Propositional

universe u
variable {α : Type u}

open MyLogic

namespace MyOrd

class MyCompatOrd (α : Type u)
  [M : MyPartialOrd α] [N : MyStrictOrd α] where
  compat {a b : α} : (a < b) ↔ (a ≤ b) ∧ (a ≠ b)

namespace MyCompatOrd

variable [M : MyPartialOrd α] [N : MyStrictOrd α]
variable [O : MyCompatOrd α (M := M) (N := N)]

-- While one can directly call
-- instMyCompatOrd.compat, this theorem asks
-- lean to search for / synthesize the
-- instMyCompatOrd for us.
theorem lt_iff_le_and_ne
  {a b : α} : (a < b) ↔ (a ≤ b) ∧ (a ≠ b) := by
  exact O.compat

theorem lt_of_le_of_lt
  {a b c : α} : (a ≤ b) → (b < c) → (a < c) := by
  intro hab hbc
  rw [O.compat] at hbc
  have hbc' := And.left hbc
  have hac := M.le_trans hab hbc'
  rw [O.compat]
  apply And.intro
  · exact hac
  · intro heq
    rw [heq] at hab
    have heq' := M.le_antisymm hab hbc'
    rw [<-O.compat, heq'] at hbc
    have : ¬(b < b) := N.lt_irrefl
    contradiction

theorem lt_of_lt_of_le
  {a b c : α} : (a < b) → (b ≤ c) → (a < c) := by
  intro hab hbc
  rw [O.compat] at hab
  have hab' := And.left hab
  have hac := M.le_trans hab' hbc
  rw [O.compat]
  apply And.intro
  · exact hac
  · intro heq
    rw [<-heq] at hbc
    have heq' := M.le_antisymm hab' hbc
    rw [<-O.compat, heq'] at hab
    have : ¬(b < b) := N.lt_irrefl
    contradiction

theorem not_ge_if_lt
  {a b : α} : (a < b) → ¬(a ≥ b) := by
  intro hlt hge
  rw [O.compat] at hlt
  have hle := And.left hlt
  have : a ≠ b := And.right hlt
  have : a = b := M.le_antisymm hle hge
  contradiction

theorem not_gt_if_le
  {a b : α} : (a ≤ b) → ¬(a > b) := by
  apply modus_tollens_neg
  exact not_ge_if_lt

end MyCompatOrd

end MyOrd
