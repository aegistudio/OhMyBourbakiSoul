import OhMyBourbakiSoul.MyBasic.MyOrd.Basic
import OhMyBourbakiSoul.MyBasic.MyOrd.Compat

universe u
variable {α : Type u}

namespace MyOrd

inductive MyCmp {α : Type u} [MyStrictOrd α] (a b : α) where
  | lt (hlt: a < b)
  | eq (heq: a = b)
  | gt (hgt: a > b)

class MyComparableOrd (α : Type u) [MyStrictOrd α] where
  cmp (a b : α) : MyCmp a b

namespace MyComparableOrd

variable [O : MyStrictOrd α]
variable [C : MyComparableOrd α]

def decide_lt_with_comparable_ord (a b : α) : Decidable (a < b) := by
  match (C.cmp a b) with
    | MyCmp.lt (hlt : a < b) =>
      exact isTrue hlt
    | MyCmp.eq (heq : a = b) =>
      exact isFalse (not_lt_if_eq heq)
    | MyCmp.gt (hgt : a > b) =>
      exact isFalse (O.lt_asymm hgt)

instance instDecidableLT : DecidableLT α :=
  decide_lt_with_comparable_ord

def decide_eq_with_comparable_ord (a b : α) : Decidable (a = b) := by
  match (C.cmp a b) with
    | MyCmp.lt (hlt : a < b) =>
      exact isFalse (ne_if_lt hlt)
    | MyCmp.eq (heq : a = b) =>
      exact isTrue heq
    | MyCmp.gt (hgt : a > b) =>
      have h := ne_if_lt hgt
      symm at h
      exact isFalse h

instance instDecidableEq : DecidableEq α :=
  decide_eq_with_comparable_ord

def decide_le_with_comparable_ord_if_compat
  [M : MyPartialOrd α] [P : MyCompatOrd α]
  (a b : α) : Decidable (a ≤ b) := by
  match (C.cmp a b) with
    | MyCmp.lt (hlt : a < b) =>
      exact isTrue (And.left (P.compat.mp hlt))
    | MyCmp.eq (heq : a = b) =>
      exact isTrue (le_if_eq heq)
    | MyCmp.gt (hgt : a > b) =>
      exact isFalse (MyCompatOrd.not_ge_if_lt hgt)

instance instDecidableLE
  [MyPartialOrd α] [MyCompatOrd α] : DecidableLE α :=
  decide_le_with_comparable_ord_if_compat

section

variable [MyPartialOrd α]
variable [MyCompatOrd α]

theorem lt_if_not_ge
  {a b : α} : ¬(a ≥ b) → (a < b) := by
  intro h
  match (cmp a b) with
    | MyCmp.lt (hlt : a < b) =>
      exact hlt
    | MyCmp.eq (heq : a = b) =>
      exfalso
      symm at heq
      have h' := le_if_eq heq
      contradiction
    | MyCmp.gt (hgt : a > b) =>
      exfalso
      rw [gt_iff_lt] at hgt
      rw [MyCompatOrd.compat] at hgt
      have h' := And.left hgt
      contradiction

theorem not_ge_iff_lt
  {a b : α} : ¬(a ≥ b) ↔ (a < b) := by
  apply Iff.intro
  · exact lt_if_not_ge
  · exact MyCompatOrd.not_ge_if_lt

theorem le_if_not_gt
  {a b : α} : ¬(a > b) → (a ≤ b) := by
  intro h
  match (cmp a b) with
    | MyCmp.lt (hlt : a < b) =>
      rw [MyCompatOrd.compat] at hlt
      exact And.left hlt
    | MyCmp.eq (heq : a = b) =>
      exact le_if_eq heq
    | MyCmp.gt (hgt : a > b) =>
      exfalso
      contradiction

theorem not_gt_iff_le
  {a b : α} : ¬(a > b) ↔ (a ≤ b) := by
  apply Iff.intro
  · exact le_if_not_gt
  · exact MyCompatOrd.not_gt_if_le

theorem le_iff_lt_or_eq
  {a b : α} : (a ≤ b) ↔ (a < b) ∨ (a = b) := by
  apply Iff.intro
  · intro hle
    rw [MyCompatOrd.compat]
    have d : Decidable (a = b) := inferInstance
    match d with
      | Decidable.isTrue h =>
        exact Or.inr h
      | Decidable.isFalse h =>
        apply Or.inl
        exact And.intro hle h
  · intro hlteq
    apply Or.elim hlteq
    · intro hlt
      rw [MyCompatOrd.compat] at hlt
      exact And.left hlt
    · intro heq
      rw [heq]
      exact MyPartialOrd.le_refl

end

end MyComparableOrd


end MyOrd
