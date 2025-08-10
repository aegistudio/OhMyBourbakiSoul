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

end MyComparableOrd

end MyOrd
