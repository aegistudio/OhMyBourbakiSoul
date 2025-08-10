import OhMyBourbakiSoul.MyBasic.MyOrd.Basic

universe u
variable {α : Type u}

namespace MyOrd

class MyCustomPartialOrd (α : Type u) where
  op : α → α → Prop
  op_refl {a : α} : (op a a)
  op_trans {a b c : α} : (op a b) → (op b c) → (op a c)
  op_antisymm {a b : α} : (op a b) → (op b a) → (a = b)

namespace MyCustomPartialOrd

structure Lift (α : Type u) [O : MyCustomPartialOrd α] where
  elem : α

variable [O : MyCustomPartialOrd α]

theorem eq_iff {a b : Lift α} :
  (a = b) ↔ (a.elem = b.elem) := by
  cases a
  cases b
  simp

def lift_le (a : α) : Lift α := Lift.mk a

instance instCoeLift : Coe α (Lift α) where
  coe := lift_le

def unlift_le (a : Lift α) : α := a.elem

instance instCoeUnlift : Coe (Lift α) α where
  coe := unlift_le

def lifted_le (a b : Lift α) : Prop := O.op a.elem b.elem

instance instanceLELift : LE (Lift α) where
  le := lifted_le

theorem lift_eq_iff {a b : α} :
  (lift_le a = lift_le b) ↔ (a = b) := by
    repeat rw [lift_le]
    apply eq_iff

theorem lift_le_iff {a b : α} :
  (lift_le a ≤ lift_le b) ↔ (O.op a b) := by rfl

theorem unlift_le_iff {a b : Lift α} :
  (a ≤ b) ↔ (O.op (unlift_le a) (unlift_le b)) := by rfl

theorem lifted_le_refl {a : Lift α} : (a ≤ a) := by
  rw [unlift_le_iff]
  exact O.op_refl

theorem lift_le_trans {a b c : Lift α} :
  (a ≤ b) → (b ≤ c) → (a ≤ c) := by
  repeat rw [lift_le_iff]
  intro hab hbc
  exact O.op_trans hab hbc

theorem lift_le_antisymm {a b : Lift α} :
  (a ≤ b) → (b ≤ a) → (a = b) := by
  repeat rw [lift_le_iff]
  intro hab hba
  have h := O.op_antisymm hab hba
  repeat rw [coe_elem] at h
  rw [<-eq_iff] at h
  exact h

instance instLiftedPartialOrd : MyPartialOrd (Lift α) where
  le_refl := lifted_le_refl
  le_trans := lift_le_trans
  le_antisymm := lift_le_antisymm

end MyCustomPartialOrd

class MyCustomStrictOrd (α : Type u) where
  op : α → α → Prop
  op_irrefl {a : α} : ¬(op a a)
  op_trans {a b c: α} : (op a b) → (op b c) → (op a c)
  op_assym {a b : α} : (op a b) → ¬(op b a)

namespace MyCustomStrictOrd

variable [O : MyCustomStrictOrd α]

structure Lift (α : Type v) [O : MyCustomStrictOrd α] where
  elem : α

theorem eq_iff (a b : Lift α) :
  (a = b) ↔ (a.elem = b.elem) := by
  cases a
  cases b
  simp

def lift_lt (a : α) : Lift α := Lift.mk a

instance instCoeLift : Coe α (Lift α) where
  coe := lift_lt

def unlift_lt (a : Lift α) : α := a.elem

instance instCoeElem : Coe (Lift α) α where
  coe := unlift_lt

def lifted_lt (a b : Lift α) : Prop := O.op a b

instance instanceLTLift : LT (Lift α) where
  lt := lifted_lt

theorem lift_eq_iff {a b : α} :
  (lift_lt a = lift_lt b) ↔ (a = b) := by
    repeat rw [lift_lt]
    apply eq_iff

theorem lift_lt_iff {a b : α} :
  (lift_lt a < lift_lt b) ↔ (O.op a b) := by rfl

theorem unlift_lt_iff {a b : Lift α} :
  (a < b) ↔ (O.op (unlift_lt a) (unlift_lt b)) := by rfl

theorem lift_lt_irrefl {a : Lift α} : ¬(a < a) := by
   rw [unlift_lt_iff]
   exact O.op_irrefl

theorem lift_lt_trans {a b c : Lift α} :
  (a < b) → (b < c) → (a < c) := by
  repeat rw [lift_lt_iff]
  intro hab hbc
  exact O.op_trans hab hbc

theorem lift_lt_asymm {a b : Lift α} :
  (a < b) → ¬(a > b) := by
  repeat rw [lift_lt_iff]
  intro hab
  exact O.op_assym hab

instance instLiftedStrictOrd : MyStrictOrd (Lift α) where
  lt_irrefl := lift_lt_irrefl
  lt_trans := lift_lt_trans
  lt_asymm := lift_lt_asymm

end MyCustomStrictOrd

end MyOrd
