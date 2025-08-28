import OhMyBourbakiSoul.MyNat.Basic
import OhMyBourbakiSoul.MyNat.AddDef
import OhMyBourbakiSoul.MyNat.MulDef
import OhMyBourbakiSoul.MyNat.OrderDef

open MyOrd

-- The only purpose of this file is to make us able
-- to write recursive functions based on metrics.
namespace MyNat

def sizeOf (n : MyNat) : Nat := by
  match n with
    | zero => exact 0
    | succ n' => exact (sizeOf n') + 1

instance instSizeOf : SizeOf MyNat where
  sizeOf := sizeOf

theorem sizeOf_zero : sizeOf zero = 0 :=
  by rfl

theorem sizeOf_succ {a : MyNat} :
  (sizeOf (succ a)) = sizeOf a + 1 := by rfl

def mkNat (a : Nat) : MyNat := by
  if a > 0 then
    exact succ (mkNat (a - 1))
  else
    exact zero

instance instCoeNatMyNat : Coe Nat MyNat where
  coe := mkNat

theorem mkNat_zero : mkNat 0 = zero := by
  unfold mkNat
  rfl

theorem mkNat_succ {a : Nat} :
  mkNat (a + 1) = succ (mkNat a) := by
  rw [mkNat]
  have h : (a + 1) > 0 := by
    rw [gt_iff_lt]
    rw [Nat.lt_iff_add_one_le]
    rw [Nat.add_le_add_iff_right]
    exact Nat.zero_le a
  rw [dif_pos h]
  rw [Nat.add_sub_assoc]
  rw [Nat.sub_self]
  rw [Nat.add_zero]
  exact Nat.le_refl 1

theorem sizeOf_cancel {a : MyNat} :
  mkNat (sizeOf a) = a := by
  revert a
  apply mathematical_induction
  · rw [sizeOf_zero]
    exact mkNat_zero
  · intro a' hp
    rw [sizeOf_succ]
    rw [mkNat_succ]
    rw [succ_inj]
    exact hp

theorem mkNat_cancel {a : Nat} :
  sizeOf (mkNat a) = a := by
  if haz : a > 0 then
    generalize ha' : a - 1 = a'
    have ha : a = a' + 1 := by
      rw [<-ha']
      rw [gt_iff_lt] at haz
      rw [Nat.lt_iff_add_one_le] at haz
      rw [<-Nat.sub_add_comm haz]
      rw [Nat.zero_add]
      rw [Nat.add_sub_assoc]
      rw [Nat.sub_self]
      rw [Nat.add_zero]
      exact Nat.le_refl 1
    rw [ha]
    rw [mkNat_succ]
    rw [sizeOf_succ]
    rw [Nat.add_right_cancel_iff]
    apply mkNat_cancel
  else
    rw [Nat.not_lt_eq] at haz
    rw [Nat.le_zero_eq] at haz
    rw [haz]
    rw [mkNat_zero]
    rw [sizeOf_zero]

theorem sizeOf_add_hom {a b : MyNat} :
  sizeOf (a + b) = (sizeOf a) + (sizeOf b) := by
  revert b
  apply mathematical_induction
  · rw [add_zero]
    rw [sizeOf_zero]
    rw [Nat.add_zero]
  · intro b hp
    rw [add_succ]
    rw [sizeOf_succ]
    rw [sizeOf_succ]
    rw [<-Nat.add_assoc]
    rw [<-hp]

theorem mkNat_add_hom {a b : Nat} :
  mkNat (a + b) = (mkNat a) + (mkNat b) := by
  rw [<-mkNat_cancel (a := a)]
  rw [<-mkNat_cancel (a := b)]
  rw [<-sizeOf_add_hom]
  repeat rw [mkNat_cancel]
  repeat rw [sizeOf_cancel]

theorem sizeOf_le_iff {a b : MyNat} :
  (a ≤ b) ↔ (sizeOf a ≤ sizeOf b) := by
  apply Iff.intro
  · intro hab
    rw [le_def] at hab
    rcases hab with ⟨c, hc⟩
    rw [<-hc]
    rw [sizeOf_add_hom]
    exact Nat.le_add_right _ _
  · intro hab
    have hab' := Nat.sub_add_cancel hab
    generalize hc : (sizeOf b) - (sizeOf a) = c
    rw [hc] at hab'
    rw [le_def]
    exists mkNat c
    have h : mkNat (c + (sizeOf a)) = mkNat (sizeOf b) := by
      rw [hab']
    rw [mkNat_add_hom] at h
    repeat rw [sizeOf_cancel] at h
    rw [add_comm]
    exact h

theorem sizeOf_eq_iff {a b : MyNat} :
  (a = b) ↔ (sizeOf a = sizeOf b) := by
  apply Iff.intro
  · intro h
    rw [h]
  · intro h
    have h' : mkNat (sizeOf a) = mkNat (sizeOf b) := by
      rw [h]
    repeat rw [sizeOf_cancel] at h'
    exact h'

theorem sizeOf_lt_iff {a b : MyNat} :
  (a < b) ↔ (sizeOf a < sizeOf b) := by
  rw [MyCompatOrd.compat]
  rw [Nat.lt_iff_le_and_ne]
  rw [sizeOf_le_iff]
  rw [ne_eq]
  rw [sizeOf_eq_iff]

theorem sizeOf_mul_hom {a b : MyNat} :
  sizeOf (a * b) = (sizeOf a) * (sizeOf b) := by
  revert b
  apply mathematical_induction
  · rw [sizeOf_zero]
    rw [Nat.mul_zero]
    rw [mul_zero]
    rw [sizeOf_zero]
  · intro b hp
    rw [mul_succ]
    rw [sizeOf_add_hom]
    rw [sizeOf_succ]
    rw [Nat.mul_add]
    rw [Nat.mul_one]
    rw [Nat.add_comm]
    rw [hp]

theorem mkNat_mul_hom {a b : Nat} :
  (mkNat a) * (mkNat b) = mkNat (a * b) := by
  rw [<-mkNat_cancel (a := a)]
  rw [<-mkNat_cancel (a := b)]
  rw [<-sizeOf_mul_hom]
  repeat rw [mkNat_cancel]
  repeat rw [sizeOf_cancel]

end MyNat
