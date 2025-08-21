import OhMyBourbakiSoul.MyBasic.MyFun.Basic
import OhMyBourbakiSoul.MyBasic.MySet.Subtype

universe u
variable {α : Type u}
variable {X Y : MySet α}

open MySet

namespace MyFun

def identity (X : MySet α) : X -→ X := MyFun.mk id

theorem identity_def
  {X : MySet α} {x : X.type} :
  (identity X) x = x := by
  change id x = x
  rfl

instance instIdentityInj : MyInj (identity X) := by
  apply MyInj.mk
  intro x x' h
  repeat rw [identity_def] at h
  exact h

instance instIdentitySurj : MySurj (identity X) := by
  apply MySurj.mk
  intro x
  exists x

instance instIdentityBij : MyBij (identity X) where

def identity' (h : X = Y) : X -→ Y := by
  apply MyFun.mk
  intro x
  have hx := x.membership
  rw (occs := [1]) [h] at hx
  exact typed x.val hx

theorem identity'_def {x : X.type} {h : X = Y} :
  ((identity' h) x).val = x.val := by
  unfold identity'
  change x.val = x.val
  rfl

instance instIdentity'Inj {h : X = Y} :
  MyInj (identity' h) := by
  apply MyInj.mk
  intro x x' hxx'
  rw [Subtype.eq_iff] at hxx'
  repeat rw [identity'_def] at hxx'
  rw [Subtype.eq_iff]
  exact hxx'

instance instIdentity'Surj {h : X = Y} :
  MySurj (identity' h) := by
  apply MySurj.mk
  intro x
  have hx := x.membership
  rw (occs := [1]) [<-h] at hx
  have (eq := hx') x' := typed x.val hx
  exists x'
  rw [Subtype.eq_iff]
  rw [identity'_def]
  rw [Subtype.eq_iff] at hx'
  rw [typed_eta] at hx'
  exact hx'

instance instIdentity'Bij {h : X = Y} :
  MyBij (identity' h) := by
  have If : MyInj (identity' h) := inferInstance
  have Sf : MySurj (identity' h) := inferInstance
  exact @MyBij.mk _ _ _ _ _ If Sf

end MyFun
