import OhMyBourbakiSoul.MyNat.Basic
import OhMyBourbakiSoul.MyNat.AddDef
import OhMyBourbakiSoul.MyNat.MulDef
import OhMyBourbakiSoul.MyNat.MonusDef
import OhMyBourbakiSoul.MyNat.OrderDef
import OhMyBourbakiSoul.MyCompose.MyNatCompose

open MyCompose
open MyOrd

namespace MyNat

-- The purpose of defining divmod operation is to find the
-- identity in the form of a = b * q + r.
def _divmod_identity (a b : MyNat) (qr : MyNat × MyNat) : Prop :=
  a = b * qr.fst + qr.snd

def _divmod_inner (a b c: MyNat) : MyNat × MyNat := by
  match b with
    | zero => exact (zero, a)
    | succ b' =>
      match (cmp a b) with
        | MyCmp.lt hlt =>
          exact (zero, a)
        | MyCmp.eq heq =>
          exact (one, zero)
        | MyCmp.gt hgt =>
          match c with
            | zero => exact (zero, a)
            | succ c' =>
              have qr := _divmod_inner (a ⊖ b) b c'
              exact (qr.fst + one, qr.snd)

theorem _divmod_inner_identity_zero_a {a b : MyNat} :
  _divmod_identity a b (zero, a) := by
  change a = b * zero + a
  rw [mul_zero]
  rw [zero_add]

theorem _divmod_inner_identity_one_zero {a b : MyNat}
  (heq : a = b): _divmod_identity a b (one, zero) := by
  change a = b * one + zero
  rw [mul_one]
  rw [add_zero]
  exact heq

theorem _divmod_inner_identity (a b c : MyNat) :
  _divmod_identity a b (_divmod_inner a b c) := by
  match b with
    | zero =>
      rw [_divmod_inner]
      rw [_divmod_identity]
      change a = zero * zero + a
      rw [mul_zero]
      rw [zero_add]
    | succ b' =>
      generalize hb : succ b' = b
      apply mathematical_induction
        λ c => ∀ (a' : MyNat),
          _divmod_identity a' b (_divmod_inner a' b c)
      · intro a'
        rw [<-hb, _divmod_inner, hb]
        match (cmp a' b) with
          | MyCmp.lt hlt | MyCmp.gt hgt =>
            change _divmod_identity a' b (zero, a')
            apply _divmod_inner_identity_zero_a
          | MyCmp.eq heq =>
            change _divmod_identity a' b (one, zero)
            apply _divmod_inner_identity_one_zero heq
      · intro c hp a'
        rw [<-hb, _divmod_inner, hb]
        match (cmp a' b) with
          | MyCmp.lt hlt =>
            change _divmod_identity a' b (zero, a')
            apply _divmod_inner_identity_zero_a
          | MyCmp.eq heq =>
            change _divmod_identity a' b (one, zero)
            apply _divmod_inner_identity_one_zero heq
          | MyCmp.gt hgt =>
            generalize hqr : _divmod_inner (a' ⊖ b) b c = qr
            change _divmod_identity a' b (qr.fst + one, qr.snd)
            have hqr' := hp (a' ⊖ b)
            rw [hqr] at hqr'
            change a' ⊖ b = b * qr.fst + qr.snd at hqr'
            change a' = b * (qr.fst + one) + qr.snd
            rw [gt_iff_lt] at hgt
            rw [lt_def] at hgt
            have hmn := monus_cancel_safe (And.left hgt)
            rw [<-hmn]
            rw [mul_left_distrib]
            rw [add_assoc]
            rw [add_comm (a := b * one)]
            rw [<-add_assoc]
            rw [<-hqr']
            rw [add_comm]
            rw [mul_one]

def divmod (a b : MyNat) := _divmod_inner a b a

def div (a b : MyNat) := (divmod a b).fst

def mod (a b : MyNat) := (divmod a b).snd

instance instDiv : Div MyNat where
  div := div

instance instMod : Mod MyNat where
  mod := mod

theorem div_def {a b : MyNat} :
  a / b = (divmod a b).fst := by rfl

theorem mod_def {a b : MyNat} :
  a % b = (divmod a b).snd := by rfl

theorem divmod_def {a b : MyNat} :
  (a / b, a % b) = (divmod a b) := by rfl

theorem div_zero {a : MyNat} : a / zero = zero := by
  rw [div_def]
  rw [divmod]
  rw [_divmod_inner]

theorem mod_zero {a : MyNat} : a % zero = a := by
  rw [mod_def]
  rw [divmod]
  rw [_divmod_inner]

theorem divmod_identity {a b : MyNat} :
  (a = b * (a / b) + (a % b)) := by
  rw [div_def]
  rw [mod_def]
  rw [divmod]
  generalize hqr : _divmod_inner a b a = qr
  have h' := _divmod_inner_identity a b a
  rw [hqr] at h'
  unfold _divmod_identity at h'
  exact h'

theorem zero_div {b : MyNat} : zero / b = zero := by
  have h := divmod_identity (a := zero) (b := b)
  cases b with
    | zero => apply div_zero
    | succ b' =>
      rw [succ_mul] at h
      rw (occs := [2]) [add_comm] at h
      symm at h
      apply add_eq_zero_cancel_left h

theorem zero_mod {b : MyNat} : zero % b = zero := by
  have h := divmod_identity (a := zero) (b := b)
  symm at h
  apply add_eq_zero_cancel h

theorem _mod_inner_succ {a b c : MyNat} :
  (a ≤ c) → (b ≠ zero) → ((_divmod_inner a b c).snd < b) := by
  intro hac hbnz
  match b with
    | zero => contradiction
    | succ b' =>
      generalize hb : succ b' = b
      revert a
      apply mathematical_induction
        λ c' => ∀ (a' : MyNat), (a' ≤ c') → (_divmod_inner a' b c').snd < b
      · intro a' ha'
        have haz : a' = zero := le_antisymm ha' zero_le
        rw [haz]
        rw [<-divmod]
        rw [<-mod_def]
        rw [zero_mod]
        rw [<-hb]
        apply zero_lt_succ
      · intro c' hp a' ha'
        rw [<-hb, _divmod_inner, hb]
        match (cmp a' b) with
          | MyCmp.lt hlt =>
            change a' < b
            exact hlt
          | MyCmp.eq heq =>
            change zero < b
            rw [<-hb]
            apply zero_lt_succ
          | MyCmp.gt hgt =>
            generalize hqr : _divmod_inner (a' ⊖ b) b c' = qr
            change qr.snd < b
            have h : b + (a' ⊖ b) = a' :=
              monus_cancel_safe (And.left hgt)
            rw [le_def] at ha'
            rcases ha' with ⟨d, hd⟩
            rw [<-add_cancel (c := d)] at h
            rw [hd] at h
            rw (occs := [1]) [<-hb] at h
            rw [add_assoc] at h
            rw [succ_add] at h
            rw [succ_inj] at h
            rw [<-add_assoc] at h
            rw [add_comm (a := b')] at h
            rw [add_assoc] at h
            have hmc' : a' ⊖ b ≤ c' := by
              exists (b' + d)
            have hp' := hp (a' ⊖ b) hmc'
            rw [hqr] at hp'
            exact hp'

-- Let's get back to the divmod identity, we would
-- like to derive the uniqueness of such identity
-- under certain condition, such as constraining
-- the relationship between r₁, r₂ and b.
theorem _divmod_unique_solution_derive_contradiction
  {a b q₁ r₁ q₂ r₂ : MyNat}
  (hab₁ : a = b * q₁ + r₁)
  (hab₂ : a = b * q₂ + r₂)
  (hrb₁ : r₁ < b)
  (hq₁q₂: q₁ < q₂) : False := by
  rw [lt_iff_succ_le] at hq₁q₂
  rw [le_def] at hq₁q₂
  rcases hq₁q₂ with ⟨d, hq⟩
  rw [<-hq] at hab₂
  rw [hab₁] at hab₂
  rw [succ_add_eq_add_succ] at hab₂
  rw [mul_left_distrib] at hab₂
  rw [add_assoc] at hab₂
  rw [add_cancel_left] at hab₂
  rw [succ_eq_add_one] at hab₂
  rw [mul_left_distrib] at hab₂
  rw [mul_one] at hab₂
  rw [add_comm (a := b * d)] at hab₂
  rw [add_assoc] at hab₂
  have hr₁b' : b ≤ r₁ := by
    rw [le_def]
    exists (b * d + r₂)
    symm
    exact hab₂
  rw [le_iff_not_gt] at hr₁b'
  contradiction

theorem divmod_unique_solution {a b q₁ r₁ q₂ r₂ : MyNat}
  (hab₁ : a = b * q₁ + r₁) (hab₂ : a = b * q₂ + r₂)
  (hrb₁ : r₁ < b) (hrb₂ : r₂ < b) :
  (r₁ = r₂) := by
  cases b with
    | zero =>
      exfalso
      have : ¬ (r₁ < zero) := by
        rw [<-le_iff_not_gt]
        apply zero_le
      contradiction
    | succ b' =>
      generalize hb' : (succ b') = b
      rw [hb'] at hab₁ hab₂ hrb₁ hrb₂
      match (cmp q₁ q₂) with
        | MyCmp.lt (hlt: q₁ < q₂) =>
          exfalso
          apply _divmod_unique_solution_derive_contradiction
            hab₁ hab₂ hrb₁ hlt
        | MyCmp.gt (hgt: q₂ < q₁) =>
          exfalso
          apply _divmod_unique_solution_derive_contradiction
            hab₂ hab₁ hrb₂ hgt
        | MyCmp.eq (heq: q₁ = q₂) =>
          rw [hab₁] at hab₂
          rw [heq] at hab₂
          rw [add_cancel_left] at hab₂
          exact hab₂

-- The main theorem of MyNat.DivModDef, proving the
-- existence and uniqueness of a / b and a % b when
-- b ≠ 0, given the divmod identity and
-- the remainder constraint.
theorem divmod_succ {a b q r : MyNat} :
  (a = (succ b) * q + r) ∧ (r < succ b) ↔
  (q = a / (succ b)) ∧ (r = a % (succ b)) := by
  apply Iff.intro
  · intro h
    rcases h with ⟨hab, hrb⟩
    generalize hq' : a / (succ b) = q'
    generalize hr' : a % (succ b) = r'
    have hab' := divmod_identity (a := a) (b := succ b)
    rw [hq', hr'] at hab'
    -- derive r = r' first.
    rw [mod_def] at hr'
    rw [divmod] at hr'
    have hr'b := _mod_inner_succ
      (le_refl (a := a)) (succ_ne_zero (a := b))
    rw [hr'] at hr'b
    have hrr' : r = r' :=
      divmod_unique_solution hab hab' hrb hr'b
    apply And.intro
    · -- prove q = q' then.
      match (cmp q q') with
      | MyCmp.lt hlt =>
        exfalso
        apply _divmod_unique_solution_derive_contradiction
          hab hab' hrb hlt
      | MyCmp.eq heq => rw [heq]
      | MyCmp.gt hgt =>
        exfalso
        apply _divmod_unique_solution_derive_contradiction
          hab' hab hr'b hgt
    · exact hrr'
  · intro hqr
    rcases hqr with ⟨hq, hr⟩
    apply And.intro
    · rw [hq, hr]
      apply divmod_identity
    · rw [hr]
      apply _mod_inner_succ le_refl succ_ne_zero

theorem divmod_nonzero {a b q r : MyNat} (hnz: b ≠ zero) :
  (a = b * q + r) ∧ (r < b) ↔
  (q = a / b) ∧ (r = a % b) := by
  rw [ne_zero_iff_succ] at hnz
  rcases hnz with ⟨b', hb'⟩
  rw [hb']
  apply divmod_succ

theorem mod_lt {a b : MyNat} (hnz : b ≠ zero) :
  (a % b < b) := by
  generalize hq : a / b = q
  generalize hr : a % b = r
  symm at hq hr
  have hqr := And.intro hq hr
  rw [<-divmod_nonzero hnz] at hqr
  exact And.right hqr

theorem mod_shift_eq
  {a b k : MyNat} (hnz : b ≠ zero) :
  (a + b * k) % b = a % b := by
  have h : a = b * (a / b) + (a % b) :=
    divmod_identity
  rw [<-add_cancel (c := b * k)] at h
  rw (occs := [2]) [<-add_comm] at h
  rw [<-add_assoc] at h
  rw [<-mul_left_distrib] at h
  have hr : (a % b) < b := mod_lt hnz
  have hqr := And.intro h hr
  rw [divmod_nonzero hnz] at hqr
  symm
  exact And.right hqr

end MyNat
