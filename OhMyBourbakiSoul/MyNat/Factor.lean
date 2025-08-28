import OhMyBourbakiSoul.MyNat.DivModDef
import OhMyBourbakiSoul.MyNat.DvdPrimeDef
import OhMyBourbakiSoul.MyNat.SizeOfDef
import OhMyBourbakiSoul.MyNat.MulOrd
import OhMyBourbakiSoul.MyBasic.MyLogic.Propositional

open MyOrd
open MyLogic

namespace MyNat

def comm_div (d a b : MyNat) := (d ∣ a) ∧ (d ∣ b)

theorem comm_div_def {d a b : MyNat} :
  (d.comm_div a b) ↔ (d ∣ a) ∧ (d ∣ b) := by rfl

theorem zero_comm_div {a b : MyNat} :
  (zero.comm_div a b) → (a = zero) ∧ (b = zero) := by
  intro h
  rw [comm_div_def] at h
  have hc : ∀ c, zero ∣ c → c = zero := by
    intro c hzc
    have d : Exclusive (c = zero) :=
      exclusive_if_decidable
    apply d.by_contra
    intro hc'
    rw [<-ne_eq] at hc'
    rw [<-zero_lt_iff_ne_zero] at hc'
    have := zero_not_dvd_nonzero hc'
    contradiction
  apply And.intro
  · apply hc a (And.left h)
  · apply hc b (And.right h)

theorem zero_comm_div_iff {a b : MyNat} :
  (zero.comm_div a b) ↔ ((a = zero) ∧ (b = zero)) := by
  apply Iff.intro
  · exact zero_comm_div
  · intro h
    rcases h with ⟨ha, hb⟩
    rw [ha, hb]
    rw [comm_div_def]
    apply And.intro <;> exact dvd_zero

-- When c ≠ zero ∨ d ≠ zero, gcd c d > zero
-- When c = zero ∧ d = zero, gcd c d = zero, this is
-- the fallback case since any n : MyNat fullfills
-- n.comm_div zero zero, there's no greatest value then.
 def is_gcd (g c d : MyNat) :=
  (g.comm_div c d) ∧ (g ≠ zero → ∀ d : MyNat, d.comm_div c d → d ≤ g)

theorem is_gcd_def {g c d : MyNat} :
  (g.is_gcd c d) ↔
  (g.comm_div c d) ∧ (g ≠ zero → ∀ d : MyNat, d.comm_div c d → d ≤ g)
  := by rfl

def comm_mul (m a b : MyNat) := (a ∣ m) ∧ (b ∣ m)

theorem comm_mul_def {m a b : MyNat} :
  (m.comm_mul a b) ↔ (a ∣ m) ∧ (b ∣ m) := by rfl

theorem zero_comm_mul {a b : MyNat} : (zero.comm_mul a b) := by
  rw [comm_mul_def]
  apply And.intro <;> exact dvd_zero

theorem comm_mul_nonzero {a b c : MyNat} :
  (c.comm_mul a b) → (c ≠ zero) → (a ≠ zero) ∧ (b ≠ zero) := by
  intro h
  rw [comm_mul_def] at h
  rcases h with ⟨hac, hbc⟩
  intro hc
  rw [<-zero_lt_iff_ne_zero] at hc
  apply And.intro
  · intro ha
    apply zero_not_dvd_nonzero hc
    rw [ha] at hac
    exact hac
  · intro hb
    apply zero_not_dvd_nonzero hc
    rw [hb] at hbc
    exact hbc

theorem comm_mul_zero {a b c : MyNat} :
  (c.comm_mul a b) → (a = zero) ∨ (b = zero) → (c = zero) := by
  intro h hab
  have d : Exclusive (c = zero) :=
    exclusive_if_decidable
  apply d.by_contra
  intro hc'
  have hab' := comm_mul_nonzero h hc'
  repeat rw [ne_eq] at hab'
  rw [<-demorgan_not_or] at hab'
  contradiction

-- When c ≠ zero ∨ d ≠ zero, lcm a b > zero
-- by explicitly requiring l > zero in that case
-- When c = zero ∧ d = zero, lcm a b = zero,
-- since it's impossible for zero ∣ succ a.
def is_lcm (l a b : MyNat) :=
  (l.comm_mul a b) ∧ (a ≠ zero → b ≠ zero → l ≠ zero) ∧
  (∀ m : MyNat, m.comm_mul a b → m > zero → l ≤ m)

theorem is_lcm_def {l a b : MyNat} :
  (l.is_lcm a b) ↔
  (l.comm_mul a b) ∧ (a ≠ zero → b ≠ zero → l ≠ zero) ∧
  (∀ m : MyNat, m.comm_mul a b → m > zero → l ≤ m) := by rfl

theorem lcm_exists {a b : MyNat} :
  ∃ l : MyNat, l.is_lcm a b := by
  match a, b with
    | zero, _ | _, zero =>
      exists zero
      rw [is_lcm_def]
      apply And.intro
      · exact zero_comm_mul
      · apply And.intro
        · intros
          contradiction
        · intro m hp hm
          exfalso
          rw [gt_iff_lt] at hm
          rw [zero_lt_iff_ne_zero] at hm
          have : m = zero := by
            apply comm_mul_zero hp
            first
              | exact Or.inl rfl
              | exact Or.inr rfl
          contradiction
    | (succ a'), (succ b') =>
      generalize ha : succ a' = a
      generalize hb : succ b' = b
      have hex : ∃ m : MyNat, (m > zero) ∧ (m.comm_mul a b) := by
        exists a * b
        rw [comm_mul]
        apply And.intro
        · rw [<-ha, <-hb]
          rw [succ_mul]
          rw [add_succ]
          rw [gt_iff_lt]
          rw [zero_lt_iff_ne_zero]
          exact succ_ne_zero
        · apply And.intro
          · rw [dvd_def]
            exists b
            rw [mul_comm]
          · rw [dvd_def]
            exists a
      have d : DecidablePred
        ((x : MyNat) ↦ (x > zero) ∧ (comm_mul x a b)) := by
        intro x
        unfold comm_mul
        infer_instance
      have l := MyNat.mu hex
      exists l.val
      rw [is_lcm_def]
      apply And.intro
      · exact And.right l.sufficient
      · apply And.intro
        · intro han hbn
          have hl := And.left l.sufficient
          rw [gt_iff_lt] at hl
          rw [zero_lt_iff_ne_zero] at hl
          exact hl
        · intro m hm hmz
          rw [<-MyComparableOrd.not_gt_iff_le]
          intro h'
          have := And.intro hmz hm
          have := l.minimal m h'
          contradiction

theorem lcm_dvd_comm_mul {a b l m : MyNat} :
  (l.is_lcm a b) → (m.comm_mul a b) → (l ∣ m) := by
  intro hl hm
  have d : Exclusive (l ∣ m) :=
    exclusive_if_decidable
  apply d.by_contra
  intro hlm
  have h : m = l * (m / l) + (m % l) :=
    divmod_identity
  generalize hq : m / l = q
  generalize hr : m % l = r
  have hrnz : r > zero := by
    rw [gt_iff_lt]
    rw [zero_lt_iff_ne_zero]
    intro hrz
    rw [hrz] at hr
    rw [dvd_iff] at hr
    contradiction
  rw [hq, hr] at h
  have hdr : ∀ d : MyNat, d ∣ l → d ∣ m → d ∣ r := by
    intro d hdl hdm
    rcases hdl with ⟨k₁, hk₁⟩
    rcases hdm with ⟨k₂, hk₂⟩
    rw [hk₁, hk₂] at h
    have hle :  k₁ * d * q ≤ k₂ * d := by
      exists r
      symm
      exact h
    rw [<-monus_cancel_safe hle] at h
    rw [add_cancel_left] at h
    rw [mul_assoc] at h
    rw [mul_comm (a := d) (b := q)] at h
    rw [<-mul_assoc] at h
    rw [<-mul_monus_distrib] at h
    rw [dvd_def]
    exists (k₂ ⊖ k₁ * q)
    symm at h
    exact h
  rw [is_lcm_def] at hl
  rw [comm_mul_def] at hl hm
  rcases hl with ⟨⟨hal, hbl⟩, hlz, hlm'⟩
  rcases hm with ⟨ham, hbm⟩
  have hrc : r.comm_mul a b := by
    rw [comm_mul_def]
    have har := hdr a hal ham
    have hbr := hdr b hbl hbm
    exact And.intro har hbr
  have hrm : l ≤ r := hlm' r hrc hrnz
  rw [<-MyComparableOrd.not_gt_iff_le] at hrm
  match a, b with
    | zero, _ | _, zero =>
      have hmz : m = zero := by
        apply dvd_antisymm dvd_zero
        first
          | exact ham
          | exact hbm
      rw [hmz] at hlm
      have : l ∣ zero := dvd_zero
      contradiction
    | succ a', succ b' =>
      have hlnz : l ≠ zero :=
        hlz succ_ne_zero succ_ne_zero
      have : r < l := by
        rw [<-hr]
        exact mod_lt hlnz
      contradiction

-- Establishing the fact lcm_dvd_comm_mul
-- sufficies to prove the Euclid's Lemma.
--
-- First, let's perform l := lcm p b, so we
-- have (b ∣ l) → (∃ k, l = k * b). And since
-- (l ∣ p * b), we get (k * b ∣ p * b) → (k ∣ p).
--
-- Now there (k ∣ p) → (k = one) ∨ (k = p).
-- · If k = one, then (b = l), and thus
--   (p ∣ lcm p b = l = b) → (p ∣ b).
-- · If k = p, then since (p ∣ a * b) by the
--   premise of the lemma and (b ∣ a * b) by
--   b presenting to the right, we have
--   (l ∣ a * b) → (k * b ∣ a * b) →
--   (k ∣ a) → (p ∣ a).
theorem euclid_lemma {a b p : MyNat} :
  (p ∈ ℙ) → (p ∣ a * b) → (p ∣ a) ∨ (p ∣ b) := by
  intro hp hpab
  have h : ∃ l : MyNat, l.is_lcm p b := lcm_exists
  rcases h with ⟨l, hl⟩
  have hl' := hl
  rw [is_lcm_def] at hl'
  have hpbl := And.left hl'
  rw [comm_mul] at hpbl
  have hpb : (p * b).comm_mul p b := by
    rw [comm_mul_def]
    apply And.intro
    · rw [dvd_def]
      exists b
      exact mul_comm
    · rw [dvd_def]
      exists p
  have hlpb : l ∣ p * b := lcm_dvd_comm_mul hl hpb
  have hbl := And.right hpbl
  rw [dvd_def] at hbl
  rcases hbl with ⟨k, hk⟩
  rw [hk] at hlpb
  match b with
    | zero =>
      exact Or.inr dvd_zero
    | succ b' =>
      generalize hb : succ b' = b
      rw [dvd_mul_both_cancel_nonzero succ_ne_zero] at hlpb
      rw [prime_mem] at hp
      rw [is_prime] at hp
      have hkv := (And.right hp) k set_def hlpb
      apply Or.elim hkv
      · intro hko
        rw [hko] at hk
        rw [one_mul] at hk
        rw [hb] at hk
        rw [hk] at hpbl
        exact Or.inr (And.left hpbl)
      · intro hkp
        rw [hb] at hpab
        have hbab : b ∣ a * b := by
          rw [dvd_def]
          exists a
        have hab : (a * b).comm_mul p b := by
          rw [comm_mul_def]
          exact And.intro hpab hbab
        rw [hb] at hl
        have hlab : l ∣ a * b :=
          lcm_dvd_comm_mul hl hab
        rw [<-hb] at hlab
        rw [hk] at hlab
        rw [dvd_mul_both_cancel_nonzero succ_ne_zero] at hlab
        rw [hkp] at hlab
        exact Or.inl hlab

end MyNat
