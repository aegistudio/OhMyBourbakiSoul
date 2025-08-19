import OhMyBourbakiSoul.MyNat.Basic
import OhMyBourbakiSoul.MyNat.OrderDef
import OhMyBourbakiSoul.MyNat.MonusDef
import OhMyBourbakiSoul.MyBasic.MyOrd.Compat
import OhMyBourbakiSoul.MyBasic.MyOrd.Cmp
import Batteries.WF

open MyOrd

universe u

namespace MyNat

-- The μ-operator is a building block of the
-- computability theory. Given a proposition
-- (p : MyNat → Prop), it allows searching
-- for the least (n : MyNat) such that (p n).
--
-- https://en.wikipedia.org/wiki/%CE%9C_operator
--
-- However, in computability theory, it's
-- possible that p does not hold for any
-- MyNat (e.g. λ n => False), in that case,
-- the μ-operator will never return, or the
-- machine will never halt. For computable
-- function f: X → Y which might involve
-- a μ-operator, for any x ∈ X triggering
-- non-terminating μ-operator, it's
-- undefined at that point. That is, the
-- computable function is actually a
-- partial function.
--
-- In the case of Lean 4, every function
-- must be total / non-partial. So they
-- require us to provide a proof to
-- justify that it will halt. So we will
-- only define μ-operator to search only
-- if there's a proof of (h : ∃ n, p n).
-- Please notice the witness need not to
-- be the MyNat returned.

def mu_rel
  (p : MyNat → Prop) [DecidablePred p] (m n : MyNat) :=
  (m = succ n) ∧ (∀ k : MyNat, (k ≤ n) → ¬(p k))

-- We construct by counting the distance
-- between the current cursor with the
-- sufficient witness m such that p m.
theorem mu_acc_monus
  (p : MyNat → Prop) [DecidablePred p]
  (m : MyNat) (h : p m) (k : MyNat) :
  Acc (mu_rel p) (m ⊖ k) := by
  match k with
    | zero =>
      rw [monus_zero]
      apply Acc.intro
      intro y hm
      unfold mu_rel at hm
      exfalso
      have h' := (And.right hm) m le_refl
      contradiction
    | succ k' =>
      have r := mu_acc_monus p m h k'
      have d : Decidable (m ≤ k') := inferInstance
      match d with
        | Decidable.isTrue hT =>
          have hmk' : m ⊖ k' = zero :=
            monus_eq_zero_iff.mpr hT
          rw [hmk'] at r
          have hmk : m ⊖ (succ k') = zero :=
            monus_eq_zero_iff.mpr (le_trans hT le_succ)
          rw [hmk]
          exact r
        | Decidable.isFalse hF =>
          rw [<-ge_iff_le] at hF
          rw [MyComparableOrd.not_ge_iff_lt] at hF
          rw [lt_iff_succ_le] at hF
          have hsk := monus_cancel_safe hF
          have hk'k : k' ≤ succ k' := le_succ
          have hk'm := le_trans hk'k hF
          have hsk' := monus_cancel_safe hk'm
          rw [succ_add_eq_add_succ] at hsk
          rw (occs := [2]) [<-hsk'] at hsk
          rw [add_cancel_left] at hsk
          generalize hl : m ⊖ (succ k') = l
          rw [hl] at hsk
          rw [<-hsk] at r hsk'
          apply Acc.intro
          intro y hy
          unfold mu_rel at hy
          rw [And.left hy]
          exact r

theorem mu_acc_overflow
  (p : MyNat → Prop) [DecidablePred p]
  (m : MyNat) (h₀ : p m)
  (k : MyNat) (h₁ : k ≥ m) :
  Acc (mu_rel p) k := by
  apply Acc.intro
  intro y h
  unfold mu_rel at h
  exfalso
  have h₂ := (And.right h) m h₁
  contradiction

theorem mu_acc
  {p : MyNat → Prop} [DecidablePred p] (h : Exists p) :
  ∀ (n : MyNat), Acc (mu_rel p) n := by
  intro n
  rcases h with ⟨m, hm⟩
  have d : Decidable (n ≤ m) := inferInstance
  match d with
    | Decidable.isTrue hT =>
      have h' := monus_cancel_safe hT
      generalize hk : m ⊖ n = k
      rw [hk] at h'
      have hkm : k ≤ m := by
        rw [add_comm] at h'
        exists n
      have h'' := monus_cancel_safe hkm
      rw [<-h''] at h'
      rw [add_comm] at h'
      rw [add_cancel_left] at h'
      have r := mu_acc_monus p m hm k
      rw [<-h'] at r
      exact r
    | Decidable.isFalse hF =>
      rw [MyComparableOrd.not_ge_iff_lt] at hF
      rw [MyCompatOrd.lt_iff_le_and_ne] at hF
      have hmn := And.left hF
      rw [<-ge_iff_le] at hmn
      exact mu_acc_overflow p m hm n hmn

def wf_mu
  {p : MyNat → Prop} [DecidablePred p] (h : Exists p) :
  WellFounded (mu_rel p) := by
  apply WellFounded.intro
  exact mu_acc h

structure Mu (p : MyNat → Prop) where
  val : MyNat
  sufficient : p val
  minimal : ∀ b : MyNat, b < val → ¬p b

def mu
  {p : MyNat → Prop} [DecidablePred p] (h : Exists p) :
  Mu p := by
  apply (wf_mu h).fix
    (C := fun (a : MyNat) => (∀ b : MyNat, (b < a) → ¬(p b)) → Mu p)
  · intro x f hx
    have d : Decidable (p x) := inferInstance
    match d with
      | Decidable.isTrue (h : p x) =>
        exact Mu.mk x h hx
      | Decidable.isFalse (h : ¬(p x)) =>
        have hb' : ∀ (b : MyNat), b < succ x → ¬(p b) := by
          intro b
          rw [lt_iff_succ_le]
          rw [le_succ_cancel]
          intro hbx
          have d' : Decidable (b = x) := inferInstance
          match d' with
            | Decidable.isTrue (h' : b = x) =>
              rw [h']
              exact h
            | Decidable.isFalse (h' : b ≠ x) =>
              apply hx
              rw [MyCompatOrd.compat]
              exact And.intro hbx h'
        have hr : mu_rel p (succ x) x := by
          unfold mu_rel
          apply And.intro
          · rfl
          · intro k hk
            apply hb'
            rw [lt_iff_succ_le]
            rw [le_succ_cancel]
            exact hk
        exact f (succ x) hr hb'
  · intro b h
    -- Well, we fill in the metavariable in this way.
    change b < zero at h
    exfalso
    rw [lt_iff_succ_le] at h
    have h' : zero < b.succ := zero_lt_succ
    have h'' := MyCompatOrd.not_ge_if_lt h'
    rw [ge_iff_le] at h''
    contradiction

end MyNat
