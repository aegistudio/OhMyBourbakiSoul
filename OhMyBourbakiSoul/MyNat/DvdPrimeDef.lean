import OhMyBourbakiSoul.MyNat.SetDef
import OhMyBourbakiSoul.MyNat.SegDef
import OhMyBourbakiSoul.MyBasic.MySet.Subtype
import OhMyBourbakiSoul.MyNat.MulDef
import OhMyBourbakiSoul.MyNat.MulOrd
import OhMyBourbakiSoul.MyNat.DivModDef
import OhMyBourbakiSoul.MyNat.Mu
import OhMyBourbakiSoul.MyBasic.MyLogic.Propositional

open MyOrd
open MySet
open MyLogic

namespace MyNat

def dvd (m n : MyNat) := ∃ k, n = k * m

instance instDvd : Dvd MyNat where
  dvd := dvd

theorem dvd_def {m n : MyNat} :
  (m ∣ n) ↔ (∃ k, n = k * m) := by rfl

theorem dvd_zero {a : MyNat} : a ∣ zero := by
  exists zero
  rw [zero_mul]

theorem zero_not_dvd_succ {a : MyNat} :
  ¬(zero ∣ succ a) := by
  intro h
  rw [dvd_def] at h
  rcases h with ⟨k, hk⟩
  rw [mul_zero] at hk
  have : a.succ ≠ zero := succ_ne_zero
  contradiction

theorem zero_not_dvd_nonzero {a : MyNat} :
  (a > zero) → ¬(zero ∣ a) := by
  intro h
  match a with
    | zero =>
      exfalso
      rw [gt_iff_lt] at h
      exact MyStrictOrd.lt_irrefl h
    | succ a' =>
      exact zero_not_dvd_succ

theorem one_dvd {a : MyNat} : one ∣ a := by
  exists a

theorem dvd_self {a : MyNat} : a ∣ a := by
  exists one
  rw [one_mul]

theorem dvd_iff {m n : MyNat} :
  (n % m = zero) ↔ m ∣ n := by
  apply Iff.intro
  · intro h
    exists n / m
    have h' := divmod_identity
      (a := n) (b := m)
    rw [h] at h'
    rw [add_zero] at h'
    rw [mul_comm] at h'
    exact h'
  · intro h
    rw [dvd_def] at h
    rcases h with ⟨k, hk⟩
    have d : Decidable (m = zero) :=
      inferInstance
    match d with
      | Decidable.isTrue h' =>
        rw [h'] at hk
        rw [mul_zero] at hk
        rw [hk, h']
        rw [mod_zero]
      | Decidable.isFalse h' =>
        have hgz := h'
        change m ≠ zero at hgz
        rw [<-zero_lt_iff_ne_zero] at hgz
        have (eq := hr) r := zero
        rw [<-hr] at hgz
        rw [mul_comm] at hk
        rw [<-add_zero (a := m * k)] at hk
        rw [<-hr] at hk
        have hp := And.intro hk hgz
        rw [divmod_nonzero h'] at hp
        rcases hp with ⟨_, hp⟩
        rw [hr] at hp
        symm
        exact hp

instance instDecideDvd {m n : MyNat} :
  Decidable (m ∣ n) := by
  have d : Decidable (n % m = zero) := inferInstance
  match d with
    | Decidable.isTrue h =>
      apply Decidable.isTrue
      rw [dvd_iff] at h
      exact h
    | Decidable.isFalse h =>
      apply Decidable.isFalse
      rw [dvd_iff] at h
      exact h

theorem not_dvd_if_lt_succ {m n : MyNat} :
  (m > succ n) → ¬(m ∣ succ n) := by
  intro hgt hdvd
  rw [dvd_def] at hdvd
  rcases hdvd with ⟨k, hk⟩
  rw [hk] at hgt
  match k with
    | zero =>
      rw [zero_mul] at hk
      have : n.succ ≠ zero := succ_ne_zero
      contradiction
    | succ k' =>
      rw [succ_mul] at hgt
      rw (occs := [1]) [<-zero_add (a := m)] at hgt
      rw [gt_iff_lt] at hgt
      rw [lt_add_cancel] at hgt
      rw [<-MyComparableOrd.not_ge_iff_lt] at hgt
      rw [ge_iff_le] at hgt
      have := zero_le (a := k' * m)
      contradiction

theorem le_succ_if_dvd {m n : MyNat} :
  (m ∣ succ n) → (m ≤ succ n) := by
  have h := modus_tollens_neg
    (not_dvd_if_lt_succ (m := m) (n := n))
  rw [<-MyComparableOrd.not_gt_iff_le]
  exact h

theorem dvd_mul {a b c : MyNat} :
  (a ∣ b) → (a ∣ b * c) := by
  intro hab
  rw [dvd_def] at hab
  rcases hab with ⟨k, hk⟩
  rw [dvd_def]
  exists k * c
  rw [hk]
  rw [mul_assoc]
  rw [mul_comm (a := a) (b := c)]
  rw [<-mul_assoc]

theorem dvd_mul_both {a b c : MyNat} :
  (a ∣ b) → (a * c ∣ b * c) := by
  intro hab
  rw [dvd_def] at hab
  rcases hab with ⟨k, hk⟩
  rw [dvd_def]
  exists k
  rw [hk]
  rw [mul_assoc]

theorem dvd_mul_both_cancel_nonzero {a b c : MyNat} :
  (c ≠ zero) → ((a * c ∣ b * c) ↔ (a ∣ b)) := by
  intro hcnz
  apply Iff.intro
  · intro h
    rw [dvd_def] at h
    rcases h with ⟨k, hk⟩
    rw [<-mul_assoc] at hk
    have hk' := mul_cancel_left hcnz hk
    rw [dvd_def]
    exists k
  · exact dvd_mul_both

theorem dvd_refl {a : MyNat} : (a ∣ a) := dvd_self

theorem dvd_trans {a b c : MyNat} :
  (a ∣ b) → (b ∣ c) → (a ∣ c) := by
  intro hab hbc
  rw [dvd_def] at hab hbc
  rcases hab with ⟨k₁, hk₁⟩
  rcases hbc with ⟨k₂, hk₂⟩
  rw [dvd_def]
  exists k₂ * k₁
  rw [mul_assoc]
  rw [<-hk₁]
  exact hk₂

theorem dvd_antisymm {a b : MyNat} :
  (a ∣ b) → (b ∣ a) → (a = b) := by
  intro hab hba
  rw [dvd_def] at hab
  rcases hab with ⟨k, hk⟩
  match (cmp k one) with
    | MyCmp.lt hlt =>
      rw [lt_iff_succ_le] at hlt
      rw [one_def] at hlt
      rw [le_succ_cancel] at hlt
      have hkz : k = zero :=
        MyPartialOrd.le_antisymm hlt zero_le
      rw [hkz] at hk
      rw [zero_mul] at hk
      rw [hk]
      match a with
        | zero =>
          rfl
        | succ a' =>
          exfalso
          rw [hk] at hba
          have : ¬(zero ∣ (succ a')) :=
            zero_not_dvd_succ
          contradiction
    | MyCmp.eq heq =>
      symm at hk
      rw [heq] at hk
      rw [one_mul] at hk
      exact hk
    | MyCmp.gt hgt =>
      match a with
        | zero =>
          symm at hk
          rw [mul_zero] at hk
          exact hk
        | succ a' =>
          exfalso
          have : ¬(b ∣ (succ a')) := by
            apply not_dvd_if_lt_succ
            rw [<-one_mul (a := succ a')]
            rw [hk]
            rw [gt_iff_lt]
            rw [lt_mul_cancel succ_ne_zero]
            exact hgt
          contradiction

def is_prime (n : MyNat) :=
  (n > one) ∧ (∀ x ∈ ℕ, (x ∣ n) → (x = one) ∨ (x = n))

theorem is_prime_def {p : MyNat} :
  (p.is_prime) ↔ (p > one) ∧ (∀ x ∈ ℕ, (x ∣ p) → (x = one) ∨ (x = p)) := by
  rfl

def is_reducible (n : MyNat) :=
  ∃ x, (x > one) ∧ (x < n) ∧ (x ∣ n)

theorem is_reducible_def {n : MyNat} :
  (n.is_reducible) ↔ (∃ x, (x > one) ∧ (x < n) ∧ (x ∣ n)) := by rfl

private inductive _MyPrimeSieve (x : MyNat) where
  | prime (h : x.is_prime)
  | reducible (h : x.is_reducible)
  | zero_one (h : ¬(x > one))

def _prime_sieve (x : MyNat) : _MyPrimeSieve x := by
  have d : Decidable (x > one) := inferInstance
  match d with
    | Decidable.isTrue h =>
      have hex : ∃ n, (n > one) ∧ (n ∣ x) := by
        exists x
        apply And.intro
        · exact h
        · exact dvd_self
      have m := MyNat.mu hex

      have contra_with_gt_dvd :
        (y : MyNat) → (y ∣ x) → (y > x) → False := by
        intro y hdvd hgt
        rw [gt_iff_lt] at h
        rw [lt_iff_succ_le] at h
        rw [le_def] at h
        rcases h with ⟨c, hc⟩
        rw [succ_add] at hc
        rw (occs := [1]) [<-hc] at hgt hdvd
        have := not_dvd_if_lt_succ hgt
        contradiction

      match (cmp m.val x) with
        | MyCmp.lt hlt =>
          apply _MyPrimeSieve.reducible
          exists m.val
          rcases m.sufficient with ⟨hmo, hdvd⟩
          apply And.intro
          · exact hmo
          · apply And.intro
            · exact hlt
            · exact hdvd
        | MyCmp.eq heq =>
          apply _MyPrimeSieve.prime
          rw [is_prime_def]
          apply And.intro
          · exact h
          · intro y hy hydvd
            match (cmp y x) with
              | MyCmp.lt hyx =>
                match (cmp y one) with
                  | MyCmp.lt hyo =>
                    rw [lt_iff_succ_le] at hyo
                    rw [one_def] at hyo
                    rw [le_succ_cancel] at hyo
                    have hoy : zero ≤ y := zero_le
                    have hyeqo := MyPartialOrd.le_antisymm hyo hoy
                    rw [hyeqo] at hyx hydvd
                    exfalso
                    exact zero_not_dvd_nonzero hyx hydvd
                  | MyCmp.eq hyo =>
                    exact Or.inl hyo
                  | MyCmp.gt hyo =>
                    rw [<-heq] at hyx
                    have hm := m.minimal y hyx
                    exfalso
                    have := And.intro hyo hydvd
                    contradiction
              | MyCmp.eq hyx =>
                exact Or.inr hyx
              | MyCmp.gt hyx =>
                exfalso
                exact contra_with_gt_dvd y hydvd hyx
        | MyCmp.gt hgt =>
          exfalso
          have := m.minimal x hgt
          have := And.intro h (dvd_self (a := x))
          contradiction
    | Decidable.isFalse h =>
      exact _MyPrimeSieve.zero_one h

theorem reducible_not_prime {n : MyNat} :
  (n.is_reducible) → ¬(n.is_prime) := by
  intro hc hp
  rw [is_reducible_def] at hc
  rcases hc with ⟨x, hx⟩
  rcases hx with ⟨hxo, hlt, hdvd⟩
  rw [is_prime_def] at hp
  have h := (And.right hp) x set_def hdvd
  apply Or.elim h
  · intro h'
    rw [h'] at hxo
    exact MyStrictOrd.lt_irrefl hxo
  · intro h'
    rw [h'] at hlt
    exact MyStrictOrd.lt_irrefl hlt

instance instDecidePrime : DecidablePred is_prime := by
  intro x
  match (_prime_sieve x) with
    | _MyPrimeSieve.prime h =>
      exact Decidable.isTrue h
    | _MyPrimeSieve.reducible h =>
      apply Decidable.isFalse
      exact reducible_not_prime h
    | _MyPrimeSieve.zero_one h =>
      apply Decidable.isFalse
      intro h'
      have := And.left h'
      contradiction

def primes : MySet MyNat :=
  unlift_subtype ({ x ∈ ℕ | is_prime x })

def ℙ := primes

theorem prime_mem {p : MyNat} : (p ∈ ℙ) ↔ (p.is_prime) := by
  unfold ℙ
  unfold primes
  have (eq := hp') p' := typed p set_def
  have hp'v : p = p'.val := by
    rw [hp']
    symm
    exact typed_eta
  rw (occs := [1]) [hp'v]
  rw [<-unlift_subtype_def]
  change p'.val.is_prime ↔ p.is_prime
  rw [hp'v]

instance instDecidePrimeMem : ℙ.decidable := by
  intro x
  have d : Decidable (is_prime x) := inferInstance
  match d with
    | Decidable.isTrue h =>
      apply Decidable.isTrue
      rw [<-mem_def]
      rw [prime_mem]
      exact h
    | Decidable.isFalse h =>
      apply Decidable.isFalse
      rw [<-mem_def]
      rw [prime_mem]
      exact h

theorem reducible_if {n : MyNat} :
  (n > one) → ¬(n.is_prime) → (n.is_reducible) := by
  intro hno hnp
  match (_prime_sieve n) with
    | _MyPrimeSieve.prime h | _MyPrimeSieve.zero_one h =>
      exfalso
      contradiction
    | _MyPrimeSieve.reducible h =>
      exact h

-- For a specific MyNat, you may prove its primality
-- by decide tactic automatically.
theorem zero_not_prime : zero ∉ ℙ := by decide -- 0 ∉ ℙ
example : one ∉ ℙ := by decide -- 1 ∉ ℙ
example : succ one ∈ ℙ := by decide -- 2 ∈ ℙ
example : succ (succ one) ∈ ℙ := by decide -- 3 ∈ ℙ
example : succ (succ (succ one)) ∉ ℙ := by decide -- 4 ∉ ℙ
example : succ (succ (succ (succ one))) ∈ ℙ := by decide -- 5 ∈ ℙ
example : succ (succ (succ (succ (succ one)))) ∉ ℙ := by decide -- 6 ∉ ℙ
example : succ (succ (succ (succ (succ (succ one))))) ∈ ℙ := by decide -- 7 ∈ ℙ
example : succ (succ (succ (succ (succ (succ (succ one)))))) ∉ ℙ := by decide -- 8 ∉ ℙ

end MyNat
