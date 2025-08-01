import OhMyBourbakiSoul.MyNat.Basic
import OhMyBourbakiSoul.MyNat.AddDef

namespace MyNat

def le (a b : MyNat) : Prop :=
  ∃ c, a + c = b

instance instLE : LE MyNat where
  le := le

@[simp] theorem le_def {a b : MyNat} :
  (a ≤ b) ↔ (∃ c, a + c = b) := by
  rfl

theorem le_refl {a : MyNat} : (a ≤ a) := by
  rw [le_def]
  exists zero

theorem zero_le {a : MyNat} : (zero ≤ a) := by
  rw [le_def]
  exists a
  rw [zero_add]

theorem le_succ {a : MyNat} : (a ≤ succ a) := by
  rw [le_def]
  exists one

theorem le_trans {a b c : MyNat} :
  (a ≤ b) → (b ≤ c) → (a ≤ c) := by
  intro hab hbc
  rw [le_def] at hab
  rcases hab with ⟨d, hd⟩
  rw [le_def] at hbc
  rcases hbc with ⟨e, he⟩
  rw [le_def]
  exists d + e
  rw [<-add_assoc, hd, he]

theorem le_antisymm {a b : MyNat} :
  (a ≤ b) → (b ≤ a) → (a = b) := by
  intro hab hba
  rw [le_def] at hab
  rcases hab with ⟨d, hd⟩
  rw [le_def] at hba
  rcases hba with ⟨e, he⟩
  have hde : d + e = zero := by
    rw [<-hd] at he
    rw [add_assoc] at he
    apply add_eq_self_cancel he
  have hd' : d = zero := add_eq_zero_cancel_left hde
  rw [hd'] at hd
  rw [add_zero] at hd
  exact hd

-- TODO: instPartialOrder

theorem le_add_cancel {a b c : MyNat} :
  (a + c ≤ b + c) ↔ (a ≤ b) := by
  apply Iff.intro
  · intro hacbc
    rw [le_def] at hacbc
    rcases hacbc with ⟨d, hd⟩
    rw [le_def]
    exists d
    rw [add_assoc] at hd
    rw [add_comm (a := c) (b := d)] at hd
    rw [<-add_assoc] at hd
    rw [add_cancel] at hd
    exact hd
  · intro hab
    rw [le_def] at hab
    rcases hab with ⟨d, hd⟩
    rw [le_def]
    exists d
    rw [add_comm (a := a) (b := c)]
    rw [add_assoc]
    rw [hd]
    rw [add_comm]

theorem le_succ_cancel {a b : MyNat} :
  (succ a ≤ succ b) ↔ (a ≤ b) := by
  repeat rw [succ_eq_add_one]
  rw [le_add_cancel]

theorem le_add_cancel_left {a b c : MyNat} :
  (c + a ≤ c + b) ↔ (a ≤ b) := by
  rw [add_comm (a := c) (b := a)]
  rw [add_comm (a := c) (b := b)]
  apply le_add_cancel

theorem le_combine {a b c d: MyNat} :
  (a ≤ b) → (c ≤ d) → (a + c ≤ b + d) := by
  intro hab hcd
  rw [le_def] at hab
  rcases hab with ⟨e, hd⟩
  rw [le_def] at hcd
  rcases hcd with ⟨f, he⟩
  rw [le_def]
  exists (e + f)
  rw [add_assoc]
  rw [add_comm (a := c)]
  rw [<-add_assoc]
  rw [<-add_assoc]
  rw [hd]
  rw [add_assoc]
  rw [add_comm (a := f) (b := c)]
  rw [he]

def lt (a b : MyNat) :=
  (a ≤ b) ∧ (a ≠ b)

instance instLT : LT MyNat where
  lt := lt

@[simp] theorem lt_def {a b : MyNat} :
  (a < b) ↔ (a ≤ b) ∧ (a ≠ b) := by
  rfl

theorem zero_lt_succ {a : MyNat} : zero < succ a := by
  rw [lt_def]
  apply And.intro
  · apply zero_le
  · symm
    apply succ_ne_zero

theorem zero_lt_one : zero < one := by
  rw [one_def]
  apply zero_lt_succ

theorem zero_lt_iff_ne_zero {a : MyNat} :
  (zero < a) ↔ (a ≠ zero) := by
  apply Iff.intro
  · intro h
    rw [lt_def] at h
    symm
    exact And.right h
  · intro h
    rw [ne_zero_iff_succ] at h
    rcases h with ⟨a', ha'⟩
    rw [ha']
    apply zero_lt_succ

theorem lt_succ {a : MyNat} : (a < succ a) := by
  rw [lt_def]
  apply And.intro
  · apply le_succ
  · apply ne_succ

theorem lt_irrefl {a : MyNat} : ¬(a < a) := by
  rw [lt_def]
  intro h
  apply And.right h
  rfl

theorem lt_trans {a b c : MyNat} :
  (a < b) → (b < c) → (a < c) := by
  intro hab hbc
  rw [lt_def] at hab
  rcases hab with ⟨haleb, haneb⟩
  rw [lt_def] at hbc
  rcases hbc with ⟨hblec, hbnec⟩
  rw [lt_def]
  apply And.intro
  · apply le_trans haleb hblec
  · intro haeqc
    rw [le_def] at haleb
    rcases haleb with ⟨d, hd⟩
    rw [haeqc] at hd
    have hcleb : c ≤ b := by
      rw [le_def]
      exists d
    have : b = c := le_antisymm hblec hcleb
    contradiction

theorem lt_iff_succ_le {a b : MyNat} :
  (a < b) ↔ (succ a ≤ b) := by
  apply Iff.intro
  · intro hab
    rw [lt_def] at hab
    rcases hab with ⟨haleb, haneb⟩
    rcases haleb with ⟨c, hc⟩
    cases c with
      | zero =>
        exfalso
        rw [add_zero] at hc
        contradiction
      | succ c' =>
        rw [<-succ_add_eq_add_succ] at hc
        exists c'
  · intro hasb
    rw [lt_def]
    have haas : a ≤ succ a := le_succ
    have haleb : a ≤ b := le_trans haas hasb
    apply And.intro
    · exact haleb
    · intro haeqb
      have hasa : succ a ≤ a := by
        rw [<-haeqb] at hasb
        exact hasb
      have : a = succ a := le_antisymm haas hasa
      have : a ≠ succ a := ne_succ
      contradiction

theorem lt_add_cancel {a b c : MyNat} :
  (a + c < b + c) ↔ (a < b) := by
  rw [lt_iff_succ_le]
  rw [succ_eq_add_one]
  rw [add_assoc]
  rw [add_comm (a := c) (b := one)]
  rw [<-add_assoc]
  rw [le_add_cancel]
  rw [<-succ_eq_add_one]
  rw [<-lt_iff_succ_le]

theorem lt_add_cancel_left {a b c : MyNat} :
  (c + a < c + b) ↔ (a < b) := by
  rw [add_comm (a := c) (b := a)]
  rw [add_comm (a := c) (b := b)]
  apply lt_add_cancel

theorem lt_succ_cancel {a b : MyNat} :
  (succ a < succ b) ↔ (a < b) := by
  repeat rw [succ_eq_add_one]
  rw [lt_add_cancel]

theorem le_combine_lt {a b c d : MyNat} :
  (a ≤ b) → (c < d) → (a + c < b + d) := by
  intro hab
  intro hcd
  rw [lt_iff_succ_le] at hcd
  have h := le_combine hab hcd
  rw [add_succ] at h
  rw [<-lt_iff_succ_le] at h
  exact h

theorem lt_combine_le {a b c d : MyNat} :
  (a < b) → (c ≤ d) → (a + c < b + d) := by
  intro hab
  intro hcd
  rw [add_comm (a := a) (b := c)]
  rw [add_comm (a := b) (b := d)]
  apply le_combine_lt hcd hab

theorem lt_combine {a b c d : MyNat} :
  (a < b) → (c < d) → (a + c < b + d) := by
  intro hab
  rw [lt_def] at hab
  have hab' := And.left hab
  intro hcd
  apply le_combine_lt hab' hcd

inductive Cmp (a b : MyNat) where
  | lt (hlt : a < b)
  | eq (heq : a = b)
  | gt (hgt : b < a)

def cmp (a b : MyNat) : Cmp a b := by
  match a with
    | zero =>
      match b with
        | zero =>
          exact Cmp.eq (Eq.refl zero)
        | succ b' =>
          exact Cmp.lt (zero_lt_succ (a := b'))
    | succ a' =>
      match b with
        | zero =>
          exact Cmp.gt (zero_lt_succ (a := a'))
        | succ b' =>
          match (cmp a' b') with
            | Cmp.lt (hlt : a' < b') =>
              rw [<-lt_succ_cancel] at hlt
              exact Cmp.lt hlt
            | Cmp.eq (heq : a' = b') =>
              rw [<-succ_inj] at heq
              exact Cmp.eq heq
            | Cmp.gt (hgt : b' < a') =>
              rw [<-lt_succ_cancel] at hgt
              exact Cmp.gt hgt

theorem lt_threeway {a b : MyNat} :
  (a < b) ∨ (a = b) ∨ (a > b) := by
  match (cmp a b) with
    | Cmp.lt hlt =>
      exact Or.inl hlt
    | Cmp.eq heq =>
      exact Or.inr (Or.inl heq)
    | Cmp.gt hgt =>
      exact Or.inr (Or.inr hgt)

theorem le_total {a b : MyNat} :
  (a ≤ b) ∨ (b ≤ a) := by
  match (cmp a b) with
    | Cmp.lt hlt =>
      rw [lt_def] at hlt
      exact Or.inl (And.left hlt)
    | Cmp.eq heq =>
      rw [heq]
      exact Or.inl le_refl
    | Cmp.gt hgt =>
      rw [lt_def] at hgt
      exact Or.inr (And.left hgt)

theorem le_iff_not_gt {a b : MyNat} :
  (a ≤ b) ↔ ¬(b < a) := by
  apply Iff.intro
  · intro hab
    intro hba
    rw [lt_def] at hba
    have : a = b := le_antisymm hab (And.left hba)
    have : a ≠ b := by
      symm
      apply And.right hba
    contradiction
  · intro hnba
    match (cmp a b) with
      | Cmp.lt (hlt : a < b) =>
        rw [lt_def] at hlt
        exact And.left hlt
      | Cmp.eq (heq : a = b) =>
        rw [heq]
        exact le_refl
      | Cmp.gt (hgt : a > b) =>
        exfalso
        exact hnba hgt

theorem le_iff_lt_or_eq {a b : MyNat} :
  (a ≤ b) ↔ (a < b) ∨ (a = b) := by
  apply Iff.intro
  · intro hab
    match (cmp a b) with
      | Cmp.lt hlt =>
        exact Or.inl hlt
      | Cmp.eq heq =>
        exact Or.inr heq
      | Cmp.gt hgt =>
        exfalso
        rw [le_iff_not_gt] at hab
        contradiction
  · intro h
    apply Or.elim h
    · intro h₁
      rw [lt_def] at h₁
      exact And.left h₁
    · intro h₂
      rw [h₂]
      exact le_refl

end MyNat
