import OhMyBourbakiSoul.MyBasic.MyOrd.Basic
import OhMyBourbakiSoul.MyBasic.MyOrd.Compat

universe u
variable {α : Type u}

namespace MyOrd

-- Instantiating this instance will forcefully create
-- a strict order such that (a < b) ↔ (a ≤ b) ∧ (a ≠ b).
class MyInduceStrict (α : Type u) [O : MyPartialOrd α] where

namespace MyInduceStrict

variable [O : MyPartialOrd α]

-- naming: "induce" when the action is to acquire
-- a MyStrictOrd from a MyPartialOrd instance;
-- "induced" when it's associated to the MyStrictOrd
-- instance to construct.
def induced_lt (a b : α) : Prop := (a ≤ b) ∧ (a ≠ b)

instance instInducedLT [MyInduceStrict α] : LT α where
  lt := induced_lt

variable [I : MyInduceStrict α]

theorem induced_lt_def {a b: α} :
  (a < b) ↔ (a ≤ b) ∧ (a ≠ b) := by rfl

theorem induced_lt_irrefl {a : α} : ¬(a < a) := by
  intro ha
  rw [induced_lt_def] at ha
  have : (a : α) ≠ (a : α) := And.right ha
  contradiction

theorem induced_lt_trans {a b c : α} :
  (a < b) → (b < c) → (a < c) := by
  intro hab hbc
  rw [induced_lt_def] at hab hbc
  rw [induced_lt_def]
  rcases hab with ⟨haleb, haneb⟩
  rcases hbc with ⟨hblec, hbnec⟩
  apply And.intro
  · apply O.le_trans haleb hblec
  · intro haeqc
    have hcleb : (c : α) ≤ (b : α) := by
      rw [haeqc] at haleb
      exact haleb
    have hbeqc : (b : α) = (c : α) := by
      apply O.le_antisymm hblec hcleb
    contradiction

theorem induced_lt_asymm {a b : α} :
  (a < b) → ¬(a > b) := by
  intro hab hba
  rw [GT.gt] at hba
  rw [induced_lt_def] at hab hba
  rcases hab with ⟨haleb, haneb⟩
  rcases hba with ⟨hblea, hbnea⟩
  have : (a : α) = (b : α) := O.le_antisymm haleb hblea
  contradiction

instance instInducedStrict : MyStrictOrd α where
  lt_irrefl := induced_lt_irrefl
  lt_asymm := induced_lt_asymm
  lt_trans := induced_lt_trans

instance instInducedCompat : MyCompatOrd
  (M := O) (N := instInducedStrict) where
  compat := induced_lt_def

end MyInduceStrict

def _induce_strict_instance (O : MyPartialOrd α) :
  MyInduceStrict α (O := O) := by constructor

def induce_strict (O : MyPartialOrd α) : MyStrictOrd α := by
  exact (_induce_strict_instance O).instInducedStrict

-- MyStrictOrder α → InducedPartial α
class MyInducePartial (α : Type u) [O : MyStrictOrd α] where

namespace MyInducePartial

variable [O : MyStrictOrd α]

def induced_le (a b : α) : Prop := (a < b) ∨ (a = b)

instance instInducedLE [MyInducePartial α]: LE α where
  le := induced_le

variable [I : MyInducePartial α]

theorem induced_le_def {a b: α} :
  (a ≤ b) ↔ (a < b) ∨ (a = b) := by rfl

theorem induced_le_refl {a : α} : (a ≤ a) := by
  rw [induced_le_def]
  apply Or.inr rfl

theorem induced_le_trans {a b c : α} :
  (a ≤ b) → (b ≤ c) → (a ≤ c) := by
  intro hab hbc
  rw [induced_le_def] at hab hbc
  rw [induced_le_def]
  apply Or.elim hab
  · intro haltb
    apply Or.elim hbc
    · intro hbltc
      exact Or.inl (O.lt_trans haltb hbltc)
    · intro hbeqc
      have haltc : (a : α) < (c : α) := by
        rw [hbeqc] at haltb
        exact haltb
      exact Or.inl haltc
  · intro haeqb
    rw [<-haeqb] at hbc
    exact hbc

theorem induced_le_antisymm {a b : α} :
  (a ≤ b) → (b ≤ a) → (a = b) := by
  intro hab hba
  rw [induced_le_def] at hab hba
  apply Or.elim hab
  · intro haltb
    apply Or.elim hba
    · intro hblta
      exfalso
      have : ¬((a : α) < (b : α)) := O.lt_asymm hblta
      contradiction
    · intro hbeqa
      exfalso
      have : (a : α) < (a : α) := by
        rw [hbeqa] at haltb
        exact haltb
      have : ¬((a : α) < (a : α)) := O.lt_irrefl
      contradiction
  · intro haeqb
    exact haeqb

instance instInducedPartial : MyPartialOrd α where
  le_refl := induced_le_refl
  le_trans := induced_le_trans
  le_antisymm := induced_le_antisymm

theorem induced_le_compat {a b : α} :
  (a < b) ↔ (a ≤ b) ∧ (a ≠ b) := by
  rw [induced_le_def]
  apply Iff.intro
  · intro hlt
    have hne : a ≠ b := ne_if_lt hlt
    exact And.intro (Or.inl hlt) hne
  · intro h
    rcases h with ⟨hlteq, hne⟩
    apply Or.elim hlteq
    · intro hlt
      exact hlt
    · intro heq
      exfalso
      contradiction

instance instInducedCompat : MyCompatOrd α
  (M := instInducedPartial) (N := O) where
  compat := induced_le_compat

end MyInducePartial

-- It's not intended for the user of this module
-- to expand and reason in this instance directly.
def _induce_partial_instance (O : MyStrictOrd α) :
  MyInducePartial α (O := O) := by constructor

def induce_partial (O : MyStrictOrd α) : MyPartialOrd α := by
  exact (_induce_partial_instance O).instInducedPartial

theorem induce_strict_cancel_induce_partial
  [O : MyStrictOrd α] :
  (induce_strict (induce_partial O)) = O := by
  rw [<-strict_eq_def]
  funext a b
  generalize hrO : induce_partial O = rO
  unfold induce_partial at hrO
  generalize hrrO : induce_strict rO = rrO
  unfold induce_strict at hrrO
  unfold MyInduceStrict.instInducedStrict at hrrO
  unfold MyInduceStrict.instInducedLT at hrrO
  rw [<-hrrO]
  generalize hrI : _induce_strict_instance rO = rI
  rw [MyInduceStrict.induced_lt_def (I := rI)]
  unfold MyInducePartial.instInducedPartial at hrO
  unfold MyInducePartial.instInducedLE at hrO
  rw [<-hrO]
  rw [MyInducePartial.induced_le_def
    (O := O) (I := _induce_partial_instance O)]
  apply Eq.propIntro
  · intro h
    rcases h with ⟨hlteq, hne⟩
    apply Or.elim hlteq
    · intro h
      exact h
    · intro h
      contradiction
  · intro h
    apply And.intro
    · exact Or.inl h
    · exact ne_if_lt (N := O) h

-- For the following proof, let's have a look
-- at these lemmas first.
theorem le_and_ne_or_not_le_implies_le
  [O : MyPartialOrd α] {a b : α} :
  ((a ≤ b) ∧ (a ≠ b)) ∨ (a = b) → (a ≤ b) := by
  intro h
  apply Or.elim h
  · intro h
    exact And.left h
  · intro h
    rw [h]
    apply O.le_refl

theorem le_implies_le_and_or_not_le_then_decidable_eq
  [O : MyPartialOrd α] {a b : α} :
  ((a ≤ b) ∧ (a ≠ b)) ∨ (a = b) →
  (a = b) ∨ (a ≠ b) := by
  intro h
  apply Or.elim h
  · intro h'
    apply Or.inr (And.right h')
  · intro h'
    apply Or.inl h'

-- But generally speaking, knowing (a ≤ b) as a
-- partial order does not necessarily imply we know
-- how to compare a and b, so there's no guarantee
-- of knowing (a = b) ∨ (a ≠ b) to be true.
theorem induce_partial_cancel_induce_strict_decidable_eq
  [O : MyPartialOrd α] [D : DecidableEq α] :
  (induce_partial (induce_strict O)) = O := by
  rw [<-partial_eq_def]
  funext a b
  generalize hrO : induce_strict O = rO
  unfold induce_strict at hrO
  generalize hrrO : induce_partial rO = rrO
  unfold induce_partial at hrrO
  unfold MyInducePartial.instInducedPartial at hrrO
  unfold MyInducePartial.instInducedLE at hrrO
  rw [<-hrrO]
  generalize hrI : _induce_partial_instance rO = rI
  rw [MyInducePartial.induced_le_def (I := rI)]
  unfold MyInduceStrict.instInducedStrict at hrO
  unfold MyInduceStrict.instInducedLT at hrO
  rw [<-hrO]
  rw [MyInduceStrict.induced_lt_def
    (O := O) (I := _induce_strict_instance O)]
  apply Eq.propIntro
  · intro h
    apply Or.elim h
    · intro h'
      exact And.left h'
    · intro h'
      rw [h']
      apply O.le_refl
  · intro hle
    -- And now, we are required to show (a ≤ b)
    -- implies (a ≤ b) ∧ (a ≠ b) ∨ (a = b). If
    -- it can be done, it literally means
    -- DecidableEq α is dispensible as soon as
    -- we have MyPartialOrd α. I don't think
    -- it's possible to infer (a = b) ∨ (a ≠ b)
    -- from simply partial order (a ≤ b).
    match (D a b) with
    | Decidable.isTrue (h : a = b) =>
      exact Or.inr h
    | Decidable.isFalse (h : a ≠ b) =>
      exact Or.inl (And.intro hle h)

end MyOrd
