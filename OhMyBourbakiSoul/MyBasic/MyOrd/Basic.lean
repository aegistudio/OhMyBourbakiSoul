universe u
variable {α : Type u}

namespace MyOrd

class MyPartialOrd (α : Type u) extends LE α where
  le_refl {a : α} : (a ≤ a)
  le_trans {a b c : α} : (a ≤ b) → (b ≤ c) → (a ≤ c)
  le_antisymm {a b : α} : (a ≤ b) → (b ≤ a) → (a = b)

class MyStrictOrd (α : Type u) extends LT α where
  lt_irrefl {a : α} : ¬(a < a)
  lt_trans {a b c : α} : (a < b) → (b < c) → (a < c)
  lt_asymm {a b : α} : (a < b) → ¬(a > b)

-- Every witness of (a < b) implies (a ≠ b), by
-- reasoning on the axioms of strict order.
theorem ne_if_lt [N : MyStrictOrd α] {a b : α} :
  (a < b) → (a ≠ b) := by
  intro hlt
  intro heq
  rw [heq] at hlt
  have : ¬(b < b) := N.lt_irrefl
  contradiction

theorem not_lt_if_eq [M : MyStrictOrd α] {a b : α} :
  (a = b) → ¬(a < b) := by
  intro heq
  rw [heq]
  exact M.lt_irrefl

theorem ne_if_not_le [M : MyPartialOrd α] {a b : α} :
  ¬(a ≤ b) → (a ≠ b) := by
  intro hnle heq
  rw [heq] at hnle
  have : b ≤ b := M.le_refl
  contradiction

theorem le_if_eq [M : MyPartialOrd α] {a b : α} :
  (a = b) → (a ≤ b) := by
  intro heq
  rw [heq]
  exact M.le_refl

theorem not_eq_or_gt_if_lt [N : MyStrictOrd α] {a b : α} :
  (a < b) → ¬((a = b) ∨ (a > b)) := by
  intro hlt h'
  apply Or.elim h'
  · intro heq
    have : a ≠ b := ne_if_lt hlt
    contradiction
  · intro hgt
    have : ¬(b < a) := N.lt_asymm hlt
    contradiction

theorem eq_iff_le_and_ge [M : MyPartialOrd α] {a b : α} :
  (a = b) ↔ (a ≤ b) ∧ (a ≥ b) := by
  apply Iff.intro
  · intro heq
    repeat rw [heq]
    have h : b ≤ b := M.le_refl
    exact And.intro h h
  · intro hlege
    rcases hlege with ⟨hle, hge⟩
    exact M.le_antisymm hle hge

def decide_eq_with_decidable_partial_ord (a b : α)
  [N : MyPartialOrd α] [D : DecidableLE α] : Decidable (a = b) := by
  match (D a b) with
    | isTrue (h : a ≤ b) =>
      match (D b a) with
        | isTrue (h' : b ≤ a) =>
          have heq := (N.le_antisymm h h')
          exact Decidable.isTrue heq
        | isFalse (h' : ¬(b ≤ a)) =>
          have hne := ne_if_not_le h'
          symm at hne
          exact Decidable.isFalse hne
    | isFalse (h : ¬(a ≤ b)) =>
      have hne := ne_if_not_le h
      exact Decidable.isFalse hne

instance instDecidableEq
  [N : MyPartialOrd α] [D : DecidableLE α] : DecidableEq α := by
  intro a b
  exact decide_eq_with_decidable_partial_ord a b

-- Note: [MyStrictOrd α] plus [D : DecidableLT α] DOES NOT
-- imply [DecidableEq α]. Consider the strict order {(0, 1)}
-- on {0, 1, 2}, although we can imply 0 ≠ 1 when we witness
-- 0 < 1, we can't decide whether it's (a = b) or (a ≠ b)
-- when we witness ¬(a < b) ∧ ¬(b < a). For example, when
-- a := 0, b := 0, it's the case that a = b; when
-- a := 1, b := 2, it's the case that a ≠ b. In fact, it's
-- required to be total if we want it to be [DecidableEq α].

-- If witness present, a partial order relation is
-- never a strict order relation, and vice versa.
theorem partial_never_strict_witness
  {M : MyPartialOrd α} {N : MyStrictOrd α} :
  α → (M.le ≠ N.lt) := by
  intro a heq
  have hle : M.le a a := M.le_refl
  have hnlt : ¬(N.lt a a) := N.lt_irrefl
  rw [heq] at hle
  contradiction

theorem partial_never_strict_inhabited
  [i : Inhabited α]
  {M : MyPartialOrd α} {N : MyStrictOrd α} :
  (M.le ≠ N.lt) := by
  apply partial_never_strict_witness i.default

theorem LE_eq_iff {O₁ O₂ : LE α} :
  (O₁.le = O₂.le) ↔ (O₁ = O₂) := by
  rcases O₁ with ⟨le₁⟩
  rcases O₂ with ⟨le₂⟩
  change (le₁ = le₂) ↔ (LE.mk le₁) = (LE.mk le₂)
  apply Iff.intro
  · intro h
    rw [h]
  · intro h'
    injection h'

theorem partial_eq_def {O₁ O₂ : MyPartialOrd α} :
  (O₁.le = O₂.le) ↔ (O₁ = O₂) := by
  cases O₁
  rename_i le₁ le_refl₁ le_trans₁ le_antisymm₁
  generalize hO₁ : MyPartialOrd.mk (toLE := le₁)
    le_refl₁ le_trans₁ le_antisymm₁ = O₁
  cases O₂
  rename_i le₂ le_refl₂ le_trans₂ le_antisymm₂
  generalize hO₂ : MyPartialOrd.mk (toLE := le₂)
    le_refl₂ le_trans₂ le_antisymm₂ = O₂
  rw [LE_eq_iff]
  rw (occs := [1]) [<-hO₁, <-hO₂]
  change (le₁ = le₂) ↔ (O₁ = O₂)
  apply Iff.intro
  · intro h
    subst h
    rw [<-hO₁, <-hO₂]
  · intro h'
    rw [<-hO₁, <-hO₂] at h'
    injection h'

theorem LT_eq_iff {O₁ O₂ : LT α} :
  (O₁.lt = O₂.lt) ↔ (O₁ = O₂) := by
  rcases O₁ with ⟨le₁⟩
  rcases O₂ with ⟨le₂⟩
  change (le₁ = le₂) ↔ (LT.mk le₁) = (LT.mk le₂)
  apply Iff.intro
  · intro h
    rw [h]
  · intro h'
    injection h'

theorem strict_eq_def {O₁ O₂ : MyStrictOrd α} :
  (O₁.lt = O₂.lt) ↔ (O₁ = O₂) := by
  cases O₁
  rename_i lt₁ lt_irrefl₁ lt_trans₁ lt_asymm₁
  generalize hO₁ : MyStrictOrd.mk (toLT := lt₁)
    lt_irrefl₁ lt_trans₁ lt_asymm₁ = O₁
  cases O₂
  rename_i lt₂ lt_irrefl₂ lt_trans₂ lt_asymm₂
  generalize hO₂ : MyStrictOrd.mk (toLT := lt₂)
    lt_irrefl₂ lt_trans₂ lt_asymm₂ = O₂
  rw [LT_eq_iff]
  rw (occs := [1]) [<-hO₁, <-hO₂]
  change (lt₁ = lt₂) ↔ (O₁ = O₂)
  apply Iff.intro
  · intro h
    subst h
    rw [<-hO₁, <-hO₂]
  · intro h'
    rw [<-hO₁, <-hO₂] at h'
    injection h'

end MyOrd
