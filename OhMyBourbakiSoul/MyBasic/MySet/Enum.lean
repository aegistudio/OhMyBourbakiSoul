import OhMyBourbakiSoul.MyBasic.MySet.Basic
import OhMyBourbakiSoul.MyBasic.MyLogic.ExistsUniq

universe u
variable {α : Type u}

namespace MySet

def singleton (e : α) : MySet α := { a | a = e }

instance instSingleton : Singleton α (MySet α) where
  singleton := singleton

theorem mem_singleton_iff {a e : α} :
  (a ∈ ({e} : MySet α)) ↔ (a = e) := by
  change (a ∈ singleton e) ↔ (a = e)
  unfold singleton
  change (a = e) ↔ (a = e)
  rfl

def insert (e : α) (s : MySet α) : MySet α :=
  { a | (a = e) ∨ (a ∈ s) }

instance instInsert : Insert α (MySet α) where
  insert := insert

theorem lawful_singleton_set :
  ∀ (a : α), insert a ∅ = ({a} : MySet α) := by
  intro a
  change insert a ∅ = singleton a
  unfold insert
  unfold singleton
  rw [eq_def]
  funext x
  change (x = a ∨ False) = (x = a)
  apply Eq.propIntro
  · intro h
    apply Or.elim h
    · intro h
      exact h
    · intro h
      exfalso
      contradiction
  · intro h
    exact Or.inl h

instance instLawfulSingleton : LawfulSingleton α (MySet α) where
  insert_empty_eq := lawful_singleton_set

theorem mem_paired_set_iff {a e₁ e₂ : α} :
  (a ∈ ({e₁, e₂} : MySet α)) ↔ (a = e₁) ∨ (a = e₂) := by
  change (a ∈ insert e₁ (singleton e₂)) ↔ (a = e₁) ∨ (a = e₂)
  unfold singleton
  unfold insert
  change (a = e₁) ∨ (a = e₂) ↔ (a = e₁) ∨ (a = e₂)
  rfl

theorem singleton_if_paired_identity {a : α} :
  {a, a} = ({a} : MySet α) := by
  rw [eq_iff]
  intro a'
  rw [mem_paired_set_iff]
  rw [mem_singleton_iff]
  apply Iff.intro
  · intro h
    apply Or.elim h <;> (intro h'; exact h')
  · intro h
    exact Or.inl h

theorem singleton_iff_exists_uniq {s : MySet α} :
  (ExistsUniq s.pred) ↔ (∃ (e : α), s = {e}) := by
  apply Iff.intro
  · intro h
    rcases h with ⟨e, he⟩
    exists e
    rw [eq_iff]
    intro a
    rw [mem_singleton_iff]
    apply Iff.intro
    · intro has
      rw [mem_def] at has
      have heq := ((And.right he) a) has
      symm at heq
      exact heq
    · intro heq
      rw [heq]
      rw [mem_def]
      exact And.left he
  · intro h
    rcases h with ⟨e, he⟩
    exists e
    apply And.intro
    · rw [<-mem_def (s := s)]
      rw [he]
      rw [mem_singleton_iff]
    · intro b hsb
      rw [<-mem_def (s := s)] at hsb
      rw [he] at hsb
      rw [mem_singleton_iff] at hsb
      symm at hsb
      exact hsb

end MySet
