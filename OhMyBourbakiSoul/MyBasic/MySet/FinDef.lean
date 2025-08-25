import OhMyBourbakiSoul.MyBasic.MyOrd.Cmp
import OhMyBourbakiSoul.MyBasic.MySet.Basic
import OhMyBourbakiSoul.MyBasic.MySet.Enum
import OhMyBourbakiSoul.MyBasic.MySet.OpsDef
import OhMyBourbakiSoul.MyBasic.MyFun.Basic
import OhMyBourbakiSoul.MyBasic.MyFun.IdDef
import OhMyBourbakiSoul.MyNat.Basic
import OhMyBourbakiSoul.MyNat.OrderDef
import OhMyBourbakiSoul.MyNat.Mu

open MyOrd
open MyNat

universe u
variable {α : Type u} {s : MySet α}

class MyCountSet (s : MySet α) where
  ctr : MySet MyNat
  decidable_ctr : ctr.decidable
  fn : ctr -→ s
  surj : fn.surj

namespace MySet
abbrev countable (s : MySet α) := MyCountSet s
end MySet

-- MyNat countability related.
namespace MySet

instance instMyNatCountSet : (univ MyNat).countable where
  ctr := univ MyNat
  decidable_ctr := λ x =>
    Decidable.isTrue (univ_def x)
  fn := MyFun.identity (univ MyNat)
  surj := inferInstance

end MySet

-- Reverse indexing related.
namespace MySet

variable (s : MySet α) [C : s.countable]

def _prop_index
    (a : α) (x : MyNat) :=
    (x ∈ C.ctr) ∧
    ((h : x ∈ C.ctr) → (C.fn ⟨x, h⟩).val = a)

theorem _prop_index_def {a : α} :
  (∃ x, s._prop_index a x) ↔ (a ∈ s) := by
  apply Iff.intro
  · intro h
    rcases h with ⟨x, ⟨hxC, hxa⟩⟩
    have hxa' := hxa hxC
    generalize hfx : C.fn ⟨x, hxC⟩ = fx
    rw [hfx] at hxa'
    rw [mem_def, <-hxa']
    exact fx.property
  · intro h
    rw [mem_def] at h
    rcases C.surj.surj ⟨a, h⟩ with ⟨x, hx⟩
    rw [Subtype.eq_iff] at hx
    change (C.fn x).val = a at hx
    exists x.val
    unfold _prop_index
    apply And.intro
    · exact x.property
    · intro h'
      exact hx

variable [D : DecidableEq α]

def _decide_index (a : α) :
  DecidablePred (s._prop_index a) := by
  intro x
  have d := C.decidable_ctr x
  match d with
    | Decidable.isTrue (h : x ∈ C.ctr) =>
      have d' := D (C.fn ⟨x, h⟩).val a
      unfold _prop_index
      match d' with
        | Decidable.isTrue h' =>
          apply Decidable.isTrue
          apply And.intro
          · exact h
          · intro h
            exact h'
        | Decidable.isFalse h' =>
          apply Decidable.isFalse
          intro h'
          have := (And.right h') h
          contradiction
    | Decidable.isFalse (h : x ∉ C.ctr) =>
      apply Decidable.isFalse
      unfold _prop_index
      intro h'
      have := And.left h'
      contradiction

def _index (a : s.type) :
  MyNat.Mu (s._prop_index a.val) := by
  have h : ∃ (x : MyNat), s._prop_index a.val x := by
    have h' := C.surj.surj a
    rcases h' with ⟨x, hx⟩
    exists x.val
    unfold _prop_index
    apply And.intro
    · exact x.property
    · intro h''
      have heq : x = ⟨x.val, h''⟩ := by rfl
      rw [<-heq]
      rw [<-Subtype.eq_iff]
      exact hx
  have i := s._decide_index a.val
  exact MyNat.mu h

def index (a : s.type) : C.ctr.type := by
  have r := s._index a
  have h : r.val ∈ C.ctr := by
    have h' := r.sufficient
    unfold _prop_index at h'
    have hr := And.left h'
    rw [mem_def] at hr
    exact hr
  exact ⟨r.val, h⟩

theorem index_def {a : s.type} :
  C.fn (s.index a) = a := by
  have h : s._prop_index a.val (s.index a).val := by
    unfold index
    change s._prop_index a.val (s._index a).val
    generalize s._index a = r
    exact r.sufficient
  unfold _prop_index at h
  have h' := (And.right h) (And.left h)
  have heq : ⟨(s.index a).val, h.left⟩ = s.index a := by rfl
  rw [heq] at h'
  rw [<-Subtype.eq_iff] at h'
  exact h'

-- If a set is countable, then we are always able to
-- build an injection from the set to MyNat.
instance instIndexInj : (MyFun.mk s.index).inj := by
  apply MyInj.mk
  intro a a'
  intro h
  change s.index a = s.index a' at h
  have hf : C.fn (s.index a) = C.fn (s.index a') := by
    rw [h]
  repeat rw [index_def] at hf
  exact hf

end MySet

class MyFinSet (s : MySet α) [C : s.countable] where
  count := C
  bound : MyNat
  bounded : ∀ n ∈ C.ctr, n ≤ bound

namespace MySet
abbrev fin (s : MySet α) [C : s.countable] := MyFinSet s
end MySet

-- Finset membership related.
namespace MySet

variable (s : MySet α) [C : s.countable] [F : s.fin]
variable [D : DecidableEq α]

def _prop_mem_index (a : α) (x : MyNat) :=
    (s._prop_index a x) ∨ (x = succ F.bound)

def _decide_mem_index (a : α) :
  DecidablePred (s._prop_mem_index a) := by
  intro x
  have d : Decidable (x = succ F.bound) :=
    inferInstance
  match d with
    | Decidable.isTrue h =>
      apply Decidable.isTrue
      exact Or.inr h
    | Decidable.isFalse h =>
      have d' := s._decide_index a x
      match d' with
        | Decidable.isTrue h' =>
          apply Decidable.isTrue
          exact Or.inl h'
        | Decidable.isFalse h' =>
          apply Decidable.isFalse
          intro h''
          apply Or.elim h'' <;> (intro; contradiction)

def _mem_index (a : α) :
  MyNat.Mu (s._prop_mem_index a) := by
  have h : ∃ (x : MyNat), s._prop_mem_index a x := by
    exists (succ F.bound)
    apply Or.inr
    rfl
  have i := s._decide_mem_index a
  exact MyNat.mu h

-- Fundamental Theorem of Finite Type / Set
--
-- When a set is finite, and can decide equality
-- of every element, then we are able to decide
-- membership of elements in the set. In fact,
-- the set predicate regresses to
-- x ∈ {a₁, a₂, ..., aₙ} ↔ (x = a₁) ∨ (x = a₂) ∨ ... ∨ (x = aₙ)
-- when viewed from set theory.
instance instMemFinset
  {s : MySet α}
  [C : s.countable] [F : s.fin]
  [D : DecidableEq α] :
  s.decidable := by
  intro a
  have m := s._mem_index a
  have d : Decidable (m.val = succ F.bound) :=
    inferInstance
  match d with
    | Decidable.isTrue h =>
      apply Decidable.isFalse
      intro h'
      rw [<-mem_def (s := s)] at h'
      rw [<-_prop_index_def] at h'
      rcases h' with ⟨x, hx⟩
      have : s._prop_mem_index a x := by
        exact Or.inl hx
      have hxm : x < m.val := by
        rw [h]
        rw [lt_iff_succ_le]
        rw [le_succ_cancel]
        unfold _prop_index at hx
        exact F.bounded x (And.left hx)
      have := m.minimal x hxm
      contradiction
    | Decidable.isFalse h =>
      apply Decidable.isTrue
      have h' := Or.resolve_right m.sufficient h
      have h'' : ∃ x, s._prop_index a x := by
        exists m.val
      rw [_prop_index_def] at h''
      rw [mem_def] at h''
      exact h''

end MySet
