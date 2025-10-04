import OhMyBourbakiSoul.MyBasic.MapsTo
import OhMyBourbakiSoul.MyBasic.MySet.Basic
import OhMyBourbakiSoul.MyBasic.MySet.Subset

universe u
variable {α : Type u}

namespace MySet

variable {X X' : MySet α}

@[reducible]
def type (s : MySet α) := Subtype s.pred

instance instCoeType {s : MySet α} :
  Coe (Subtype s.pred) (s.type) where
  coe := x ↦ x

instance instCoeSubtype {s : MySet α} :
  Coe (s.type) (Subtype s.pred) where
  coe := x ↦ x

abbrev nonempty (s : MySet α) := Nonempty s.type

theorem empty_not_nonempty :
  ¬((∅ : MySet α).nonempty) := by
  intro h
  rcases h with ⟨n, hn⟩
  rw [<-mem_def] at hn
  have := empty_def n
  contradiction

def type.membership {s : MySet α} (x : s.type) : x.val ∈ s := by
  rw [mem_def]
  exact x.property

def typed {s : MySet α} (a : α) (h : a ∈ s) : s.type := by
  apply Subtype.mk a
  rw [<-mem_def]
  exact h

theorem typed_eta {s : MySet α} {a : α} {h : a ∈ s} :
  (typed a h).val = a := by
  unfold typed
  rfl

def lift_univ (x : α) : (univ α).type := by
  apply (univ α).typed
  exact univ_def x

theorem lift_univ_def {x : α} :
  (lift_univ x).val = x := by rfl

def lift_subtype (h : X ⊆ X') (x : X.type) : X'.type := by
  rw [subset_def] at h
  apply typed x.val
  exact h x.val x.membership

theorem lift_subtype_def {h : X ⊆ X'} {x : X.type} :
  (lift_subtype h x).val = x.val := by rfl

-- { x ∈ type | term }
syntax "{ " withoutPosition(ident " ∈ " term " | " term) " }" : term

@[irreducible]
def restrict (X : MySet α) (p : X.type -> Prop) :=
  { x : α | ∃ (x' : X.type), (x = x'.val) ∧ (p x') }

macro_rules
  | `({ $x ∈ $s | $p }) => `(restrict $s fun $x => $p)

-- Pretty printing when matching restrict.
@[app_unexpander restrict]
def unexpand_restrict : Lean.PrettyPrinter.Unexpander
  | `($_ $s fun $x:ident => $p) => `({ $x ∈ $s | $p })
  | _ => throw ()

theorem restrict_subset {p : X.type -> Prop} :
  (restrict X p) ⊆ X := by
  rw [subset_def]
  intro x hx
  unfold restrict at hx
  change ∃ (x' : X.type), (x = x'.val) ∧ (p x') at hx
  rcases hx with ⟨x', hx'⟩
  have hxx' := x'.membership
  rw [<-And.left hx'] at hxx'
  exact hxx'

theorem restrict_def {p : X.type -> Prop} {x : X.type}:
  (x.val ∈ restrict X p) ↔ (p x) := by
  unfold restrict
  rw [mem_def]
  change (∃ x', (x.val = x'.val) ∧ (p x')) ↔ (p x)
  apply Iff.intro
  · intro ⟨x', ⟨hxx', hpx'⟩⟩
    rw [<-Subtype.eq_iff] at hxx'
    rw [hxx']
    exact hpx'
  · intro hpx
    exists x

end MySet
