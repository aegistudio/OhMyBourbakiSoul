import OhMyBourbakiSoul.MyBasic.MySet.Basic
import OhMyBourbakiSoul.MyBasic.MySet.Subset

universe u
variable {α : Type u}

namespace MySet

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
