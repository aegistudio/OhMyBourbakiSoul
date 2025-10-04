import OhMyBourbakiSoul.MyBasic.MySet.OpsDef
import OhMyBourbakiSoul.MyBasic.MySet.Restrict

universe u v
variable {α : Type u} {β : Type v}

namespace MySet

def prod (X : MySet α) (Y : MySet β) : MySet (α × β) :=
  { ((a, b) : α × β) | (a ∈ X) ∧ (b ∈ Y) }

infix:0 " × " => prod

variable {X X₁ X₂ : MySet α} {x : α}
variable {Y Y₁ Y₂ : MySet β} {y : β}

theorem prod_def :
  (x, y) ∈ (X × Y) ↔ (x ∈ X) ∧ (y ∈ Y) := by
  rfl

theorem prod_comm :
  (x, y) ∈ (X × Y) ↔ (y, x) ∈ (Y × X) := by
  repeat rw [prod_def]
  exact And.comm

theorem prod_bigcup {A : MySet (MySet α)} :
  ((⋃ A) × Y) = ⋃ {(X × Y) || X ∈ A} := by
  rw [eq_iff]
  intro (x, y)
  rw [prod_def]
  repeat rw [bigcup_def]
  apply Iff.intro
  · intro ⟨hX, hyY⟩
    rcases hX with ⟨X, ⟨hXA, hxX⟩⟩
    exists (X × Y)
    apply And.intro
    · rw [transform_def]
      exists X
    · rw [prod_def]
      exact ⟨hxX, hyY⟩
  · intro ⟨XY, hXY⟩
    rw [transform_def] at hXY
    rcases hXY with ⟨hXA, hxyXY⟩
    rcases hXA with ⟨X, ⟨hXA, hXY⟩⟩
    rw [hXY] at hxyXY
    rw [prod_def] at hxyXY
    rcases hxyXY with ⟨hxX, hyY⟩
    apply And.intro
    · exists X
    · exact hyY

theorem prod_intersect :
  ((X₁ × Y₁) ∩ (X₂ × Y₂)) = ((X₁ ∩ X₂) × (Y₁ ∩ Y₂)) := by
  rw [eq_iff]
  intro (x, y)
  rw [intersect_def]
  repeat rw [prod_def]
  rw [<-and_assoc]
  rw [and_assoc (c := x ∈ X₂)]
  rw [And.comm (a := y ∈ Y₁)]
  rw [<-and_assoc (c := y ∈ Y₁)]
  rw [and_assoc]
  repeat rw [<-intersect_def]

theorem prod_union_left :
  (X × (Y₁ ∪ Y₂)) = (X × Y₁) ∪ (X × Y₂) := by
  rw [eq_iff]
  intro (x, y)
  rw [prod_def]
  rw [union_def]
  rw [and_or_left]
  repeat rw [<-prod_def]
  rw [<-union_def]

theorem prod_union_right {X₁ X₂ : MySet α} {Y : MySet β} :
  ((X₁ ∪ X₂) × Y) = (X₁ × Y) ∪ (X₂ × Y) := by
  rw [eq_iff]
  intro (x, y)
  rw [union_def]
  repeat rw [<-prod_comm (X := Y)]
  rw [<-union_def]
  rw [prod_union_left]

end MySet
