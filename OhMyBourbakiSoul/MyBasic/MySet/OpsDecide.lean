import OhMyBourbakiSoul.MyBasic.MySet.OpsDef

universe u
variable {α : Type u}

namespace MySet

instance instDecideUnion {s₁ s₂ : MySet α}
  [s₁.decidable] [s₂.decidable] :
  (s₁ ∪ s₂).decidable := by
  intro x
  rw [<-mem_def]
  rw [union_def]
  infer_instance

instance instDecideIntersect {s₁ s₂ : MySet α}
  [s₁.decidable] [s₂.decidable] :
  (s₁ ∩ s₂).decidable := by
  intro x
  rw [<-mem_def]
  rw [intersect_def]
  infer_instance

instance instDecideComplement {s : MySet α}
  [s.decidable] : (sᶜ).decidable := by
  intro x
  rw [<-mem_def]
  rw [complement_def]
  infer_instance

instance instDecideSetDiff {s₁ s₂ : MySet α}
  [s₁.decidable] [s₂.decidable] :
  (s₁ \ s₂).decidable := by
  intro x
  rw [<-mem_def]
  rw [sdiff_def]
  infer_instance

end MySet
