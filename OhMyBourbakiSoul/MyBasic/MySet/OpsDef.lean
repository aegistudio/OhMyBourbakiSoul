import OhMyBourbakiSoul.MyBasic.MySet.Basic
import OhMyBourbakiSoul.MyBasic.MySet.Subset
import OhMyBourbakiSoul.MyBasic.MySet.Enum
import OhMyBourbakiSoul.MyBasic.MySet.Transform

universe u
variable {α : Type u}

namespace MySet

def union (s₁ s₂ : MySet α) : MySet α :=
  { x : α | (x ∈ s₁) ∨ (x ∈ s₂) }

instance instUnion : Union (MySet α) where
  union := union

theorem union_def {a : α} {s₁ s₂ : MySet α} :
  (a ∈ (s₁ ∪ s₂)) ↔ (a ∈ s₁) ∨ (a ∈ s₂) := by
  change (a ∈ union s₁ s₂) ↔ (a ∈ s₁) ∨ (a ∈ s₂)
  change (a ∈ s₁) ∨ (a ∈ s₂) ↔ (a ∈ s₁) ∨ (a ∈ s₂)
  rfl

def bigcup (A : MySet (MySet α)) : MySet α :=
  { x : α | ∃ s ∈ A, x ∈ s }

prefix:max "⋃ " => bigcup

theorem bigcup_def {a : α} {A : MySet (MySet α)} :
  (a ∈ ⋃ A) ↔ (∃ s ∈ A, a ∈ s) := by
  change (a ∈ bigcup A) ↔ (∃ s ∈ A, a ∈ s)
  change (∃ s ∈ A, a ∈ s) ↔ (∃ s ∈ A, a ∈ s)
  rfl

def intersect (s₁ s₂ : MySet α) : MySet α :=
  { x : α | (x ∈ s₁) ∧ (x ∈ s₂) }

instance instIntersect : Inter (MySet α) where
  inter := intersect

theorem intersect_def {a : α} {s₁ s₂ : MySet α} :
  (a ∈ (s₁ ∩ s₂)) ↔ (a ∈ s₁) ∧ (a ∈ s₂) := by
  change (a ∈ intersect s₁ s₂) ↔ (a ∈ s₁) ∧ (a ∈ s₂)
  change (a ∈ s₁) ∧ (a ∈ s₂) ↔ (a ∈ s₁) ∧ (a ∈ s₂)
  rfl

def bigcap (A : MySet (MySet α)) : MySet α :=
  { x : α | ∀ s ∈ A, x ∈ s }

prefix:max "⋂ " => bigcap

theorem bigcap_def {a : α} {A : MySet (MySet α)} :
  (a ∈ ⋂ A) ↔ (∀ s ∈ A, a ∈ s) := by
  change (a ∈ bigcap A) ↔ (∀ s ∈ A, a ∈ s)
  change (∀ s ∈ A, a ∈ s) ↔ (∀ s ∈ A, a ∈ s)
  rfl

def sdiff (s₁ s₂ : MySet α) : MySet α :=
  { x : α | (x ∈ s₁) ∧ ¬(x ∈ s₂) }

instance instSetDiff : SDiff (MySet α) where
  sdiff := sdiff

theorem sdiff_def {a : α} {s₁ s₂ : MySet α} :
  (a ∈ s₁ \ s₂) ↔ (a ∈ s₁) ∧ (a ∉ s₂) := by
  change (a ∈ sdiff s₁ s₂) ↔ (a ∈ s₁) ∧ (a ∉ s₂)
  change (a ∈ s₁) ∧ ¬(a ∈ s₂) ↔ (a ∈ s₁) ∧ (a ∉ s₂)
  rfl

def complement (s : MySet α) : MySet α :=
  { x : α | (x ∉ s) }

postfix:max "ᶜ" => complement

theorem complement_def {a : α} {s : MySet α} :
  (a ∈ sᶜ) ↔ (a ∉ s) := by
  change (a ∈ complement s) ↔ (a ∉ s)
  change (a ∉ s) ↔ (a ∉ s)
  rfl

theorem sdiff_eq_cap_complement {s₁ s₂ : MySet α} :
  (s₁ \ s₂) = (s₁ ∩ s₂ᶜ) := by
  rw [eq_iff]
  intro a
  rw [sdiff_def, intersect_def, complement_def]

theorem univ_complement : (univ α)ᶜ = ∅ := by
  rw [<-empty_iff]
  intro x h
  rw [complement_def] at h
  have : x ∈ univ α := univ_def x
  contradiction

theorem empty_complement : ∅ᶜ = univ α := by
  rw [<-univ_iff]
  intro x
  rw [complement_def]
  intro h
  have : x ∉ ∅ := empty_def x
  contradiction

def powerset (s : MySet α) : MySet (MySet α) :=
  { s' : MySet α | s' ⊆ s }

prefix:max "𝒫" => powerset

theorem powerset_def {s' s : MySet α} :
  (s' ∈ 𝒫 s) ↔ (s' ⊆ s) := by
  change (s' ∈ powerset s) ↔ (s' ⊆ s)
  change (s' ⊆ s) ↔ (s' ⊆ s)
  rfl

end MySet

-- Useful and common theorems built merely on the
-- imports and definitions above.
namespace MySet

theorem bigcup_empty : (⋃ ∅) = (∅ : MySet α) := by
  rw [<-empty_iff]
  intro a h
  unfold bigcup at h
  change ∃ s, s ∈ ∅ ∧ a ∈ s at h
  rcases h with ⟨s, hs⟩
  have : s ∈ ∅ := And.left hs
  have : s ∉ ∅ := empty_def s
  contradiction

theorem bigcup_two {s₁ s₂ : MySet α} :
  (s₁ ∪ s₂) = (⋃ {s₁, s₂}) := by
  rw [eq_iff]
  intro a
  unfold bigcup
  rw [union_def]
  change a ∈ s₁ ∨ a ∈ s₂ ↔ ∃ s, (s ∈ {(s₁ : MySet α), s₂}) ∧ a ∈ s
  apply Iff.intro
  · intro h
    apply Or.elim h
    · intro h'
      exists s₁
      rw [mem_paired_set_iff]
      apply And.intro
      · exact Or.inl rfl
      · exact h'
    · intro h'
      exists s₂
      rw [mem_paired_set_iff]
      apply And.intro
      · exact Or.inr rfl
      · exact h'
  · intro h
    rcases h with ⟨s, hs⟩
    rw [mem_paired_set_iff] at hs
    rcases hs with ⟨hs, has⟩
    apply Or.elim hs
    · intro h
      rw [h] at has
      exact Or.inl has
    · intro h
      rw [h] at has
      exact Or.inr has

theorem union_comm {s₁ s₂ : MySet α} :
  (s₁ ∪ s₂) = (s₂ ∪ s₁) := by
  rw [eq_iff]
  intro a
  repeat rw [union_def]
  apply Or.comm

theorem subset_bigcup {A : MySet (MySet α)} :
  ∀ s ∈ A, s ⊆ ⋃ A := by
  intro s hsA
  rw [subset_def]
  intro a has
  rw [bigcup_def]
  exists s

theorem bigcup_supset {A : MySet (MySet α)} :
  ∀ s ∈ A, ⋃ A ⊇ s := by
  intro s
  rw [Superset]
  revert s
  exact subset_bigcup

theorem bigcup_subset_iff
  {A : MySet (MySet α)} {b : MySet α} :
  (∀ s ∈ A, s ⊆ b) ↔ (⋃ A ⊆ b) := by
  rw [subset_def]
  apply Iff.intro
  · intro h x hxA
    rw [bigcup_def] at hxA
    rcases hxA with ⟨s, hs⟩
    have h' := h s (And.left hs)
    rw [subset_def] at h'
    exact (h' x) (And.right hs)
  · intro h s hsA
    rw [subset_def]
    intro x hxs
    apply h x
    rw [bigcup_def]
    exists s

theorem subset_bigcup_if
  {A : MySet (MySet α)} {b : MySet α} :
  (∃ s ∈ A, b ⊆ s) → (b ⊆ ⋃ A) := by
  intro h
  rcases h with ⟨s, hs⟩
  rw [subset_def]
  intro a hab
  rw [bigcup_def]
  exists s
  apply And.intro
  · exact And.left hs
  · have h' := And.right hs
    rw [subset_def] at h'
    exact h' a hab

-- WARN: if not inhabited, when A = ∅, and b ≠ ∅,
-- there's lhs = b, while the rhs = ∅.
theorem bigcup_inhabited_union_distrib
  {A : MySet (MySet α)} {a₀ b : MySet α} :
  (a₀ ∈ A) → ((⋃ A) ∪ b = ⋃ { a ∪ b || a ∈ A }) := by
  intro ha₀A
  rw [eq_iff]
  intro x
  apply Iff.intro
  · intro h
    rw [union_def] at h
    rw [bigcup_def] at h
    apply Or.elim h
    · intro hxA
      rcases hxA with ⟨a₁, ha₁⟩
      rw [bigcup_def]
      exists a₁ ∪ b
      apply And.intro
      · rw [transform_def]
        exists a₁
        exact And.intro (And.left ha₁) rfl
      · rw [union_def]
        exact Or.inl (And.right ha₁)
    · intro hxb
      rw [bigcup_def]
      exists a₀ ∪ b
      apply And.intro
      · rw [transform_def]
        exists a₀
      · rw [union_def]
        exact Or.inr hxb
  · intro h
    rw [bigcup_def] at h
    rcases h with ⟨s, hs⟩
    rcases hs with ⟨hsTA, hxs⟩
    rw [transform_def] at hsTA
    rcases hsTA with ⟨a₂, ha₂⟩
    rw [And.right ha₂] at hxs
    rw [union_def, bigcup_def]
    rw [union_def] at hxs
    apply Or.elim hxs
    · intro hxa₂
      apply Or.inl
      exists a₂
      apply And.intro
      · exact And.left ha₂
      · exact hxa₂
    · intro hxb
      apply Or.inr
      exact hxb

theorem bigcup_nonempty_union_distrib
  {A : MySet (MySet α)} {b : MySet α}
  (h : Nonempty (Subtype A.pred)) :
  ((⋃ A) ∪ b = ⋃ { a ∪ b || a ∈ A }) := by
  rcases h with ⟨x, hx⟩
  rw [<-mem_def (s := A)] at hx
  exact bigcup_inhabited_union_distrib hx

theorem bigcup_intersect_distrib
  {A : MySet (MySet α)} {b : MySet α} :
  ((⋃ A) ∩ b = ⋃ { a ∩ b || a ∈ A }) := by
  rw [eq_iff]
  intro x
  apply Iff.intro
  · intro h
    rw [intersect_def] at h
    rcases h with ⟨hxTA, hxb⟩
    rw [bigcup_def] at hxTA
    rcases hxTA with ⟨a₁, ha₁⟩
    rw [bigcup_def]
    exists a₁ ∩ b
    apply And.intro
    · rw [transform_def]
      exists a₁
      apply And.intro
      · exact And.left ha₁
      · rfl
    · apply And.intro
      · exact And.right ha₁
      · exact hxb
  · intro h
    rw [bigcup_def] at h
    rcases h with ⟨s, hs⟩
    rcases hs with ⟨hsTA, hxs⟩
    rw [transform_def] at hsTA
    rcases hsTA with ⟨a₁, ha₁⟩
    rw [And.right ha₁] at hxs
    rw [intersect_def] at hxs
    rw [intersect_def]
    apply And.intro
    · rw [bigcup_def]
      exists a₁
      apply And.intro
      · exact And.left ha₁
      · exact And.left hxs
    · exact And.right hxs

theorem bigcap_empty : (⋂ ∅) = (univ α) := by
  rw [<-univ_iff]
  intro a
  unfold bigcap
  change ∀ (s : MySet α), s ∈ ∅ → a ∈ s
  intro s hsn
  exfalso
  have : s ∉ ∅ := empty_def s
  contradiction

theorem bigcap_two {s₁ s₂ : MySet α} :
  (s₁ ∩ s₂) = (⋂ {s₁, s₂}) := by
  rw [eq_iff]
  intro a
  unfold bigcap
  rw [intersect_def]
  change a ∈ s₁ ∧ a ∈ s₂ ↔ ∀ s, ((s ∈ {(s₁ : MySet α), s₂}) → a ∈ s)
  apply Iff.intro
  · intro h s
    rw [mem_paired_set_iff]
    intro h'
    apply Or.elim h'
    · intro heq
      rw [heq]
      exact And.left h
    · intro heq
      rw [heq]
      exact And.right h
  · intro h
    apply And.intro
    · have hp : s₁ ∈ ({s₁, s₂} : MySet (MySet α)) := by
        rw [mem_paired_set_iff]
        exact Or.inl rfl
      exact (h s₁) hp
    · have hp : s₂ ∈ ({s₁, s₂} : MySet (MySet α)) := by
        rw [mem_paired_set_iff]
        exact Or.inr rfl
      exact (h s₂) hp

theorem intersect_comm {s₁ s₂ : MySet α} :
  (s₁ ∩ s₂) = (s₂ ∩ s₁) := by
  rw [eq_iff]
  intro a
  repeat rw [intersect_def]
  apply And.comm

theorem bigcap_subset {A : MySet (MySet α)} :
  ∀ s ∈ A, ⋂ A ⊆ s := by
  intro s hsA
  rw [subset_def]
  intro a haN
  rw [bigcap_def] at haN
  exact haN s hsA

theorem intersect_subset_right {a b : MySet α} :
  (a ∩ b ⊆ b) := by
  rw [bigcap_two]
  apply bigcap_subset b
  rw [mem_paired_set_iff]
  exact Or.inr rfl

theorem intersect_subset_left {a b : MySet α} :
  (a ∩ b ⊆ a) := by
  rw [intersect_comm]
  exact intersect_subset_right

theorem intersect_empty {a : MySet α} :
  (a ∩ ∅) = ∅ := by
  have h : ∅ ⊆ (a ∩ ∅) := empty_subset
  have h' : (a ∩ ∅) ⊆ ∅ := intersect_subset_right
  exact subset_antisymm h' h

theorem subset_bigcap_iff
  {a : MySet α} {B : MySet (MySet α)} :
  (∀ b ∈ B, a ⊆ b) ↔ (a ⊆ ⋂ B) := by
  rw [subset_def]
  apply Iff.intro
  · intro h x hxa
    rw [bigcap_def]
    intro s hsB
    have h' := h s hsB
    rw [subset_def] at h'
    exact (h' x) hxa
  · intro h s hsB
    rw [subset_def]
    intro x hxa
    apply h x hxa
    exact hsB

-- WARN: if not inhabited, when A = ∅, and b ≠ univ,
-- there's lhs = b while the rhs = univ.
theorem bigcap_inhabited_intersect_distrib
  {A : MySet (MySet α)} {a₀ b : MySet α} :
  (a₀ ∈ A) → ((⋂ A) ∩ b = ⋂ { a ∩ b || a ∈ A }) := by
  intro ha₀A
  rw [eq_iff]
  intro x
  apply Iff.intro
  · intro h
    rw [intersect_def] at h
    rw [bigcap_def] at h
    rcases h with ⟨hxA, hxb⟩
    rw [bigcap_def]
    intro s hs
    rw [transform_def] at hs
    rcases hs with ⟨a₁, ha₁⟩
    rw [And.right ha₁]
    rw [intersect_def]
    apply And.intro
    · exact hxA a₁ (And.left ha₁)
    · exact hxb
  · intro h
    rw [bigcap_def] at h
    rw [intersect_def]
    apply And.intro
    · rw [bigcap_def]
      intro a₁ ha₁
      have ha₁b : a₁ ∩ b ⊆ a₁ :=
        intersect_subset_left
      apply subset_def.mp ha₁b
      apply h
      rw [transform_def]
      exists a₁
    · have ha₀b : a₀ ∩ b ⊆ b :=
        intersect_subset_right
      apply subset_def.mp ha₀b
      apply h
      rw [transform_def]
      exists a₀

theorem bigcap_nonempty_intersect_distrib
  {A : MySet (MySet α)} {b : MySet α}
  (h : Nonempty (Subtype A.pred)) :
  ((⋂ A) ∩ b = ⋂ { a ∩ b || a ∈ A }) := by
  rcases h with ⟨x, hx⟩
  rw [<-mem_def (s := A)] at hx
  exact bigcap_inhabited_intersect_distrib hx

theorem bigcap_union_subdistrib
  {A : MySet (MySet α)} {b : MySet α} :
  ((⋂ A) ∪ b ⊆ ⋂ { a ∪ b || a ∈ A }) := by
  rw [subset_def]
  intro x h
  rw [union_def] at h
  rw [bigcap_def]
  intro s hs
  rw [transform_def] at hs
  rcases hs with ⟨a₁, ha₁⟩
  rw [And.right ha₁]
  rw [union_def]
  apply Or.elim h
  · intro hxA
    rw [bigcap_def] at hxA
    apply Or.inl
    apply hxA a₁
    exact And.left ha₁
  · intro hxb
    exact Or.inr hxb

theorem bigcap_union_distrib_if_exclusive_mem
  {A : MySet (MySet α)} {b : MySet α} :
  (∀ (x : α), (x ∈ b) ∨ (x ∉ b)) →
  ((⋂ A) ∪ b = ⋂ { a ∪ b || a ∈ A }) := by
  intro hp
  rw [eq_iff]
  intro x
  have hp' := hp x
  apply Iff.intro
  · apply subset_def.mpr
    rw [<-subset_def]
    exact bigcap_union_subdistrib
  · intro h
    rw [bigcap_def] at h
    rw [union_def]
    apply Or.elim hp'
    · apply Or.intro_right
    · intro hxnb
      apply Or.inl
      rw [bigcap_def]
      intro a ha
      have hab : x ∈ a ∪ b := by
        apply h (a ∪ b)
        rw [transform_def]
        exists a
      rw [union_def] at hab
      apply Or.elim hab
      · intro h
        exact h
      · intro h
        exfalso
        contradiction

end MySet
