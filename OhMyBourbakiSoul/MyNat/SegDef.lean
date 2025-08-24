import OhMyBourbakiSoul.MyBasic.MySet.Basic
import OhMyBourbakiSoul.MyBasic.MySet.Fin
import OhMyBourbakiSoul.MyBasic.MySet.Exclusive
import OhMyBourbakiSoul.MyBasic.MyOrd.Basic
import OhMyBourbakiSoul.MyBasic.MyOrd.Compat
import OhMyBourbakiSoul.MyBasic.MyFun.IdDef
import OhMyBourbakiSoul.MyBasic.MyFun.EmptyDef
import OhMyBourbakiSoul.MyBasic.MyLogic.Exclusive
import OhMyBourbakiSoul.MyNat.OrderDef
import OhMyBourbakiSoul.MyNat.Mu

universe u
variable {α : Type u}

open MyOrd
open MySet

namespace MyNat

-- seg n := {0, 1, ..., n-1}
--
-- In the classical Zermelo-Fraenkel set
-- theory natural numbers are implemented
-- by the von-Neumann ordinals that is not
-- greater than any limit ordinal. Like:
--
-- 0           = {}        = ∅
-- 1 = 0 ∪ {0} = {0}       = {∅}
-- 2 = 1 ∪ {1} = {0, 1}    = {∅, {∅}}
-- 3 = 2 ∪ {2} = {0, 1, 2} = {∅, {∅}, {∅, {∅}}}
-- ...
--
-- Therefore there must be Seg n = n from
-- a classical perspective of view.
def seg (n : MyNat) : MySet MyNat :=
  { m : MyNat | m < n }

theorem mem_seg_iff {m n : MyNat} :
  (m ∈ n.seg) ↔ (m < n) := by
  change (m < n) ↔ (m < n)
  rfl

theorem mem_succ_seg_iff {m n : MyNat} :
  (m ∈ (succ n).seg) ↔ (m ≤ n) := by
  rw [mem_seg_iff]
  rw [lt_iff_succ_le]
  rw [le_succ_cancel]

theorem seg_zero_is_empty : zero.seg = ∅ := by
  rw [<-empty_iff]
  intro x hx
  rw [mem_seg_iff] at hx
  rw [<-MyComparableOrd.not_ge_iff_lt] at hx
  have : zero ≤ x := zero_le
  contradiction

theorem seg_succ_def {n : MyNat} :
  (succ n).seg = n.seg ∪ {n} := by
  rw [eq_iff]
  intro x
  rw [union_def]
  rw [mem_singleton_iff]
  repeat rw [mem_seg_iff]
  rw [lt_iff_succ_le]
  rw [le_succ_cancel]
  exact le_iff_lt_or_eq

theorem seg_eq_iff {m n : MyNat} :
  (m = n) ↔ (m.seg = n.seg) := by
  apply Iff.intro
  · intro h
    rw [h]
  · intro h
    have h' {a b : MyNat} :
      (a < b) → (a.seg ≠ b.seg) := by
      intro hab heq
      rw [eq_iff] at heq
      have : a ∈ b.seg := mem_seg_iff.mpr hab
      have : a ∉ b.seg := by
        rw [<-heq a]
        rw [mem_seg_iff]
        exact MyStrictOrd.lt_irrefl
      contradiction
    match (cmp m n) with
      | MyCmp.lt hlt =>
        exfalso
        have := h' hlt
        contradiction
      | MyCmp.eq heq =>
        trivial
      | MyCmp.gt hgt =>
        exfalso
        have := h' hgt
        symm at h
        contradiction

theorem seg_empty_iff {n : MyNat} :
  (n = zero) ↔ (n.seg = ∅) := by
  rw [<-seg_zero_is_empty]
  exact seg_eq_iff

theorem seg_subset_iff {m n : MyNat} :
  (m ≤ n) ↔ (m.seg ⊆ n.seg) := by
  apply Iff.intro
  · intro hmn
    rw [subset_def]
    intro x hx
    change x < m at hx
    change x < n
    exact MyCompatOrd.lt_of_lt_of_le hx hmn
  · rw [subset_def]
    intro hs
    rw [<-MyComparableOrd.not_gt_iff_le]
    intro hmn
    rw [gt_iff_lt] at hmn
    have hn := hs n hmn
    rw [mem_seg_iff] at hn
    exact MyStrictOrd.lt_irrefl hn

theorem seg_ssubset_iff {m n : MyNat} :
  (m < n) ↔ (m.seg ⊂ n.seg) := by
  rw [MyCompatOrd.compat]
  change (m ≤ n) ∧ ¬(m = n) ↔ (m.seg ⊂ n.seg)
  rw [ssubset_def]
  rw [seg_subset_iff]
  rw [seg_eq_iff]

instance instMyNatSegDecidable {n : MyNat} :
  n.seg.decidable := by
  intro m
  have d : Decidable (m < n) := inferInstance
  exact d

instance instMyNatSegCountSet {n : MyNat} :
  n.seg.countable where
  ctr := n.seg
  decidable_ctr := inferInstance
  fn := MyFun.identity n.seg
  surj := inferInstance

instance instMyNatSegFinSet {n : MyNat} :
  n.seg.fin (C := instMyNatSegCountSet) where
  bound := n
  bounded := by
    intro m hm
    change m < n at hm
    rw [MyCompatOrd.compat] at hm
    exact And.left hm

theorem seg_induced_exclusive_emptiness
  {n : MyNat} {s : MySet MyNat} :
  (s.exclusive) →
  (Exclusive (s ∩ n.seg).nonempty) := by
  revert n
  apply mathematical_induction
  · intro hs
    rw [seg_zero_is_empty]
    rw [intersect_empty]
    apply Or.inr
    exact empty_not_nonempty
  · intro n hp hs
    apply Or.elim (hp hs)
    · intro h
      rcases h with ⟨n', hn'⟩
      rw [<-mem_def] at hn'
      apply Or.inl
      exists n'
      rw [<-mem_def]
      rw [intersect_def]
      apply And.intro
      · exact And.left hn'
      · have h' := And.right hn'
        rw [mem_seg_iff] at h'
        rw [mem_seg_iff]
        exact MyStrictOrd.lt_trans h' lt_succ
    · intro h
      apply Or.elim (hs n)
      · intro h'
        apply Or.inl
        exists n
        rw [<-mem_def]
        apply And.intro
        · exact h'
        · rw [mem_seg_iff]
          exact lt_succ
      · intro h'
        apply Or.inr
        intro h''
        rcases h'' with ⟨n', hn'⟩
        rw [<-mem_def] at hn'
        rw [intersect_def] at hn'
        match (cmp n' n) with
          | MyCmp.lt hlt =>
            rw [<-mem_seg_iff] at hlt
            have : (s ∩ n.seg).nonempty := by
              exists n'
              rw [<-mem_def]
              rw [intersect_def]
              apply And.intro
              · exact And.left hn'
              · exact hlt
            contradiction
          | MyCmp.eq heq =>
            rw [<-mem_def] at h'
            have hns := And.left hn'
            rw [heq] at hns
            contradiction
          | MyCmp.gt hgt =>
            have hn'n := And.right hn'
            rw [mem_succ_seg_iff] at hn'n
            rw [<-MyComparableOrd.not_gt_iff_le] at hn'n
            contradiction

instance instDecidableEmpty
  {n : MyNat} {s : MySet MyNat}
  [s.decidable] :
  (Decidable (s ∩ n.seg).nonempty) := by
  have hex : ∃ m, ((m ∈ s) ∧ (m < n)) ∨ (m = n) := by
    exists n
    exact Or.inr rfl
  have m := MyNat.mu hex
  have d : Decidable (m.val = n) := inferInstance
  match d with
    | Decidable.isTrue h =>
      apply Decidable.isFalse
      intro h'
      rcases h' with ⟨n', hn'⟩
      rw [<-mem_def] at hn'
      rw [intersect_def] at hn'
      have hm := m.minimal
      have hp := And.right hn'
      rw [mem_seg_iff] at hp
      rw [<-h] at hp
      apply hm n' hp
      apply Or.inl
      rw [mem_seg_iff] at hn'
      exact hn'
    | Decidable.isFalse h =>
      apply Decidable.isTrue
      have hm := m.sufficient
      have hm' := Or.resolve_right hm h
      exists m.val

instance instMyNatSegRangeCountSet {n : MyNat}
  {s : MySet α} {f : n.seg -→ s} :
  f.range.countable where
  ctr := n.seg
  decidable_ctr := inferInstance
  fn := f.trim
  surj := inferInstance

instance instMyNatSegRangeFinSet {n : MyNat}
  {s : MySet α} {f : n.seg -→ s} :
  f.range.fin (C := instMyNatSegRangeCountSet) where
  bound := n
  bounded := by
    intro x hx
    change x ∈ n.seg at hx
    rw [mem_seg_iff] at hx
    rw [MyCompatOrd.compat] at hx
    exact And.left hx

end MyNat
