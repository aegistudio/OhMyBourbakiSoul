import OhMyBourbakiSoul.MyBasic.MySet.Basic
import OhMyBourbakiSoul.MyBasic.MySet.FinDef
import OhMyBourbakiSoul.MyBasic.MySet.OpsDecide
import OhMyBourbakiSoul.MyBasic.MyOrd.Basic
import OhMyBourbakiSoul.MyBasic.MyOrd.Compat
import OhMyBourbakiSoul.MyNat.SegDef

open MyOrd
open MySet

namespace MyNat

-- For writing the following theorems simpler.
local instance instCoeSegSucc {n : MyNat} :
  Coe n.seg.type (succ n).seg.type where
  coe := x ↦ ⟨
    x.val,
    MyStrictOrd.lt_trans x.property lt_succ,
  ⟩

private structure _MyPigeonholeFix
  {m n : MyNat}
  (f : ((succ m).seg -→ (succ n).seg))
  (v : n.seg.type) (x : m.seg.type) where
  y : n.seg.type
  compat : (f x ≠ n) → (y.val = (f x).val)
  contract : (f x = n) → (y.val = v.val)

-- We fix the function, so that g(x) yield
-- the original function value if f(x) ≠ n,
-- and yield the specified value v if there
-- has already been f(x) = n.
def _pigeonhole_fix {m n : MyNat}
  (f : (succ m).seg -→ (succ n).seg)
  (v : n.seg.type) :
  (x : m.seg.type) → (_MyPigeonholeFix f v x) := by
  intro x
  have (eq := hy) y := f x
  have d : Decidable (y = n) := inferInstance
  match d with
    | Decidable.isTrue h =>
      apply _MyPigeonholeFix.mk v
      · intro h'
        exfalso
        rw [<-hy] at h'
        contradiction
      · intro h'
        rw [<-hy] at h'
    | Decidable.isFalse h =>
      have hyp := y.membership
      rw [mem_succ_seg_iff] at hyp
      have hy' : y.val < n := by
        rw [MyCompatOrd.compat]
        exact And.intro hyp h
      rw [<-mem_seg_iff] at hy'
      have (eq := hy') y' := typed y.val hy'
      apply _MyPigeonholeFix.mk y'
      · intro h'
        rw [<-hy] at h'
        rw [<-hy]
        exact Subtype.eq_iff.mp hy'
      · intro h'
        exfalso
        rw [<-hy] at h'
        contradiction

theorem _pigeonhole_preserve_arguments {m n : MyNat}
  {f : (succ m).seg -→ (succ n).seg}
  {x₁ : (succ m).seg.type} {v y₁ : n.seg.type} :
  (f x₁ = y₁) → (x₁.val < m) →
  (∃ x₁', (((_pigeonhole_fix f v) x₁').y = y₁)) := by
  intro hx₁ hx₁'
  rw [<-mem_seg_iff] at hx₁'
  have (eq := hx₁') x₁' := typed x₁.val hx₁'
  exists x₁'
  generalize (_pigeonhole_fix f _) x₁' = y
  have hfx₁' : (f x₁').val = y₁.val := by
    rw [Subtype.eq_iff] at hx₁
    change (f x₁).val = y₁.val at hx₁
    rw [<-hx₁]
    apply MyFun.image_val_eq_if
    change x₁'.val = x₁.val
    rw [hx₁']
    apply typed_eta

  rw [Subtype.eq_iff]
  rw [<-hfx₁']
  apply y.compat
  intro heq
  rw [hfx₁'] at heq
  have hy₁p := y₁.membership
  rw [mem_seg_iff] at hy₁p
  rw [heq] at hy₁p
  exact MyStrictOrd.lt_irrefl hy₁p

-- Given a surjection f: [m+1] → [n+2], we may
-- fix it into a surjection g: [m] → [n+1].
--
-- Please notice g : [m] → [n] is not
-- constructible from f : [m+1] → [n+1] when
-- n = 0. In that case, it suffices to let
-- f(x) = 0, then g(x) is undefinable.
theorem _pigeonhole_surj_fixable {m n : MyNat}
  (f : ((succ m).seg -→ (succ (succ n)).seg)) [s: f.surj] :
  ∃ (g : (m.seg -→ (succ n).seg)), g.surj := by
  generalize hy₀ : f ⟨m, lt_succ⟩ = y₀
  rcases s.surj ⟨succ n, lt_succ⟩ with ⟨x₀, hx₀⟩

  have d : Decidable (y₀ = succ n) := inferInstance
  match d with
    -- If f(m) = n+1, then it suffices to evict this
    -- (m, n+1), and fix those x such that f(x) = n+1
    -- by pointing f(x) = n.
    | Decidable.isTrue h =>
      have (eq := hg) g : m.seg -→ (succ n).seg :=
        x ↦ ((_pigeonhole_fix f ⟨n, lt_succ⟩) x).y

      exists g
      apply MySurj.mk
      intro y₁
      rcases s.surj y₁ with ⟨x₁, hx₁⟩
      change f x₁ = y₁ at hx₁

      have hx₁' : x₁.val < m := by
        rw [MyCompatOrd.compat]
        apply And.intro
        · have h := x₁.membership
          rw [mem_succ_seg_iff] at h
          exact h
        · intro heq
          have hm : x₁ = ⟨m, lt_succ⟩ := by
            rw [Subtype.eq_iff]
            exact heq
          rw [Subtype.eq_iff] at hx₁
          change (f x₁).val = y₁.val at hx₁
          rw [hm] at hx₁
          rw [Subtype.eq_iff] at hy₀
          rw [hx₁] at hy₀
          rw [h] at hy₀
          have hy₁ := y₁.membership
          rw [mem_seg_iff] at hy₁
          rw [hy₀] at hy₁
          exact MyStrictOrd.lt_irrefl hy₁

      rw [hg]
      change ∃ x₁', ((_pigeonhole_fix f _) x₁').y = y₁
      apply _pigeonhole_preserve_arguments hx₁ hx₁'

    -- If f(m) = y₀ < n+1, then since f is surjective,
    -- there must be some x₀ such that f(x₀) = n+1.
    -- Then we evict (m, n+1) and fix x₀ by letting
    -- f(x₀) point to y₀.
    | Decidable.isFalse h =>
      have hy₀le := y₀.membership
      rw [mem_succ_seg_iff] at hy₀le
      have hy₀lt : y₀ < n.succ := by
        rw [MyCompatOrd.compat]
        exact And.intro hy₀le h
      clear hy₀le

      rw [<-mem_seg_iff] at hy₀lt
      have (eq := hy₀') y₀' := typed y₀.val hy₀lt

      have (eq := hg) g : m.seg -→ (succ n).seg :=
        x ↦ ((_pigeonhole_fix f y₀') x).y

      exists g
      apply MySurj.mk
      intro y₁
      rcases s.surj y₁ with ⟨x₁, hx₁⟩
      change f x₁ = y₁ at hx₁

      rw [hg]
      change ∃ x₁', ((_pigeonhole_fix f _) x₁').y = y₁
      clear hg

      have d' : Decidable (x₁.val < m) := inferInstance
      match d' with
        | Decidable.isTrue hx₁' =>
          apply _pigeonhole_preserve_arguments hx₁ hx₁'
        | Decidable.isFalse h =>
          have hx₀m : x₀.val < m := by
            rw [MyCompatOrd.compat]
            apply And.intro
            · have h := x₀.membership
              rw [mem_succ_seg_iff] at h
              exact h
            · intro h
              have hx₀m : x₀ = ⟨m, lt_succ⟩ := by
                rw [Subtype.eq_iff]
                exact h
              rw [hx₀m] at hx₀
              rw [hx₀] at hy₀
              rw [Subtype.eq_iff] at hy₀
              change (succ n) = y₀.val at hy₀
              symm at hy₀
              contradiction

          have hx₀' := hx₀m
          rw [<-mem_seg_iff] at hx₀'
          have (eq := hx₀') x₀' := typed x₀.val hx₀'
          exists x₀'
          generalize (_pigeonhole_fix f y₀' x₀') = y

          rw [MyComparableOrd.not_gt_iff_le] at h
          have hx₁p := x₁.membership
          rw [mem_succ_seg_iff] at hx₁p
          have hx₁m : x₁ = ⟨m, lt_succ⟩ := by
            rw [Subtype.eq_iff]
            exact MyPartialOrd.le_antisymm hx₁p h
          rw [<-hx₁m] at hy₀
          rw [Subtype.eq_iff] at hy₀ hx₁
          change (f x₁).val = y₁.val at hx₁
          have heq := hy₀
          rw [hx₁] at heq
          rw [Subtype.eq_iff]
          rw [heq]
          rw [Subtype.eq_iff] at hy₀'
          change y₀'.val = y₀.val at hy₀'
          rw [<-hy₀']

          apply y.contract
          rw [Subtype.eq_iff] at hx₀
          change (f x₀).val = succ n at hx₀
          rw [hx₀']
          exact hx₀

theorem pigeonhole_surj {m n : MyNat}
  (f : m.seg -→ n.seg) :
  (m < n) → ¬(f.surj) := by
  revert m n
  apply mathematical_induction
  · intro n f h hs
    rw [seg_zero_is_empty] at f
    have hsj := hs.surj
    have y : Subtype (n.seg) :=
      Subtype.mk zero h
    rcases hsj y with ⟨x, _⟩
    have hx := x.membership
    rw [mem_seg_iff] at hx
    have hx' : x.val ≥ zero := zero_le
    rw [ge_iff_le] at hx'
    rw [<-MyComparableOrd.not_gt_iff_le] at hx'
    contradiction
  · intro m hp n f hmn hs
    match n with
      | zero =>
        have hmn' : zero ≤ m.succ := zero_le
        rw [<-MyComparableOrd.not_gt_iff_le] at hmn'
        contradiction
      | succ n' =>
        rw [lt_succ_cancel] at hmn
        match n' with
          | zero =>
            rw [<-MyComparableOrd.not_ge_iff_lt] at hmn
            have : zero ≤ m := zero_le
            contradiction
          | succ n'' =>
            rcases _pigeonhole_surj_fixable f with ⟨g, hg⟩
            have := hp g hmn
            contradiction

theorem _pigeonhole_inj_restrict_suffices {m n : MyNat}
  (f : (succ m).seg -→ (succ n).seg) [s: f.inj] :
  (∀ x : m.seg.type, (f x) ≠ n) →
  ∃ (g : m.seg -→ n.seg), g.inj := by
  intro h

  have hsms : m.seg ⊆ (succ m).seg := by
    rw [<-seg_subset_iff]
    exact le_succ

  -- FIXME: What hinders Lean 4 from synthesizing
  -- instances automatically?
  have (eq := hg₀) g₀ := f.restrict m.seg hsms
  have Ig₀ : g₀.inj := by
    rw [hg₀]
    infer_instance

  have hg₀r : g₀.range ⊆ n.seg := by
    rw [subset_def]
    intro y hy
    rw [MyFun.range_mem] at hy
    rcases hy with ⟨x₀, hx₀⟩
    rw [hg₀] at hx₀
    rw [<-MyFun.restrict_compat] at hx₀
    have (eq := hy₀) y₀ := f x₀
    have hy₀y : y₀.val = y := by
      rw [Subtype.eq_iff] at hy₀
      rw [hx₀, hy₀]
      apply MyFun.image_val_eq_if
      rfl
    rw [<-hy₀y, hy₀]
    rw [mem_seg_iff]
    rw [MyCompatOrd.compat]
    apply And.intro
    · rw [<-hy₀]
      rw [<-mem_succ_seg_iff]
      exact y₀.membership
    · exact h x₀

  exists (g₀.trim).expand n.seg hg₀r
  infer_instance

theorem _pigeonhole_inj_swap_suffices {m n : MyNat}
  (f : (succ m).seg -→ (succ n).seg) [i : f.inj]
  (v : n.seg.type) :
  (v.val = (f ⟨m, lt_succ⟩).val) →
  (∃ g : m.seg -→ n.seg, g.inj) := by
  intro hv
  have (eq := hg) g : m.seg -→ n.seg :=
    x ↦ (_pigeonhole_fix f v x).y
  exists g
  apply MyInj.mk
  intro x₁ x₂ hx₁x₂
  rw [hg] at hx₁x₂
  change (_pigeonhole_fix f v x₁).y = (_pigeonhole_fix f v x₂).y at hx₁x₂
  generalize hy₁ : (_pigeonhole_fix f v x₁) = y₁
  generalize hy₂ : (_pigeonhole_fix f v x₂) = y₂
  rw [hy₁, hy₂] at hx₁x₂

  have hfv : ∀ x, ((_pigeonhole_fix f v x).y = v) → (f x = n) := by
    intro x hx
    generalize hy' : (_pigeonhole_fix f v x) = y'
    symm at hv
    have hm : Exclusive (f x = n) := exclusive_if_decidable
    apply hm.by_contra
    intro h'
    have h'' := y'.compat h'
    rw [hy'] at hx
    rw [Subtype.eq_iff] at hx
    rw [hx] at h''
    rw [<-hv] at h''
    rw [<-Subtype.eq_iff] at h''
    have hinj := i.inj _ _ h''
    rw [Subtype.eq_iff] at hinj
    change m = x.val at hinj
    have hm' := x.membership
    rw [mem_seg_iff] at hm'
    rw [<-hinj] at hm'
    exact MyStrictOrd.lt_irrefl hm'

  have hfnv : ∀ x,
    ((_pigeonhole_fix f v x).y ≠ v) →
    ((_pigeonhole_fix f v x).y = f x) := by
    intro x hx
    rw [Subtype.eq_iff]
    generalize hy' : (_pigeonhole_fix f v x) = y'
    apply y'.compat
    intro h
    have h' := y'.contract h
    rw [<-hy'] at h'
    rw [<-Subtype.eq_iff] at h'
    contradiction

  have d : Decidable (y₁.y = v) := inferInstance
  match d with
    | Decidable.isTrue h =>
      have hfx₁ : f x₁ = n := by
        apply hfv x₁
        rw (occs := [3]) [<-h]
        rw [hy₁]
      have hfx₂ : f x₂ = n := by
        apply hfv x₂
        rw [hx₁x₂] at h
        rw (occs := [3]) [<-h]
        rw [hy₂]
      have hfx₁x₂ : f x₁ = f x₂ := by
        rw (occs := [3]) [<-hfx₂] at hfx₁
        rw [Subtype.eq_iff]
        exact hfx₁
      have h' := i.inj _ _ hfx₁x₂
      rw [Subtype.eq_iff]
      rw [Subtype.eq_iff] at h'
      exact h'
    | Decidable.isFalse h =>
      have hfx₁ : y₁.y = f x₁ := by
        rw [<-hy₁] at h
        have h' := hfnv x₁ h
        rw [Subtype.eq_iff] at h'
        rw [Subtype.eq_iff]
        rw [hy₁] at h'
        exact h'
      have hfx₂ : y₂.y = f x₂ := by
        rw [hx₁x₂, <-hy₂] at h
        have h' := hfnv x₂ h
        rw [Subtype.eq_iff] at h'
        rw [Subtype.eq_iff]
        rw [hy₂] at h'
        exact h'
      have hfx₁x₂ : f x₁ = f x₂ := by
        rw [<-hx₁x₂] at hfx₂
        rw (occs := [1]) [hfx₂] at hfx₁
        symm
        exact hfx₁
      have h' := i.inj _ _ hfx₁x₂
      rw [Subtype.eq_iff]
      rw [Subtype.eq_iff] at h'
      exact h'

-- Given an injection f : [m+1] → [n+1], we may
-- fix it into an injection g : [m] → [n].
theorem _pigeonhole_inj_fixable {m n : MyNat}
  (f : (succ m).seg -→ (succ n).seg) [i : f.inj] :
  ∃ (g : m.seg -→ n.seg), g.inj := by
  have (eq := him) im := f.range ∩ {y | y = n}
  have d : Decidable (im ∩ (succ n).seg).nonempty := by
    rw [him]
    infer_instance

  have hsms : m.seg ⊆ (succ m).seg := by
    rw [<-seg_subset_iff]
    exact le_succ

  match d with
    | Decidable.isTrue h =>
      rcases h with ⟨y, hy⟩
      rw [<-mem_def] at hy
      rw [him] at hy
      rw [intersect_def] at hy
      rcases hy with ⟨hyim, _⟩
      rw [intersect_def] at hyim
      rcases hyim with ⟨hyr, hyn⟩
      change y = n at hyn
      rw [hyn] at hyr
      rw [MyFun.range_mem] at hyr
      rcases hyr with ⟨x₀, hx₀⟩

      generalize hy₀ : f ⟨m, lt_succ⟩ = y₀
      have hy₀n : (x₀ ≠ m) → (y₀ < n) := by
        intro hx₀m
        rw [<-MyComparableOrd.not_ge_iff_lt]
        intro hge
        have hle := y₀.membership
        rw [mem_succ_seg_iff] at hle
        have heq := MyPartialOrd.le_antisymm hle hge
        rw [Subtype.eq_iff] at hy₀
        rw [heq] at hy₀
        rw (occs :=[1]) [<-hy₀] at hx₀
        rw [<-Subtype.eq_iff] at hx₀
        have hmx₀ := (i.inj ⟨m, lt_succ⟩ x₀) hx₀
        rw [Subtype.eq_iff] at hmx₀
        symm at hmx₀
        contradiction

      have d' : Decidable (x₀ = m) := inferInstance
      match d' with
        | Decidable.isTrue h' =>
          apply _pigeonhole_inj_restrict_suffices f
          intro x hx
          rw (occs := [3]) [hx₀] at hx
          rw [<-Subtype.eq_iff] at hx
          have hxx₀ := i.inj _ _ hx
          rw [Subtype.eq_iff] at hxx₀
          change x.val = x₀.val at hxx₀
          rw [h'] at hxx₀
          have hxm' := x.membership
          rw [mem_seg_iff] at hxm'
          rw [hxx₀] at hxm'
          exact MyStrictOrd.lt_irrefl hxm'
        | Decidable.isFalse h' =>
          have hy₀' := hy₀n h'
          rw [<-mem_seg_iff] at hy₀'
          have (eq := hy₀') y₀' := typed y₀.val hy₀'
          apply _pigeonhole_inj_swap_suffices f y₀'
          rw [hy₀', typed_eta]
          rw [<-Subtype.eq_iff]
          symm
          exact hy₀
    | Decidable.isFalse h =>
      apply _pigeonhole_inj_restrict_suffices f
      intro x hx
      apply h
      exists n
      rw [<-mem_def]
      rw [intersect_def]
      apply And.intro
      · rw [him]
        rw [intersect_def]
        apply And.intro
        · rw [MyFun.range_mem]
          symm at hx
          exists x
        · rfl
      · rw [mem_succ_seg_iff]
        exact MyPartialOrd.le_refl

theorem pigeonhole_inj {m n : MyNat}
  (f : m.seg -→ n.seg) :
  (m > n) → ¬(f.inj) := by
  revert m n
  apply mathematical_induction
  · intro n f hz
    exfalso
    rw [gt_iff_lt] at hz
    rw [<-MyComparableOrd.not_ge_iff_lt] at hz
    rw [ge_iff_le] at hz
    have : zero ≤ n := zero_le
    contradiction
  · intro m hp n f h hi
    match n with
      | zero =>
        have hf : f.codomain = ∅ := by
          rw [<-seg_zero_is_empty]
          rfl
        have h := MyFun.empty_domain_if_empty_codomain hf
        change (succ m).seg = ∅ at h
        rw [<-seg_empty_iff] at h
        have : m.succ ≠ zero := succ_ne_zero
        contradiction
      | succ n' =>
        rw [gt_iff_lt] at h
        rw [lt_succ_cancel] at h
        have h' := _pigeonhole_inj_fixable f
        rcases h' with ⟨g, hg⟩
        have := hp g h
        contradiction

theorem pigeonhole {m n : MyNat} :
  (m = n) ↔ (∃ f : m.seg -→ n.seg, f.bij) := by
  apply Iff.intro
  · intro h
    rw [seg_eq_iff] at h
    exists MyFun.identity' h
    infer_instance
  · intro h'
    rcases h' with ⟨f, hf⟩
    match (cmp m n) with
      | MyCmp.lt hlt =>
        exfalso
        have := pigeonhole_surj f hlt
        have := hf.toMySurj
        contradiction
      | MyCmp.eq heq =>
        exact heq
      | MyCmp.gt hgt =>
        exfalso
        have := pigeonhole_inj f hgt
        have := hf.toMyInj
        contradiction

end MyNat
