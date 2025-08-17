import OhMyBourbakiSoul.MyBasic.MySet.Basic
import OhMyBourbakiSoul.MyBasic.MySet.Subset
import OhMyBourbakiSoul.MyBasic.MySet.Subtype
import OhMyBourbakiSoul.MyBasic.MyLogic.ExistsUniq

open MySet

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
variable {X : MySet α} {Y : MySet β} {Z : MySet γ}

class MyFun (X : MySet α) (Y : MySet β) where
  fn: Subtype X → Subtype Y

namespace MyFun

def coe_fn (f : MyFun X Y) (x : Subtype X) : Subtype Y := f.fn x

instance instCoeFn : CoeFun (MyFun X Y)
  (fun _ => Subtype X → Subtype Y) where
  coe := coe_fn

def domain (_ : MyFun X Y) : MySet α := X

theorem domain_def {f : MyFun X Y} :
  X = f.domain := by rfl

def codomain (_ : MyFun X Y) : MySet β := Y

theorem codomain_def {f : MyFun X Y} :
  Y = f.codomain := by rfl

def range (f : MyFun X Y) : MySet β :=
  λ y : β => ∃ x : Subtype X, y = f x

theorem range_def {f : MyFun X Y} :
  ∀ x : Subtype X, (f x).val ∈ f.range := by
  intro x
  unfold range
  rw [mem_def]
  exists x

theorem range_mem {f : MyFun X Y} {y : β}:
  (y ∈ f.range) ↔ (∃ x : Subtype X, y = (f x).val) := by
  rfl

theorem range_subsets_codomain {f : MyFun X Y} :
  (f.range ⊆ f.codomain) := by
  rw [subset_def]
  intro y hy
  unfold range at hy
  rw [mem_def] at hy
  rcases hy with ⟨x, hx⟩
  generalize hy' : f x = y'
  rw [hy'] at hx
  have hyY := y'.property
  rw [<-hx] at hyY
  exact hyY

def restrict
  (f : MyFun X Y) (X' : MySet α) (h : X' ⊆ X) : MyFun X' Y :=
  MyFun.mk λ (x' : Subtype X') => f (lift_subtype h x')

theorem restrict_compat
  {f : MyFun X Y} {X' : MySet α} {h : X' ⊆ X} :
  ∀ x : Subtype X',
  f (lift_subtype h x) = (f.restrict X' h) x := by
  intro x
  change (f (lift_subtype h x)) = (f (lift_subtype h x))
  rfl

def trim (f : MyFun X Y) : MyFun f.domain f.range := by
  apply MyFun.mk
  intro x
  generalize hy : f x = y
  have hyr : (f x).val ∈ f.range := range_def x
  rw [hy] at hyr
  exact Subtype.mk y.val hyr

theorem trim_compat {f : MyFun X Y} :
  ∀ x : Subtype X, (f.trim x).val = (f x).val := by
  intro x
  rfl

def expand
  (f : MyFun X Y) (Y' : MySet β) (h : Y ⊆ Y') : MyFun X Y' :=
  MyFun.mk λ (x : Subtype X) => lift_subtype h (f x)

theorem expand_compat
  {f : MyFun X Y} {Y' : MySet β} {h : Y ⊆ Y'} :
  ∀ x : Subtype X,
  lift_subtype h (f x) = (f.expand Y' h) x := by
  intro x
  change lift_subtype h (f x) = lift_subtype h (f x)
  rfl

def compose
  (g : MyFun Y Z) (f : MyFun X Y) : MyFun X Z :=
  MyFun.mk (g ∘ f)

end MyFun

class MyInj (f : MyFun X Y) where
  inj: ∀ x : Subtype X, ∀ x' : Subtype X,
      (f x = f x') → (x = x')

namespace MyInj

open MyFun

theorem uniq_preimage {f : MyFun X Y} [If : MyInj f] :
  ∀ y : Subtype f.range, ∃! x : Subtype X,
  f x = y.val := by
  intro y
  have hy := y.property
  rw [<-mem_def (s := f.range)] at hy
  rw [range_mem] at hy
  rcases hy with ⟨x, hx⟩
  exists x
  apply And.intro
  · symm at hx
    exact hx
  · intro x' hx'
    rw [hx] at hx'
    apply If.inj
    rw [<-Subtype.eq_iff] at hx'
    symm at hx'
    exact hx'

theorem compose_inj
  (g : MyFun Y Z) [Ig : MyInj g]
  (f : MyFun X Y) [If : MyInj f] :
  MyInj (compose g f) := by
  apply MyInj.mk
  intro x x' h
  change (g ∘ f) x = (g ∘ f) x' at h
  change g (f x) = g (f x') at h
  have h' := Ig.inj (f x) (f x') h
  exact If.inj x x' h'

instance instCompInj
  {g : MyFun Y Z} [Ig : MyInj g]
  {f : MyFun X Y} [If : MyInj f] :
  MyInj (compose g f) := compose_inj g f

def inverse_fn
  {f : MyFun X Y} [If : MyInj f]
  [uc : UCPred λ y => (If.uniq_preimage y).prop] :
  Subtype f.range → Subtype f.domain := by
  intro y
  have hy := If.uniq_preimage y
  have x := (uc.uniq_choose_pred y).uniq_choose hy
  exact x.val

def inverse
  {f : MyFun X Y} [If : MyInj f]
  [uc : UCPred λ y => (If.uniq_preimage y).prop] :
  MyFun f.range f.domain := MyFun.mk inverse_fn

theorem inverse_def
  {f : MyFun X Y} [If : MyInj f]
  [uc : UCPred λ y => (If.uniq_preimage y).prop] :
  If.inverse ∘ f.trim = id := by
  funext x
  change If.inverse (f.trim x) = x
  generalize hy : f.trim x = y
  change inverse_fn y = x
  unfold inverse_fn
  generalize hhy' : If.uniq_preimage y = hy'
  change (have x := (uc.uniq_choose_pred y).uniq_choose hy'; x.val) = x
  generalize hx' : (uc.uniq_choose_pred y).uniq_choose hy' = x'
  change x'.val = x
  apply If.inj
  rw [Subtype.eq_iff]
  have hx'p := x'.property
  rw [hx'p, <-hy]
  exact trim_compat x

theorem inverse_inj
  {f : MyFun X Y} [If : MyInj f]
  [uc : UCPred λ y => (If.uniq_preimage y).prop] :
  MyInj (If.inverse) := by
  apply MyInj.mk
  intro y y' hxx'
  have hx₀ := f.trim.range_mem.mp y.property
  rcases hx₀ with ⟨x, hx⟩
  rw [<-Subtype.eq_iff] at hx
  rw [hx] at hxx'
  have hx₀' := f.trim.range_mem.mp y'.property
  rcases hx₀' with ⟨x', hx'⟩
  rw [<-Subtype.eq_iff] at hx'
  rw [hx'] at hxx'
  change (inverse ∘ f.trim) x = (inverse ∘ f.trim) x' at hxx'
  repeat rw [inverse_def] at hxx'
  change x = x' at hxx'
  rw [hx, hx', hxx']

instance instInverseInj
  {f : MyFun X Y} [If : MyInj f]
  [uc : UCPred λ y => (If.uniq_preimage y).prop] :
  MyInj (If.inverse) := inverse_inj

end MyInj

class MySurj (f : MyFun X Y) where
  surj: ∀ (y : Subtype Y), (∃ x : Subtype X, f x = y)

namespace MySurj

open MyFun

theorem range_is_codomain (f : MyFun X Y) [S: MySurj f] :
  f.range = f.codomain := by
  apply subset_antisymm
  · exact range_subsets_codomain
  · rw [subset_def]
    intro y hy
    rw [mem_def] at hy
    generalize hy' : Subtype.mk y hy = y'
    rcases S.surj y' with ⟨x', hx'⟩
    unfold range
    rw [mem_def]
    exists x'
    have hy'' : y = y'.val := Subtype.eq_iff.mp hy'
    rw [hy'']
    apply Subtype.eq_iff.mp
    symm
    exact hx'

def compose_surj
  (g : MyFun Y Z) [Sg : MySurj g]
  (f : MyFun X Y) [Sf : MySurj f] :
  MySurj (compose g f) := by
  apply MySurj.mk
  intro z
  change ∃ x, ((g ∘ f) x) = z
  rcases Sg.surj z with ⟨y, hy⟩
  rcases Sf.surj y with ⟨x, hx⟩
  exists x
  change g (f x) = z
  rw [hx, hy]

instance instCompSurj
  {g : MyFun Y Z} [Sg : MySurj g]
  {f : MyFun X Y} [Sf : MySurj f] :
  MySurj (compose g f) := compose_surj g f

end MySurj

class MyBij (f : MyFun X Y) extends MyInj f, MySurj f
