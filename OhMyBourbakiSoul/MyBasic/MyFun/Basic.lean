import OhMyBourbakiSoul.MyBasic.MapsTo
import OhMyBourbakiSoul.MyBasic.MySet.Basic
import OhMyBourbakiSoul.MyBasic.MySet.Subset
import OhMyBourbakiSoul.MyBasic.MySet.Subtype
import OhMyBourbakiSoul.MyBasic.MyLogic.ExistsUniq

open MySet

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
variable {X : MySet α} {Y : MySet β} {Z : MySet γ}

structure MyFun (X : MySet α) (Y : MySet β) where
  fn: X.type → Y.type

@[reducible]
def myfun (X : MySet α) (Y : MySet β) := MyFun X Y

infix:0 " -→ " => myfun

-- x ⊢→ f x
syntax term " ⊢→ " term : term

macro_rules
  | `($x ⊢→ $p) => ``(MyFun.mk ($x ↦ $p))

namespace MyFun

def coe_fn (f : X -→ Y) (x : X.type) : Y.type := f.fn x

instance instCoeFn : CoeFun (X -→ Y)
  (_ ↦ X.type → Y.type) where
  coe := coe_fn

def coe_myfun (f : X.type → Y.type) : X -→ Y := MyFun.mk f

instance instCoeMyFun : Coe (X.type → Y.type) (X -→ Y) where
  coe := coe_myfun

theorem image_eq_if {x₁ x₂ : X.type} {f : X -→ Y} :
  (x₁.val = x₂.val) → (f x₁ = f x₂) := by
  intro heq
  rw [<-Subtype.eq_iff] at heq
  rw [heq]

theorem image_val_eq_if {x₁ x₂ : X.type} {f : X -→ Y} :
  (x₁.val = x₂.val) → ((f x₁).val = (f x₂).val) := by
  intro h
  rw [<-Subtype.eq_iff]
  exact image_eq_if h

def domain (_ : X -→ Y) : MySet α := X

theorem domain_def {f : X -→ Y} :
  X = f.domain := by rfl

def codomain (_ : X -→ Y) : MySet β := Y

theorem codomain_def {f : X -→ Y} :
  Y = f.codomain := by rfl

def range (f : X -→ Y) : MySet β :=
  { y : β | ∃ x, y = (f x).val }

theorem range_def {f : X -→ Y} :
  ∀ x : X.type, (f x).val ∈ f.range := by
  intro x
  unfold range
  rw [mem_def]
  exists x

theorem range_mem {f : X -→ Y} {y : β}:
  (y ∈ f.range) ↔ (∃ x : X.type, y = (f x).val) := by
  rfl

theorem range_subsets_codomain {f : X -→ Y} :
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
  (f : X -→ Y) (X' : MySet α) (h : X' ⊆ X) : X' -→ Y :=
  x' ↦ f (lift_subtype h x')

theorem restrict_compat
  {f : X -→ Y} {X' : MySet α} {h : X' ⊆ X} :
  ∀ x : X'.type,
  f (lift_subtype h x) = (f.restrict X' h) x := by
  intro x
  change (f (lift_subtype h x)) = (f (lift_subtype h x))
  rfl

def trim (f : X -→ Y) : f.domain -→ f.range := by
  apply MyFun.mk
  intro x
  generalize hy : f x = y
  have hyr : (f x).val ∈ f.range := range_def x
  rw [hy] at hyr
  exact Subtype.mk y.val hyr

theorem trim_compat {f : X -→ Y} :
  ∀ x : X.type, (f.trim x).val = (f x).val := by
  intro x
  rfl

def expand
  (f : X -→ Y) (Y' : MySet β) (h : Y ⊆ Y') : X -→ Y' :=
  x ↦ lift_subtype h (f x)

theorem expand_compat
  {f : X -→ Y} {Y' : MySet β} {h : Y ⊆ Y'} :
  ∀ x : X.type,
  lift_subtype h (f x) = (f.expand Y' h) x := by
  intro x
  change lift_subtype h (f x) = lift_subtype h (f x)
  rfl

def compose
  (g : Y -→ Z) (f : X -→ Y) : X -→ Z := (g ∘ f)

end MyFun

class MyInj (f : X -→ Y) where
  inj: ∀ x : X.type, ∀ x' : X.type,
      (f x = f x') → (x = x')

namespace MyFun
abbrev inj (f : X -→ Y) := MyInj f
end MyFun

namespace MyInj

open MyFun

theorem uniq_preimage {f : X -→ Y} [If : f.inj] :
  ∀ y : f.range.type, ∃! x : X.type,
  (f x).val = y.val := by
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

abbrev uc_preimage {f : X -→ Y} (If : f.inj) :=
  UCPred (y ↦ (If.uniq_preimage y).prop)

theorem mk_uniq_preimage {f : X -→ Y} :
  (∀ y : f.range.type, ∃! x : X.type, (f x).val = y.val) →
  f.inj := by
  intro h
  apply MyInj.mk
  intro x x' hx
  have (eq := hy) y := f x
  have hy' : y.val ∈ f.range := by
    rw [range_mem]
    exists x
    rw [hy]
  have (eq := hy') y' := typed y.val hy'
  have h' := h y'
  apply h'.unique_if <;>
  · rw [hy', typed_eta]
    rw [<-Subtype.eq_iff]
    repeat rw [<-hx]
    symm
    exact hy

theorem compose_inj
  (g : Y -→ Z) [Ig : g.inj]
  (f : X -→ Y) [If : f.inj] :
  (compose g f).inj := by
  apply MyInj.mk
  intro x x' h
  change (g ∘ f) x = (g ∘ f) x' at h
  change g (f x) = g (f x') at h
  have h' := Ig.inj (f x) (f x') h
  exact If.inj x x' h'

instance instCompInj
  {g : Y -→ Z} [Ig : g.inj]
  {f : X -→ Y} [If : f.inj] :
  (compose g f).inj := compose_inj g f

def inverse_fn
  {f : X -→ Y} [If : f.inj] [uc : If.uc_preimage] :
  f.range.type → f.domain.type := by
  intro y
  have hy := If.uniq_preimage y
  have x := (uc.uniq_choose_pred y).uniq_choose hy
  exact x.val

def inverse
  {f : X -→ Y} [If : f.inj] [uc : If.uc_preimage] :
  f.range -→ f.domain := MyFun.mk inverse_fn

theorem inverse_def
  {f : X -→ Y} [If : f.inj] [uc : If.uc_preimage] :
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
  {f : X -→ Y} [If : f.inj] [uc : If.uc_preimage] :
  If.inverse.inj := by
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
  {f : X -→ Y} [If : f.inj] [uc : If.uc_preimage] :
  If.inverse.inj := inverse_inj

theorem trim_inj
  {f : X -→ Y} [If : f.inj] :
  f.trim.inj := by
  apply MyInj.mk
  intro x x' hxx'
  rw [Subtype.eq_iff] at hxx'
  repeat rw [trim_compat] at hxx'
  rw [<-Subtype.eq_iff] at hxx'
  exact If.inj x x' hxx'

instance instTrimInj
  {f : X -→ Y} [If : f.inj] :
  f.trim.inj := trim_inj

theorem restrict_inj
  {f : X -→ Y}  [If : f.inj]
  {X' : MySet α} {h : X' ⊆ X} :
  (f.restrict X' h).inj := by
  apply MyInj.mk
  intro x x' hxx'
  repeat rw [<-restrict_compat] at hxx'
  have h' := If.inj _ _ hxx'
  rw [Subtype.eq_iff] at h'
  repeat rw [lift_subtype_def] at h'
  rw [Subtype.eq_iff]
  exact h'

instance instRestrictInj
  {f : X -→ Y} [If : f.inj]
  {X' : MySet α} {h : X' ⊆ X} :
  (f.restrict X' h).inj := restrict_inj

theorem expand_inj
  {f : X -→ Y} [If : f.inj]
  {Y' : MySet β} {h : Y ⊆ Y'} :
  (f.expand Y' h).inj := by
  apply MyInj.mk
  intro x x' hxx'
  repeat rw [<-expand_compat] at hxx'
  rw [Subtype.eq_iff] at hxx'
  repeat rw [lift_subtype_def] at hxx'
  rw [<-Subtype.eq_iff] at hxx'
  exact If.inj x x' hxx'

instance instExpandInj
  {f : X -→ Y} [If : f.inj]
  {Y' : MySet β} {h : Y ⊆ Y'} :
  (f.expand Y' h).inj := expand_inj

end MyInj

class MySurj (f : X -→ Y) where
  surj: ∀ (y : Y.type), (∃ x : X.type, f x = y)

namespace MyFun
abbrev surj (f : X -→ Y) := MySurj f
end MyFun

namespace MySurj

open MyFun

theorem range_is_codomain (f : X -→ Y) [S: f.surj] :
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

theorem compose_surj
  (g : Y -→ Z) [Sg : g.surj]
  (f : X -→ Y) [Sf : f.surj] :
  (compose g f).surj := by
  apply MySurj.mk
  intro z
  change ∃ x, ((g ∘ f) x) = z
  rcases Sg.surj z with ⟨y, hy⟩
  rcases Sf.surj y with ⟨x, hx⟩
  exists x
  change g (f x) = z
  rw [hx, hy]

instance instCompSurj
  {g : Y -→ Z} [Sg : g.surj]
  {f : X -→ Y} [Sf : f.surj] :
  (compose g f).surj := compose_surj g f

theorem trim_surj
  {f : X -→ Y} : f.trim.surj := by
  apply MySurj.mk
  intro y
  have hy := y.property
  rw [<-mem_def] at hy
  rw [range_mem] at hy
  rcases hy with ⟨x, hx⟩
  exists x
  rw [Subtype.eq_iff]
  rw [trim_compat x]
  symm at hx
  exact hx

instance instTrimSurj
  {f : X -→ Y} : f.trim.surj := trim_surj

end MySurj

class MyBij (f : X -→ Y) extends f.inj, f.surj

namespace MyFun
abbrev bij (f : X -→ Y) := MyBij f
end MyFun

namespace MyBij

instance instAutoBij {f : X -→ Y}
  [If : f.inj] [Sf : f.surj] : f.bij :=
  @MyBij.mk _ _ _ _ _ If Sf

end MyBij
