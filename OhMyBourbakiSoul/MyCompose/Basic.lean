universe u
variable {α : Type u}

namespace MyCompose

theorem compose_assoc {f g h : α → α} :
  (f ∘ g) ∘ h = f ∘ (g ∘ h) := by
  funext x
  change (f ∘ g) (h x) = f ((g ∘ h) x)
  change (f (g (h x))) = f (g (h x))
  rfl

theorem compose_id {f : α → α} :
  f ∘ id = f := by
  funext x
  change f (id x) = f x
  change f x = f x
  rfl

theorem compose_id_left {f : α → α} :
  id ∘ f = f := by
  funext x
  change id (f x) = f x
  change f x = f x
  rfl

theorem compose_apply {f g : α → α} {x : α} :
  (f ∘ g) x = f (g x) := by
  rfl

end MyCompose
