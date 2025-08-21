-- x ↦ f x
syntax term " ↦ " term : term

macro_rules
  | `($x ↦ $p) => ``(fun $x => $p)
