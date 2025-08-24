namespace MyLogic

variable {p q : Prop}

theorem contra_with_iff_not : ¬(p ↔ ¬p) := by
  intro hpnp
  have hnp : p → False := by
    intro hp
    have hnp := hpnp.mp hp
    contradiction
  have hp : p := hpnp.mpr hnp
  contradiction

theorem modus_tollens_pos : (p → q) → (¬q → ¬p) := by
  intro hpq hnq hp
  have hq := hpq hp
  contradiction

theorem modus_tollens_neg : (p → ¬q) → (q → ¬p) := by
  intro hpnq hq hp
  have hnq := hpnq hp
  contradiction

end MyLogic
