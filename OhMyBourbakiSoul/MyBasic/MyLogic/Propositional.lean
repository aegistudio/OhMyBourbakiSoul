namespace MyLogic

variable {p : Prop}

theorem contra_with_iff_not : ¬(p ↔ ¬p) := by
  intro hpnp
  have hnp : p → False := by
    intro hp
    have hnp := hpnp.mp hp
    contradiction
  have hp : p := hpnp.mpr hnp
  contradiction

end MyLogic
