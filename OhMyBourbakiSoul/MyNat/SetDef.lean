import OhMyBourbakiSoul.MyNat.Basic
import OhMyBourbakiSoul.MyBasic.MySet.Basic
import OhMyBourbakiSoul.MyBasic.MySet.Subtype

open MySet

namespace MyNat

def ℕ := univ MyNat

theorem set_def {a : MyNat} : a ∈ ℕ := by
  exact univ_def a

end MyNat
