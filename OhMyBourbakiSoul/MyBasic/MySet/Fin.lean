import OhMyBourbakiSoul.MyBasic.MySet.Basic
import OhMyBourbakiSoul.MyBasic.MySet.OpsDef
import OhMyBourbakiSoul.MyBasic.MyFun.Basic
import OhMyBourbakiSoul.MyNat.Basic
import OhMyBourbakiSoul.MyNat.OrderDef

universe u
variable {α : Type u} {s : MySet α}

class MyCountSet (s : MySet α) [D : DecidableEq α] where
  decide_eq := D
  ctr : MySet MyNat
  fn : MyFun ctr s
  surj : MySurj fn

class MyFinSet (s : MySet α) [DecidableEq α]
  extends MyCountSet s where
  bound : MyNat
  bounded: ∀ n ∈ ctr, n ≤ bound
