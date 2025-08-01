import OhMyBourbakiSoul.MyNat.Basic
import OhMyBourbakiSoul.MyNat.AddDef
import OhMyBourbakiSoul.MyNat.MulDef
import OhMyBourbakiSoul.MyNat.OrderDef
import OhMyBourbakiSoul.MyCompose.MyNatCompose

open MyCompose

namespace MyNat

def nat_mul (a : MyNat) : MyNat -> MyNat := λ x => a * x

theorem nat_mul_def {a x : MyNat} :
  (nat_mul a) x = a * x := by
  change (λ x => a * x) x = a * x
  rfl

theorem one_mul_identity : (nat_mul one) = id := by
  funext x
  rw [nat_mul_def]
  rw [one_mul]
  rw [id]

def pow (a n : MyNat) : MyNat := ((nat_mul a) ^ n) one

instance instPow : HPow MyNat MyNat MyNat where
  hPow := pow

theorem pow_def {a n : MyNat} :
  a ^ n = ((nat_mul a) ^ n) one := by rfl

theorem pow_zero {a : MyNat} : a ^ zero = one := by
  rw [pow_def]
  rw [compose_nat_pow_zero]
  rw [id]

theorem zero_pow {n : MyNat} : zero ^ (succ n) = zero := by
  rw [pow_def]
  rw [compose_nat_pow_succ]
  rw [compose_apply]
  rw [nat_mul_def]
  rw [zero_mul]

theorem pow_one {a : MyNat} : a ^ one = a := by
  rw [pow_def]
  rw [compose_nat_pow_one]
  unfold nat_mul
  rw [mul_one]

theorem pow_mul_apply {a n b : MyNat} :
  (a ^ n) * b = ((nat_mul a) ^ n) b := by
  revert n
  apply mathematical_induction
  · rw [pow_zero]
    rw [one_mul]
    rw [compose_nat_pow_zero]
    rw [id]
  · intro n hp
    rw [pow_def]
    rw [compose_nat_pow_succ]
    rw [compose_apply]
    rw [compose_apply]
    rw [nat_mul_def]
    rw [nat_mul_def]
    rw [mul_assoc]
    rw [<-pow_def]
    rw [hp]

theorem pow_add_hom {a m n: MyNat} :
  a ^ (m + n) = (a ^ m) * (a ^ n) := by
  rw [pow_mul_apply]
  repeat rw [pow_def]
  rw [<-compose_nat_pow_add_hom]
  rw [compose_apply]

end MyNat
