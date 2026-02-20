import Mathlib.Tactic

namespace Analysis.Ch04.Sec01

structure Integer_ where
  minuend : ℕ
  subtrahend : ℕ

def Integer_.eqiv : Integer_ → Integer_ → Prop :=
  fun ⟨a, b⟩ ⟨c, d⟩ => a + d = c + b

theorem Integer_.eqiv_refl : ∀ x : Integer_, Integer_.eqiv x x := by
  intro ⟨a, b⟩
  simp [Integer_.eqiv]

theorem Integer_.eqiv_symm {x y : Integer_} : x.eqiv y → y.eqiv x := by
  intro h
  simp only [Integer_.eqiv] at *
  exact h.symm

theorem Integer_.eqiv_trans {x y z : Integer_} : x.eqiv y → y.eqiv z → x.eqiv z := by
  intro hxy hyz
  simp only [Integer_.eqiv] at *
  have : x.minuend + y.subtrahend = y.minuend + x.subtrahend := hxy
  have : y.minuend + z.subtrahend = z.minuend + y.subtrahend := hyz
  linarith

instance Integer_.instSetoid : Setoid Integer_ where
  r := Integer_.eqiv
  iseqv := {
    refl := Integer_.eqiv_refl,
    symm := Integer_.eqiv_symm,
    trans := Integer_.eqiv_trans,
  }

@[simp]
theorem Integer_.eqiv_iff (a b c d : ℕ) : Integer_.eqiv ⟨a, b⟩ ⟨c, d⟩ ↔ a + d = c + b := by
  rfl
def Integer := Quotient Integer_.instSetoid
def Integer.formalDiff (a b : ℕ) : Integer := Quotient.mk Integer_.instSetoid ⟨a, b⟩
infix:100 " —— " => Integer.formalDiff

theorem Integer.eqiv_iff (a b c d : ℕ) : a —— b = c —— d ↔ a + d = c + b := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound h

theorem Integer.eq_diff (n : Integer) : ∃ a b, n = a —— b := by
  apply n.ind _
  intro ⟨a, b⟩
  exists a, b

def Integer.add : Integer → Integer → Integer :=
  Quotient.lift₂ (fun ⟨a, b⟩ ⟨c, d⟩ => (a + c) —— (b + d)) (
    by
      intro ⟨a, b⟩ ⟨c, d⟩ ⟨a', b'⟩ ⟨c', d'⟩ h1 h2
      replace h1 : a + b' = a' + b := h1
      replace h2 : c + d' = c' + d := h2
      simp
      sorry
  )

instance : Add Integer := ⟨Integer.add⟩

end Analysis.Ch04.Sec01
