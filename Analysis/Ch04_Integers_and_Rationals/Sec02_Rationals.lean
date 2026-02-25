import Mathlib.Tactic

import Analysis.Common

open Analysis.Common

namespace Analysis.Ch04.Sec02

structure Rational_ where
  numerator : ℤ
  denominator : ℤ
  nonzero : denominator ≠ 0

def Rational_.eq : Rational_ → Rational_ → Prop :=
  fun ⟨a, b, _⟩ ⟨c, d, _⟩ => a * d = c * b

theorem Rational_.eq_rfl : ∀ x : Rational_, x.eq x := by
  rintro ⟨a, b, _⟩
  simp [Rational_.eq]

theorem Rational_.eq_symm {x y : Rational_} : x.eq y → y.eq x := by
  intro h
  simp only [Rational_.eq] at h
  exact h.symm

theorem Rational_.eq_trans : ∀ {x y z : Rational_}, x.eq y → y.eq z → x.eq z := by
  rintro ⟨a, b, hb⟩ ⟨c, d, hd⟩ ⟨e, f, hf⟩ h₁ h₂
  simp only [Rational_.eq] at *
  apply_fun (· * f) at h₁
  apply_fun (· * b) at h₂
  ring_nf at h₁ h₂
  rw [<-h₁, mul_comm, <-mul_assoc, mul_comm, mul_assoc] at h₂
  apply mul_left_cancel₀ hd at h₂
  linarith

instance Rational_.instSetoid : Setoid Rational_ where
  r := Rational_.eq
  iseqv := {
    refl := Rational_.eq_rfl,
    symm := Rational_.eq_symm,
    trans := Rational_.eq_trans
  }

@[simp]
theorem Rational_.eq_iff (a b c d : ℤ) (hb : b ≠ 0) (hd : d ≠ 0) :
    (⟨a, b, hb⟩ : Rational_) ≈ ⟨c, d, hd⟩ ↔ a * d = c * b := by rfl
def Rational := Quotient Rational_.instSetoid

def Rational.formalDiv (a b : ℤ) : Rational :=
  Quotient.mk Rational_.instSetoid (if h : b ≠ 0 then ⟨a, b, h⟩ else ⟨0, 1, by decide⟩)

infix:100 " // " => Rational.formalDiv

theorem Rational.eq (a c : ℤ) {b d : ℤ} (hb : b ≠ 0) (hd : d ≠ 0) :
    a // b = c // d ↔ a * d = c * b := by sorry

end Analysis.Ch04.Sec02
