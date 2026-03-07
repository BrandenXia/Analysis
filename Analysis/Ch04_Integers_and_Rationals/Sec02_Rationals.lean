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
    a // b = c // d ↔ a * d = c * b := by
  constructor
  · intro h
    simp only [Rational.formalDiv, hb, hd, ne_eq, not_false_eq_true, reduceDIte] at h
    apply Quotient.exact h
  · intro h
    apply Quotient.sound
    simp only [hb, hd, ne_eq, not_false_eq_true, reduceDIte, Rational_.eq_iff]
    exact h

theorem Rational.eq_diff (n : Rational) : ∃ a b, b ≠ 0 ∧ n = a // b := by
  apply Quotient.ind _ n
  intro ⟨a, b, h⟩
  refine ⟨a, b, h, ?_⟩
  simp [formalDiv, h]

instance Rational.decidableEq : DecidableEq Rational := by
  intro a b
  have : ∀ n m,
      Decidable (Quotient.mk Rational_.instSetoid n = Quotient.mk Rational_.instSetoid m) := by
    intro ⟨a, b, hb⟩ ⟨c, d, hd⟩
    exact if h : a * d = c * b then
      isTrue (Quotient.sound h)
    else
      isFalse (fun h_eq => h (Quotient.exact h_eq))
  exact Quotient.recOnSubsingleton₂ a b this

def Rational.Add : Rational → Rational → Rational :=
  Quotient.lift₂ (fun ⟨a, b, hb⟩ ⟨c, d, hd⟩ => (a * d + c * b) // (b * d))
    <| by
      intro ⟨a, b, hb⟩ ⟨c, d, hd⟩ ⟨a', b', hb'⟩ ⟨c', d', hd'⟩ h1 h2
      simp_all [eq]
      grind

instance : Add Rational := ⟨Rational.Add⟩

theorem Rational.add_eq (a c : ℤ) {b d : ℤ} (hb : b ≠ 0) (hd : d ≠ 0) :
    a // b + c // d = (a * d + c * b) // (b * d) := by
  change Rational.Add (a // b) (c // d) = (a * d + c * b) // (b * d)
  simp [Rational.formalDiv, Rational.Add, hb, hd]

def Rational.Mul : Rational → Rational → Rational :=
  Quotient.lift₂ (fun ⟨a, b, hb⟩ ⟨c, d, hd⟩ => (a * c) // (b * d))
    <| by
      intro ⟨a, b, hb⟩ ⟨c, d, hd⟩ ⟨a', b', hb'⟩ ⟨c', d', hd'⟩ h1 h2
      simp_all [eq]
      grind

instance : Mul Rational := ⟨Rational.Mul⟩

theorem Rational.mul_eq (a c : ℤ) {b d : ℤ} (hb : b ≠ 0) (hd : d ≠ 0) :
    (a // b) * (c // d) = (a * c) // (b * d) := by
  change Rational.Mul (a // b) (c // d) = (a * c) // (b * d)
  simp [Rational.formalDiv, Rational.Mul, hb, hd]

def Rational.Neg : Rational → Rational :=
  Quotient.lift (fun ⟨a, b, hb⟩ => (-a) // b)
    <| by
      intro ⟨a, b, hb⟩ ⟨a', b', hb'⟩ h
      simp_all [eq]

instance : Neg Rational := ⟨Rational.Neg⟩

theorem Rational.neg_eq (a : ℤ) {b : ℤ} (hb : b ≠ 0) :
    - (a // b) = (-a) // b := by
  change Rational.Neg (a // b) = (-a) // b
  simp [Rational.formalDiv, Rational.Neg, hb]

instance : IntCast Rational where
  intCast n := n // 1

instance : NatCast Rational where
  natCast n := (n : ℤ) // 1

instance {n : ℕ} : OfNat Rational n where
  ofNat := (n : ℤ) // 1

theorem Rational.coe_Int_eq (n : ℤ) : (n : Rational) = n // 1 := by rfl
theorem Rational.coe_Nat_eq (n : ℕ) : (n : Rational) = n // 1 := by rfl
theorem Rational.ofNat_eq (n : ℕ) : (ofNat(n) : Rational) = (ofNat(n) : Nat) // 1 := by rfl

theorem Rational.natCast_succ (n : ℕ) : ((n + 1 : ℕ) : Rational) = (n : Rational) + 1 := by
  simp [ofNat_eq, Rational.coe_Nat_eq, Rational.add_eq]

theorem Rational.intCast_add (n m : ℤ) : (n : Rational) + (m : Rational) = (n + m : ℤ) := by
  simp [Rational.coe_Int_eq, Rational.add_eq]

theorem Rational.intCast_mul (n m : ℤ) : (n : Rational) * (m : Rational) = (n * m : ℤ) := by
  simp [Rational.coe_Int_eq, Rational.mul_eq]

theorem Rational.intCast_neg (n : ℤ) : - (n : Rational) = (-n : ℤ) := by
  simp [Rational.coe_Int_eq, Rational.neg_eq]

theorem Rational.coe_Int_inj : Function.Injective (fun n : ℤ => (n : Rational)) := by
  intro n m h
  simp only [Rational.coe_Int_eq, eq, ne_eq, one_ne_zero, not_false_eq_true, mul_one] at h
  exact h

def Rational.Inv : Rational → Rational :=
  Quotient.lift (fun ⟨a, b, hb⟩ => b // a)
    <| by
      intro ⟨a, b, hb⟩ ⟨a', b', hb'⟩ h
      simp_all only [Rational_.eq_iff]
      by_cases ha : a = 0
      · simp_all [formalDiv]
      · rw [<-ne_eq] at ha
        let hab' := mul_ne_zero ha hb'
        simp only [h, ne_eq, mul_eq_zero, not_or] at hab'
        let ha' := And.left hab'
        rw [<-ne_eq] at ha'
        simp only [ne_eq, not_false_eq_true, eq, ha', ha]
        rw [mul_comm]
        conv in b' * a => rw [mul_comm]
        symm
        exact h

instance : Inv Rational := ⟨Rational.Inv⟩

theorem Rational.inv_eq (a : ℤ) {b : ℤ} (hb : b ≠ 0) (ha : a ≠ 0) :
    (a // b)⁻¹ = b // a := by
  change Rational.Inv (a // b) = b // a
  simp [Rational.formalDiv, Rational.Inv, hb, ha]

end Analysis.Ch04.Sec02
