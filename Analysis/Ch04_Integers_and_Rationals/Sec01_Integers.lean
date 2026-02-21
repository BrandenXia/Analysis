import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

import Analysis.Common

open Analysis.Common

namespace Analysis.Ch04.Sec01

structure Integer_ where
  minuend : ℕ
  subtrahend : ℕ

def Integer_.eq : Integer_ → Integer_ → Prop :=
  fun ⟨a, b⟩ ⟨c, d⟩ => a + d = c + b

theorem Integer_.eq_refl : ∀ x : Integer_, Integer_.eq x x := by
  intro ⟨a, b⟩
  simp [Integer_.eq]

theorem Integer_.eq_symm {x y : Integer_} : x.eq y → y.eq x := by
  intro h
  simp only [Integer_.eq] at *
  exact h.symm

theorem Integer_.eq_trans {x y z : Integer_} : x.eq y → y.eq z → x.eq z := by
  intro hxy hyz
  simp only [Integer_.eq] at *
  have : x.minuend + y.subtrahend = y.minuend + x.subtrahend := hxy
  have : y.minuend + z.subtrahend = z.minuend + y.subtrahend := hyz
  linarith

instance Integer_.instSetoid : Setoid Integer_ where
  r := Integer_.eq
  iseqv := {
    refl := Integer_.eq_refl,
    symm := Integer_.eq_symm,
    trans := Integer_.eq_trans,
  }

@[simp]
theorem Integer_.eq_iff (a b c d : ℕ) : Integer_.eq ⟨a, b⟩ ⟨c, d⟩ ↔ a + d = c + b := by
  rfl
def Integer := Quotient Integer_.instSetoid
def Integer.FormalDiff (a b : ℕ) : Integer := Quotient.mk Integer_.instSetoid ⟨a, b⟩
infix:100 " —— " => Integer.FormalDiff

theorem Integer.eq (a b c d : ℕ) : a —— b = c —— d ↔ a + d = c + b := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound h

theorem Integer.eq_diff (n : Integer) : ∃ a b, n = a —— b := by
  apply n.ind _
  intro ⟨a, b⟩
  exists a, b

def Integer.Add : Integer → Integer → Integer :=
  Quotient.lift₂ (fun ⟨a, b⟩ ⟨c, d⟩ => (a + c) —— (b + d)) (
    by
      intro ⟨a, b⟩ ⟨c, d⟩ ⟨a', b'⟩ ⟨c', d'⟩ h1 h2
      replace h1 : a + b' = a' + b := h1
      replace h2 : c + d' = c' + d := h2
      simp only [Integer.eq]
      linarith
  )

instance : Add Integer := ⟨Integer.Add⟩

theorem Integer.add_eq (a b c d : ℕ) : (a —— b) + (c —— d) = (a + c) —— (b + d) := by
  rfl

theorem Integer.mul_congr_right (a b c d c' d' : ℕ) (h : c —— d = c' —— d') :
    (a * c + b * d) —— (a * d + b * c) = (a * c' + b * d') —— (a * d' + b * c') := by
  simp only [Integer.eq] at *
  calc
    _ = a * (c + d') + b * (c' + d) := by group
    _ = a * (c' + d) + b * (c + d') := by rw [h]
    _ = _ := by group

def Integer.Mul : Integer → Integer → Integer :=
  Quotient.lift₂ (fun ⟨a, b⟩ ⟨c, d⟩ => (a * c + b * d) —— (a * d + b * c)) (
    by
      intro ⟨a, b⟩ ⟨c, d⟩ ⟨a', b'⟩ ⟨c', d'⟩ h1 h2
      replace h1 : a + b' = a' + b := h1
      replace h2 : c + d' = c' + d := h2
      apply Iff.mpr <| Integer.eq c d c' d' at h2
      simp only
      rw [Integer.mul_congr_right a b c d c' d' h2]
      simp only [Integer.eq]
      calc
        _ = (a + b') * c' + (a' + b) * d' := by group
        _ = (a' + b) * c' + (a + b') * d' := by rw [h1]
        _ = _ := by group
  )

instance : Mul Integer := ⟨Integer.Mul⟩

theorem Integer.mul_eq (a b c d : ℕ) :
    (a —— b) * (c —— d) = (a * c + b * d) —— (a * d + b * c) := by
  rfl

instance {n : ℕ} : OfNat Integer n := ⟨n —— 0⟩
instance : NatCast Integer := ⟨fun n => n —— 0⟩
theorem Integer.ofNat_eq (n : ℕ) : ofNat(n) = n —— 0 := by rfl
theorem Integer.natCast_eq (n : ℕ) : (n : Integer) = n —— 0 := by rfl
@[simp]
theorem Integer.natCast_ofNat (n : ℕ) : ((ofNat(n) : ℕ) : Integer) = ofNat(n) := by rfl
@[simp]
theorem Integer.ofNat_inj (m n : ℕ) :
    (ofNat(n) : Integer) = (ofNat(m) : Integer) ↔ ofNat(n) = ofNat(m) := by
  simp only [ofNat_eq, eq, add_zero]
  rfl
@[simp]
theorem Integer.natCast_inj (m n : ℕ) :
    ((n : Integer) = (m : Integer)) ↔ (n : Integer) = (m : Integer) := by
  simp only [natCast_eq, eq, add_zero]

def Integer.Neg : Integer → Integer :=
  Quotient.lift (fun ⟨a, b⟩ => b —— a) (
    by
      intro ⟨a, b⟩ ⟨a', b'⟩ h
      simp only [Integer.eq]
      replace h : a + b' = a' + b := h
      simp [add_comm, h]
  )

instance : Neg Integer := ⟨Integer.Neg⟩

theorem Integer.neg_eq (a b : ℕ) : -(a —— b) = b —— a := by rfl

def Integer.is_positive (x : Integer) : Prop := ∃ n : ℕ, n > 0 ∧ x =  n 
def Integer.is_negative (x : Integer) : Prop := ∃ n : ℕ, n > 0 ∧ x = -n

theorem Integer.trichotomy (x : Integer) :
    one_hot x.is_positive x.is_negative (x = 0) := by
  apply at_least_at_most_one_hot
  · obtain ⟨a, b⟩ := x
    rcases Nat.lt_trichotomy a b with (ha | hab | hb)
    · right; left
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt ha
      exists n + 1
      constructor
      · simp
      · change a —— (a + n + 1) = 0 —— (n + 1)
        simp only [eq]
        linarith
    · right; right
      change a —— b = 0 —— 0
      simp only [eq, add_zero, zero_add]
      exact hab
    · left
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hb
      exists n + 1
      constructor
      · simp
      · change (b + n + 1) —— b = (n + 1) —— 0
        simp only [eq]
        linarith
  · and_intros
    · by_contra
      obtain ⟨n, hn, rfl⟩ := this.1
      obtain ⟨m, hm, neg⟩ := this.2
      simp only [natCast_eq, neg_eq, eq, add_zero, Nat.add_eq_zero_iff] at neg
      simp only [And.left neg] at hn
      contradiction
    · by_contra
      obtain ⟨n, hn, rfl⟩ := this.1
      let neg := this.2
      change n —— 0 = 0 —— 0 at neg
      simp only [eq, add_zero] at neg
      simp only [neg] at hn
      contradiction
    · by_contra
      obtain ⟨n, hn, rfl⟩ := this.1
      let neg := this.2
      change 0 —— n = 0 —— 0 at neg
      simp only [eq, add_zero, zero_add] at neg
      symm at neg
      simp only [neg] at hn
      contradiction

instance : AddGroup Integer := by
  apply AddGroup.ofLeftAxioms
  case assoc =>
    rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ 
    change (a₁ —— a₂) + (b₁ —— b₂) + (c₁ —— c₂) = (a₁ —— a₂) + ((b₁ —— b₂) + (c₁ —— c₂))
    simp only [Integer.add_eq, Integer.eq]
    abel
  case zero_add =>
    rintro ⟨a, b⟩
    change (0 —— 0) + (a —— b) = a —— b
    simp only [Integer.add_eq, zero_add]
  case neg_add_cancel =>
    rintro ⟨a, b⟩
    change -(a —— b) + (a —— b) = (0 —— 0)
    simp only [Integer.neg_eq, Integer.add_eq, Integer.eq]
    abel

instance : AddCommGroup Integer where
  add_comm := by
    rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    change (a₁ —— a₂) + (b₁ —— b₂) = (b₁ —— b₂) + (a₁ —— a₂)
    simp only [Integer.add_eq, Integer.eq]
    abel

instance : CommMonoid Integer where
  mul_assoc := by
    rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩
    change (a₁ —— a₂) * (b₁ —— b₂) * (c₁ —— c₂) = (a₁ —— a₂) * ((b₁ —— b₂) * (c₁ —— c₂))
    simp only [Integer.mul_eq, Integer.eq]
    group
  mul_comm := by
    rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    change (a₁ —— a₂) * (b₁ —— b₂) = (b₁ —— b₂) * (a₁ —— a₂)
    simp only [Integer.mul_eq, Integer.eq]
    group
  one_mul := by
    rintro ⟨a, b⟩
    change (1 —— 0) * (a —— b) = a —— b
    simp only [Integer.mul_eq, Integer.eq]
    group
  mul_one := by
    rintro ⟨a, b⟩
    change (a —— b) * (1 —— 0) = a —— b
    simp only [Integer.mul_eq, Integer.eq]
    group

instance : CommRing Integer where
  left_distrib := by
    rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩
    change (a₁ —— a₂) * ((b₁ —— b₂) + (c₁ —— c₂)) =
      (a₁ —— a₂) * (b₁ —— b₂) + (a₁ —— a₂) * (c₁ —— c₂)
    simp only [Integer.add_eq, Integer.mul_eq, Integer.eq]
    group
  right_distrib := by
    rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩
    change ((a₁ —— a₂) + (b₁ —— b₂)) * (c₁ —— c₂) =
      (a₁ —— a₂) * (c₁ —— c₂) + (b₁ —— b₂) * (c₁ —— c₂)
    simp only [Integer.add_eq, Integer.mul_eq, Integer.eq]
    group
  zero_mul := by
    rintro ⟨a, b⟩
    change (0 —— 0) * (a —— b) = 0 —— 0
    simp only [Integer.mul_eq, Integer.eq]
    abel
  mul_zero := by
    rintro ⟨a, b⟩
    change (a —— b) * (0 —— 0) = 0 —— 0
    simp only [Integer.mul_eq, Integer.eq]
    abel

theorem Integer.sub_eq (a b : Integer) : a - b = a + (-b) := by rfl

theorem Integer.sub_eq_formal_sub (a b : ℕ) : (a : Integer) - (b : Integer) = a —— b := by
  simp only [Integer.sub_eq, Integer.natCast_eq, Integer.neg_eq, Integer.add_eq, Integer.eq]
  abel

end Analysis.Ch04.Sec01
