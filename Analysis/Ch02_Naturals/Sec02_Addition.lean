import Mathlib.Tactic
import Mathlib.Tactic.Contrapose

import Analysis.Ch02_Naturals.Sec01_PeanoAxioms

open Analysis.Ch02.Sec01

namespace Analysis.Ch02.Sec01

def Natural.Add (n m : Natural) := match n with
  | Natural.zero => m
  | n'++ => (Natural.Add n' m)++

instance : Add Natural := ⟨Natural.Add⟩

theorem add_zero (n : Natural) : n + Natural.zero = n := by
  apply mathematical_induction (fun n => n + Natural.zero = n)
  case h0 => rfl
  case h1 =>
    intro n ih
    change (n + Natural.zero)++ = (n++)
    rw [ih]

theorem add_succ (n m : Natural) : n + m++ = (n + m)++ := by
  apply mathematical_induction (fun n => n + m++ = (n + m)++)
  case h0 => rfl
  case h1 =>
    intro n ih
    change (n + m++)++ = ((n++ + m)++)
    rw [ih]
    rfl

theorem add_comm (n m : Natural) : n + m = m + n := by
  apply mathematical_induction (fun n => n + m = m + n)
  case h0 =>
    rw [add_zero]
    rfl
  case h1 =>
    intro n ih
    rw [add_succ]
    change (n + m)++ = ((m + n)++)
    congr

theorem add_assoc (a b c : Natural) : (a + b) + c = a + (b + c) := by
  apply mathematical_induction (fun a => (a + b) + c = a + (b + c))
  case h0 => rfl
  case h1 =>
    intro a ih
    conv =>
      lhs
      rw [add_comm]
      conv =>
        rhs
        rw [add_comm, add_succ]
      rw [add_succ]
      conv =>
        rhs
        rw [add_comm]
        conv =>
          lhs
          rw [add_comm]
    conv =>
      rhs
      rw [add_comm, add_succ]
      conv =>
        rhs
        rw [add_comm]
    rw [ih]

theorem cancellation_law (a b c : Natural) : a + b = a + c → b = c := by
  apply mathematical_induction (fun a => a + b = a + c → b = c)
  case h0 =>
    intro ih
    apply ih
  case h1 =>
    intro n ih h
    let succ_contrapos := Mathlib.Tactic.Contrapose.contrapose₁ <|
      diff_natural_diff_succ (n + b) (n + c)
    exact ih <| succ_contrapos h

def is_positive (n : Natural) : Prop := n ≠ Natural.zero

theorem add_positive_eq_positive (n m : Natural) (h : is_positive n) : is_positive (n + m) := by
    apply mathematical_induction (fun m => is_positive <| n + m)
    case h0 =>
      rw [add_zero]
      exact h
    case h1 =>
      intro m ih
      conv =>
        rhs
        rw [add_succ]
      apply zero_not_successor

theorem add_eq_zero (n m : Natural) (h : n + m = Natural.zero) :
    n = Natural.zero ∧ m = Natural.zero := by
  by_contra h'
  rw [not_and_or, <-ne_eq] at h'
  cases h'
  case inl hl =>
    let contra := add_positive_eq_positive n m hl
    contradiction
  case inr hr =>
    let contra := add_positive_eq_positive m n hr
    rw [add_comm] at contra
    contradiction

end Analysis.Ch02.Sec01
