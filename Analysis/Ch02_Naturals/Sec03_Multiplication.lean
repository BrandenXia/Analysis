import Mathlib.Logic.ExistsUnique
import Mathlib.Tactic
import Mathlib.Tactic.Contrapose

import Analysis.Ch02_Naturals.Sec01_PeanoAxioms
import Analysis.Ch02_Naturals.Sec02_Addition

open Analysis.Ch02.Sec01
open Analysis.Ch02.Sec02

namespace Analysis.Ch02.Sec03

def Natural.Mul (n m : Natural) := match n with
  | Natural.zero => Natural.zero
  | n'++ => (Natural.Mul n' m) + m

instance : Mul Natural := ⟨Natural.Mul⟩

theorem mul_comm (n m : Natural) : n * m = m * n := by
  apply mathematical_induction (fun n => n * m = m * n)
  case h0 =>
    change Natural.zero = m * Natural.zero
    apply mathematical_induction (fun m => Natural.zero = m * Natural.zero)
    case h0 => rfl
    case h1 =>
      intro m' ih
      change Natural.zero = (m' * Natural.zero) + Natural.zero
      rw [<-ih]
      rfl
  case h1 =>
    intro n' ih
    change (n' * m) + m = m * n'++
    rw [ih]
    apply mathematical_induction (fun m => (m * n') + m = m * n'++)
    case h0 => rfl
    case h1 =>
      intro m' ih'
      change m' * n' + n' + m'++ = m' * n'++ + n'++
      rw [<-ih', add_succ, add_succ, add_assoc, add_comm n', <-add_assoc]

theorem mul_zero (n : Natural) : n * Natural.zero = Natural.zero := by
  rw [mul_comm]
  rfl

theorem mul_succ (n m : Natural) : n * m++ = n * m + n := by
  rw [mul_comm]
  change m * n + n = n * m + n
  rw [mul_comm]

theorem no_zero_divisors (n m : Natural) :
    n * m = Natural.zero ↔ n = Natural.zero ∨ m = Natural.zero
  := by
    constructor
    · apply mathematical_induction
        (fun n => n * m = Natural.zero → n = Natural.zero ∨ m = Natural.zero)
      case h0 => simp
      case h1 =>
        intro n ih h
        apply Sec02.add_eq_zero at h
        right
        exact And.right h
    · intro h
      apply Or.elim h
      · intro neq0
        subst n
        rfl
      · intro meq0
        subst m
        rw [mul_comm]
        rfl

theorem positive_mul (n m : Natural) (h : is_positive n ∧ is_positive m) :
    is_positive (n * m) := by
  apply Iff.mpr <| not_congr <| no_zero_divisors n m
  rw [not_or]
  exact h

theorem mul_left_distrib (a b c : Natural) :
    a * (b + c) = a * b + a * c := by
  apply mathematical_induction (fun c => a * (b + c) = a * b + a * c)
  case h0 => simp [add_zero, mul_zero]
  case h1 =>
    intro n ih
    rw [add_succ, mul_succ, ih, mul_succ, add_assoc]

theorem mul_right_distrib (a b c : Natural) :
    (b + c) * a = b * a + c * a := by
  simp [mul_comm, mul_left_distrib]

theorem mul_assoc (a b c : Natural) :
    a * b * c = a * (b * c) := by
  apply mathematical_induction (fun a => a * b * c = a * (b * c))
  case h0 => rfl
  case h1 =>
    intro n ih
    change (n * b + b) * c = n * (b * c) + b * c
    rw [mul_right_distrib, ih]

theorem mul_preserves_order (a b c : Natural) (h : a < b) (h1 : is_positive c) :
    a * c < b * c := by
  apply Iff.mp <| Natural.ordering_add_positive a b at h
  obtain ⟨d, d_pos, a2b⟩ := h
  apply_fun (· * c) at a2b
  rw [mul_right_distrib] at a2b
  apply Iff.mpr <| Natural.ordering_add_positive (a * c) (b * c)
  exists d * c
  constructor
  · apply positive_mul
    exact ⟨d_pos, h1⟩
  · exact a2b

theorem mul_cancellation_law (a b c : Natural) (c_pos : is_positive c)
    (h : a * c = b * c) : a = b := by
  rcases natural_trichotomy a b with (a_lt_b | a_eq_b | b_lt_a)
  · let contra := And.left a_lt_b
    apply mul_preserves_order at contra
    let contra' := And.right <| contra c_pos
    contradiction
  · exact And.left <| And.right a_eq_b
  · let contra := And.right <| And.right b_lt_a
    apply mul_preserves_order at contra
    let contra' := And.right <| contra c_pos
    symm at contra'
    contradiction

theorem euclid_division_lemma (n q : Natural) (qh : is_positive q) :
    ∃ m r, Natural.zero ≤ r ∧ r < q ∧ n = m * q + r := by
  apply mathematical_induction (fun n => ∃ m r, Natural.zero ≤ r ∧ r < q ∧ n = m * q + r)
  case h0 =>
    exists Natural.zero, Natural.zero
    repeat constructor
    · symm
      exact qh
    · simp [mul_zero, mul_comm, add_zero]
  case h1 =>
    intro n ih
    obtain ⟨m, r, r_geq_0, r_lt_q, n_eq_mq_plus_r⟩ := ih
    rcases natural_trichotomy r++ q with (r_lt_q' | r_eq_q | q_lt_r)
    · exists m, (r++)
      and_intros
      · exists (r++)
      · exact And.left <| And.left r_lt_q'
      · exact And.left <| And.right r_lt_q'
      · rw [add_succ]
        congr
    · exists m++, Natural.zero
      and_intros
      · apply Natural.ordering_rfl
      · exists q
      · symm
        exact qh
      · subst n
        rw [add_zero, <-add_succ]
        change m * q + r++ = m * q + q
        congr
        exact And.left <| And.right r_eq_q
    · obtain ⟨d, d_pos, q2rpp⟩ := Iff.mp (Natural.ordering_add_positive q r++)
        <| And.right <| And.right q_lt_r
      replace q_lt_r := And.right <| And.right q_lt_r
      obtain ⟨d', d'pos, r2q⟩ := Iff.mp (Natural.ordering_add_positive r q) r_lt_q
      rw [r2q] at q2rpp
      cases d' with
      | zero => contradiction
      | succ d' =>
        rw [add_succ] at q2rpp
        change r++ = ((r + d' + d)++) at q2rpp
        apply succ_injective at q2rpp
        rw [Sec02.add_assoc] at q2rpp
        conv at q2rpp =>
          lhs
          rw [<-Sec02.add_zero r]
        apply add_cancellation_law at q2rpp
        symm at q2rpp
        apply Sec02.add_eq_zero at q2rpp
        let contra := And.right q2rpp
        contradiction

def Natural.Exponentiation (m n : Natural) := match n with
  | .zero => Natural.succ Natural.zero
  | .succ n' => (Natural.Exponentiation m n') * m

instance : HomogeneousPow Natural := ⟨Natural.Exponentiation⟩

end Analysis.Ch02.Sec03
