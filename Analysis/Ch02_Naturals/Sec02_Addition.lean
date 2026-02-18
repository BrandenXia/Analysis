import Mathlib.Logic.ExistsUnique
import Mathlib.Tactic
import Mathlib.Tactic.Contrapose

import Analysis.Ch02_Naturals.Sec01_PeanoAxioms

open Analysis.Ch02.Sec01

namespace Analysis.Ch02.Sec02

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

theorem exact_succ (a : Natural) (h : is_positive a) : ∃! b, b++ = a := by
  cases a with
  | zero => contradiction
  | succ b =>
    exists b
    constructor
    · rfl
    · intro b' h
      let succ_contrapos := Mathlib.Tactic.Contrapose.contrapose₁ <| diff_natural_diff_succ b b'
      symm at h
      exact symm <| succ_contrapos h

def Natural.less_than_or_eq (n m : Natural) : Prop := ∃ a, n + a = m

instance : LE Natural := ⟨Natural.less_than_or_eq⟩

def Natural.less_than (n m : Natural) : Prop := Natural.less_than_or_eq n m ∧ n ≠ m

instance : LT Natural := ⟨Natural.less_than⟩

theorem Natural.ordering_rfl (a : Natural) : a ≥ a := by
  exists Natural.zero
  rw [add_zero]

theorem Natural.ordering_trans (a b c : Natural) : a ≥ b ∧ b ≥ c → a ≥ c := by
  intro h
  obtain ⟨d, a2b⟩ := h.1
  obtain ⟨e, b2c⟩ := h.2
  let f := e + d
  exists f
  rw [<-add_assoc, b2c, a2b]

theorem Natural.ordering_antisymm (a b : Natural) : a ≥ b ∧ b ≥ a → a = b := by
  intro h
  obtain ⟨d, a2b⟩ := h.1
  obtain ⟨e, b2a⟩ := h.2
  rw [<-b2a, add_assoc] at a2b
  conv at a2b =>
    rhs
    change Natural.zero + a
    rw [add_comm]
  let cancelled := cancellation_law a (e + d) Natural.zero a2b
  apply add_eq_zero at cancelled
  rw [cancelled.1, add_zero] at b2a
  exact b2a

theorem Natural.ordering_add_preserves (a b c : Natural) : a ≥ b → a + c ≥ b + c := by
  intro h
  obtain ⟨d, a2b⟩ := h
  exists d
  rw [add_assoc]
  conv =>
    lhs; rhs
    rw [add_comm]
  rw [<-add_assoc, a2b]

theorem Natural.ordering_add_positive (a b : Natural) :
    a < b ↔ ∃ d, is_positive d ∧ b = a + d := by
  constructor
  case mp =>
    intro h
    obtain ⟨d, a2b⟩ := h.1
    exists d
    constructor
    · change ¬ d = Natural.zero
      by_contra
      rw [this, add_zero] at a2b
      let contra := h.2
      contradiction
    · symm at a2b
      exact a2b
  case mpr =>
    intro h
    obtain ⟨d, d_pos, b_eq⟩ := h
    constructor
    · exists d
      symm at b_eq
      exact b_eq
    · by_contra
      rw [this] at b_eq
      conv at b_eq =>
        lhs
        change Natural.zero + b
        rw [add_comm]
      let contra := cancellation_law b Natural.zero d
      apply contra at b_eq
      change d ≠ Natural.zero at d_pos
      symm at d_pos
      contradiction


theorem Natural.ordering_succ (a b : Natural) : a < b ↔ a++ ≤ b := by
  constructor
  case mp =>
    intro h
    apply Iff.mp <| Natural.ordering_add_positive a b at h
    obtain ⟨d, d_pos, b_eq⟩ := h
    cases d with
    | zero => contradiction
    | succ d' =>
      rw [add_succ] at b_eq
      exists d'
      symm at b_eq
      exact b_eq
  case mpr =>
    intro h
    obtain ⟨d, b_eq⟩ := h
    change (a + d)++ = b at b_eq
    rw [<-add_succ] at b_eq
    constructor
    · exists (d++)
    · by_contra
      rw [this] at b_eq
      conv at b_eq =>
        rhs
        change Natural.zero + b
        rw [add_comm]
      let contra := cancellation_law b d++ Natural.zero
      apply contra at b_eq
      contradiction

def one_hot (p q r : Prop) : Prop :=
  (   p ∧ ¬ q ∧ ¬ r) ∨
  ( ¬ p ∧   q ∧ ¬ r) ∨
  ( ¬ p ∧ ¬ q ∧   r)

theorem at_least_at_most_one_hot (p q r : Prop)
    (at_least : p ∨ q ∨ r) (at_most : ¬ (p ∧ q) ∧ ¬ (p ∧ r) ∧ ¬ (q ∧ r)) :
      one_hot p q r := by
  rcases at_least with hp | hq | hr
  · left
    refine ⟨hp, ?_, ?_⟩
    · intro hq; exact at_most.1 ⟨hp, hq⟩
    · intro hr; exact at_most.2.1 ⟨hp, hr⟩
  · right; left
    refine ⟨?_, hq, ?_⟩
    · intro hp; exact at_most.1 ⟨hp, hq⟩
    · intro hr; exact at_most.2.2 ⟨hq, hr⟩
  · right; right
    refine ⟨?_, ?_, hr⟩
    · intro hp; exact at_most.2.1 ⟨hp, hr⟩
    · intro hq; exact at_most.2.2 ⟨hq, hr⟩

theorem natural_trichotomy (a b : Natural) : one_hot (a < b) (a = b) (a > b) := by
  apply at_least_at_most_one_hot
  case at_least =>
    apply mathematical_induction (fun a => a < b ∨ a = b ∨ a > b)
    case h0 =>
      cases b with
      | zero => right; left; rfl
      | succ b' =>
        left
        constructor
        · exists (b'++)
        · symm; apply zero_not_successor
    case h1 =>
      intro a ih
      rcases ih with (h_lt | h_eq | h_gt)
      case inl =>
        apply Iff.mp <| Natural.ordering_succ a b at h_lt
        by_cases h : (a++ = b)
        · right; left; exact h
        · left; constructor
          · exact h_lt
          · exact h
      case inr.inl =>
        right; right;
        constructor
        · exists (Natural.zero++)
          rw [add_succ, add_zero]
          symm
          congr
        · symm
          by_contra
          subst b
          change Natural.zero + a++ = Natural.zero + a at this
          rw [add_succ, add_comm, <-add_succ] at this
          apply cancellation_law a Natural.zero++ Natural.zero at this
          contradiction
      case inr.inr =>
        right; right
        change b < (a++)
        apply Iff.mpr <| Natural.ordering_add_positive b (a++)
        obtain ⟨d, b2a⟩ := h_gt.left
        exists (d++)
        constructor
        · apply zero_not_successor
        · rw [add_succ]
          symm
          congr
  case at_most =>
    and_intros
    case refine_1 =>
      by_contra
      let fst := And.right <| And.left this
      let snd := And.right this
      contradiction
    case refine_2.refine_1 =>
      by_contra
      let fst := And.right <| And.left this
      let snd := And.intro (And.left <| And.left this) (And.left <| And.right this)
      apply Natural.ordering_antisymm at snd
      symm at snd
      contradiction
    case refine_2.refine_2 =>
      by_contra
      let fst := And.left this
      let snd := And.right <| And.right this
      symm at snd
      contradiction

theorem strong_induction_prep (m m₀ : Natural) (P : Natural → Prop)
    (h : ∀ m', m₀ ≤ m' ∧ m' ≤ m ∧ P m') : ∀ (n m : Natural), m₀ ≤ m ∧ m < n → P m := by
  let Q := fun n : Natural => ∀ m, m₀ ≤ m ∧ m < n → P m
  apply mathematical_induction Q
  · intro n h'
    let contra := And.right h'
    apply Iff.mp <| Natural.ordering_add_positive n Natural.zero at contra
    obtain ⟨d, d_pos, n_eq⟩ := contra
    symm at n_eq
    apply add_eq_zero at n_eq
    let zero_contra' := And.right n_eq
    contradiction
  · intro n ih
    let bound_h := And.right <| And.right <| h n
    intro m nh
    let trichotomy := natural_trichotomy m n
    rcases trichotomy with (h_lt | h_eq | h_gt)
    · exact ih m <| And.intro (And.left nh) (And.left h_lt)
    · rw [And.left <| And.right h_eq]
      exact bound_h
    · let nh' := And.right nh
      let mh' := And.right <| And.right h_gt
      apply Iff.mp <| Natural.ordering_add_positive m n++ at nh'
      apply Iff.mp <| Natural.ordering_add_positive n m at mh'
      obtain ⟨d, d_pos, n_eq⟩ := nh'
      obtain ⟨e, e_pos, m_eq⟩ := mh'
      rw [m_eq] at n_eq
      cases d with
      | zero => contradiction
      | succ k =>
        rw [add_assoc, add_succ, add_succ] at n_eq
        apply Mathlib.Tactic.Contrapose.contrapose₁ <|
          diff_natural_diff_succ n (n + (e + k)) at n_eq
        change Natural.zero + n = n + (e + k) at n_eq
        rw [add_comm] at n_eq
        apply cancellation_law n Natural.zero (e + k) at n_eq
        symm at n_eq
        apply add_eq_zero at n_eq
        let zero_contra := And.left n_eq
        contradiction

theorem strong_induction (m₀ : Natural) (P : Natural → Prop) :
    ∀ m ≥ m₀, (∀ m', m₀ ≤ m' ∧ m' ≤ m ∧ P m') → P m := by
  intro m mh h
  apply strong_induction_prep m m₀ P h m++ m
  constructor
  · exact mh
  · constructor
    · exists (Natural.zero++)
      rw [add_succ, add_zero]
    · by_contra
      change Natural.zero + m = Natural.zero + m++ at this
      conv at this =>
        left
        rw [add_comm]
      conv at this =>
        right
        rw [add_succ, add_comm, <-add_succ]
      apply cancellation_law m Natural.zero Natural.zero++ at this
      symm at this
      apply zero_not_successor at this
      exact this

end Analysis.Ch02.Sec02
