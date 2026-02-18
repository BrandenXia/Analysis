import Mathlib.Logic.ExistsUnique

namespace Analysis.Ch02.Sec01

inductive Natural where
  | zero : Natural
  | succ : Natural → Natural

postfix:max "++" => Natural.succ

axiom zero_not_successor (n : Natural) : n++ ≠ Natural.zero

axiom diff_natural_diff_succ (n m : Natural) : n ≠ m → n++ ≠ m++

axiom mathematical_induction (P : Natural → Prop) (h0 : P Natural.zero)
    (h1 : ∀ n, P n → P n++) :
  ∀ n : Natural, P n

def recursive_step (fₙ : Natural → Natural → Natural) (c : Natural) : Natural → Natural
  | Natural.zero => c
  | n++ => fₙ n (recursive_step fₙ c n)

theorem recursive_definitions (fₙ : Natural → Natural → Natural) (c : Natural) :
  ∃! a : Natural → Natural,
    a Natural.zero = c
    ∧ ∀ n, a n++ = fₙ n (a n)
  := by
    let a : Natural → Natural := recursive_step fₙ c
    exists a
    constructor
    · constructor
      · rfl
      · intro n
        rfl
    · intro a' ha'
      apply funext
      apply mathematical_induction (fun n => a' n = a n)
      case h0 => apply And.left ha'
      case h1 =>
        intro n ih
        rw [And.right ha' n]
        congr

end Analysis.Ch02.Sec01
