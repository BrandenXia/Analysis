import Mathlib.Tactic

namespace Analysis.Common

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

end Analysis.Common
