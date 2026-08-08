/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Axioms

/-!
# The backward diamond and uniqueness of origins

`bstep_diamond` is where the Square Property and BTI first pay for
themselves: two different ways of undoing the same state reconverge.

`unique_origin` is its consequence under well-foundedness — however you
rewind, you arrive at the same place.  This is the state-level shadow of
causal consistency, and it is exactly the soundness property a reversible
debugger needs.

## References

* [I. Lanese, I. Phillips, I. Ulidowski, *An Axiomatic Theory for Reversible
  Computation*, ACM TOCL 25(2), 2024][LPU2024]
-/

universe u v

namespace Cslib.LTS

variable {State : Type u} {Label : Type v} {lts : LTS State Label}
variable {Indep : Transition State Label → Transition State Label → Prop}

/--
**Backward diamond.**  Two undo steps out of the same state either agree or
reconverge in one further step each.

Decidable equality of transitions is what keeps the case split below
constructive, exactly as in the Rocq development this layer is ported from.
-/
theorem bstep_diamond [DecidableEq State] [DecidableEq Label]
    [SquareProperty lts Indep] [BTI lts Indep]
    {p q₁ q₂ : State} (h₁ : BStep lts p q₁) (h₂ : BStep lts p q₂) :
    q₁ = q₂ ∨ ∃ w, BStep lts q₁ w ∧ BStep lts q₂ w := by
  obtain ⟨t, htv, htb, hts, htt⟩ := h₁
  obtain ⟨u, huv, hub, hus, hut⟩ := h₂
  refine Decidable.byCases (p := t = u) (fun htu => ?_) (fun htu => ?_)
  · subst htu
    exact Or.inl (htt ▸ hut ▸ rfl)
  · refine Or.inr ?_
    have hco : t.Coinitial u := hts.trans hus.symm
    have hind := BTI.bti (Indep := Indep) htv huv hco htb hub htu
    obtain ⟨w, hw₁, hw₂⟩ := SquareProperty.square (Indep := Indep) htv huv hind
    exact ⟨w, ⟨_, hw₁, hub, htt, rfl⟩, ⟨_, hw₂, htb, hut, rfl⟩⟩

/-- An origin admits no backward step, so any rewinding from it is trivial. -/
theorem Origin.reflTransGen_eq {o p : State} (ho : Origin lts o)
    (h : Relation.ReflTransGen (BStep lts) o p) : o = p := by
  rcases reflTransGen_cases_head h with h | ⟨c, hc, _⟩
  · exact h
  · exact absurd hc (ho c)

/--
**Uniqueness of origins.**  However a state is rewound, the origin reached is
the same.
-/
theorem unique_origin [DecidableEq State] [DecidableEq Label]
    [SquareProperty lts Indep] [BTI lts Indep]
    [WellFoundedBwd lts] [BStepDec lts] {p o₁ o₂ : State}
    (h₁ : Relation.ReflTransGen (BStep lts) p o₁) (ho₁ : Origin lts o₁)
    (h₂ : Relation.ReflTransGen (BStep lts) p o₂) (ho₂ : Origin lts o₂) :
    o₁ = o₂ := by
  induction p using (WellFoundedBwd.wf (lts := lts)).induction generalizing o₁ o₂ with
  | _ p ih =>
    rcases reflTransGen_cases_head h₁ with rfl | ⟨q₁, hq₁, hr₁⟩
    · exact ho₁.reflTransGen_eq h₂
    rcases reflTransGen_cases_head h₂ with rfl | ⟨q₂, hq₂, hr₂⟩
    · exact (ho₂.reflTransGen_eq h₁).symm
    rcases bstep_diamond (Indep := Indep) hq₁ hq₂ with rfl | ⟨w, hw₁, hw₂⟩
    · exact ih q₁ hq₁ hr₁ ho₁ hr₂ ho₂
    · obtain ⟨o, hpath, ho⟩ := exists_origin (lts := lts) w
      have e₁ : o₁ = o := ih q₁ hq₁ hr₁ ho₁ (.head hw₁ hpath) ho
      have e₂ : o₂ = o := ih q₂ hq₂ hr₂ ho₂ (.head hw₂ hpath) ho
      exact e₁.trans e₂.symm

end Cslib.LTS
