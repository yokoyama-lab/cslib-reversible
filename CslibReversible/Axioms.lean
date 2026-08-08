/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Path
import Mathlib.Logic.Relation

/-!
# The axioms of reversible computation

Lanese, Phillips and Ulidowski show that the standard properties of reversible
systems — the Parabolic Lemma, causal consistency, causal safety and causal
liveness — all follow from a small set of axioms on a labelled transition
system equipped with an independence relation.  This file states those axioms
as classes, in the style CSLib uses for `LTS.Deterministic`.

The point of the exercise is that a concrete reversible language discharges
the axioms *once* and inherits the theory, instead of reproving it.

## Main definitions

- `IsIndep`: the independence relation only relates coinitial transitions.
- `IndepIrrefl`, `IndepSymm`: independence is irreflexive and symmetric — part
  of the definition of an LTSI rather than an added axiom.
- `SquareProperty`: coinitial independent transitions can each be replayed
  after the other, converging on a common state.
- `BTI`: distinct coinitial backward transitions are independent.
- `IndepSymm`, `CLG`: the two structural axioms needed for causal
  consistency proper.  `CLG` says independence is determined by the labels
  and coinitiality.
- `BStep`, `Origin`, `WellFoundedBwd`: undoing terminates.
- `BStepDec`: undoing is decidable — the debugger's step-back function.
  Keeping this constructive is what makes the development axiom-free;
  classically it is trivial.

## Main statements

- `exists_origin`: from `WellFoundedBwd` and `BStepDec`, every state can be
  rewound to an origin.

## References

* [I. Lanese, I. Phillips, I. Ulidowski, *An Axiomatic Theory for Reversible
  Computation*, ACM TOCL 25(2), 2024][LPU2024]
-/

universe u v

namespace Cslib.LTS

variable {State : Type u} {Label : Type v}

/-- An independence relation relates only coinitial transitions (LPU's axiom IC). -/
class IsIndep (lts : LTS State Label)
    (Indep : Transition State Label → Transition State Label → Prop) : Prop where
  /-- Independent transitions leave the same state. -/
  coinitial : ∀ {t u : Transition State Label}, Indep t u → t.Coinitial u

/--
**Square Property.**  Coinitial independent transitions can each be performed
after the other, with the same label and direction, converging on a common
state.
-/
class SquareProperty (lts : LTS State Label)
    (Indep : Transition State Label → Transition State Label → Prop) : Prop where
  /-- The square closes. -/
  square : ∀ {t u : Transition State Label}, t.Valid lts → u.Valid lts → Indep t u →
    ∃ w, (Transition.mk t.tgt u.lbl u.dir w).Valid lts ∧
         (Transition.mk u.tgt t.lbl t.dir w).Valid lts

/-- **Backward Transitions are Independent.** -/
class BTI (lts : LTS State Label)
    (Indep : Transition State Label → Transition State Label → Prop) : Prop where
  /-- Distinct coinitial backward transitions are independent. -/
  bti : ∀ {t u : Transition State Label}, t.Valid lts → u.Valid lts →
    t.Coinitial u → t.IsBwd → u.IsBwd → t ≠ u → Indep t u

/--
Independence is irreflexive.

Together with `IndepSymm` this is part of the *definition* of an LTS with
independence in [LPU2024] (Definition 3.10), not an extra axiom: an
independence relation is by definition irreflexive and symmetric.
-/
class IndepIrrefl (Indep : Transition State Label → Transition State Label → Prop) : Prop where
  /-- No transition is independent of itself. -/
  irrefl : ∀ {t : Transition State Label}, ¬ Indep t t

/-- Independence is symmetric. -/
class IndepSymm (Indep : Transition State Label → Transition State Label → Prop) : Prop where
  /-- Symmetry. -/
  symm : ∀ {t u : Transition State Label}, Indep t u → Indep u t

/--
**Coinitial label-generated independence.**  Independence depends only on the
labels of the transitions and on their being coinitial.

This is what yields reversal-compatibility of causal equivalence; LPU obtain
the corresponding property from PCI/IRE/IEC instead.  It holds outright in
footprint-based instances, where independence is a direction-blind condition
on labels.
-/
class CLG (Indep : Transition State Label → Transition State Label → Prop) : Prop where
  /-- Independence transports along equal labels. -/
  clg : ∀ {t u t₂ u₂ : Transition State Label}, Indep t u →
    t₂.lbl = t.lbl → u₂.lbl = u.lbl → t₂.Coinitial u₂ → Indep t₂ u₂

/-- One step of undoing. -/
def BStep (lts : LTS State Label) (p q : State) : Prop :=
  ∃ t : Transition State Label, t.Valid lts ∧ t.IsBwd ∧ t.src = p ∧ t.tgt = q

/-- A state with nothing left to undo. -/
def Origin (lts : LTS State Label) (p : State) : Prop := ∀ q, ¬ BStep lts p q

/-- **Well-foundedness.**  There is no infinite backward computation. -/
class WellFoundedBwd (lts : LTS State Label) : Prop where
  /-- Undoing terminates. -/
  wf : WellFounded (fun q p => BStep lts p q)

/--
A computable backward stepper: the step-back function of a reversible
debugger.  Any concrete reversible machine has one.
-/
class BStepDec (lts : LTS State Label) where
  /-- Decide whether an undo step exists, and produce it if so. -/
  step : ∀ p : State, PSum {q // BStep lts p q} (∀ q, ¬ BStep lts p q)

/--
Head-case analysis for `Relation.ReflTransGen`.

Mathlib's `Relation.ReflTransGen.cases_head` proves the same thing but pulls
in `Classical.choice`.  Since every other result in this development is
constructive, we reprove it rather than inherit the dependency.
-/
theorem reflTransGen_cases_head {α : Type _} {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) :
    a = b ∨ ∃ c, r a c ∧ Relation.ReflTransGen r c b := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hbc ih =>
    rcases ih with rfl | ⟨c, hac, hcb⟩
    · exact Or.inr ⟨_, hbc, .refl⟩
    · exact Or.inr ⟨c, hac, hcb.tail hbc⟩

variable {lts : LTS State Label}

theorem BStep.of_trans {t : Transition State Label} (hv : t.Valid lts) (hb : t.IsBwd) :
    BStep lts t.src t.tgt := ⟨t, hv, hb, rfl, rfl⟩

theorem Origin.not_bstep {p q : State} (h : Origin lts p) : ¬ BStep lts p q := h q

/--
Every state can be rewound to an origin.

This is the constructive form: `BStepDec` supplies the steps and
`WellFoundedBwd` guarantees the search stops.
-/
theorem exists_origin [WellFoundedBwd lts] [BStepDec lts] (p : State) :
    ∃ o, Relation.ReflTransGen (BStep lts) p o ∧ Origin lts o := by
  refine (WellFoundedBwd.wf (lts := lts)).induction
    (C := fun p => ∃ o, Relation.ReflTransGen (BStep lts) p o ∧ Origin lts o) p ?_
  intro p ih
  rcases BStepDec.step (lts := lts) p with ⟨q, hq⟩ | h
  · obtain ⟨o, hpath, ho⟩ := ih q hq
    exact ⟨o, .head hq hpath, ho⟩
  · exact ⟨p, .refl, h⟩

end Cslib.LTS
