/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Events

/-!
# Counting events along a path

`eventCount t₀ r` is the net number of times the event of `t₀` occurs in the
path `r`: occurrences of the event count `+1`, occurrences of the *reverse*
event count `-1`.  This is Definition 4.8 of [LPU2020], and it is the quantity
in terms of which causal safety and causal liveness are stated — "the event
has not (yet) been undone" is `eventCount = 0`.

## Main statement

`eventCount_of_cEq` is Lemma 4.9: **the count is invariant under causal
equivalence.**  Both generating moves preserve it for the same reason, once
one knows what they do to events:

* a *swap* replaces `t` by a transition of the same event, and likewise for
  `u`, so it permutes the contributions;
* a *cancellation* removes `t` together with `t.rev`, whose contributions are
  negatives of each other.

## `EventRev` is discharged, not assumed

The cancellation case needs `SameEvent t t' → SameEvent t.rev t'.rev`.  In
[LPU2020] this is implicit in the notation `[P, a, Q]` for reverse events
being well defined, and it is read off their *general* definition of events
(Definition 4.1), whose rotational symmetry is built in.

It used to be a named hypothesis here.  It no longer is: `sameEvent_rev`
derives it from `CPI` and `IndepSymm`, and the instance below means any
development that has those two gets it without asking.  The class is kept only
so that an instance which establishes it some other way can still be
supplied.

## References

* [I. Lanese, I. Phillips, I. Ulidowski, *An Axiomatic Approach to Reversible
  Computation*, FoSSaCS 2020, Definitions 4.1, 4.5, 4.8 and Lemma 4.9][LPU2020]
-/

universe u v

namespace Cslib.LTS

variable {State : Type u} {Label : Type v} {lts : LTS State Label}
variable {Indep : Transition State Label → Transition State Label → Prop}

/--
**Reversal maps events to reverse events.**

Derived from `CPI` by the instance below; see the module docstring.
-/
class EventRev (lts : LTS State Label)
    (Indep : Transition State Label → Transition State Label → Prop) : Prop where
  /-- Same event implies same reverse event. -/
  eventRev : ∀ {t t' : Transition State Label},
    SameEvent lts Indep t t' → SameEvent lts Indep t.rev t'.rev

/-- `CPI` and symmetry of independence already give reversal-compatibility. -/
instance eventRev_of_cpi [CPI lts Indep] [IndepSymm Indep] : EventRev lts Indep where
  eventRev := sameEvent_rev

section Count

variable [DecidableRel (SameEvent lts Indep)]

/--
The contribution of a single transition to the count of the event of `t₀`:
`+1` for the event, `-1` for the reverse event, `0` otherwise.
-/
def occ (lts : LTS State Label) (Indep : Transition State Label → Transition State Label → Prop)
    [DecidableRel (SameEvent lts Indep)] (t₀ x : Transition State Label) : ℤ :=
  (if SameEvent lts Indep x t₀ then 1 else 0) -
  (if SameEvent lts Indep x t₀.rev then 1 else 0)

/-- The net number of occurrences of the event of `t₀` along a path. -/
def eventCount (lts : LTS State Label)
    (Indep : Transition State Label → Transition State Label → Prop)
    [DecidableRel (SameEvent lts Indep)]
    (t₀ : Transition State Label) (r : List (Transition State Label)) : ℤ :=
  (r.map (occ lts Indep t₀)).sum

@[simp] theorem eventCount_nil (t₀ : Transition State Label) :
    eventCount lts Indep t₀ [] = 0 := rfl

@[simp] theorem eventCount_cons (t₀ x : Transition State Label)
    (r : List (Transition State Label)) :
    eventCount lts Indep t₀ (x :: r) = occ lts Indep t₀ x + eventCount lts Indep t₀ r := rfl

@[simp] theorem eventCount_append (t₀ : Transition State Label)
    (r₁ r₂ : List (Transition State Label)) :
    eventCount lts Indep t₀ (r₁ ++ r₂)
      = eventCount lts Indep t₀ r₁ + eventCount lts Indep t₀ r₂ := by
  simp [eventCount]

/-- Transitions of the same event contribute equally. -/
theorem occ_congr {x y : Transition State Label} (h : SameEvent lts Indep x y)
    (t₀ : Transition State Label) : occ lts Indep t₀ x = occ lts Indep t₀ y := by
  unfold occ
  have h₁ : SameEvent lts Indep x t₀ ↔ SameEvent lts Indep y t₀ :=
    ⟨fun hx => (h.symm).trans hx, fun hy => h.trans hy⟩
  have h₂ : SameEvent lts Indep x t₀.rev ↔ SameEvent lts Indep y t₀.rev :=
    ⟨fun hx => (h.symm).trans hx, fun hy => h.trans hy⟩
  simp only [h₁, h₂]

/-- A transition and its reversal contribute opposite amounts. -/
theorem occ_rev [EventRev lts Indep] (t₀ x : Transition State Label) :
    occ lts Indep t₀ x.rev = - occ lts Indep t₀ x := by
  have key : ∀ a b : Transition State Label,
      SameEvent lts Indep a.rev b ↔ SameEvent lts Indep a b.rev := by
    intro a b
    constructor
    · intro h; simpa using EventRev.eventRev h
    · intro h; simpa using EventRev.eventRev h
  have h₁ : SameEvent lts Indep x.rev t₀ ↔ SameEvent lts Indep x t₀.rev := key x t₀
  have h₂ : SameEvent lts Indep x.rev t₀.rev ↔ SameEvent lts Indep x t₀ := by
    rw [key x t₀.rev]; simp
  unfold occ
  simp only [h₁, h₂]
  split_ifs <;> omega

/--
**Lemma 4.9.**  The count of an event is invariant under causal equivalence.
-/
theorem eventCount_of_cEq [IndepSymm Indep] [EventRev lts Indep]
    {p q : State} {l₁ l₂ : List (Transition State Label)}
    (h : CEq lts Indep p q l₁ l₂) (t₀ : Transition State Label) :
    eventCount lts Indep t₀ l₁ = eventCount lts Indep t₀ l₂ := by
  induction h with
  | @swap p q t u u' t' hind hu'l hu'd ht'l ht'd hcL hcR =>
    obtain ⟨hts, htv, hu's, hu'v, hu't⟩ := hcL
    obtain ⟨hus, huv, ht's, ht'v, ht't⟩ := hcR
    have d : Diamond lts t u u' t' :=
      { validT := htv, validU := huv, validU' := hu'v, validT' := ht'v,
        coinitial := hus.trans hts.symm, srcU' := hu's, srcT' := ht's,
        cofinal := hu't.trans ht't.symm,
        lblU' := hu'l, dirU' := hu'd, lblT' := ht'l, dirT' := ht'd }
    have e₁ : SameEvent lts Indep t t' := SameEvent.of_diamond d hind
    have e₂ : SameEvent lts Indep u u' :=
      SameEvent.of_diamond d.swap (IndepSymm.symm hind)
    simp only [eventCount_cons, eventCount_nil, occ_congr e₁, occ_congr e₂]
    omega
  | @cancel p t hv hs =>
    simp only [eventCount_cons, eventCount_nil, occ_rev]
    omega
  | ctx _ _ _ ih => simp [ih]
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Count

end Cslib.LTS
