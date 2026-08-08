/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Ladder

/-!
# Causal safety

**A transition cannot be undone until everything it caused has been undone.**

Formally (Definition 5.19(1) of [LPU2024], `CSci`): if `t₀` is still undoable
after a path `r`, then the *event* of `t₀` is coinitially independent of every
event that genuinely occurs in `r`.

## Why the event-level statement, and not the transition-level one

[LPU2024] also give a transition-level form (`CSι`, Definition 5.1), whose
conclusion is `Indep t₀ t` rather than `CIndep t₀ t`, and which needs `IRE` on
top of pre-reversibility.  **That form is unusable here.**  This development
assumes `IsIndep` — the axiom LPU call IC, "independence is coinitial"
(Definition 6.1) — and IC and IRE are jointly degenerate: IRE transports
independence along `SameEvent`, IC forces independent transitions to share a
source, and `SameEvent` does not preserve sources.  Together they collapse
every event that is independent of anything to a single source state.

`CSci` has no such problem, and is *weaker in hypotheses too*: Theorem 5.20
derives it from pre-reversibility alone, with no `IRE`.

The proof is the paper's.  The Ladder Lemma produces a *second* path from the
same source to the same target, all of whose steps are coinitially independent
of the event of `t₀`; causal consistency identifies it with `r`; and the event
count, being invariant, transports "occurs in `r`" to "occurs in the ladder
path", where independence is available by construction.

## References

* [I. Lanese, I. Phillips, I. Ulidowski, *An Axiomatic Theory for Reversible
  Computation*, ACM TOCL 25(2), 2024, Definition 5.1, Lemma 5.4,
  Theorem 5.5][LPU2024]
-/

universe u v

namespace Cslib.LTS

variable {State : Type u} {Label : Type v} {lts : LTS State Label}
variable {Indep : Transition State Label → Transition State Label → Prop}

/--
**Lemma 5.4.**  Coinitially independent events have independent occurrences —
any of them.
-/
theorem CIndep.toIndep [IndepSymm Indep] [IRE lts Indep] {a b : Transition State Label}
    (h : CIndep lts Indep a b) : Indep a b := by
  obtain ⟨t, u, -, -, ha, hb, -, hi⟩ := h
  have h₁ : Indep a u := IRE.ire ha hi
  have h₂ : Indep b a := IRE.ire hb (IndepSymm.symm h₁)
  exact IndepSymm.symm h₂

section Count

variable [DecidableRel (SameEvent lts Indep)]

/-- If an event occurs positively along a path, some step of the path is an occurrence. -/
theorem exists_mem_of_eventCount_pos {t₀ : Transition State Label}
    {s : List (Transition State Label)}
    (h : 0 < eventCount lts Indep t₀ s) : ∃ u ∈ s, SameEvent lts Indep u t₀ := by
  induction s with
  | nil => simp [eventCount] at h
  | cons x s ih =>
    by_cases hx : SameEvent lts Indep x t₀
    · exact ⟨x, List.mem_cons_self .., hx⟩
    · have hocc : occ lts Indep t₀ x ≤ 0 := by
        unfold occ; rw [if_neg hx]; split_ifs <;> omega
      rw [eventCount_cons] at h
      obtain ⟨u, hu, hsu⟩ := ih (by omega)
      exact ⟨u, List.mem_cons_of_mem _ hu, hsu⟩

/-- `t₀` is still undoable at `R`: some occurrence of its event arrives at `R`. -/
def Undoable (lts : LTS State Label)
    (Indep : Transition State Label → Transition State Label → Prop)
    (t₀ : Transition State Label) (R : State) : Prop :=
  ∃ s, s.Valid lts ∧ s.tgt = R ∧ SameEvent lts Indep t₀ s

/--
**Causal safety** (Theorem 5.20, `CSci`).  If `t₀` can still be undone after
`r`, then its event is coinitially independent of every event occurring in
`r`.

Only pre-reversibility is used.  The hypothesis `eventCount t₀ r = 0` of
Definition 5.19 is stated for faithfulness; the argument does not use it.
-/
theorem causal_safety [DecidableEq State] [DecidableEq Label]
    [SquareProperty lts Indep] [BTI lts Indep] [WellFoundedBwd lts] [BStepDec lts]
    [IsIndep lts Indep] [IndepSymm Indep] [CLG Indep] [CPI lts Indep]
    [EventRev lts Indep]
    {t₀ : Transition State Label} {R : State} {r : List (Transition State Label)}
    (hr : Chained lts t₀.tgt r R)
    (_hzero : eventCount lts Indep t₀ r = 0)
    (hundo : Undoable lts Indep t₀ R) :
    ∀ t ∈ r, 0 < eventCount lts Indep t r → CIndep lts Indep t₀ t := by
  obtain ⟨d, -, hdt, hsame⟩ := hundo
  -- The ladder path from `t₀.tgt` to `d.tgt = R`, independent of `t₀` throughout.
  obtain ⟨s, hs, hci⟩ := ladder (Indep := Indep) hsame
  rw [hdt] at hs
  -- Causal consistency identifies it with `r`.
  have hcc : CEq lts Indep t₀.tgt R r s := causal_consistency (Indep := Indep) hr hs
  intro t ht hpos
  -- The count is invariant, so the event of `t` occurs in the ladder path too.
  have hpos' : 0 < eventCount lts Indep t s := by
    rwa [← eventCount_of_cEq (Indep := Indep) hcc t]
  obtain ⟨u, hu, hut⟩ := exists_mem_of_eventCount_pos (Indep := Indep) hpos'
  exact (hci u hu).congrRight hut

/--
**Coinitial IRE** (Definition 5.21): coinitially independent events have
independent occurrences *whenever those occurrences are coinitial*.

This is the form of `IRE` that survives `IsIndep`, and it is what causal
liveness needs.
-/
class CIRE (lts : LTS State Label)
    (Indep : Transition State Label → Transition State Label → Prop) : Prop where
  /-- Coinitial occurrences of independent events are independent. -/
  cire : ∀ {t u : Transition State Label},
    CIndep lts Indep t u → t.Coinitial u → Indep t u

end Count

end Cslib.LTS
