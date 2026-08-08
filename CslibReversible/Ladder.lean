/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.EventCount

/-!
# Coinitially independent events, and the Ladder Lemma

Causal safety and liveness are stated about *events*, so independence has to
be lifted from transitions to events.  `CIndep` does that (Definition 4.14 of
[LPU2024]), and the **Ladder Lemma** (Lemma 4.19) is the structural result
that makes it usable:

> if `t` and `t'` are occurrences of the same event, then there is a path from
> the target of `t` to the target of `t'` every step of which is coinitially
> independent of that event.

The name is the paper's: the derivation of `t ∼ t'` is a ladder of diamonds,
and the path is read off its rungs.  The proof here is exactly that — an
induction on how `SameEvent` was generated, where the base case reads off a
single diamond and the symmetry case reverses the path.

## References

* [I. Lanese, I. Phillips, I. Ulidowski, *An Axiomatic Theory for Reversible
  Computation*, ACM TOCL 25(2), 2024, Definition 4.14, Lemmas 4.15 and
  4.19][LPU2024]
-/

universe u v

namespace Cslib.LTS

variable {State : Type u} {Label : Type v} {lts : LTS State Label}
variable {Indep : Transition State Label → Transition State Label → Prop}

/--
**Coinitially independent events.**  Two events are coinitially independent
when they have coinitial independent occurrences.
-/
def CIndep (lts : LTS State Label)
    (Indep : Transition State Label → Transition State Label → Prop)
    (a b : Transition State Label) : Prop :=
  ∃ t u, t.Valid lts ∧ u.Valid lts ∧
    SameEvent lts Indep a t ∧ SameEvent lts Indep b u ∧ t.Coinitial u ∧ Indep t u

/-- `CIndep` depends only on the event of its first argument. -/
theorem CIndep.congrLeft {a a' b : Transition State Label}
    (h : SameEvent lts Indep a a') (hc : CIndep lts Indep a b) : CIndep lts Indep a' b := by
  obtain ⟨t, u, htv, huv, ha, hb, hco, hi⟩ := hc
  exact ⟨t, u, htv, huv, h.symm.trans ha, hb, hco, hi⟩

/-- `CIndep` depends only on the event of its second argument. -/
theorem CIndep.congrRight {a b b' : Transition State Label}
    (h : SameEvent lts Indep b b') (hc : CIndep lts Indep a b) : CIndep lts Indep a b' := by
  obtain ⟨t, u, htv, huv, ha, hb, hco, hi⟩ := hc
  exact ⟨t, u, htv, huv, ha, h.symm.trans hb, hco, hi⟩

/--
**Lemma 4.15.**  Coinitial independence of events is settled by the forward
events: if `a` is independent of `b` then it is independent of the reverse of
`b` as well.

The proof completes the square with `SquareProperty` and then walks the
independence one corner round it with `CPI`.
-/
theorem CIndep.revRight [SquareProperty lts Indep] [IsIndep lts Indep]
    [IndepSymm Indep] [CPI lts Indep] [EventRev lts Indep]
    {a b : Transition State Label} (h : CIndep lts Indep a b) : CIndep lts Indep a b.rev := by
  obtain ⟨t, u, htv, huv, ha, hb, hco, hi⟩ := h
  obtain ⟨u', t', d⟩ := Diamond.ofSquare (Indep := Indep) htv huv hi
  -- Walk the independence from the corner `P` to the corner `R`.
  have hi' : Indep t' u.rev := CPI.cpi d.swap (IndepSymm.symm hi)
  refine ⟨t', u.rev, d.validT', Transition.rev_valid huv, ?_, ?_, ?_, hi'⟩
  · exact ha.trans (SameEvent.of_diamond d hi)
  · exact EventRev.eventRev hb
  · simpa [Transition.Coinitial] using d.srcT'

/--
**Coinitially independent events carry different labels** (Proposition 4.17).

Here labels and directions are separate fields of a transition, so the paper's
`und(α) ≠ und(β)` is simply an inequality of labels.

The paper routes this through the non-degeneracy of independent diamonds and
hence through Unique Transition.  Neither is needed here: a transition *is* its
four fields, so two coinitial transitions with the same label and direction can
only differ in their target, and that is exactly the distinctness `BLD` needs.
The three cases are:

* both backward — `BLD` collapses them, contradicting irreflexivity;
* both forward — `SquareProperty` closes the square, and `BLD` applied to the
  two reversed far edges collapses the targets, again contradicting
  irreflexivity;
* one of each — the labels are then mutually inverse, so `not_indep_of_rev_lbl`
  applies directly.
-/
theorem lbl_ne_of_cIndep [DecidableEq State] [DecidableEq Label]
    [SquareProperty lts Indep] [BTI lts Indep] [CPI lts Indep]
    [IndepSymm Indep] [IndepIrrefl Indep]
    {a b : Transition State Label} (h : CIndep lts Indep a b) : a.lbl ≠ b.lbl := by
  obtain ⟨t, u, htv, huv, ha, hb, hco, hi⟩ := h
  intro hab
  have hlbl : t.lbl = u.lbl := ha.lbl_eq.symm.trans (hab.trans hb.lbl_eq)
  have hne : t ≠ u := fun he => IndepIrrefl.irrefl (he ▸ hi)
  cases htd : t.dir <;> cases hud : u.dir
  · -- Both forward: reverse the far edges of the square and apply `BLD`.
    obtain ⟨w, hw₁, hw₂⟩ := SquareProperty.square (Indep := Indep) htv huv hi
    have hbwd₁ : (Transition.mk t.tgt u.lbl u.dir w).rev.IsBwd := by
      simp [Transition.IsBwd, Transition.rev, hud, Dir.rev]
    have hbwd₂ : (Transition.mk u.tgt t.lbl t.dir w).rev.IsBwd := by
      simp [Transition.IsBwd, Transition.rev, htd, Dir.rev]
    have heq := bld_of_sp_bti_cpi (Indep := Indep)
      (Transition.rev_valid hw₁) (Transition.rev_valid hw₂) hbwd₁ hbwd₂ rfl
      (by simpa using hlbl.symm)
    have htgt : t.tgt = u.tgt := by simpa using congrArg Transition.tgt heq
    exact hne (Transition.ext hco hlbl (htd.trans hud.symm) htgt)
  · -- Mutually inverse labels.
    exact not_indep_of_rev_lbl (Indep := Indep) htv huv hco.symm hlbl.symm
      (by rw [hud, htd]; rfl) hi
  · exact not_indep_of_rev_lbl (Indep := Indep) huv htv hco hlbl
      (by rw [hud, htd]; rfl) (IndepSymm.symm hi)
  · -- Both backward: `BLD` collapses them.
    exact hne (bld_of_sp_bti_cpi (Indep := Indep) htv huv htd hud hco hlbl)

/--
**The Ladder Lemma.**  Two occurrences of the same event are joined by a path
every step of which is coinitially independent of that event.
-/
theorem ladder [SquareProperty lts Indep] [IsIndep lts Indep]
    [IndepSymm Indep] [CPI lts Indep] [EventRev lts Indep]
    {t t' : Transition State Label} (h : SameEvent lts Indep t t') :
    ∃ s, Chained lts t.tgt s t'.tgt ∧ ∀ u ∈ s, CIndep lts Indep t u := by
  induction h with
  | rel x y hxy =>
    -- One rung of the ladder: read the path off the far side of the diamond.
    obtain ⟨u, u', d, hi⟩ := hxy
    refine ⟨[u'], ⟨d.srcU', d.validU', d.cofinal⟩, ?_⟩
    intro z hz
    rcases List.mem_singleton.mp hz with rfl
    exact ⟨x, u, d.validT, d.validU, SameEvent.refl _,
      (SameEvent.of_diamond d.swap (IndepSymm.symm hi)).symm, d.coinitial.symm, hi⟩
  | refl x => exact ⟨[], rfl, by simp⟩
  | symm x y hxy ih =>
    obtain ⟨s, hs, hci⟩ := ih
    refine ⟨revPath s, hs.revPath, ?_⟩
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_revPath.mp hz
    exact ((hci w hw).congrLeft hxy).revRight
  | trans x y z hxy _ ih₁ ih₂ =>
    obtain ⟨s₁, h₁, c₁⟩ := ih₁
    obtain ⟨s₂, h₂, c₂⟩ := ih₂
    refine ⟨s₁ ++ s₂, h₁.append h₂, ?_⟩
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact c₁ w hw
    · exact (c₂ w hw).congrLeft hxy.symm

end Cslib.LTS
