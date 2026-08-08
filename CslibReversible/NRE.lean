/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.CausalSafety

/-!
# Towards no repeated events

Causal *liveness* needs one more structural fact than causal safety: along a
path out of an origin, a forward event happens at most once (`NRE`,
Definition 4.18 of [LPU2024]).  This file assembles what that rests on.

* `exists_forward_of_origin` — out of an origin the Parabolic Lemma has no
  backward half to give, so every path is causally equivalent to a
  forward-only one.
* `eventCount_nonneg_of_forward` — a forward-only path can never decrease the
  count of a forward event, because occurrences of the *reverse* event are
  backward transitions and there are none.
* `eventCount_eq_zero_of_sameEvent` — Lemma 4.20: between two occurrences of
  the same event, that event's net count is zero.  This is the Ladder Lemma
  plus the observation that the ladder's rungs all carry a different label.

## No hypotheses left here

Backward label determinism and Proposition 4.17 used to be stated as classes.
Both are now theorems — `bld_of_sp_bti_cpi` in `CslibReversible.Events` and
`lbl_ne_of_cIndep` in `CslibReversible.Ladder`.

## References

* [I. Lanese, I. Phillips, I. Ulidowski, *An Axiomatic Theory for Reversible
  Computation*, ACM TOCL 25(2), 2024, Definitions 4.5 and 4.18,
  Propositions 4.6, 4.17 and 4.21, Lemma 4.20][LPU2024]
-/

universe u v

namespace Cslib.LTS

variable {State : Type u} {Label : Type v} {lts : LTS State Label}
variable {Indep : Transition State Label → Transition State Label → Prop}

/--
Out of an origin, every path is causally equivalent to a forward-only path:
the Parabolic Lemma's backward half has nowhere to go.
-/
theorem exists_forward_of_origin [DecidableEq State] [DecidableEq Label]
    [SquareProperty lts Indep] [BTI lts Indep]
    {o q : State} {l : List (Transition State Label)}
    (ho : Origin lts o) (h : Chained lts o l q) :
    ∃ f, (∀ x ∈ f, x.IsFwd) ∧ CEq lts Indep o q l f := by
  obtain ⟨b, f, hb, hf, hq⟩ := parabolic (Indep := Indep) h
  rcases b with _ | ⟨t, b'⟩
  · exact ⟨f, hf, by simpa using hq⟩
  · exfalso
    obtain ⟨hts, htv, -⟩ := hq.chained_right
    exact ho t.tgt ⟨t, htv, hb t (by simp), hts, rfl⟩

section Count

variable [DecidableRel (SameEvent lts Indep)]

/-- A forward-only path never decreases the count of a forward event. -/
theorem eventCount_nonneg_of_forward {t₀ : Transition State Label} (h₀ : t₀.IsFwd)
    {f : List (Transition State Label)} (hf : ∀ x ∈ f, x.IsFwd) :
    0 ≤ eventCount lts Indep t₀ f := by
  induction f with
  | nil => simp
  | cons x f ih =>
    have hx : x.dir = Dir.fwd := hf x (by simp)
    have hne : ¬ SameEvent lts Indep x t₀.rev := by
      intro hs
      have hd := hs.dir_eq
      rw [hx] at hd
      simp [Transition.rev, Dir.rev, show t₀.dir = Dir.fwd from h₀] at hd
    have hocc : 0 ≤ occ lts Indep t₀ x := by
      unfold occ; rw [if_neg hne]; split_ifs <;> omega
    have hrest := ih fun y hy => hf y (by simp [hy])
    rw [eventCount_cons]; omega

/-- A path all of whose labels differ from that of `t₀` does not move its count. -/
theorem eventCount_eq_zero_of_lbl_ne {t₀ : Transition State Label}
    {s : List (Transition State Label)}
    (h : ∀ u ∈ s, u.lbl ≠ t₀.lbl) : eventCount lts Indep t₀ s = 0 := by
  induction s with
  | nil => simp
  | cons x s ih =>
    have hx : x.lbl ≠ t₀.lbl := h x (by simp)
    have h₁ : ¬ SameEvent lts Indep x t₀ := fun hs => hx hs.lbl_eq
    have h₂ : ¬ SameEvent lts Indep x t₀.rev := fun hs => hx (by simpa using hs.lbl_eq)
    have hocc : occ lts Indep t₀ x = 0 := by
      unfold occ; rw [if_neg h₁, if_neg h₂]; omega
    have hrest := ih fun y hy => h y (by simp [hy])
    rw [eventCount_cons, hocc, hrest]
    omega

/--
**Lemma 4.20.**  Between two occurrences of the same event, the net count of
that event along any connecting path is zero.

The Ladder Lemma supplies a connecting path whose every step is coinitially
independent of the event, hence — by `CIndepLabel` — carries a different
label; such a path moves no count.  Causal consistency transports the
conclusion to the given path.
-/
theorem eventCount_eq_zero_of_sameEvent [DecidableEq State] [DecidableEq Label]
    [SquareProperty lts Indep] [BTI lts Indep] [WellFoundedBwd lts] [BStepDec lts]
    [IsIndep lts Indep] [IndepSymm Indep] [CLG Indep] [CPI lts Indep]
    [EventRev lts Indep] [IndepIrrefl Indep]
    {t t' : Transition State Label} (h : SameEvent lts Indep t t')
    {r : List (Transition State Label)} (hr : Chained lts t.tgt r t'.tgt) :
    eventCount lts Indep t r = 0 := by
  obtain ⟨s, hs, hci⟩ := ladder (Indep := Indep) h
  have hcc : CEq lts Indep t.tgt t'.tgt r s := causal_consistency (Indep := Indep) hr hs
  rw [eventCount_of_cEq (Indep := Indep) hcc t]
  exact eventCount_eq_zero_of_lbl_ne fun u hu =>
    (lbl_ne_of_cIndep (hci u hu)).symm

/-- The count only depends on the event of the base point. -/
theorem eventCount_congr_base [EventRev lts Indep] {t₀ t₁ : Transition State Label}
    (h : SameEvent lts Indep t₀ t₁) (l : List (Transition State Label)) :
    eventCount lts Indep t₀ l = eventCount lts Indep t₁ l := by
  have hocc : ∀ x, occ lts Indep t₀ x = occ lts Indep t₁ x := by
    intro x
    have e₁ : SameEvent lts Indep x t₀ ↔ SameEvent lts Indep x t₁ :=
      ⟨fun hx => hx.trans h, fun hx => hx.trans h.symm⟩
    have e₂ : SameEvent lts Indep x t₀.rev ↔ SameEvent lts Indep x t₁.rev :=
      ⟨fun hx => hx.trans (EventRev.eventRev h),
       fun hx => hx.trans (EventRev.eventRev h.symm)⟩
    unfold occ; simp only [e₁, e₂]
  unfold eventCount
  congr 1
  exact List.map_congr_left fun x _ => hocc x

/--
**No repeated events** (Definition 4.18, Proposition 4.21).  A forward event
occurs at most once along a forward-only path.

The argument is the paper's.  If it occurred twice, Lemma 4.20 would force the
count between the two occurrences to be zero, but that stretch is forward-only
and already contains the second occurrence, so its count is at least one.
-/
theorem nre [DecidableEq State] [DecidableEq Label]
    [SquareProperty lts Indep] [BTI lts Indep] [WellFoundedBwd lts] [BStepDec lts]
    [IsIndep lts Indep] [IndepSymm Indep] [CLG Indep] [CPI lts Indep]
    [EventRev lts Indep] [IndepIrrefl Indep]
    {t₀ : Transition State Label} (h₀ : t₀.IsFwd)
    {p q : State} {f : List (Transition State Label)}
    (hf : ∀ x ∈ f, x.IsFwd) (hc : Chained lts p f q) :
    eventCount lts Indep t₀ f ≤ 1 := by
  induction f generalizing p with
  | nil => simp
  | cons x f' ih =>
    obtain ⟨hxs, hxv, hc'⟩ := hc
    have hxf : x.dir = Dir.fwd := hf x (by simp)
    have hf' : ∀ y ∈ f', y.IsFwd := fun y hy => hf y (by simp [hy])
    have hnrev : ¬ SameEvent lts Indep x t₀.rev := by
      intro hs
      have hd := hs.dir_eq
      rw [hxf] at hd
      simp [Transition.rev, Dir.rev, show t₀.dir = Dir.fwd from h₀] at hd
    by_cases hxe : SameEvent lts Indep x t₀
    · -- `x` is an occurrence; there can be no second one.
      have hocc : occ lts Indep t₀ x = 1 := by
        unfold occ; rw [if_pos hxe, if_neg hnrev]; omega
      have hzero : eventCount lts Indep t₀ f' ≤ 0 := by
        by_contra hcon
        have hpos : 0 < eventCount lts Indep t₀ f' := by omega
        obtain ⟨y, hy, hye⟩ := exists_mem_of_eventCount_pos (Indep := Indep) hpos
        obtain ⟨B, C, rfl⟩ := List.append_of_mem hy
        obtain ⟨m, hB, hyC⟩ := Chained.split hc'
        obtain ⟨hys, hyv, -⟩ := hyC
        have hxy : SameEvent lts Indep x y := hxe.trans hye.symm
        have hpath : Chained lts x.tgt (B ++ [y]) y.tgt := hB.append ⟨hys, hyv, rfl⟩
        have hz := eventCount_eq_zero_of_sameEvent (Indep := Indep) hxy hpath
        have hyfwd : y.dir = Dir.fwd := hf' y (by simp)
        have hynr : ¬ SameEvent lts Indep y x.rev := by
          intro hs
          have hd := hs.dir_eq
          rw [hyfwd] at hd
          simp [Transition.rev, Dir.rev, hxf] at hd
        have hy1 : eventCount lts Indep x [y] = 1 := by
          simp only [eventCount_cons, eventCount_nil, occ]
          rw [if_pos hxy.symm, if_neg hynr]; omega
        have hBnn : 0 ≤ eventCount lts Indep x B :=
          eventCount_nonneg_of_forward hxf fun z hz' => hf' z (by simp [hz'])
        rw [eventCount_append, hy1] at hz
        omega
      rw [eventCount_cons, hocc]; omega
    · have hocc : occ lts Indep t₀ x = 0 := by
        unfold occ; rw [if_neg hxe, if_neg hnrev]; omega
      have := ih hf' hc'
      rw [eventCount_cons, hocc]; omega

end Count

end Cslib.LTS
