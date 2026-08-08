/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.NRE

/-!
# Towards causal liveness

Causal liveness is the converse of causal safety: *if* an event is independent
of everything that has happened since, it *can* be undone.  Where safety needs
only pre-reversibility, liveness needs one more axiom, and Theorem 5.29 of
[LPU2024] identifies exactly which: `BFCIRE`.

The engine is `pushEvent` below.  Undoing `t₀` after a path means producing an
occurrence of its event that *ends* where the path ends; `pushEvent` produces
it, by commuting a transition rightwards past everything its event is
independent of.  Each commutation replaces the transition by another
occurrence of the same event, and `CIndep.congrLeft` carries the independence
hypothesis along — which is why the induction closes.

## References

* [I. Lanese, I. Phillips, I. Ulidowski, *An Axiomatic Theory for Reversible
  Computation*, ACM TOCL 25(2), 2024, Definitions 5.19 and 5.28,
  Theorem 5.29][LPU2024]
-/

universe u v

namespace Cslib.LTS

variable {State : Type u} {Label : Type v} {lts : LTS State Label}
variable {Indep : Transition State Label → Transition State Label → Prop}

/--
**Backward-Forward CIRE** (Definition 5.28).  `CIRE` specialised to the case
where the coinitial pair consists of the reversal of a forward transition and
the forward transition that follows it.

This is the axiom Theorem 5.29 shows to be *necessary and sufficient* for
causal liveness — unlike `IRE`, which is sufficient but not necessary (and, in
the presence of `IsIndep`, degenerate).
-/
class BFCIRE (lts : LTS State Label)
    (Indep : Transition State Label → Transition State Label → Prop) : Prop where
  /-- Consecutive forward transitions of independent events can be commuted. -/
  bfcire : ∀ {t u : Transition State Label}, t.IsFwd → u.IsFwd → u.src = t.tgt →
    CIndep lts Indep t u → Indep t.rev u

/--
Commuting a forward transition past the next one, when the reversal of the
first is independent of the second.

The result `t'` is another occurrence of the same event as `t`, which is what
makes this usable as an induction step.
-/
theorem swap_fwd [SquareProperty lts Indep] [EventRev lts Indep]
    {t u : Transition State Label} {p q : State}
    (hc : Chained lts p [t, u] q) (hft : t.IsFwd) (hfu : u.IsFwd) (hind : Indep t.rev u) :
    ∃ u' t', u'.IsFwd ∧ t'.IsFwd ∧ SameEvent lts Indep t t' ∧
      CEq lts Indep p q [t, u] [u', t'] := by
  obtain ⟨hts, htv, hus, huv, hut⟩ := hc
  have hft' : t.dir = Dir.fwd := hft
  have hrv : t.rev.Valid lts := Transition.rev_valid htv
  obtain ⟨w, hw₁, hw₂⟩ := SquareProperty.square (Indep := Indep) hrv huv hind
  set u' : Transition State Label := Transition.mk t.src u.lbl u.dir w
  set tr : Transition State Label := Transition.mk u.tgt t.lbl t.dir.rev w
  have hu'v : u'.Valid lts := hw₁
  have htrv : tr.Valid lts := hw₂
  have ht'v : tr.rev.Valid lts := Transition.rev_valid htrv
  -- The diamond, and the paths the causal-equivalence chain needs.
  have cP : Chained lts p [t] t.tgt := ⟨hts, htv, rfl⟩
  have cU' : Chained lts p [u'] w := ⟨hts, hu'v, rfl⟩
  have cT' : Chained lts w [tr.rev] q := ⟨rfl, ht'v, by simpa using hut⟩
  have cL : Chained lts t.tgt [t.rev, u'] w := ⟨rfl, hrv, ⟨rfl, hu'v, rfl⟩⟩
  have cR : Chained lts t.tgt [u, tr] w := ⟨hus, huv, ⟨rfl, htrv, rfl⟩⟩
  have cTU : Chained lts p [t, u] q := ⟨hts, htv, hus, huv, hut⟩
  have d : Diamond lts t.rev u u' tr :=
    { validT := hrv, validU := huv, validU' := hu'v, validT' := htrv,
      coinitial := hus, srcU' := rfl, srcT' := rfl, cofinal := rfl,
      lblU' := rfl, dirU' := rfl, lblT' := rfl, dirT' := rfl }
  have c1 : CEq lts Indep t.tgt w [t.rev, u'] [u, tr] :=
    CEq.swap hind rfl rfl rfl rfl cL cR
  have c2 : CEq lts Indep p w [t, t.rev, u'] [u'] := by
    simpa using (CEq.cancel (Indep := Indep) htv hts).appendRight cU'
  have c3 : CEq lts Indep p w [t, t.rev, u'] [t, u, tr] := by
    simpa using CEq.appendLeft cP c1
  have c4 : CEq lts Indep p w [u'] [t, u, tr] := c2.symm.trans c3
  have c5 : CEq lts Indep p q [u', tr.rev] [t, u, tr, tr.rev] := by
    simpa using c4.appendRight cT'
  have c6 : CEq lts Indep p q [t, u, tr, tr.rev] [t, u] := by
    simpa using CEq.appendLeft cTU
      (CEq.cancel (Indep := Indep) htrv (by simpa using hut))
  -- `tr` is the reverse of an occurrence of the event of `t`.
  have hsame : SameEvent lts Indep t tr.rev := by
    have := SameEvent.of_diamond d hind
    simpa using EventRev.eventRev this
  have htrd : tr.dir = t.dir.rev := rfl
  refine ⟨u', tr.rev, hfu, ?_, hsame, (c5.trans c6).symm⟩
  simp [Transition.IsFwd, htrd, hft']

/--
**Commuting an event to the end of a path.**

If every step of `f` belongs to an event coinitially independent of the event
of `t`, then `t` can be moved past all of them.  What comes out at the far end
is a different transition — but an occurrence of the same event, arriving
exactly where `f` arrived.

This is the step the paper describes as "commuting `t'₀` with all such
transitions using SP and BFCIRE".  The induction closes because each
commutation preserves the event, so `CIndep.congrLeft` re-establishes the
hypothesis for the next step.
-/
theorem pushEvent [SquareProperty lts Indep] [EventRev lts Indep] [BFCIRE lts Indep]
    {t : Transition State Label} {f : List (Transition State Label)} {p q : State}
    (hft : t.IsFwd) (hf : ∀ x ∈ f, x.IsFwd)
    (hc : Chained lts p (t :: f) q)
    (hci : ∀ x ∈ f, CIndep lts Indep t x) :
    ∃ f' t', (∀ x ∈ f', x.IsFwd) ∧ SameEvent lts Indep t t' ∧ t'.IsFwd ∧
      CEq lts Indep p q (t :: f) (f' ++ [t']) := by
  induction f generalizing t p with
  | nil =>
    exact ⟨[], t, by simp, SameEvent.refl t, hft, by simpa using CEq.refl hc⟩
  | cons x f'' ih =>
    obtain ⟨hts, htv, hxs, hxv, hc''⟩ := hc
    have hfx : x.IsFwd := hf x (by simp)
    have hf'' : ∀ y ∈ f'', y.IsFwd := fun y hy => hf y (by simp [hy])
    have hind : Indep t.rev x :=
      BFCIRE.bfcire hft hfx hxs (hci x (by simp))
    have hcTU : Chained lts p [t, x] x.tgt := ⟨hts, htv, hxs, hxv, rfl⟩
    obtain ⟨u', t'', hfu', hft'', hsame, hsw⟩ :=
      swap_fwd (Indep := Indep) hcTU hft hfx hind
    obtain ⟨hu's, hu'v, ht''s, ht''v, ht''t⟩ := hsw.chained_right
    have hchain : Chained lts u'.tgt (t'' :: f'') q :=
      ⟨ht''s, ht''v, by rw [ht''t]; exact hc''⟩
    have hci'' : ∀ y ∈ f'', CIndep lts Indep t'' y :=
      fun y hy => (hci y (by simp [hy])).congrLeft hsame
    obtain ⟨g, t''', hg, hsame2, hft''', hcq⟩ := ih hft'' hf'' hchain hci''
    refine ⟨u' :: g, t''', ?_, hsame.trans hsame2, hft''', ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hfu'
      · exact hg y hy
    · have s1 : CEq lts Indep p q (t :: x :: f'') (u' :: t'' :: f'') := by
        simpa using hsw.appendRight (post := f'') hc''
      have s2 : CEq lts Indep p q (u' :: t'' :: f'') (u' :: (g ++ [t'''])) := by
        simpa using CEq.appendLeft (pre := [u']) ⟨hu's, hu'v, rfl⟩ hcq
      simpa using s1.trans s2

section Count

variable [DecidableRel (SameEvent lts Indep)]

/-- A forward transition is an occurrence of its own event and of nothing reverse. -/
theorem occ_self {t₀ : Transition State Label} (h₀ : t₀.IsFwd) :
    occ lts Indep t₀ t₀ = 1 := by
  have hne : ¬ SameEvent lts Indep t₀ t₀.rev := by
    intro hs
    have hd := hs.dir_eq
    simp [Transition.rev, Dir.rev, show t₀.dir = Dir.fwd from h₀] at hd
  unfold occ; rw [if_pos (SameEvent.refl t₀), if_neg hne]; omega

/-- A backward-only path never increases the count of a forward event. -/
theorem eventCount_nonpos_of_backward {t₀ : Transition State Label} (h₀ : t₀.IsFwd)
    {b : List (Transition State Label)} (hb : ∀ x ∈ b, x.IsBwd) :
    eventCount lts Indep t₀ b ≤ 0 := by
  induction b with
  | nil => simp
  | cons x b ih =>
    have hx : x.dir = Dir.bwd := hb x (by simp)
    have hne : ¬ SameEvent lts Indep x t₀ := by
      intro hs
      have hd := hs.dir_eq
      rw [hx] at hd
      simp [show t₀.dir = Dir.fwd from h₀] at hd
    have hocc : occ lts Indep t₀ x ≤ 0 := by
      unfold occ; rw [if_neg hne]; split_ifs <;> omega
    have := ih fun y hy => hb y (by simp [hy])
    rw [eventCount_cons]; omega

/-- A forward path containing an occurrence has a positive count for it. -/
theorem eventCount_pos_of_mem {x : Transition State Label}
    {f : List (Transition State Label)} (hf : ∀ y ∈ f, y.IsFwd) (hx : x ∈ f) (hxf : x.IsFwd) :
    0 < eventCount lts Indep x f := by
  induction f with
  | nil => cases hx
  | cons y f ih =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · have h1 : occ lts Indep x x = 1 := occ_self hxf
      have hrest : 0 ≤ eventCount lts Indep x f :=
        eventCount_nonneg_of_forward hxf fun z hz => hf z (by simp [hz])
      rw [eventCount_cons, h1]; omega
    · have hyf : y.IsFwd := hf y (by simp)
      have hnrev : ¬ SameEvent lts Indep y x.rev := by
        intro hs
        have hd := hs.dir_eq
        rw [show y.dir = Dir.fwd from hyf] at hd
        simp [Transition.rev, Dir.rev, show x.dir = Dir.fwd from hxf] at hd
      have hy0 : 0 ≤ occ lts Indep x y := by
        unfold occ; rw [if_neg hnrev]; split_ifs <;> omega
      have := ih (fun z hz => hf z (by simp [hz])) hx'
      rw [eventCount_cons]; omega

/-- A nonzero count exposes an occurrence of the event or of its reverse. -/
theorem exists_mem_of_eventCount_ne_zero {t₀ : Transition State Label}
    {s : List (Transition State Label)} (h : eventCount lts Indep t₀ s ≠ 0) :
    ∃ u ∈ s, SameEvent lts Indep u t₀ ∨ SameEvent lts Indep u t₀.rev := by
  induction s with
  | nil => simp at h
  | cons x s ih =>
    by_cases hx : SameEvent lts Indep x t₀
    · exact ⟨x, by simp, Or.inl hx⟩
    · by_cases hx' : SameEvent lts Indep x t₀.rev
      · exact ⟨x, by simp, Or.inr hx'⟩
      · have hocc : occ lts Indep t₀ x = 0 := by
          unfold occ; rw [if_neg hx, if_neg hx']; omega
        rw [eventCount_cons, hocc] at h
        obtain ⟨u, hu, hcase⟩ := ih (by omega)
        exact ⟨u, by simp [hu], hcase⟩

/--
**Causal liveness** (Theorem 5.29, `CLci`).  If the event of `t₀` is
coinitially independent of everything that has happened since, then `t₀` can
be undone: some occurrence of its event arrives exactly where the path
arrived.

This is the converse of `causal_safety`, and unlike it, it needs an axiom
beyond pre-reversibility — `BFCIRE`, which Theorem 5.29 shows to be exactly
the right one.
-/
theorem causal_liveness [DecidableEq State] [DecidableEq Label]
    [SquareProperty lts Indep] [BTI lts Indep] [WellFoundedBwd lts] [BStepDec lts]
    [IsIndep lts Indep] [IndepSymm Indep] [CLG Indep] [CPI lts Indep]
    [EventRev lts Indep] [IndepIrrefl Indep] [BFCIRE lts Indep]
    {t₀ : Transition State Label} {R : State} {r : List (Transition State Label)}
    (h₀ : t₀.IsFwd) (ht₀v : t₀.Valid lts)
    (hr : Chained lts t₀.tgt r R)
    (hzero : eventCount lts Indep t₀ r = 0)
    (hyp : ∀ x ∈ r, 0 < eventCount lts Indep x r → CIndep lts Indep t₀ x) :
    Undoable lts Indep t₀ R := by
  -- Put `t₀ :: r` in parabolic normal form.
  have hchain : Chained lts t₀.src (t₀ :: r) R := ⟨rfl, ht₀v, hr⟩
  obtain ⟨b, f, hb, hf, hpar⟩ := parabolic (Indep := Indep) hchain
  -- The event of `t₀` occurs exactly once, and only the forward half can host it.
  have hcount : eventCount lts Indep t₀ (b ++ f) = 1 := by
    rw [← eventCount_of_cEq (Indep := Indep) hpar t₀, eventCount_cons, occ_self h₀, hzero]
    omega
  have hbn : eventCount lts Indep t₀ b ≤ 0 := eventCount_nonpos_of_backward h₀ hb
  have hfp : 0 < eventCount lts Indep t₀ f := by
    rw [eventCount_append] at hcount; omega
  obtain ⟨t', ht'f, ht'e⟩ := exists_mem_of_eventCount_pos (Indep := Indep) hfp
  obtain ⟨A, f', rfl⟩ := List.append_of_mem ht'f
  -- Decompose the normal form around that occurrence.
  obtain ⟨T, -, hfc⟩ := Chained.split hpar.chained_right
  obtain ⟨m, -, hrest⟩ := Chained.split hfc
  obtain ⟨ht's, ht'v, hf'c⟩ := hrest
  have ht'fwd : t'.IsFwd := hf t' (by simp)
  have hf' : ∀ x ∈ f', x.IsFwd := fun x hx => hf x (by simp [hx])
  have hsame₀ : SameEvent lts Indep t₀ t' := ht'e.symm
  -- The ladder from `t₀` to that occurrence, and causal consistency with `r`.
  obtain ⟨s, hs, hsci⟩ := ladder (Indep := Indep) hsame₀
  have hsf : Chained lts t₀.tgt (s ++ f') R := hs.append hf'c
  have hcc : CEq lts Indep t₀.tgt R r (s ++ f') := causal_consistency (Indep := Indep) hr hsf
  -- Every step after the occurrence is independent of the event of `t₀`.
  have hkey : ∀ x ∈ f', CIndep lts Indep t₀ x := by
    intro x hx
    have hxf : x.IsFwd := hf' x hx
    have hxpos : 0 < eventCount lts Indep x f' := eventCount_pos_of_mem hf' hx hxf
    have hsplit : eventCount lts Indep x r
        = eventCount lts Indep x s + eventCount lts Indep x f' := by
      rw [eventCount_of_cEq (Indep := Indep) hcc x, eventCount_append]
    by_cases hzs : eventCount lts Indep x s = 0
    · -- The event of `x` genuinely occurs in `r`; use the hypothesis.
      have hrpos : 0 < eventCount lts Indep x r := by rw [hsplit, hzs]; omega
      obtain ⟨u, hu, hux⟩ := exists_mem_of_eventCount_pos (Indep := Indep) hrpos
      have hupos : 0 < eventCount lts Indep u r := by
        rwa [eventCount_congr_base (Indep := Indep) hux r]
      exact (hyp u hu hupos).congrRight hux
    · -- The event of `x` already appears on the ladder, where independence is free.
      obtain ⟨u, hu, hcase⟩ := exists_mem_of_eventCount_ne_zero (Indep := Indep) hzs
      rcases hcase with hux | hux
      · exact (hsci u hu).congrRight hux
      · have := ((hsci u hu).congrRight hux).revRight
        simpa using this
  -- Commute the occurrence to the end.
  obtain ⟨g, tdag, -, hsame', -, hcq⟩ :=
    pushEvent (Indep := Indep) ht'fwd hf' (⟨ht's, ht'v, hf'c⟩ : Chained lts m (t' :: f') R)
      (fun x hx => (hkey x hx).congrLeft hsame₀)
  obtain ⟨n, -, hlast⟩ := Chained.split hcq.chained_right
  obtain ⟨-, htdv, htdt⟩ := hlast
  exact ⟨tdag, htdv, htdt, hsame₀.trans hsame'⟩

end Count

end Cslib.LTS
