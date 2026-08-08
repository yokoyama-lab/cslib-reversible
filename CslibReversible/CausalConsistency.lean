/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Parabolic
import CslibReversible.RevPath

/-!
# Causal consistency

**Coinitial cofinal paths are causally equivalent.**  If two computations
start in the same state and end in the same state, then one can be turned into
the other by permuting independent steps and inserting or deleting undo/redo
pairs — they differ by no causal content whatsoever.

The proof follows Lanese–Phillips–Ulidowski:

* `normalize_path` — every state can be rewound to an origin along an explicit
  backward path;
* `bwd_cc` — two backward paths out of the same state reach the same origin
  and are causally equivalent.  This is the well-founded induction where the
  Square Property and BTI do the work: when the two paths begin with different
  transitions, the diamond gives a common successor, and both legs are
  compared with it;
* `fwd_cc_from_origin` — the forward statement, obtained from the backward one
  by reversal (`CEq.rev`) rather than proved again;
* `causal_consistency` — put both paths in parabolic normal form, deepen each
  backward half all the way to the origin by inserting a cancelling pair, and
  match the halves.

## References

* [I. Lanese, I. Phillips, I. Ulidowski, *An Axiomatic Theory for Reversible
  Computation*, ACM TOCL 25(2), 2024][LPU2024]
-/

universe u v

namespace Cslib.LTS

variable {State : Type u} {Label : Type v} {lts : LTS State Label}
variable {Indep : Transition State Label → Transition State Label → Prop}

/-- A backward path gives a chain of backward steps. -/
theorem reflTransGen_of_chained_bwd {l : List (Transition State Label)} {p o : State}
    (h : Chained lts p l o) (hb : ∀ x ∈ l, x.IsBwd) :
    Relation.ReflTransGen (BStep lts) p o := by
  induction l generalizing p with
  | nil => cases h; exact .refl
  | cons t l ih =>
    obtain ⟨hs, hv, hc⟩ := h
    exact .head ⟨t, hv, hb t (by simp), hs, rfl⟩ (ih hc fun x hx => hb x (by simp [hx]))

/-- Every state can be rewound to an origin along an explicit backward path. -/
theorem normalize_path [WellFoundedBwd lts] [BStepDec lts] (p : State) :
    ∃ l o, Chained lts p l o ∧ (∀ x ∈ l, x.IsBwd) ∧ Origin lts o := by
  refine (WellFoundedBwd.wf (lts := lts)).induction
    (C := fun p => ∃ l o, Chained lts p l o ∧ (∀ x ∈ l, x.IsBwd) ∧ Origin lts o) p ?_
  intro p ih
  rcases BStepDec.step (lts := lts) p with ⟨q, hq⟩ | horig
  · obtain ⟨l, o, hc, hb, ho⟩ := ih q hq
    obtain ⟨t, hv, hd, hs, ht⟩ := hq
    refine ⟨t :: l, o, ⟨hs, hv, by rw [ht]; exact hc⟩, ?_, ho⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hd
    · exact hb x hx
  · exact ⟨[], p, rfl, by simp, horig⟩

/--
**Backward causal consistency.**  Two backward paths out of the same state
reach the same origin, and are causally equivalent.
-/
theorem bwd_cc [DecidableEq State] [DecidableEq Label]
    [SquareProperty lts Indep] [BTI lts Indep] [WellFoundedBwd lts] [BStepDec lts]
    {p : State} {l₁ l₂ : List (Transition State Label)} {o₁ o₂ : State}
    (hc₁ : Chained lts p l₁ o₁) (hb₁ : ∀ x ∈ l₁, x.IsBwd) (ho₁ : Origin lts o₁)
    (hc₂ : Chained lts p l₂ o₂) (hb₂ : ∀ x ∈ l₂, x.IsBwd) (ho₂ : Origin lts o₂) :
    o₁ = o₂ ∧ CEq lts Indep p o₁ l₁ l₂ := by
  induction p using (WellFoundedBwd.wf (lts := lts)).induction generalizing l₁ l₂ o₁ o₂ with
  | _ p ih =>
    have heo : o₁ = o₂ :=
      unique_origin (Indep := Indep)
        (reflTransGen_of_chained_bwd hc₁ hb₁) ho₁
        (reflTransGen_of_chained_bwd hc₂ hb₂) ho₂
    subst heo
    refine ⟨rfl, ?_⟩
    rcases l₁ with _ | ⟨t, l₁'⟩
    · rcases l₂ with _ | ⟨u, l₂'⟩
      · exact CEq.refl hc₁
      · -- `p` is already the origin, so the other path cannot start.
        exfalso
        obtain ⟨hus, huv, -⟩ := hc₂
        have hp : p = o₁ := hc₁
        subst hp
        exact ho₁ u.tgt ⟨u, huv, hb₂ u (by simp), hus, rfl⟩
    · rcases l₂ with _ | ⟨u, l₂'⟩
      · exfalso
        obtain ⟨hts, htv, -⟩ := hc₁
        have hp : p = o₁ := hc₂
        subst hp
        exact ho₁ t.tgt ⟨t, htv, hb₁ t (by simp), hts, rfl⟩
      · obtain ⟨hts, htv, hc₁'⟩ := hc₁
        obtain ⟨hus, huv, hc₂'⟩ := hc₂
        have hbt : t.IsBwd := hb₁ t (by simp)
        have hbu : u.IsBwd := hb₂ u (by simp)
        have hb₁' : ∀ x ∈ l₁', x.IsBwd := fun x hx => hb₁ x (by simp [hx])
        have hb₂' : ∀ x ∈ l₂', x.IsBwd := fun x hx => hb₂ x (by simp [hx])
        refine Decidable.byCases (p := t = u) (fun htu => ?_) (fun htu => ?_)
        · -- Same first step: strip it and recurse.
          subst htu
          have hstep : BStep lts p t.tgt := ⟨t, htv, hbt, hts, rfl⟩
          obtain ⟨-, hceq⟩ := ih t.tgt hstep hc₁' hb₁' ho₁ hc₂' hb₂' ho₁
          simpa using CEq.appendLeft (pre := [t]) ⟨hts, htv, rfl⟩ hceq
        · -- Different first steps: open the diamond and compare both legs
          -- against a common backward path to the origin.
          have hco : t.Coinitial u := hts.trans hus.symm
          have hind := BTI.bti (Indep := Indep) htv huv hco hbt hbu htu
          obtain ⟨w, hv1, hv2⟩ := SquareProperty.square (Indep := Indep) htv huv hind
          set u' : Transition State Label := Transition.mk t.tgt u.lbl u.dir w
          set t' : Transition State Label := Transition.mk u.tgt t.lbl t.dir w
          obtain ⟨sg, o3, hcs, hbs, ho3⟩ := normalize_path (lts := lts) w
          -- Left leg.
          have hstept : BStep lts p t.tgt := ⟨t, htv, hbt, hts, rfl⟩
          have hcu' : Chained lts t.tgt (u' :: sg) o3 := ⟨rfl, hv1, hcs⟩
          have hbu' : ∀ x ∈ u' :: sg, x.IsBwd := by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hbu
            · exact hbs x hx
          obtain ⟨heo3, hceq1⟩ := ih t.tgt hstept hc₁' hb₁' ho₁ hcu' hbu' ho3
          subst heo3
          -- Right leg.
          have hstepu : BStep lts p u.tgt := ⟨u, huv, hbu, hus, rfl⟩
          have hct' : Chained lts u.tgt (t' :: sg) o₁ := ⟨rfl, hv2, hcs⟩
          have hbt' : ∀ x ∈ t' :: sg, x.IsBwd := by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hbt
            · exact hbs x hx
          obtain ⟨-, hceq2⟩ := ih u.tgt hstepu hc₂' hb₂' ho₁ hct' hbt' ho₁
          -- Assemble: t :: l₁' ~ t :: u' :: sg ~ u :: t' :: sg ~ u :: l₂'.
          have cL : Chained lts p [t, u'] w := ⟨hts, htv, rfl, hv1, rfl⟩
          have cR : Chained lts p [u, t'] w := ⟨hus, huv, rfl, hv2, rfl⟩
          have sswap : CEq lts Indep p w [t, u'] [u, t'] :=
            CEq.swap hind rfl rfl rfl rfl cL cR
          have s1 : CEq lts Indep p o₁ (t :: l₁') (t :: u' :: sg) := by
            simpa using CEq.appendLeft (pre := [t]) ⟨hts, htv, rfl⟩ hceq1
          have s2 : CEq lts Indep p o₁ (t :: u' :: sg) (u :: t' :: sg) := by
            simpa using sswap.appendRight (post := sg) hcs
          have s3 : CEq lts Indep p o₁ (u :: t' :: sg) (u :: l₂') := by
            simpa using CEq.appendLeft (pre := [u]) ⟨hus, huv, rfl⟩ hceq2.symm
          exact (s1.trans s2).trans s3

/--
**Forward causal consistency from an origin**, by duality: reverse both paths,
apply `bwd_cc`, and reverse back.
-/
theorem fwd_cc_from_origin [DecidableEq State] [DecidableEq Label]
    [SquareProperty lts Indep] [BTI lts Indep] [WellFoundedBwd lts] [BStepDec lts]
    [IndepSymm Indep] [CLG Indep]
    {o q : State} {l₁ l₂ : List (Transition State Label)} (ho : Origin lts o)
    (h₁ : Chained lts o l₁ q) (hf₁ : ∀ x ∈ l₁, x.IsFwd)
    (h₂ : Chained lts o l₂ q) (hf₂ : ∀ x ∈ l₂, x.IsFwd) :
    CEq lts Indep o q l₁ l₂ := by
  obtain ⟨-, hr⟩ :=
    bwd_cc (Indep := Indep) h₁.revPath (revPath_isBwd hf₁) ho
      h₂.revPath (revPath_isBwd hf₂) ho
  simpa using hr.rev

/--
**Causal consistency.**  Two paths with the same source and the same target
are causally equivalent.
-/
theorem causal_consistency [DecidableEq State] [DecidableEq Label]
    [SquareProperty lts Indep] [BTI lts Indep] [WellFoundedBwd lts] [BStepDec lts]
    [IndepSymm Indep] [CLG Indep]
    {p q : State} {l₁ l₂ : List (Transition State Label)}
    (h₁ : Chained lts p l₁ q) (h₂ : Chained lts p l₂ q) :
    CEq lts Indep p q l₁ l₂ := by
  -- Parabolic normal forms.
  obtain ⟨b₁, f₁, hb₁, hf₁, hq₁⟩ := parabolic (Indep := Indep) h₁
  obtain ⟨b₂, f₂, hb₂, hf₂, hq₂⟩ := parabolic (Indep := Indep) h₂
  obtain ⟨m₁, hbc₁, hfc₁⟩ := Chained.split hq₁.chained_right
  obtain ⟨m₂, hbc₂, hfc₂⟩ := Chained.split hq₂.chained_right
  -- Deepen each backward half all the way to an origin.
  obtain ⟨n₁, o₁, hn₁, hnb₁, ho₁⟩ := normalize_path (lts := lts) m₁
  obtain ⟨n₂, o₂, hn₂, hnb₂, ho₂⟩ := normalize_path (lts := lts) m₂
  have happ : ∀ {x y : List (Transition State Label)} {P : Transition State Label → Prop},
      (∀ z ∈ x, P z) → (∀ z ∈ y, P z) → ∀ z ∈ x ++ y, P z := by
    intro x y P hx hy z hz
    rcases List.mem_append.mp hz with h | h
    · exact hx z h
    · exact hy z h
  have hB₁ : Chained lts p (b₁ ++ n₁) o₁ := hbc₁.append hn₁
  have hB₂ : Chained lts p (b₂ ++ n₂) o₂ := hbc₂.append hn₂
  obtain ⟨heo, hceqB⟩ :=
    bwd_cc (Indep := Indep) hB₁ (happ hb₁ hnb₁) ho₁ hB₂ (happ hb₂ hnb₂) ho₂
  subst heo
  -- The forward halves, deepened symmetrically.
  have hF₁ : Chained lts o₁ (revPath n₁ ++ f₁) q := hn₁.revPath.append hfc₁
  have hF₂ : Chained lts o₁ (revPath n₂ ++ f₂) q := hn₂.revPath.append hfc₂
  have hceqF : CEq lts Indep o₁ q (revPath n₁ ++ f₁) (revPath n₂ ++ f₂) :=
    fwd_cc_from_origin (Indep := Indep) ho₁
      hF₁ (happ (revPath_isFwd hnb₁) hf₁) hF₂ (happ (revPath_isFwd hnb₂) hf₂)
  -- Deepening is causally invisible: it inserts a cancelling pair.
  have hD₁ : CEq lts Indep p q (b₁ ++ f₁) ((b₁ ++ n₁) ++ (revPath n₁ ++ f₁)) := by
    have := CEq.ctx hbc₁ (cancel_path (Indep := Indep) hn₁).symm hfc₁
    simpa [List.append_assoc] using this
  have hD₂ : CEq lts Indep p q (b₂ ++ f₂) ((b₂ ++ n₂) ++ (revPath n₂ ++ f₂)) := by
    have := CEq.ctx hbc₂ (cancel_path (Indep := Indep) hn₂).symm hfc₂
    simpa [List.append_assoc] using this
  have hceqD : CEq lts Indep p q ((b₁ ++ n₁) ++ (revPath n₁ ++ f₁))
      ((b₂ ++ n₂) ++ (revPath n₂ ++ f₂)) :=
    (hceqB.appendRight hF₁).trans (CEq.appendLeft hB₂ hceqF)
  exact hq₁.trans (hD₁.trans (hceqD.trans (hD₂.symm.trans hq₂.symm)))

end Cslib.LTS
