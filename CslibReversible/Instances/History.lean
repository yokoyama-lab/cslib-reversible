/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Diamond

/-!
# The history extension of an LTS

Any LTS becomes reversible if its states are made to carry the record of how
they were reached.  This is the Landauer embedding, and it is the shape every
concrete reversible language takes: R-CORE, CR-CORE and RCCS all differ in
*what* they remember, not in *that* they remember.

The point of this file is the uniqueness lemma `bwd_unique`: a backward
transition of `histLTS` is determined by its source, because the head of the
history says both which label was used and where it came from.  Everything
downstream — that undoing terminates, that it is decidable, and (in
`Instances.Product`) that BTI holds — rests on it.
-/

universe u v

namespace Cslib.LTS

variable {State : Type u} {Label : Type v}

/-- A state together with the history it needs in order to be undone. -/
abbrev Hist (State : Type u) (Label : Type v) : Type (max u v) :=
  State × List (State × Label)

/--
The history extension of an LTS: a forward step records where it came from.
-/
def histLTS (lts : LTS State Label) : LTS (Hist State Label) Label where
  Tr := fun p μ q => lts.Tr p.1 μ q.1 ∧ q.2 = (p.1, μ) :: p.2

@[simp] theorem histLTS_tr {lts : LTS State Label} {p q : Hist State Label} {μ : Label} :
    (histLTS lts).Tr p μ q ↔ lts.Tr p.1 μ q.1 ∧ q.2 = (p.1, μ) :: p.2 := Iff.rfl

section

variable {lts : LTS State Label}

/-- A valid backward transition reads off the head of the history of its source. -/
theorem histLTS_bwd_src {t : Transition (Hist State Label) Label}
    (hv : t.Valid (histLTS lts)) (hb : t.IsBwd) :
    t.src.2 = (t.tgt.1, t.lbl) :: t.tgt.2 := by
  rw [Transition.Valid, hb] at hv
  exact hv.2

/-- The step underlying a valid backward transition. -/
theorem histLTS_bwd_tr {t : Transition (Hist State Label) Label}
    (hv : t.Valid (histLTS lts)) (hb : t.IsBwd) :
    lts.Tr t.tgt.1 t.lbl t.src.1 := by
  rw [Transition.Valid, hb] at hv
  exact hv.1

/--
**Backward transitions are unique.**  Two valid backward transitions with the
same source are equal: the history determines the label and the target.
-/
theorem histLTS_bwd_unique {t u : Transition (Hist State Label) Label}
    (htv : t.Valid (histLTS lts)) (htb : t.IsBwd)
    (huv : u.Valid (histLTS lts)) (hub : u.IsBwd)
    (hs : t.src = u.src) : t = u := by
  have ht := histLTS_bwd_src htv htb
  have hu := histLTS_bwd_src huv hub
  rw [hs, hu] at ht
  obtain ⟨hhd, htl⟩ := List.cons.injEq .. ▸ ht
  obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ hhd
  refine Transition.ext hs ?_ (htb.trans hub.symm) ?_
  · exact h2.symm
  · exact Prod.ext h1.symm htl.symm

end

end Cslib.LTS
