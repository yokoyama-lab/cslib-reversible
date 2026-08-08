/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Instances.Grounded

/-!
# R-CORE

A port of the token-based small-step semantics of R-CORE, the minimalist
reversible language of Makino and Yokoyama (RC 2026).  The Rocq development
this follows is `yokoyama-lab/rcore-semantics` (`proofs.v`, axiom-free); the
syntax, the store, the reversible update operator and the twelve rules of
`exec_ss` are transcribed, together with the well-formedness predicate the
backward determinism theorem is relative to.

The point of the exercise is that R-CORE joins the axiom layer through
`Instances.Restrict`: it exhibits `WfCC`, shows it closed under steps in both
directions, and proves backward determinism relative to it.  Nothing about the
axioms of reversible computation is proved here.

## Labels

R-CORE's semantics is a reduction semantics, so there is nothing to observe on
a step and every transition carries the same label.  Lanese, Phillips and
Ulidowski treat reduction semantics the same way.

## Main definitions

- `Val`, `Expr`, `Cmd`, `ContCmd`: the syntax, with the control token in the
  command tree.
- `odot`: the reversible update operator, partial and self-inverse.
- `Step`: the twelve rules of `exec_ss`.
- `WfCC`: well-formedness — no assignment mentions its own target.

## References

* [T. Makino, T. Yokoyama, *Small-Step Semantics with Meta-Level Reversibility
  for a Reversible Core Language*, RC 2026, LNCS][MakinoYokoyama2026]
  DOI 10.1007/978-3-032-30839-9_12
-/

universe u

namespace Cslib.LTS.RCore

/-! ## Syntax -/

/-- Values: binary trees over `nil`. -/
inductive Val : Type where
  /-- The empty tree. -/
  | nil : Val
  /-- A pair. -/
  | pair (a b : Val) : Val
  deriving DecidableEq, Repr

variable {n : Nat}

/-- Variables. -/
abbrev Var (n : Nat) := Fin n

/-- Expressions.  Every form reads variables only, so evaluation is total in
the store and partial only through `hd` and `tl`. -/
inductive Expr (n : Nat) : Type where
  /-- A variable. -/
  | var (x : Var n) : Expr n
  /-- The constant `nil`. -/
  | nil : Expr n
  /-- The first component of a pair. -/
  | hd (x : Var n) : Expr n
  /-- The second component of a pair. -/
  | tl (x : Var n) : Expr n
  /-- Pairing. -/
  | cons (x y : Var n) : Expr n
  /-- Equality test, returning `pair nil nil` for true and `nil` for false. -/
  | eq (x y : Var n) : Expr n
  deriving DecidableEq

/-- Commands. -/
inductive Cmd (n : Nat) : Type where
  /-- Reversible assignment `x ^= e`. -/
  | ass (x : Var n) (e : Expr n) : Cmd n
  /-- Sequence. -/
  | seq (c₁ c₂ : Cmd n) : Cmd n
  /-- `from x loop c until y`. -/
  | loop (x : Var n) (c : Cmd n) (y : Var n) : Cmd n
  deriving DecidableEq

/--
A command with exactly one control token.

`atPre c` is the token just before `c`, `atPost c` just after it, and the
remaining constructors say where in the tree the token sits.
-/
inductive ContCmd (n : Nat) : Type where
  /-- The token is before the command. -/
  | atPre (c : Cmd n) : ContCmd n
  /-- The token is after the command. -/
  | atPost (c : Cmd n) : ContCmd n
  /-- The token is at the head of a loop, between the two tests. -/
  | midLoop (x : Var n) (c : Cmd n) (y : Var n) : ContCmd n
  /-- The token is in the left component of a sequence. -/
  | seqL (cc : ContCmd n) (c₂ : Cmd n) : ContCmd n
  /-- The token is in the right component of a sequence. -/
  | seqR (c₁ : Cmd n) (cc : ContCmd n) : ContCmd n
  /-- The token is inside the body of a loop. -/
  | inLoop (x : Var n) (cc : ContCmd n) (y : Var n) : ContCmd n
  deriving DecidableEq

/-! ## Stores and semantic auxiliaries -/

/-- A store assigns a value to every variable. -/
abbrev Store (n : Nat) := Var n → Val

/-- Updating one variable. -/
def update (s : Store n) (x : Var n) (v : Val) : Store n :=
  fun y => if y = x then v else s y

@[simp] theorem update_eq (s : Store n) (x : Var n) (v : Val) : update s x v x = v := by
  simp [update]

@[simp] theorem update_ne (s : Store n) {x y : Var n} (h : y ≠ x) (v : Val) :
    update s x v y = s y := by simp [update, h]

/-- Expression evaluation. -/
def evalExpr (s : Store n) : Expr n → Option Val
  | .var x => some (s x)
  | .nil => some .nil
  | .hd x => match s x with | .pair a _ => some a | .nil => none
  | .tl x => match s x with | .pair _ b => some b | .nil => none
  | .cons x y => some (.pair (s x) (s y))
  | .eq x y => some (if s x = s y then .pair .nil .nil else .nil)

/--
The reversible update operator.

`odot d e` is `e` when the target holds `nil`, and `nil` when the target
already holds `e`; otherwise the assignment is undefined.  This is what makes
assignment injective in its target.
-/
def odot : Val → Val → Option Val
  | .nil, e => some e
  | d@(.pair _ _), e => if d = e then some .nil else none

/-- `odot` is its own inverse where it is defined. -/
theorem odot_inv {d e v : Val} (h : odot d e = some v) : odot v e = some d := by
  cases d with
  | nil =>
    simp only [odot, Option.some.injEq] at h
    subst h
    cases e with
    | nil => rfl
    | pair a b => simp [odot]
  | pair a b =>
    simp only [odot] at h
    split at h
    · rename_i he; subst he
      simp only [Option.some.injEq] at h
      subst h
      rfl
    · exact absurd h (by simp)

/-- The target of an assignment is determined by its result. -/
theorem odot_left_injective {d₁ d₂ e v : Val}
    (h₁ : odot d₁ e = some v) (h₂ : odot d₂ e = some v) : d₁ = d₂ := by
  cases d₁ with
  | nil =>
    cases d₂ with
    | nil => rfl
    | pair a b =>
      simp only [odot, Option.some.injEq] at h₁
      simp only [odot] at h₂
      split at h₂
      · rename_i he; subst he
        simp only [Option.some.injEq] at h₂
        exact absurd (h₁.trans h₂.symm) (by simp)
      · exact absurd h₂ (by simp)
  | pair a b =>
    simp only [odot] at h₁
    split at h₁
    · rename_i he; subst he
      simp only [Option.some.injEq] at h₁
      subst h₁
      cases d₂ with
      | nil => simp only [odot, Option.some.injEq] at h₂; exact absurd h₂ (by simp)
      | pair c d =>
        simp only [odot] at h₂
        split at h₂
        · rename_i he₂; exact he₂.symm
        · exact absurd h₂ (by simp)
    · exact absurd h₁ (by simp)

/-! ## The small-step semantics -/

/-- A configuration: a command with its token, and a store. -/
abbrev Config (n : Nat) := ContCmd n × Store n

/--
The twelve rules of `exec_ss`.

The first three groups move the token through an assignment, a loop and a
sequence; the last three propagate a step under a context.
-/
inductive Step : Config n → Config n → Prop where
  /-- Perform an assignment. -/
  | asn {x : Var n} {e : Expr n} {s : Store n} {vE vNew : Val}
      (hE : evalExpr s e = some vE) (hO : odot (s x) vE = some vNew) :
      Step (.atPre (.ass x e), s) (.atPost (.ass x e), update s x vNew)
  /-- Enter a loop: the entry test holds. -/
  | loopEnter {x : Var n} {c : Cmd n} {y : Var n} {s : Store n} (h : s x ≠ .nil) :
      Step (.atPre (.loop x c y), s) (.midLoop x c y, s)
  /-- Leave a loop: the exit test holds. -/
  | loopExit {x : Var n} {c : Cmd n} {y : Var n} {s : Store n} (h : s y ≠ .nil) :
      Step (.midLoop x c y, s) (.atPost (.loop x c y), s)
  /-- Go round again: the exit test fails. -/
  | loopIter₁ {x : Var n} {c : Cmd n} {y : Var n} {s : Store n} (h : s y = .nil) :
      Step (.midLoop x c y, s) (.inLoop x (.atPre c) y, s)
  /-- Come back to the loop head: the entry test fails. -/
  | loopIter₂ {x : Var n} {c : Cmd n} {y : Var n} {s : Store n} (h : s x = .nil) :
      Step (.inLoop x (.atPost c) y, s) (.midLoop x c y, s)
  /-- Enter a sequence. -/
  | seqEnter {c₁ c₂ : Cmd n} {s : Store n} :
      Step (.atPre (.seq c₁ c₂), s) (.seqL (.atPre c₁) c₂, s)
  /-- Cross from the first component to the second. -/
  | seqMid {c₁ c₂ : Cmd n} {s : Store n} :
      Step (.seqL (.atPost c₁) c₂, s) (.seqR c₁ (.atPre c₂), s)
  /-- Leave a sequence. -/
  | seqExit {c₁ c₂ : Cmd n} {s : Store n} :
      Step (.seqR c₁ (.atPost c₂), s) (.atPost (.seq c₁ c₂), s)
  /-- Step under the left component of a sequence. -/
  | ctxSeqL {cc cc' : ContCmd n} {c₂ : Cmd n} {s s' : Store n}
      (h : Step (cc, s) (cc', s')) :
      Step (.seqL cc c₂, s) (.seqL cc' c₂, s')
  /-- Step under the right component of a sequence. -/
  | ctxSeqR {c₁ : Cmd n} {cc cc' : ContCmd n} {s s' : Store n}
      (h : Step (cc, s) (cc', s')) :
      Step (.seqR c₁ cc, s) (.seqR c₁ cc', s')
  /-- Step under the body of a loop. -/
  | ctxLoop {x : Var n} {cc cc' : ContCmd n} {y : Var n} {s s' : Store n}
      (h : Step (cc, s) (cc', s')) :
      Step (.inLoop x cc y, s) (.inLoop x cc' y, s')

/-! ## Well-formedness -/

/-- `e` does not mention `x`.  This is what rules out `x ^= x`. -/
inductive NfExpr (x : Var n) : Expr n → Prop where
  /-- A variable other than `x`. -/
  | var {y : Var n} (h : y ≠ x) : NfExpr x (.var y)
  /-- The constant `nil`. -/
  | nil : NfExpr x .nil
  /-- `hd y` for `y` other than `x`. -/
  | hd {y : Var n} (h : y ≠ x) : NfExpr x (.hd y)
  /-- `tl y` for `y` other than `x`. -/
  | tl {y : Var n} (h : y ≠ x) : NfExpr x (.tl y)
  /-- `cons y z` for `y`, `z` other than `x`. -/
  | cons {y z : Var n} (hy : y ≠ x) (hz : z ≠ x) : NfExpr x (.cons y z)
  /-- `eq y z` for `y`, `z` other than `x`. -/
  | eq {y z : Var n} (hy : y ≠ x) (hz : z ≠ x) : NfExpr x (.eq y z)

/-- No assignment mentions its own target. -/
inductive WfCmd : Cmd n → Prop where
  /-- An assignment whose right-hand side avoids its target. -/
  | ass {x : Var n} {e : Expr n} (h : NfExpr x e) : WfCmd (.ass x e)
  /-- A sequence of well-formed commands. -/
  | seq {c₁ c₂ : Cmd n} (h₁ : WfCmd c₁) (h₂ : WfCmd c₂) : WfCmd (.seq c₁ c₂)
  /-- A loop with a well-formed body. -/
  | loop {x : Var n} {c : Cmd n} {y : Var n} (h : WfCmd c) : WfCmd (.loop x c y)

/-- Well-formedness of a command carrying the token. -/
inductive WfCC : ContCmd n → Prop where
  /-- Before a well-formed command. -/
  | atPre {c : Cmd n} (h : WfCmd c) : WfCC (.atPre c)
  /-- After a well-formed command. -/
  | atPost {c : Cmd n} (h : WfCmd c) : WfCC (.atPost c)
  /-- At the head of a loop with a well-formed body. -/
  | midLoop {x : Var n} {c : Cmd n} {y : Var n} (h : WfCmd c) : WfCC (.midLoop x c y)
  /-- In the left component of a sequence. -/
  | seqL {cc : ContCmd n} {c₂ : Cmd n} (h : WfCC cc) (h₂ : WfCmd c₂) : WfCC (.seqL cc c₂)
  /-- In the right component of a sequence. -/
  | seqR {c₁ : Cmd n} {cc : ContCmd n} (h₁ : WfCmd c₁) (h : WfCC cc) : WfCC (.seqR c₁ cc)
  /-- Inside the body of a loop. -/
  | inLoop {x : Var n} {cc : ContCmd n} {y : Var n} (h : WfCC cc) : WfCC (.inLoop x cc y)

/-- The self-assignment `x ^= x` is exactly what well-formedness excludes. -/
theorem not_nfExpr_self (x : Var n) : ¬ NfExpr x (.var x) := by
  rintro ⟨h⟩; exact h rfl

/--
A well-formed right-hand side reads the same before and after its own
assignment.  This is the lemma backward determinism turns on.
-/
theorem evalExpr_update_of_nf {x : Var n} {e : Expr n} (h : NfExpr x e)
    (s : Store n) (v : Val) : evalExpr (update s x v) e = evalExpr s e := by
  cases h <;> simp_all [evalExpr, update]

/-! ## Well-formedness is closed under steps, in both directions -/

/-- Steps preserve well-formedness. -/
theorem wf_step_preserved {p q : Config n} (h : Step p q) (hw : WfCC p.1) : WfCC q.1 := by
  induction h with
  | asn => cases hw with | atPre hc => exact .atPost hc
  | loopEnter => cases hw with | atPre hc => cases hc with | loop hb => exact .midLoop hb
  | loopExit => cases hw with | midLoop hb => exact .atPost (.loop hb)
  | loopIter₁ => cases hw with | midLoop hb => exact .inLoop (.atPre hb)
  | loopIter₂ => cases hw with | inLoop hcc => cases hcc with | atPost hb => exact .midLoop hb
  | seqEnter => cases hw with | atPre hc => cases hc with | seq h₁ h₂ => exact .seqL (.atPre h₁) h₂
  | seqMid =>
    cases hw with
    | seqL hcc h₂ => cases hcc with | atPost h₁ => exact .seqR h₁ (.atPre h₂)
  | seqExit =>
    cases hw with
    | seqR h₁ hcc => cases hcc with | atPost h₂ => exact .atPost (.seq h₁ h₂)
  | ctxSeqL _ ih => cases hw with | seqL hcc h₂ => exact .seqL (ih hcc) h₂
  | ctxSeqR _ ih => cases hw with | seqR h₁ hcc => exact .seqR h₁ (ih hcc)
  | ctxLoop _ ih => cases hw with | inLoop hcc => exact .inLoop (ih hcc)

/-- Steps reflect well-formedness. -/
theorem wf_step_reflected {p q : Config n} (h : Step p q) (hw : WfCC q.1) : WfCC p.1 := by
  induction h with
  | asn => cases hw with | atPost hc => exact .atPre hc
  | loopEnter => cases hw with | midLoop hb => exact .atPre (.loop hb)
  | loopExit => cases hw with | atPost hc => cases hc with | loop hb => exact .midLoop hb
  | loopIter₁ => cases hw with | inLoop hcc => cases hcc with | atPre hb => exact .midLoop hb
  | loopIter₂ => cases hw with | midLoop hb => exact .inLoop (.atPost hb)
  | seqEnter =>
    cases hw with
    | seqL hcc h₂ => cases hcc with | atPre h₁ => exact .atPre (.seq h₁ h₂)
  | seqMid =>
    cases hw with
    | seqR h₁ hcc => cases hcc with | atPre h₂ => exact .seqL (.atPost h₁) h₂
  | seqExit => cases hw with | atPost hc => cases hc with | seq h₁ h₂ => exact .seqR h₁ (.atPost h₂)
  | ctxSeqL _ ih => cases hw with | seqL hcc h₂ => exact .seqL (ih hcc) h₂
  | ctxSeqR _ ih => cases hw with | seqR h₁ hcc => exact .seqR h₁ (ih hcc)
  | ctxLoop _ ih => cases hw with | inLoop hcc => exact .inLoop (ih hcc)

/-! ## Nothing steps into a token sitting before a command -/

/--
No rule produces `atPre`.

This is what separates the rule that enters a construct from the rule that
steps underneath it, and it is used at every such overlap in the backward
determinism proof.
-/
theorem no_step_into_atPre {q : Config n} {c : Cmd n} {s : Store n} :
    ¬ Step q (.atPre c, s) := by
  intro h; cases h

/-! ## Backward determinism -/

/-- Stores that agree off `x` evaluate an `x`-free expression alike. -/
theorem evalExpr_congr_of_nf {x : Var n} {e : Expr n} (h : NfExpr x e) {s₁ s₂ : Store n}
    (hag : ∀ y, y ≠ x → s₁ y = s₂ y) : evalExpr s₁ e = evalExpr s₂ e := by
  cases h <;> simp_all [evalExpr]

/--
**Backward determinism, relative to well-formedness.**

This is `ss_bwd_deterministic_tgt` of the Rocq development: the side condition
sits on the configuration the two backward steps leave from.

Well-formedness is needed in exactly one case, the assignment: it is what lets
the right-hand side be evaluated in the *target* store, and hence lets the
target of the assignment be recovered by inverting `odot`.  Without it `x ^= x`
collapses every value to `nil` and the step cannot be undone.

The remaining overlaps are settled without it: the two rules that reach a loop
head are told apart by the entry test, and every rule that enters a construct
is told apart from the rule that steps underneath it by `no_step_into_atPre`.
-/
theorem bwd_det : ∀ {p q₁ : Config n}, Step q₁ p →
    ∀ {r q₂ : Config n}, Step q₂ r → p = r → WfCC p.1 → q₁ = q₂ := by
  intro p q₁ h₁
  induction h₁ with
  | @asn x e s vE vNew hE hO =>
    rintro r q₂ h₂ heq hw
    cases h₂
    case asn x₂ e₂ s₂ vE₂ vNew₂ hE₂ hO₂ =>
      simp only [Prod.mk.injEq, ContCmd.atPost.injEq, Cmd.ass.injEq] at heq
      obtain ⟨⟨rfl, rfl⟩, hst⟩ := heq
      cases hw with
      | atPost hc =>
        cases hc with
        | ass hnf =>
          have hv : vNew = vNew₂ := by simpa using congrFun hst x
          have hag : ∀ y, y ≠ x → s y = s₂ y := by
            intro y hy
            have hc := congrFun hst y
            simpa [update, hy] using hc
          have hee : evalExpr s e = evalExpr s₂ e := evalExpr_congr_of_nf hnf hag
          rw [hE, hE₂] at hee
          have hvE : vE = vE₂ := Option.some.inj hee
          subst hvE; subst hv
          have hx : s x = s₂ x := odot_left_injective hO hO₂
          refine Prod.ext rfl (funext fun y => ?_)
          by_cases hy : y = x
          · subst hy; exact hx
          · exact hag y hy
    all_goals simp_all [Prod.mk.injEq]
  | loopEnter h => rintro r q₂ h₂ heq hw; cases h₂ <;> simp_all [Prod.mk.injEq]
  | loopExit h => rintro r q₂ h₂ heq hw; cases h₂ <;> simp_all [Prod.mk.injEq]
  | @loopIter₁ x c y s h =>
    rintro r q₂ h₂ heq hw
    cases h₂
    case ctxLoop cc cc' s₀ s₀' hin =>
      simp only [Prod.mk.injEq, ContCmd.inLoop.injEq] at heq
      obtain ⟨⟨rfl, hcc, rfl⟩, rfl⟩ := heq
      subst hcc
      exact absurd hin no_step_into_atPre
    all_goals simp_all [Prod.mk.injEq]
  | loopIter₂ h => rintro r q₂ h₂ heq hw; cases h₂ <;> simp_all [Prod.mk.injEq]
  | @seqEnter c₁ c₂ s =>
    rintro r q₂ h₂ heq hw
    cases h₂
    case ctxSeqL cc cc' c₂' s₀ s₀' hin =>
      simp only [Prod.mk.injEq, ContCmd.seqL.injEq] at heq
      obtain ⟨⟨hcc, rfl⟩, rfl⟩ := heq
      subst hcc
      exact absurd hin no_step_into_atPre
    all_goals simp_all [Prod.mk.injEq]
  | @seqMid c₁ c₂ s =>
    rintro r q₂ h₂ heq hw
    cases h₂
    case ctxSeqR c₁' cc cc' s₀ s₀' hin =>
      simp only [Prod.mk.injEq, ContCmd.seqR.injEq] at heq
      obtain ⟨⟨rfl, hcc⟩, rfl⟩ := heq
      subst hcc
      exact absurd hin no_step_into_atPre
    all_goals simp_all [Prod.mk.injEq]
  | seqExit => rintro r q₂ h₂ heq hw; cases h₂ <;> simp_all [Prod.mk.injEq]
  | @ctxSeqL cc cc' c₂ s s' hin ih =>
    rintro r q₂ h₂ heq hw
    cases h₂
    case seqEnter c₁' c₂' s₀ =>
      simp only [Prod.mk.injEq, ContCmd.seqL.injEq] at heq
      obtain ⟨⟨hcc, rfl⟩, rfl⟩ := heq
      subst hcc
      exact absurd hin no_step_into_atPre
    case ctxSeqL cc₂ cc₂' c₂₂ s₂ s₂' hin₂ =>
      simp only [Prod.mk.injEq, ContCmd.seqL.injEq] at heq
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
      have hwcc : WfCC cc' := by cases hw with | seqL hcc _ => exact hcc
      have := ih hin₂ rfl hwcc
      simp_all
    all_goals simp_all [Prod.mk.injEq]
  | @ctxSeqR c₁ cc cc' s s' hin ih =>
    rintro r q₂ h₂ heq hw
    cases h₂
    case seqMid c₁' c₂' s₀ =>
      simp only [Prod.mk.injEq, ContCmd.seqR.injEq] at heq
      obtain ⟨⟨rfl, hcc⟩, rfl⟩ := heq
      subst hcc
      exact absurd hin no_step_into_atPre
    case ctxSeqR c₁₂ cc₂ cc₂' s₂ s₂' hin₂ =>
      simp only [Prod.mk.injEq, ContCmd.seqR.injEq] at heq
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
      have hwcc : WfCC cc' := by cases hw with | seqR _ hcc => exact hcc
      have := ih hin₂ rfl hwcc
      simp_all
    all_goals simp_all [Prod.mk.injEq]
  | @ctxLoop x cc cc' y s s' hin ih =>
    rintro r q₂ h₂ heq hw
    cases h₂
    case loopIter₁ x₂ c₂ y₂ s₂ h₂' =>
      simp only [Prod.mk.injEq, ContCmd.inLoop.injEq] at heq
      obtain ⟨⟨rfl, hcc, rfl⟩, rfl⟩ := heq
      exact absurd hin (hcc ▸ no_step_into_atPre)
    case ctxLoop x₂ cc₂ cc₂' y₂ s₂ s₂' hin₂ =>
      simp only [Prod.mk.injEq, ContCmd.inLoop.injEq] at heq
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := heq
      have hwcc : WfCC cc' := by cases hw with | inLoop hcc => exact hcc
      have := ih hin₂ rfl hwcc
      simp_all
    all_goals simp_all [Prod.mk.injEq]

/-! ## R-CORE as an instance -/

/--
R-CORE as an `LTS`.

The semantics is a reduction semantics, so there is nothing to observe on a
step and every transition carries the same label.
-/
def lts (n : Nat) : LTS (Config n) Unit := ⟨fun p _ q => Step p q⟩

@[simp] theorem lts_Tr {p q : Config n} {a : Unit} : (lts n).Tr p a q ↔ Step p q := Iff.rfl

/-- Well-formedness carries a sub-LTS: it is preserved and reflected by steps. -/
theorem stepClosed (n : Nat) : StepClosed (lts n) (fun cfg => WfCC cfg.1) where
  fwd h hp := wf_step_preserved h hp
  bwd h hq := wf_step_reflected h hq

/-- R-CORE is backward deterministic on its well-formed configurations. -/
theorem bwdDeterministicOn (n : Nat) :
    BwdDeterministicOn (lts n) (fun cfg => WfCC cfg.1) := by
  intro p q₁ q₂ a b hw h₁ h₂
  exact ⟨rfl, bwd_det h₁ h₂ rfl hw⟩

/-- The well-formed configurations of R-CORE, as a transition system. -/
abbrev wfLTS (n : Nat) : LTS {cfg : Config n // WfCC cfg.1} Unit :=
  (lts n).restrict (fun cfg => WfCC cfg.1)

instance instBTI (n : Nat) : BTI (wfLTS n) NoIndep :=
  have := bwdDeterministic_restrict (bwdDeterministicOn n)
  inferInstance

/--
**The Parabolic Lemma for R-CORE.**

Every computation of a well-formed R-CORE configuration is causally equivalent
to one that undoes and then redoes.  Nothing about R-CORE is used in the proof:
it is the general theorem applied to the instance.
-/
theorem parabolic_rcore [DecidableEq (Store n)]
    {l : List (Transition {cfg : Config n // WfCC cfg.1} Unit)}
    {p q : {cfg : Config n // WfCC cfg.1}} (hc : Chained (wfLTS n) p l q) :
    ∃ lb lf, (∀ x ∈ lb, x.IsBwd) ∧ (∀ x ∈ lf, x.IsFwd) ∧
      CEq (wfLTS n) NoIndep p q l (lb ++ lf) :=
  parabolic (Indep := NoIndep) hc

/-- **Undoing is confluent for R-CORE.** -/
theorem bstep_diamond_rcore [DecidableEq (Store n)]
    {p q₁ q₂ : {cfg : Config n // WfCC cfg.1}}
    (h₁ : BStep (wfLTS n) p q₁) (h₂ : BStep (wfLTS n) p q₂) :
    q₁ = q₂ ∨ ∃ w, BStep (wfLTS n) q₁ w ∧ BStep (wfLTS n) q₂ w :=
  bstep_diamond (Indep := NoIndep) h₁ h₂

/-! ## Why causal consistency does not follow -/

/--
A loop whose body leaves the store alone, run on the store that is `nil`
everywhere, cycles in three steps.

`causal_consistency` and `unique_origin` need `WellFoundedBwd`, and this
configuration refutes it: undoing goes round the cycle forever.  The axiom of
Lanese, Phillips and Ulidowski that there is no infinite backward computation
is not a property of a language with unbounded iteration; it holds only of the
configurations reachable from a program's start in finitely many steps.  The
Square Property, BTI and everything derived from them — the Parabolic Lemma,
confluence of undoing — are unaffected, which is why they are harvested above
and causal consistency is not.
-/
theorem loop_cycles (n : Nat) (hn : 0 < n) :
    ∃ (p₁ p₂ p₃ : Config n), WfCC p₁.1 ∧ Step p₁ p₂ ∧ Step p₂ p₃ ∧ Step p₃ p₁ := by
  let x : Var n := ⟨0, hn⟩
  let c : Cmd n := .ass x .nil
  let s : Store n := fun _ => .nil
  refine ⟨(.midLoop x c x, s), (.inLoop x (.atPre c) x, s), (.inLoop x (.atPost c) x, s),
    .midLoop (.ass .nil), .loopIter₁ rfl, ?_, .loopIter₂ rfl⟩
  have hupd : update s x .nil = s := by
    funext y; simp only [update]; split <;> rfl
  have hstep : Step ((.atPre c : ContCmd n), s) (.atPost c, update s x .nil) :=
    Step.asn (e := Expr.nil) rfl rfl
  rw [hupd] at hstep
  exact Step.ctxLoop hstep

/-! ## The configurations a program reaches -/

/-- A token sitting before a command has nothing to undo. -/
theorem origin_atPre {c : Cmd n} {s : Store n} : Origin (lts n) (.atPre c, s) := by
  intro q hq
  obtain ⟨a, ha⟩ := bstep_iff.mp hq
  exact no_step_into_atPre ha

/-- A program's start is grounded. -/
theorem grounded_atPre {c : Cmd n} {s : Store n} : Grounded (lts n) (.atPre c, s) :=
  grounded_of_origin origin_atPre

/--
**Everything a program reaches from its start is well-formed and grounded.**

So the cycle of `loop_cycles` is not reached by any program: it is a
configuration of the term algebra, not of a run.  On the part that runs do
reach, `WellFoundedBwd` holds — by `wellFoundedBwd_grounded`, without being
assumed.
-/
theorem wf_grounded_of_run {p q : Config n} (hw : WfCC p.1) (hg : Grounded (lts n) p)
    (h : Relation.ReflTransGen (fun a b : Config n => Step a b) p q) :
    GroundedOn (lts n) (fun cfg => WfCC cfg.1) q := by
  induction h with
  | refl => exact ⟨hw, hg⟩
  | tail _ hstep ih =>
    exact ⟨wf_step_preserved hstep ih.1,
      ih.2.fwd (bwdDeterministicOn n) (a := ()) (wf_step_preserved hstep ih.1) hstep⟩

/-- Running a well-formed program from its start stays in the good part. -/
theorem run_from_start {c : Cmd n} {s : Store n} {q : Config n} (hc : WfCmd c)
    (h : Relation.ReflTransGen (fun a b : Config n => Step a b) (.atPre c, s) q) :
    GroundedOn (lts n) (fun cfg => WfCC cfg.1) q :=
  wf_grounded_of_run (.atPre hc) grounded_atPre h

/--
**Causal consistency for R-CORE**, on the configurations its programs reach.

The well-foundedness that `loop_cycles` refutes globally is supplied here by
`Instances.Grounded`, so iteration is no obstacle.  The one obligation left to
R-CORE is `BStepDec` — a computable step-back, which is the reverse
interpreter: for an assignment it inverts `odot` in the target store, which
`odot_inv` already justifies, and elsewhere it reads the rule off the token's
position.
-/
theorem causal_consistency_rcore [DecidableEq (Store n)] [BStepDec (lts n)]
    {p q : {cfg : Config n // GroundedOn (lts n) (fun cfg => WfCC cfg.1) cfg}}
    {l₁ l₂ : List (Transition
      {cfg : Config n // GroundedOn (lts n) (fun cfg => WfCC cfg.1) cfg} Unit)}
    (h₁ : Chained ((lts n).restrict _) p l₁ q) (h₂ : Chained ((lts n).restrict _) p l₂ q) :
    CEq ((lts n).restrict _) NoIndep p q l₁ l₂ :=
  causal_consistency_grounded (bwdDeterministicOn n) (stepClosed n) h₁ h₂

end Cslib.LTS.RCore

