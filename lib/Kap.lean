/-
Copyright (c) 2026 Liran Shaul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Liran Shaul

This file is part of the formalization project accompanying the paper:
  "Formalization in Lean of faithfully flat descent of projectivity"
  by Liran Shaul, Charles University in Prague.

We develop the Kaplansky devissage theory for modules, which is the main tool used
in Section 1 of the paper to reduce the study of projective modules to the countably
generated case. The central results are:

* `kaplansky_devissage_iff_direct_sum`: A module M over a ring R admits a Kaplansky
  devissage (an ordinal-indexed filtration whose successive quotients are countably
  generated direct summands) if and only if M is an internal direct sum of countably
  generated submodules. This formalizes Tags 058V and 058W of the Stacks Project.

* `dirsummand_of_dirSumCountable`: If M is a direct sum of countably generated
  modules, then any direct summand N of M also decomposes as a direct sum of
  countably generated modules. This is Theorem 1 of Kaplansky and Tag 058X of
  the Stacks Project, and is the main step in showing projective modules are direct
  sums of countably generated projective modules.

* `isInternal_of_filtration`: A general criterion: an ordinal-indexed filtration of
  a module P with direct complement submodules at each successor step gives an
  internal direct sum decomposition of P.

## Key Definitions

* `Submodule.IsCountablyGenerated`: A submodule N is countably generated if it has
  a countable spanning subset.
* `IsRelativeComplement`: A submodule C is a relative complement of A in B if
  A ⊕ C = B (internally).
* `KaplanskyDevissage R M S`: An ordinal-S-indexed filtration of M where each
  successive quotient is a countably generated direct summand. The index type uses
  `Set.Iio S` rather than `∀ α, α < S → ...` to avoid an unnecessary universe bump.

## References

* Kaplansky, "Projective modules", Ann. of Math. 68 (1958), Theorem 1.
* Stacks Project, Tags 058V, 058W, 058X.
-/

import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Data.Set.Countable

import Mathlib.Algebra.Module.Projective

import Mathlib.Algebra.Module.Shrink
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.Data.Fintype.Lattice


open Ordinal Submodule DirectSum Set



open LinearMap hiding id
open Finsupp




noncomputable section


variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-- A submodule N is countably generated if it has a countable subset which spans it
over R. This is the notion used throughout the Kaplansky devissage theory. -/
def Submodule.IsCountablyGenerated
  {R : Type u} {M : Type v}
  [Ring R] [AddCommGroup M] [Module R M]
  (N : Submodule R M) : Prop :=
  ∃ s : Set N, s.Countable ∧ span R s = ⊤

/-- A submodule C is a relative complement of A in B if A and C are both contained
in B, are disjoint, and together generate B (i.e., A ⊕ C = B internally). This
avoids working with quotient modules in the devissage, since we only need to handle
direct summands. -/
def IsRelativeComplement
  {R : Type u} {M : Type v}
  [Ring R] [AddCommGroup M] [Module R M]
  (A B C : Submodule R M) : Prop :=
  A ≤ B ∧ C ≤ B ∧ Disjoint A C ∧ A ⊔ C = B




universe u v w


/-- A Kaplansky devissage of an R-module M indexed by an ordinal S is an S-indexed
increasing filtration `seq : Set.Iio S → Submodule R M` satisfying:
- `seq 0 = ⊥` (starts at zero);
- `⨆ α, seq α = ⊤` (exhausts M);
- `seq` is continuous at limit ordinals;
- at each successor step `seq(succ α) / seq(α)` is a countably generated direct
  summand of M (captured via `IsRelativeComplement`).

Note: we use `seq : Set.Iio S → Submodule R M` rather than
`seq : ∀ α : Ordinal, α < S → Submodule R M` to ensure we stay at universe level w
and avoid Lean jumping from w to w+1. -/
structure KaplanskyDevissage
    (R : Type u) [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (S : Ordinal.{w}) where
  seq : Set.Iio S → Submodule R M
  monotone : ∀ α β : Set.Iio S, α ≤ β → seq α ≤ seq β
  zero_eq_bot (h : 0 < S) : seq ⟨0, h⟩ = ⊥
  union_eq_top : (⨆ α : Set.Iio S, seq α) = ⊤
  limit_continuity : ∀ α : Set.Iio S,
    Order.IsSuccLimit α.val →
    seq α = ⨆ β : {x : Set.Iio S // x.val < α.val}, seq β.val
  succ_step : ∀ (α : Ordinal.{w}) (h : Order.succ α < S),
    ∃ C : Submodule R M,
      IsRelativeComplement
        (seq ⟨α, (Order.lt_succ α).trans h⟩)
        (seq ⟨Order.succ α, h⟩)
        C ∧
      C.IsCountablyGenerated


open Classical in
/-- The main equivalence: a module M is an internal direct sum of countably generated
submodules if and only if it admits a Kaplansky devissage. This formalizes
Tags 058V and 058W of the Stacks Project.

Forward direction: given a direct sum decomposition M = ⊕ᵢ Cᵢ, we build a devissage
by filtering according to a well-ordering of the index set, taking seq(α) to be the
direct sum of the Cᵢ for i < α in the ordering.

Backward direction: given a devissage, the complements C(α) at each successor step
provide the summands of the direct sum decomposition. The independence proof uses
a finite "maximal ordinal peeling" induction: given an element in the intersection
of one summand with the join of the others, we reduce to zero by successively peeling
off the largest-ordinal contribution. -/
theorem kaplansky_devissage_iff_direct_sum
    {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] :
    (∃ (ι : Type w) (fam : ι → Submodule R M),
      DirectSum.IsInternal fam ∧ ∀ i, (fam i).IsCountablyGenerated)
    ↔
    ∃ (S : Ordinal.{w}), Nonempty (KaplanskyDevissage R M S) := by
  constructor
  · intro cond
    obtain ⟨ι, fam, interFam, allCount⟩ := cond
    let T := Ordinal.type (WellOrderingRel (α := ι))
    let S := Order.succ T
    use S
    -- seq(α) = ⊕ { fam(enum β) | β < α, β < T }
    let seq : Set.Iio S → Submodule R M := fun ⟨α, hα⟩ =>
      ⨆ (β : Ordinal) (hβ : β < α) (hβT : β < T), fam (Ordinal.enum WellOrderingRel ⟨β, hβT⟩)
    refine ⟨⟨seq, ?monotone, ?zero_eq_bot, ?union_eq_top, ?limit_continuity, ?succ_step⟩⟩
    case monotone =>
      intro α β hab
      apply iSup_mono
      intro γ
      apply iSup_mono'
      intro hγα
      exact ⟨hγα.trans_le hab, le_rfl⟩
    case zero_eq_bot =>
      intro h
      simp only [seq, Ordinal.not_lt_zero, not_false_eq_true, iSup_neg, iSup_neg, iSup_bot]
    case union_eq_top =>
      apply eq_top_iff.mpr
      rw [← DirectSum.IsInternal.submodule_iSup_eq_top interFam]
      apply iSup_le
      intro i
      -- For each index i, embed fam(i) into seq at level succ(typein i)
      let β := Ordinal.typein WellOrderingRel i
      have hβT : β < T := Ordinal.typein_lt_type WellOrderingRel i
      have hβS : Order.succ β < S := Order.succ_lt_succ hβT
      apply le_iSup_of_le ⟨Order.succ β, hβS⟩
      apply le_iSup_of_le β
      apply le_iSup_of_le (Order.lt_succ β)
      apply le_iSup_of_le hβT
      have : Ordinal.enum WellOrderingRel ⟨β, hβT⟩ = i := Ordinal.enum_typein WellOrderingRel i
      rw [this]
    case limit_continuity =>
      intro α hLimit
      apply le_antisymm
      · -- seq α ≤ ⨆ β < α, seq β: for each γ < α, find β with γ < β < α using limit hypothesis
        apply iSup_le
        intro γ
        apply iSup_le
        intro hγα
        apply iSup_le
        intro hγT
        have hSucc : Order.succ γ < α.val := hLimit.succ_lt hγα
        have hSuccS : Order.succ γ < S := hSucc.trans α.prop
        apply le_iSup_of_le ⟨⟨Order.succ γ, hSuccS⟩, hSucc⟩
        apply le_iSup_of_le γ
        apply le_iSup_of_le (Order.lt_succ γ)
        apply le_iSup_of_le hγT
        exact le_refl _
      · -- ⨆ β < α, seq β ≤ seq α: straightforward by monotonicity
        apply iSup_le
        intro ⟨β, hβα⟩
        apply iSup_le
        intro γ
        apply iSup_le
        intro hγβ
        apply iSup_le
        intro hγT
        apply le_iSup_of_le γ
        apply le_iSup_of_le (hγβ.trans hβα)
        apply le_iSup_of_le hγT
        exact le_refl _
    case succ_step =>
      intro α hSuccS
      by_cases hαT : α < T
      · -- α < T: the complement is fam(enum α), the next summand in the well-ordering
        use fam (Ordinal.enum WellOrderingRel ⟨α, hαT⟩)
        constructor
        · refine ⟨?_, ?_, ?_, ?_⟩
          · -- seq α ≤ seq(succ α): monotonicity
            apply iSup_le
            intro β
            apply iSup_le
            intro hβα
            apply iSup_le
            intro hβT
            apply le_iSup_of_le β
            apply le_iSup_of_le (hβα.trans (Order.lt_succ α))
            apply le_iSup_of_le hβT
            exact le_refl _
          · -- fam(enum α) ≤ seq(succ α)
            apply le_iSup_of_le α
            apply le_iSup_of_le (Order.lt_succ α)
            apply le_iSup_of_le hαT
            exact le_refl _
          · -- Disjoint(seq α, fam(enum α)): follows from iSupIndep of the original fam
            rw [disjoint_iff]
            apply eq_bot_iff.mpr
            intro x ⟨hxSeq, hxFam⟩
            have indep : iSupIndep fam := DirectSum.IsInternal.submodule_iSupIndep interFam
            -- The indices below α form a set s not containing enum(α)
            let s : Set ι := { i | ∃ (β : Ordinal)
              (hβα : β < α) (hβT : β < T), i = Ordinal.enum WellOrderingRel ⟨β, hβT⟩ }
            have hαNotInS : Ordinal.enum WellOrderingRel ⟨α, hαT⟩ ∉ s := by
              intro ⟨β, hβα, hβT, hEq⟩
              have : (⟨β, hβT⟩ : Set.Iio T) = ⟨α, hαT⟩ := by
                rw [← Ordinal.enum_inj]
                exact hEq.symm
              simp only [Subtype.mk.injEq] at this
              exact (ne_of_lt hβα) this
            have hSeqLe : seq ⟨α, (Order.lt_succ α).trans hSuccS⟩ ≤ ⨆ i ∈ s, fam i := by
              apply iSup_le; intro β; apply iSup_le; intro hβα; apply iSup_le; intro hβT
              apply le_biSup (f := fam)
              exact ⟨β, hβα, hβT, rfl⟩
            have hDisj := indep.disjoint_biSup hαNotInS
            have hxBiSup : x ∈ ⨆ i ∈ s, fam i := hSeqLe hxSeq
            rw [disjoint_iff] at hDisj
            have : x ∈ fam (Ordinal.enum WellOrderingRel ⟨α, hαT⟩) ⊓ ⨆ i ∈ s,
              fam i := ⟨hxFam, hxBiSup⟩
            rw [hDisj] at this
            exact this
          · -- seq α ⊔ fam(enum α) = seq(succ α): split by β < α or β = α
            apply le_antisymm
            · apply sup_le
              · apply iSup_le; intro β; apply iSup_le; intro hβα; apply iSup_le; intro hβT
                apply le_iSup_of_le β
                apply le_iSup_of_le (hβα.trans (Order.lt_succ α))
                apply le_iSup_of_le hβT
                exact le_refl _
              · apply le_iSup_of_le α
                apply le_iSup_of_le (Order.lt_succ α)
                apply le_iSup_of_le hαT
                exact le_refl _
            · apply iSup_le; intro β; apply iSup_le; intro hβSucc; apply iSup_le; intro hβT
              have hβα : β ≤ α := Order.lt_succ_iff.mp hβSucc
              rcases hβα.lt_or_eq with hβα_lt | hβα_eq
              · apply le_sup_of_le_left
                apply le_iSup_of_le β
                apply le_iSup_of_le hβα_lt
                apply le_iSup_of_le hβT
                exact le_refl _
              · apply le_sup_of_le_right
                subst hβα_eq
                exact le_refl _
        · exact allCount _
      · -- α ≥ T: then succ α ≥ S = succ T, contradiction with hSuccS < S
        exfalso
        have hαT' : T ≤ α := not_lt.mp hαT
        have : S ≤ Order.succ α := Order.succ_le_succ hαT'
        exact not_lt.mpr this hSuccS
  · intro cond
    obtain ⟨S, KapEx⟩ := cond
    let Kap := KapEx.some
    -- The index type for the direct sum: successor ordinals strictly below S
    let ι' := { α : Ordinal // Order.succ α < S }
    -- ι' is small at universe w, inherited from the smallness of Set.Iio S
    have small_ι' : Small.{w} ι' := by
      have h1 : Small.{w} (Set.Iio S) := Ordinal.small_Iio S
      let f : ι' → Set.Iio S := fun x => ⟨x.val, (Order.lt_succ x.val).trans x.prop⟩
      have hf : Function.Injective f := fun a b h => by
        simp only [Subtype.mk.injEq, f] at h
        exact Subtype.ext h
      exact small_of_injective hf
    let ι := Shrink.{w} ι'
    -- fam': for each α with succ α < S, the complement at step α from the devissage
    let fam' : ι' → Submodule R M := fun ⟨α, hα⟩ =>
      (Kap.succ_step α hα).choose
    let fam : ι → Submodule R M := fam' ∘ (equivShrink ι').symm
    refine ⟨ι, fam, ?_, ?_⟩
    · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
      constructor

      · -- Independence of fam: we first prove it for fam' (over ι'), then transport
        --  along the equivalence equivShrink ι'.
        classical

        have hind' : iSupIndep fam' := by
          intro i0
          rw [disjoint_iff]
          apply eq_bot_iff.mpr
          intro x hx
          rcases hx with ⟨hx0, hxrest⟩

-- Step A: extract a finite set of indices t ⊆ ι' \ {i0} witnessing x ∈ ⨆ j ∈ t, fam' j.
-- We use `Submodule.mem_span_finite_of_mem_span` to reduce the infinite join to a finite one.
          let Others : Submodule R M := ⨆ j : {j // j ≠ i0}, fam' j.1
          have hxOthers : x ∈ Others := by
            simp only [Others]
            simp only [iSup_subtype'] at hxrest
            exact hxrest

          have hOthers_eq_span :
              Others = Submodule.span R (⋃ j : {j // j ≠ i0}, (fam' j.1 : Set M)) := by
              exact Submodule.iSup_eq_span _

          have hFinSup : ∃ (t : Finset ι'), i0 ∉ t ∧ x ∈ ⨆ j ∈ t, fam' j := by
            rw [hOthers_eq_span] at hxOthers
            obtain ⟨T, hTsub, hxT⟩ := Submodule.mem_span_finite_of_mem_span hxOthers
            have hmem : ∀ m ∈ T, ∃ j : {j : ι' // j ≠ i0}, m ∈ fam' j.1 := by
              intro m hm
              have : m ∈ ⋃ j : {j // j ≠ i0}, (fam' j.1 : Set M) := hTsub hm
              simp only [Set.mem_iUnion] at this
              exact this
            choose f hf using hmem
            let t : Finset ι' := T.attach.image (fun ⟨m, hm⟩ => (f m hm).1)
            refine ⟨t, ?_, ?_⟩
            · simp only [t, Finset.mem_image, Finset.mem_attach,
              true_and, Subtype.exists, not_exists]
              intro m hm h
              exact (f m hm).2 h
            · apply Submodule.span_le.mpr _ hxT
              intro m hm
              have hfm := hf m hm
              have hidx : (f m hm).1 ∈ t := by
                simp only [t, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
                exact ⟨m, hm, rfl⟩
              exact le_biSup (f := fam') hidx hfm

          obtain ⟨t, ht0, hx_t⟩ := hFinSup

          -- Step B: prove x = 0 by "maximal ordinal peeling" on t.
          -- At each step we show the contribution from the largest-ordinal index in t is zero,
          -- using disjointness from the devissage filtration, then reduce to a smaller t.
          let ord : ι' → Ordinal := fun j => j.val

          by_cases ht : t = ∅
          · subst ht
            simp only [Finset.notMem_empty, iSup_false, iSup_bot] at hx_t
            exact hx_t
          · obtain ⟨jmax, hjmax_t, hjmax_max⟩ :
                ∃ jmax : ι', jmax ∈ t ∧ ∀ j ∈ t, ord j ≤ ord jmax :=
              Finset.exists_max_image t ord (Finset.nonempty_iff_ne_empty.mpr ht)

            have : x = 0 := by
              let α0 := i0.val
              have prop0 := (Kap.succ_step α0 i0.prop).choose_spec.1
              have hfam0_disj : Disjoint (Kap.seq ⟨α0, (Order.lt_succ α0).trans i0.prop⟩)
                (fam' i0) :=
                prop0.2.2.1
              have hfam0_le : fam' i0 ≤ Kap.seq ⟨Order.succ α0, i0.prop⟩ := prop0.2.1

              -- x ∈ fam' i0 ≤ seq(succ α0)
              have hx_seq : x ∈ Kap.seq ⟨Order.succ α0, i0.prop⟩ := hfam0_le hx0

              -- Key claim: (⨆ j ∈ t, fam' j) ⊓ seq(succ α0) ≤ seq(α0).
              -- Indices below α0 contribute to seq(α0), indices above α0 are disjoint from
              -- seq(succ α0) by the devissage, so they contribute 0.
              have hclaim : (⨆ j ∈ t, fam' j) ⊓ Kap.seq ⟨Order.succ α0, i0.prop⟩ ≤
                  Kap.seq ⟨α0, (Order.lt_succ α0).trans i0.prop⟩ := by
                intro y ⟨hy_sup, hy_seq⟩

                let t_low := t.filter (fun j => ord j < ord i0)
                let t_high := t.filter (fun j => ord j > ord i0)

                -- Low indices: their complements lie below seq(α0)
                have hlow : ∀ j ∈ t_low, fam' j ≤
                  Kap.seq ⟨α0, (Order.lt_succ α0).trans i0.prop⟩ := by
                  intro j hj
                  simp only [Finset.mem_filter, t_low] at hj
                  obtain ⟨_, hord_lt⟩ := hj
                  let αj := j.val
                  have propj := (Kap.succ_step αj j.prop).choose_spec.1
                  have h1 : fam' j ≤ Kap.seq ⟨Order.succ αj, j.prop⟩ := propj.2.1
                  have h2 : Order.succ αj ≤ α0 := Order.succ_le_of_lt hord_lt
                  exact h1.trans (Kap.monotone _ _ h2)

                -- High indices: their complements are disjoint from seq(succ α0)
                have hhigh : ∀ j ∈ t_high, fam' j ⊓ Kap.seq ⟨Order.succ α0, i0.prop⟩ = ⊥ := by
                  intro j hj
                  simp only [Finset.mem_filter, t_high] at hj
                  obtain ⟨_, hord_gt⟩ := hj
                  let αj := j.val
                  have propj := (Kap.succ_step αj j.prop).choose_spec.1
                  have hfamj_disj : Disjoint (Kap.seq ⟨αj, (Order.lt_succ αj).trans j.prop⟩)
                    (fam' j) :=
                    propj.2.2.1
                  have h1 : Order.succ α0 ≤ αj := Order.succ_le_of_lt hord_gt
                  have h2 : Kap.seq ⟨Order.succ α0, i0.prop⟩ ≤
                      Kap.seq ⟨αj, (Order.lt_succ αj).trans j.prop⟩ := Kap.monotone _ _ h1
                  apply eq_bot_iff.mpr
                  calc fam' j ⊓ Kap.seq ⟨Order.succ α0, i0.prop⟩
                      ≤ fam' j ⊓ Kap.seq ⟨αj, (Order.lt_succ αj).trans j.prop⟩ :=
                        inf_le_inf_left _ h2
                    _ ≤ Kap.seq ⟨αj, (Order.lt_succ αj).trans j.prop⟩ ⊓ fam' j := by rw [inf_comm]
                    _ = ⊥ := hfamj_disj.eq_bot

                -- t splits into t_low ∪ t_high since i0 ∉ t
                have ht_split : t = t_low ∪ t_high := by
                  ext j
                  simp only [Finset.mem_union, Finset.mem_filter, t_low, t_high]
                  constructor
                  · intro hj
                    have hjne : j ≠ i0 := fun h => ht0 (h ▸ hj)
                    have hord_ne : ord j ≠ ord i0 := fun h => hjne (Subtype.ext h)
                    rcases hord_ne.lt_or_gt with hlt | hgt
                    · left; exact ⟨hj, hlt⟩
                    · right; exact ⟨hj, hgt⟩
                  · intro h
                    rcases h with ⟨hj, _⟩ | ⟨hj, _⟩ <;> exact hj

                rw [ht_split] at hy_sup
                rw [Finset.iSup_union] at hy_sup
                simp only [SetLike.mem_coe] at hy_sup
                rw [Submodule.mem_sup] at hy_sup
                obtain ⟨y_low, hy_low, y_high, hy_high, hy_eq⟩ := hy_sup

                have hy_low_seq : y_low ∈ Kap.seq ⟨α0, (Order.lt_succ α0).trans i0.prop⟩ := by
                  have : (⨆ j ∈ t_low, fam' j) ≤
                    Kap.seq ⟨α0, (Order.lt_succ α0).trans i0.prop⟩ := by
                    apply iSup₂_le
                    intro j hj
                    exact hlow j hj
                  exact this hy_low

                -- y_high ∈ (⨆ j ∈ t_high, fam' j) ⊓ seq(succ α0) = ⊥, proved by induction
                -- on cardinality of t_high using maximal-ordinal peeling
                have hy_high_zero : y_high = 0 := by
                  have hy_low_seq' : y_low ∈ Kap.seq ⟨Order.succ α0, i0.prop⟩ :=
                    Kap.monotone _ _ (Order.le_succ α0) hy_low_seq
                  have hy_high_seq : y_high ∈ Kap.seq ⟨Order.succ α0, i0.prop⟩ := by
                    have hy_sum : y_low + y_high ∈ Kap.seq ⟨Order.succ α0, i0.prop⟩ :=
                      hy_eq ▸ hy_seq
                    have : y_high = (y_low + y_high) - y_low := by simp only [add_sub_cancel_left]
                    rw [this]
                    exact Submodule.sub_mem _ hy_sum hy_low_seq'
                  have hbot : (⨆ j ∈ t_high, fam' j) ⊓ Kap.seq ⟨Order.succ α0, i0.prop⟩ = ⊥ := by
                    rw [eq_bot_iff]
                    intro z hz
                    rw [Submodule.mem_inf] at hz
                    obtain ⟨hz_sup, hz_seq⟩ := hz
                    rw [← Finset.sup_eq_iSup] at hz_sup

                    suffices key : ∀ s : Finset ι', s ⊆ t_high →
                        ∀ w, w ∈ s.sup fam' → w ∈ Kap.seq ⟨Order.succ α0, i0.prop⟩ → w = 0 by
                      exact key t_high (Finset.Subset.refl _) z hz_sup hz_seq

                    -- Induction on the cardinality of s: at each step, peel off the
                    -- maximal-ordinal element of s using devissage disjointness.
                    intro s hs
                    induction hn : s.card generalizing s with
                    | zero =>
                      intro w hw _
                      rw [Finset.card_eq_zero] at hn
                      simp only [hn, Finset.sup_empty, Submodule.mem_bot] at hw
                      exact hw
                    | succ n ih_card =>
                      intro w hw hw_seq

                      have hs_nonempty : s.Nonempty := Finset.card_pos.mp (by omega)
                      obtain ⟨jmax, hjmax_in, hjmax_max⟩ :=
                        Finset.exists_max_image s (fun j => j.val) hs_nonempty

                      have hjmax_high : jmax ∈ t_high := hs hjmax_in

                      have hjmax_prop := (Kap.succ_step jmax.val jmax.prop).choose_spec.1
                      have hjmax_disj : Disjoint (Kap.seq ⟨jmax.val, _⟩)
                        (fam' jmax) := hjmax_prop.2.2.1
                      have hjmax_le : fam' jmax ≤
                        Kap.seq ⟨Order.succ jmax.val, jmax.prop⟩ := hjmax_prop.2.1

                      have hord_jmax : Order.succ α0 ≤ jmax.val := by
                        have hmem := Finset.mem_filter.mp (hs hjmax_in)
                        exact Order.succ_le_of_lt hmem.2

                      have hjmax_val_lt_S : jmax.val < S := (Order.lt_succ jmax.val).trans jmax.prop

                      have hK_le_jmax : Kap.seq ⟨Order.succ α0, i0.prop⟩ ≤
                        Kap.seq ⟨jmax.val, hjmax_val_lt_S⟩ :=
                        Kap.monotone _ _ hord_jmax

                      -- Peel off jmax from s: define s' = s \ {jmax}
                      let s' := s.erase jmax
                      have hs'_card : s'.card = n := by
                        rw [Finset.card_erase_of_mem hjmax_in]; omega
                      have hs'_sub : s' ⊆ t_high := fun x hx => hs (Finset.mem_of_mem_erase hx)

                      have hs_eq : s = insert jmax s' := by
                        ext x
                        simp only [Finset.mem_insert, Finset.mem_erase, s']
                        constructor
                        · intro hx
                          by_cases hxj : x = jmax
                          · left; exact hxj
                          · right; exact ⟨hxj, hx⟩
                        · intro hx
                          rcases hx with rfl | ⟨_, hx⟩
                          · exact hjmax_in
                          · exact hx

                      rw [hs_eq, Finset.sup_insert] at hw
                      rw [Submodule.mem_sup] at hw
                      obtain ⟨wmax, hwmax, ws', hws', hw_eq⟩ := hw

                      -- All elements of s' have ordinal < jmax, so fam' j ≤ seq(jmax)
                      have hws'_in_jmax : ws' ∈ Kap.seq ⟨jmax.val, hjmax_val_lt_S⟩ := by
                        have hsup_le : s'.sup fam' ≤ Kap.seq ⟨jmax.val, hjmax_val_lt_S⟩ := by
                          apply Finset.sup_le
                          intro j hj
                          have hj_in_s : j ∈ s := Finset.mem_of_mem_erase hj
                          have hj_ne_jmax : j ≠ jmax := Finset.ne_of_mem_erase hj
                          have hj_le : j.val ≤ jmax.val := hjmax_max j hj_in_s
                          have hj_lt : j.val < jmax.val := lt_of_le_of_ne hj_le
                            (fun h => hj_ne_jmax (Subtype.ext h))
                          have hsucc_le : Order.succ j.val ≤ jmax.val := Order.succ_le_of_lt hj_lt
                          have hj_prop := (Kap.succ_step j.val j.prop).choose_spec.1
                          have hfamj_le : fam' j ≤ Kap.seq ⟨Order.succ j.val, j.prop⟩ := hj_prop.2.1
                          have hseq_le : Kap.seq ⟨Order.succ j.val, j.prop⟩ ≤
                            Kap.seq ⟨jmax.val, hjmax_val_lt_S⟩ :=
                            Kap.monotone _ _ hsucc_le
                          exact hfamj_le.trans hseq_le
                        exact hsup_le hws'
                      have hw_in_jmax : w ∈ Kap.seq ⟨jmax.val, _⟩ := hK_le_jmax hw_seq

                      -- wmax ∈ fam'(jmax) ∩ seq(jmax) = ⊥, so wmax = 0
                      have hwmax_in_jmax : wmax ∈ Kap.seq ⟨jmax.val, hjmax_val_lt_S⟩ := by
                        rw [← hw_eq] at hw_in_jmax
                        exact Submodule.sub_mem _ hw_in_jmax hws'_in_jmax |> fun h => by
                          simp only [add_sub_cancel_right] at h
                          exact h
                      have hwmax_zero : wmax = 0 := by
                        have hmem : wmax ∈ fam' jmax ⊓ Kap.seq ⟨jmax.val, hjmax_val_lt_S⟩ :=
                           ⟨hwmax, hwmax_in_jmax⟩
                        rw [inf_comm, hjmax_disj.eq_bot] at hmem
                        exact hmem
                      have hw_eq' : w = ws' := by rw[← hw_eq, hwmax_zero, zero_add]

                      -- Apply IH to s' (which has cardinality n)
                      rw [hw_eq']
                      have hws'_zero : ws' = 0 :=
                        ih_card s' hs'_sub hs'_card ws' hws' (hw_eq' ▸ hw_seq)
                      rw [hws'_zero]
                  have : y_high ∈ (⨆ j ∈ t_high, fam' j) ⊓ Kap.seq ⟨Order.succ α0, i0.prop⟩ :=
                    ⟨hy_high, hy_high_seq⟩
                  rw [hbot] at this
                  exact this

                rw [← hy_eq, hy_high_zero, add_zero]
                exact hy_low_seq

              -- x ∈ fam' i0 ∩ seq(α0) = ⊥ by the devissage disjointness condition
              have hx_in_seq0 : x ∈ Kap.seq ⟨α0, (Order.lt_succ α0).trans i0.prop⟩ :=
                hclaim ⟨hx_t, hx_seq⟩
              have : x ∈ Kap.seq ⟨α0, (Order.lt_succ α0).trans i0.prop⟩ ⊓ fam' i0 :=
                ⟨hx_in_seq0, hx0⟩
              rw [hfam0_disj.eq_bot] at this
              exact this

            exact this

        -- Transport iSupIndep from fam' to fam along the shrink equivalence
        have hind : iSupIndep fam := by
          have hinj : Function.Injective (equivShrink ι').symm := (equivShrink ι').symm.injective
          exact hind'.comp hinj

        exact hind


      · -- iSup fam = ⊤: induction on ordinals, using limit continuity and succ_step
        rw [eq_top_iff, ← Kap.union_eq_top]
        apply iSup_le
        intro ⟨α, hαS⟩
        induction α using Ordinal.induction with
        | h β ih =>
          by_cases hβ0 : β = 0
          · subst hβ0
            rw [Kap.zero_eq_bot hαS]
            exact bot_le
          · by_cases hLimit : Order.IsSuccLimit β
            · rw [Kap.limit_continuity ⟨β, hαS⟩ hLimit]
              apply iSup_le
              intro ⟨⟨γ, hγS⟩, hγβ⟩
              exact ih γ hγβ hγS
            · -- β is a successor: extract predecessor and apply succ_step
              have hSucc : ∃ γ, β = Order.succ γ := by
                have hNotMin : ¬IsMin β := by
                  simp only [isMin_iff_eq_bot, bot_eq_zero']
                  exact hβ0
                have hNotPrelimit : ¬Order.IsSuccPrelimit β := fun hp => hLimit ⟨hNotMin, hp⟩
                simp only [Order.IsSuccPrelimit, not_forall] at hNotPrelimit
                obtain ⟨γ, hγ⟩ := hNotPrelimit
                push_neg at hγ
                exact ⟨γ, (Order.succ_eq_of_covBy hγ).symm⟩
              obtain ⟨γ, rfl⟩ := hSucc
              have hγS : γ < S := (Order.lt_succ γ).trans hαS
              have key := (Kap.succ_step γ hαS).choose_spec.1
              rw [← key.2.2.2]
              apply sup_le
              · exact ih γ (Order.lt_succ γ) hγS
              · -- fam'(γ) = fam(equivShrink(γ)) ≤ ⨆ i, fam i
                let idx : ι' := ⟨γ, hαS⟩
                have : (Kap.succ_step γ hαS).choose = fam' idx := rfl
                rw [this]
                calc fam' idx
                    = fam ((equivShrink ι') idx) := by simp [fam]
                  _ ≤ ⨆ i, fam i := le_iSup fam _
    · intro i
      simp only [fam, fam', Function.comp_apply]
      exact ((Kap.succ_step _ _).choose_spec).2



/-- If U is a submodule that is "closed under components" — meaning that for any x ∈ U,
whenever a component `comp k (p x)` or `comp k (q x)` is nonzero then fam(k) ≤ U —
then U equals the join of exactly those summands fam(k) that it contains.

This is an abstract version of the key step in the Kaplansky devissage construction
for direct summands: a submodule that is stable under both projections of a
splitting M = N ⊕ K is automatically a union of full summands from the decomposition. -/
lemma submodule_eq_iSup_of_closed_under_components
    {ι : Type w} (fam : ι → Submodule R M)
    (comp : ι → M →ₗ[R] M)
    (hcomp_mem : ∀ i x, comp i x ∈ fam i)
    (hsum :
      ∀ x : M, ∃ s : Finset ι, x = ∑ i ∈ s, comp i x)
    (p q : M →ₗ[R] M)
    (hpq : ∀ x : M, x = p x + q x)
    (U : Submodule R M)
    (hclosed :
      ∀ x : M, x ∈ U → ∀ i : ι,
        (comp i (p x) ≠ 0 ∨ comp i (q x) ≠ 0) → fam i ≤ U) :
    U = ⨆ i : {i // fam i ≤ U}, fam i.1 := by
  apply Submodule.ext_iff.mpr
  intro x
  constructor
  · intro xinU
    obtain ⟨s,sum⟩ := hsum x
    suffices hterm :  ∀ i : ι, i ∈ s → (comp i) x ≠ 0 →
    (comp i) x ∈ ⨆ i : {i // fam i ≤ U}, fam i.1 by
      rw[sum]
      apply Submodule.sum_mem
      intro i hi
      by_cases h : (comp i) x = 0
      · simp only [h]
        apply zero_mem
      · exact hterm i hi h
    intro i iins compnz
    have t1: (comp i) x ∈ fam i := by apply hcomp_mem

    have : (comp i) (p x) ≠ 0 ∨ (comp i) (q x) ≠ 0 := by
      by_contra h
      push_neg at h
      obtain ⟨h1,h2⟩ := h
      have : x = (p x) + (q x) := hpq x
      rw[this,map_add,h1,h2,add_zero] at compnz
      contradiction

    have h_incl : fam i ≤ U := by apply hclosed x xinU i this
    let i_subtype : { i // fam i ≤ U } := ⟨i, h_incl⟩
    exact Submodule.mem_iSup_of_mem i_subtype t1

  · intro xin
    rw[Submodule.mem_iSup_iff_exists_finset] at xin
    obtain ⟨s,xinp⟩ := xin
    rw[Submodule.mem_iSup_finset_iff_exists_sum] at xinp
    obtain ⟨μ,sum⟩ := xinp
    rw[←sum]
    suffices prop1 : ∀ i: s, (μ i).val ∈ U by
      refine Submodule.sum_mem U ?_
      intro i iins
      exact prop1 ⟨i, iins⟩
    intro i
    have prop1: fam (i.val) ≤ U := by exact i.1.2
    have prop2 : ((μ i : fam (↑i : ι)) : M) ∈ fam (↑i : ι) := by exact (μ i).property
    exact prop1 prop2



-- The following theorem has a large heartbeat budget due to the extensive transfinite
-- construction involving repeated unfolding of `Ordinal.limitRecOn`, nested inductions,
-- and substantial manipulation of `DirectSum`/`DFinsupp` infrastructure.
/- If M is an internal direct sum of countably generated submodules and N is a direct
summand of M (i.e., there are maps i : N → M and π : M → N with π ∘ i = id), then
N is also a direct sum of countably generated submodules. This is Theorem 1 of Kaplansky
and Tag 058X of the Stacks Project.

The proof constructs a Kaplansky devissage for N by transfinite recursion on the
well-ordering of the index set ι. At each successor step, we choose the least index
not yet consumed (with respect to a well-ordering), then enlarge the current submodule
by all summands fam(k) whose "components" (with respect to the projections p = i ∘ π
and q = id - i ∘ π) are touched by the new summand or any summand already included.
This enlargement is countable, ensuring that each successive quotient is countably
generated. The stability of the construction under both projections (recorded in the
`PQ` predicate) is what allows the filtration to restrict to a filtration of N. -/
set_option maxHeartbeats 800000 in -- see above for explantion about heartbeats
open Classical in
theorem dirsummand_of_dirSumCountable {R : Type u} [Ring R]
    {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (exDecom : ∃ (ι : Type w) (fam : ι → Submodule R M),
      DirectSum.IsInternal fam ∧ ∀ i, (fam i).IsCountablyGenerated)
    (i : N →ₗ[R] M) (π : M →ₗ[R] N) (hπi : π.comp i = LinearMap.id) :
    ∃ (κ : Type w) (fam' : κ → Submodule R N),
      DirectSum.IsInternal fam' ∧ ∀ j, (fam' j).IsCountablyGenerated := by

obtain ⟨ι, fam, interFam, allCount⟩ := exDecom
let T := Ordinal.type (WellOrderingRel (α := ι))
let S := Order.succ T
suffices Nonempty (KaplanskyDevissage R N S) by
  exact kaplansky_devissage_iff_direct_sum.mpr ⟨S, this⟩

  -- Define Nseq(α) = (Mseq α).comap i, where Mseq(α) = ⊕ { fam(enum β) | β ∈ consumed(α) }
  -- and consumed(α) is built by transfinite recursion, adding one new "Binf" set at each step.

let equiv := LinearEquiv.ofBijective (DirectSum.coeLinearMap fam) interFam

-- comp k x is the k-th component of x in the direct sum decomposition
let comp : ι → M →ₗ[R] M := fun k =>
  (fam k).subtype.comp ((DirectSum.component R ι (fun i => ↥(fam i)) k).comp equiv.symm.toLinearMap)

have hcomp_mem : ∀ k x, comp k x ∈ fam k := by
  intro k x
  exact (DirectSum.component R ι (fun i => ↥(fam i)) k (equiv.symm x)).property

-- Different summands have disjoint supports: comp k x = 0 when x ∈ fam j, j ≠ k
have hcomp_proj : ∀ k j : ι, k ≠ j → ∀ x ∈ fam j, comp k x = 0 := by
  intro k j hkj x hx
  simp only [comp, LinearMap.comp_apply, Submodule.subtype_apply]
  suffices h : (DirectSum.component R ι (fun i => ↥(fam i)) k) (equiv.symm x) = 0 by
    simp[h]
  have key : equiv.symm x = DirectSum.of (fun i => ↥(fam i)) j ⟨x, hx⟩ := by
    apply equiv.injective
    simp only [LinearEquiv.apply_symm_apply, equiv, LinearEquiv.ofBijective_apply,
      DirectSum.coeLinearMap_of]

  rw [key]
  have : (DirectSum.of (fun i => ↥(fam i)) j ⟨x, hx⟩) k = 0 :=
    DFinsupp.single_eq_of_ne (Ne.symm hkj.symm)
  exact this

-- Any x ∈ M equals the finite sum of its components (from the direct sum structure)
have hsum : ∀ x, ∃ s : Finset ι, x = ∑ i ∈ s, comp i x := by
  intro x
  use (equiv.symm x).support
  have hx_eq : x = (DirectSum.coeLinearMap fam) (equiv.symm x) := by
    exact (equiv.apply_symm_apply x).symm
  let f := equiv.symm x
  conv_lhs => rw [hx_eq]
  change _ = ∑ k ∈ f.support, (fam k).subtype ((f : Π₀ i, ↥(fam i)) k)
  rw [show (DirectSum.coeLinearMap fam) f =
    (DFinsupp.sumAddHom (fun i => (fam i).subtype)) f from rfl]
  rw [DFinsupp.sumAddHom_apply]
  rfl

let supp : M → Finset ι := fun x => Classical.choose (hsum x)
have hsupp : ∀ x : M, x = ∑ k ∈ supp x, comp k x := fun x => Classical.choose_spec (hsum x)

-- supp x contains every k with comp k x ≠ 0
have hsupp_complete : ∀ x k, comp k x ≠ 0 → k ∈ supp x := by
  intro x k hne
  by_contra hk
  have := hsupp x
  have hck : comp k x = ∑ i ∈ supp x, comp k (comp i x) := by
    conv_lhs => rw [this]
    rw [map_sum]
  have hzero : ∀ i ∈ supp x, comp k (comp i x) = 0 := by
    intro i hi
    by_cases hik : k = i
    · exact absurd (hik ▸ hi) hk
    · exact hcomp_proj k i hik _ (hcomp_mem i x)
  rw [Finset.sum_eq_zero hzero] at hck
  exact hne hck

-- p = i ∘ π is the projection of M onto the image of N;
-- q = id - i ∘ π is the complementary projection onto the kernel of π
let p : M →ₗ[R] M := i ∘ₗ π
let q : M →ₗ[R] M := LinearMap.id - i ∘ₗ π

have hpq : ∀ x : M, x = p x + q x := by
  intro x
  simp only [p, q, sub_eq_add_neg,coe_comp,
  Function.comp_apply, LinearMap.add_apply, id_coe, id_eq, LinearMap.neg_apply,
  add_neg_cancel_comm_assoc]

-- A State records the set of consumed indices C, the corresponding submodule Mα = ⊕_{k∈C} fam k,
-- and stability under both projections p and q.
let State :=
    {data : (Set ι) × (Submodule R M) //
      let C := data.1
      let Mα := data.2
      C.Countable ∧
      Mα = ⨆ k ∈ C, fam k ∧
      (∀ x : M, x ∈ Mα → p x ∈ Mα) ∧
      (∀ x : M, x ∈ Mα → q x ∈ Mα)}


-- succCase: the successor step of the transfinite construction.
-- If the current Mα = ⊤ we stop. Otherwise, we pick the least unconsumed index j
-- and add all indices "touched" by j (iterating through p and q components) to
-- form a countable enlargement Binf. The new state C' = C ∪ Binf remains countable
-- and the corresponding submodule is stable under both p and q.
let succCase :
      (α : Ordinal.{w}) → State → State := by
  intro α st
  let C := st.1.1
  let Mα := st.1.2
  have hC_countable : C.Countable := st.2.1
  have hMα_eq : Mα = ⨆ k ∈ C, fam k := st.2.2.1
  have pstableα : ∀ x : M, x ∈ Mα → p x ∈ Mα := st.2.2.2.1
  have qstableα : ∀ x : M, x ∈ Mα → q x ∈ Mα := st.2.2.2.2

  by_cases htop : Mα = ⊤
  · exact ⟨⟨C, Mα⟩, hC_countable, hMα_eq, pstableα, qstableα⟩
  · let Bad : Set ι := {j | ¬ fam j ≤ Mα}
    have hBad : Bad.Nonempty := by
      by_contra h
      push_neg at h
      have : ∀ j: ι, fam j ≤ Mα := by
        intro j
        by_contra h'
        have : j ∈ Bad := by apply h'
        rw[h] at this
        contradiction
      have misall: Mα = ⊤ := by
        have : ⨆ j, fam j ≤ Mα := iSup_le this
        rw [DirectSum.IsInternal.submodule_iSup_eq_top interFam] at this
        exact top_le_iff.mp this
      contradiction
    -- j: the least unconsumed index in the well-ordering on ι
    let j : ι := WellFounded.min (IsWellFounded.wf (r := WellOrderingRel)) Bad hBad
    have hj_not_le : ¬ fam j ≤ Mα := by
      have : j ∈ Bad := by exact WellFounded.min_mem IsWellFounded.wf Bad hBad
      exact this
    let Nj : Submodule R M := fam j
    have NjCount : Nj.IsCountablyGenerated := allCount j
    let genSet : Set Nj := Classical.choose NjCount
    have hgen_count : genSet.Countable := (Classical.choose_spec NjCount).1
    have hgen_span : Submodule.span R genSet = ⊤ := (Classical.choose_spec NjCount).2

    -- Bstep: one step of the component-closure operation
    let Bstep : Set ι → Set ι := fun B =>
      B ∪ {k : ι | ∃ i ∈ B, ∃ x ∈ fam i, comp k (p x) ≠ 0 ∨ comp k (q x) ≠ 0}

    -- B n: the n-th iterate of Bstep starting from {j}
    let B0 : Set ι := {j}
    let B : ℕ → Set ι := Nat.rec B0 (fun _n Bn => Bstep Bn)

    -- Binf: the closure of {j} under the component operation for both p and q
    let Binf : Set ι := ⋃ n : ℕ, B n

    let U : Submodule R M := Mα ⊔ (⨆ k ∈ Binf, fam k)

    -- Any element of Mα has zero component outside Mα, since Mα is a union of summands
    have hMα_comp_zero : ∀ w ∈ Mα, ∀ k' : ι, ¬(fam k' ≤ Mα) → comp k' w = 0 := by
      intro w hw k' hk'
      rw [hMα_eq, Submodule.iSup_eq_span] at hw
      refine Submodule.span_induction (p := fun x _ => comp k' x = 0) ?_ ?_ ?_ ?_ hw
      · intro x hx
        simp only [Set.mem_iUnion] at hx
        obtain ⟨k, hxk⟩ := hx
        by_cases hkC : k ∈ C
        · simp only [iSup_pos hkC] at hxk
          have hkle : fam k ≤ Mα := by rw [hMα_eq]; exact le_biSup (f := fam) hkC
          have hne : k' ≠ k := fun h => hk' (h ▸ hkle)
          exact hcomp_proj k' k hne x hxk
        · simp only [iSup_neg hkC] at hxk
          rw [hxk, map_zero]
      · simp only [map_zero]
      · intro x y _ _ hx hy
        simp only [map_add, hx, hy, add_zero]
      · intro r x _ hx
        simp only [map_smul, hx, smul_zero]


    -- Binf is countable: each B n is countable (proved by induction),
    -- and Binf is a countable union of countable sets.
    have hBinf_countable : Binf.Countable := by
      apply Set.countable_iUnion
      intro n
      induction n with
      | zero =>
        exact Set.countable_singleton j
      | succ n ih =>
        apply Set.Countable.union ih
        have heq : {k | ∃ i ∈ B n, ∃ x ∈ fam i, comp k (p x) ≠ 0 ∨ comp k (q x) ≠ 0} =
            ⋃ (i : ι) (_ : i ∈ B n), {k | ∃ x ∈ fam i, comp k (p x) ≠ 0 ∨ comp k (q x) ≠ 0} := by
          ext k
          simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
        rw [heq]
        apply Set.Countable.biUnion ih
        intro i _hi
        have hfami_count : (fam i).IsCountablyGenerated := allCount i
        obtain ⟨genI, hgenI_count, hgenI_span⟩ := hfami_count

        -- The set of k touched by fam i is contained in a countable union of finite supports
        have hsubset : {k | ∃ x ∈ fam i, comp k (p x) ≠ 0 ∨ comp k (q x) ≠ 0} ⊆
            ⋃ (g : fam i) (_ : g ∈ genI), ((supp (p g.val) ∪ supp (q g.val)) : Set ι) := by
          intro k hk
          simp only [Set.mem_setOf_eq] at hk
          obtain ⟨x, hx, hkx⟩ := hk
          simp only [Set.mem_iUnion, Set.mem_union, Finset.mem_coe]
          have hx_span : (⟨x, hx⟩ : fam i) ∈ Submodule.span R genI := by
            rw [hgenI_span]; exact Submodule.mem_top
          rcases hkx with hkp | hkq
          · have : ∃ g ∈ genI, comp k (p g.val) ≠ 0 := by
              refine Submodule.span_induction (p := fun y _ => comp k (p y.val) ≠ 0 →
                  ∃ g ∈ genI, comp k (p g.val) ≠ 0) ?_ ?_ ?_ ?_ hx_span hkp
              · intro g hg hne
                exact ⟨g, hg, hne⟩
              · intro h; simp at h
              · intro a b _ _ iha ihb hne
                by_cases ha : comp k (p a.val) = 0
                · have hb : comp k (p b.val) ≠ 0 := fun hb => hne (by simp [ha, hb])
                  exact ihb hb
                · exact iha ha
              · intro r a _ ih hne
                simp only [SetLike.val_smul, map_smul] at hne
                have ha : comp k (p a.val) ≠ 0 := fun ha => hne (by simp [ha])
                exact ih ha
            obtain ⟨g, hg, hgne⟩ := this
            exact ⟨g, hg, Or.inl (hsupp_complete (p g.val) k hgne)⟩
          · have : ∃ g ∈ genI, comp k (q g.val) ≠ 0 := by
              refine Submodule.span_induction (p := fun y _ => comp k (q y.val) ≠ 0 →
                  ∃ g ∈ genI, comp k (q g.val) ≠ 0) ?_ ?_ ?_ ?_ hx_span hkq
              · intro g hg hne
                exact ⟨g, hg, hne⟩
              · intro h; simp at h
              · intro a b _ _ iha ihb hne
                by_cases ha : comp k (q a.val) = 0
                · have hb : comp k (q b.val) ≠ 0 := fun hb => hne (by simp [ha, hb])
                  exact ihb hb
                · exact iha ha
              · intro r a _ ih hne
                simp only [SetLike.val_smul, map_smul] at hne
                have ha : comp k (q a.val) ≠ 0 := fun ha => hne (by simp [ha])
                exact ih ha
            obtain ⟨g, hg, hgne⟩ := this
            exact ⟨g, hg, Or.inr (hsupp_complete (q g.val) k hgne)⟩

        apply Set.Countable.mono hsubset
        apply Set.Countable.biUnion hgenI_count
        intro g _hg
        apply Set.Countable.union
        · exact Finset.countable_toSet _
        · exact Finset.countable_toSet _


    have hj_in_Binf : j ∈ Binf := by
      apply Set.mem_iUnion.mpr
      exact ⟨0, Set.mem_singleton j⟩

    have hfamj_le : fam j ≤ ⨆ k ∈ Binf, fam k := le_biSup (f := fam) hj_in_Binf

    -- Binf is closed under the component operation: if i ∈ Binf, x ∈ fam i, and
    -- comp k (p x) ≠ 0 or comp k (q x) ≠ 0, then k ∈ Binf
    have hBinf_closed : ∀ i ∈ Binf, ∀ x ∈ fam i, ∀ k : ι,
        (comp k (p x) ≠ 0 ∨ comp k (q x) ≠ 0) → k ∈ Binf := by
      intro i hi x hx k hk
      rw [Set.mem_iUnion] at hi
      obtain ⟨n, hin⟩ := hi
      apply Set.mem_iUnion.mpr
      use n + 1
      right
      exact ⟨i, hin, x, hx, hk⟩

    -- U is closed under the component condition (combining Mα-closure and Binf-closure)
    have hclosedU : ∀ x : M, x ∈ U → ∀ k : ι,
        (comp k (p x) ≠ 0 ∨ comp k (q x) ≠ 0) → fam k ≤ U := by
      intro x hx k hk
      rw [Submodule.mem_sup] at hx
      obtain ⟨y, hy, z, hz, hyzsum⟩ := hx
      by_cases hkMα : fam k ≤ Mα
      · exact le_sup_of_le_left hkMα
      · apply le_sup_of_le_right
        -- The Mα-part of x has zero k-component, so the Binf-part carries the nonzero component
        have hpy : p y ∈ Mα := pstableα y hy
        have hqy : q y ∈ Mα := qstableα y hy
        have hcomp_py_zero : comp k (p y) = 0 := hMα_comp_zero (p y) hpy k hkMα
        have hcomp_qy_zero : comp k (q y) = 0 := hMα_comp_zero (q y) hqy k hkMα
        have hpx : p x = p y + p z := by rw [← hyzsum]; simp [map_add]
        have hqx : q x = q y + q z := by rw [← hyzsum]; simp [map_add]
        have hcomp_px : comp k (p x) = comp k (p z) := by
          rw [hpx, map_add, hcomp_py_zero, zero_add]
        have hcomp_qx : comp k (q x) = comp k (q z) := by
          rw [hqx, map_add, hcomp_qy_zero, zero_add]
        have cond' : comp k (p z) ≠ 0 ∨ comp k (q z) ≠ 0 := by
          rcases hk with hcp | hcq
          · left; rwa [← hcomp_px]
          · right; rwa [← hcomp_qx]
        have hz' : z ∈ ⨆ k ∈ Binf, fam k := hz
        rw [Submodule.iSup_eq_span] at hz'

        -- Use span induction on z to show k ∈ Binf, exploiting closure of Binf
        have hk_in_Binf : k ∈ Binf := by
          have hsimp : (⋃ i, ↑(⨆ (_ : i ∈ Binf), fam i)) = ⋃ i ∈ Binf, (fam i : Set M) := by
            ext x
            simp only [Set.mem_iUnion, SetLike.mem_coe]
            constructor
            · intro ⟨i, hx⟩
              by_cases hi : i ∈ Binf
              · exact ⟨i, hi, by simp only [iSup_pos hi] at hx; exact hx⟩
              · simp only [iSup_neg hi, mem_bot] at hx
                subst hx
                exact ⟨j, hj_in_Binf, zero_mem _⟩
            · intro ⟨i, hi, hx⟩
              exact ⟨i, by simp only [iSup_pos hi]; exact hx⟩
          rw [hsimp] at hz'

          refine Submodule.span_induction (p := fun w _ =>
              (comp k (p w) ≠ 0 ∨ comp k (q w) ≠ 0) → k ∈ Binf) ?_ ?_ ?_ ?_ hz' cond'
          · intro w hw hcond
            simp only [Set.mem_iUnion] at hw
            obtain ⟨i, hi, hwi⟩ := hw
            exact hBinf_closed i hi w hwi k hcond
          · intro hcond
            simp only [map_zero, ne_eq, not_true_eq_false, or_self] at hcond
          · intro a b _ _ iha ihb hcond
            simp only [map_add] at hcond
            by_cases ha : comp k (p a) ≠ 0 ∨ comp k (q a) ≠ 0
            · exact iha ha
            · push_neg at ha
              rcases hcond with hcp | hcq
              · have : comp k (p b) ≠ 0 := by
                  intro hpb
                  rw [ha.1, hpb, add_zero] at hcp
                  exact hcp rfl
                exact ihb (Or.inl this)
              · have : comp k (q b) ≠ 0 := by
                  intro hqb
                  rw [ha.2, hqb, add_zero] at hcq
                  exact hcq rfl
                exact ihb (Or.inr this)
          · intro r a _ ih hcond
            simp only [map_smul] at hcond
            have ha : comp k (p a) ≠ 0 ∨ comp k (q a) ≠ 0 := by
              rcases hcond with hcp | hcq
              · left
                intro hpa
                rw [hpa, smul_zero] at hcp
                exact hcp rfl
              · right
                intro hqa
                rw [hqa, smul_zero] at hcq
                exact hcq rfl
            exact ih ha
        exact le_biSup (f := fam) hk_in_Binf

    -- U = ⊔ { fam k | fam k ≤ U } by the abstract closure lemma
    have hUdecomp : U = ⨆ t : {k // fam k ≤ U}, fam t.1 :=
      submodule_eq_iSup_of_closed_under_components
        (R := R) (M := M)
        (fam := fam) (comp := comp)
        (hcomp_mem := hcomp_mem) (hsum := hsum)
        (p := p) (q := q) (hpq := hpq)
        (U := U)
        (hclosed := hclosedU)

    -- U is stable under p
    have pstableU : ∀ x : M, x ∈ U → p x ∈ U := by
      intro x hx
      have hxsum : p x = ∑ k ∈ supp (p x), comp k (p x) := hsupp (p x)
      rw [hxsum]
      refine Submodule.sum_mem U ?_
      intro k hk
      by_cases hzero : comp k (p x) = 0
      · simp only [hzero, zero_mem]
      · have hk' : (comp k (p x) ≠ 0 ∨ comp k (q x) ≠ 0) := Or.inl hzero
        have hle : fam k ≤ U := hclosedU x hx k hk'
        exact hle (hcomp_mem k (p x))

    -- U is stable under q
    have qstableU : ∀ x : M, x ∈ U → q x ∈ U := by
      intro x hx
      have hxsum : q x = ∑ k ∈ supp (q x), comp k (q x) := hsupp (q x)
      rw [hxsum]
      refine Submodule.sum_mem U ?_
      intro k hk
      by_cases hzero : comp k (q x) = 0
      · simp only [hzero, zero_mem]
      · have hk' : (comp k (p x) ≠ 0 ∨ comp k (q x) ≠ 0) := Or.inr hzero
        have hle : fam k ≤ U := hclosedU x hx k hk'
        exact hle (hcomp_mem k (q x))

    let C' := C ∪ Binf
    have hC'_countable : C'.Countable := hC_countable.union hBinf_countable
    have hU_eq_C' : U = ⨆ k ∈ C', fam k := by
      simp only [U, C']
      rw [hMα_eq, Set.union_comm, iSup_union, sup_comm]
    exact ⟨⟨C', U⟩, hC'_countable, hU_eq_C', pstableU, qstableU⟩

-- computeBinf j C: the closure of {j} under the p-and-q component operation,
-- starting from {j} and iterating countably many steps. This is the same construction
-- used in succCase above, extracted as a named helper for use in the transfinite recursion.
let computeBinf (j : ι) (C : Set ι) : Set ι :=
  let Bstep : Set ι → Set ι := fun B =>
    B ∪ {k : ι | ∃ i ∈ B, ∃ x ∈ fam i, comp k (p x) ≠ 0 ∨ comp k (q x) ≠ 0}
  let B0 : Set ι := {j}
  let B : ℕ → Set ι := Nat.rec B0 (fun _n Bn => Bstep Bn)
  ⋃ n : ℕ, B n

have compl_nonempty_of_ne_univ : ∀ C : Set ι, C ≠ Set.univ → Cᶜ.Nonempty := by
  intro C hC
  rw [Set.nonempty_compl]
  exact hC

-- consumed α: the set of indices consumed by stage α of the transfinite recursion.
-- At zero: ∅. At a successor: add computeBinf of the least unconsumed index.
-- At a limit: take the union.
let consumed : Ordinal.{w} → Set ι := fun o =>
  Ordinal.limitRecOn o
    ∅
    (fun α C =>
      if h : C = Set.univ then Set.univ
      else
        let Unc := Cᶜ
        let hUnc := compl_nonempty_of_ne_univ C h
        let j := WellFounded.min (IsWellFounded.wf (r := WellOrderingRel)) Unc hUnc
        C ∪ computeBinf j C)
    (fun α _hLim f => ⋃ (β : Ordinal.{w}) (hβ : β < α), f β hβ)

-- Mseq α: the submodule of M generated by fam k for k ∈ consumed α
let Mseq : Ordinal.{w} → Submodule R M := fun α => ⨆ i ∈ consumed α, fam i

-- consumed is monotone under ≤ on ordinals
have consumed_mono : ∀ (α β : Ordinal.{w}), α ≤ β → consumed α ⊆ consumed β := by
  intro α β hle
  induction β using Ordinal.induction with
  | h β ih =>
    rcases hle.lt_or_eq with hlt | rfl
    · by_cases hβ0 : β = 0
      · simp only [hβ0, Ordinal.not_lt_zero] at hlt
      · by_cases hβlim : Order.IsSuccLimit β
        · -- At a limit, consumed β = ⋃ γ < β, consumed γ ⊇ consumed α
          intro i hi
          unfold consumed
          rw [Ordinal.limitRecOn_limit (o := β) (h := hβlim)]
          refine Set.mem_iUnion.mpr ?_
          refine ⟨α, ?_⟩
          refine Set.mem_iUnion.mpr ?_
          refine ⟨hlt, ?_⟩
          exact hi

        · have ⟨γ, hγ⟩ : ∃ γ, β = Order.succ γ := by
            have hNotMin : ¬IsMin β := fun h => hβ0 h.eq_bot
            have hNotPrelimit : ¬Order.IsSuccPrelimit β := fun hp => hβlim ⟨hNotMin, hp⟩
            simp only [Order.IsSuccPrelimit, not_forall, not_not] at hNotPrelimit
            obtain ⟨γ, hγ⟩ := hNotPrelimit
            exact ⟨γ, (Order.succ_eq_of_covBy hγ).symm⟩
          subst hγ
          have hαγ : α ≤ γ := Order.lt_succ_iff.mp hlt
          -- consumed(succ γ) ⊇ consumed γ ⊇ consumed α
          have hsub : consumed γ ⊆ consumed (Order.succ γ) := by
            unfold consumed
            rw [Ordinal.limitRecOn_succ]
            split_ifs with h
            · exact Set.subset_univ _
            · exact Set.subset_union_left
          exact Set.Subset.trans (ih γ (Order.lt_succ γ) hαγ) hsub
    · exact Set.Subset.rfl

have Mseq_mono : ∀ α β : Ordinal.{w}, α ≤ β → Mseq α ≤ Mseq β := by
  intro α β hle
  apply biSup_mono
  intro i hi
  exact consumed_mono α β hle hi

-- PQ: the property that a submodule is stable under both projections p and q
let PQ : Submodule R M → Prop :=
  fun U => (∀ x, x ∈ U → p x ∈ U) ∧ (∀ x, x ∈ U → q x ∈ U)

-- Each Mseq α satisfies PQ, proved by transfinite induction:
-- at zero: trivial; at limit: directed union; at successor: use succCase stability
have PQ_Mseq : ∀ α : Ordinal.{w}, PQ (Mseq α) := by
  intro α
  induction α using Ordinal.induction with
  | h α ih =>
    by_cases h0 : α = 0
    · subst h0
      simp only [PQ, Mseq, consumed]
      simp only [limitRecOn_zero, mem_empty_iff_false, not_false_eq_true, iSup_neg, iSup_bot,
        mem_bot, forall_eq, map_zero, and_self]
    · by_cases hLim : Order.IsSuccLimit α
      · simp only [PQ, Mseq]
        have hconsumed_limit : consumed α = ⋃ (β : Ordinal.{w}) (hβ : β < α), consumed β := by
          unfold consumed
          rw [Ordinal.limitRecOn_limit (h := hLim)]
        have hMseq_eq : (⨆ i ∈ consumed α, fam i) =
          ⨆ (β : Ordinal.{w}) (hβ : β < α), ⨆ i ∈ consumed β, fam i := by
          rw [hconsumed_limit]
          apply le_antisymm
          · apply iSup₂_le
            intro k hk
            simp only [Set.mem_iUnion] at hk
            obtain ⟨β, hβ, hk'⟩ := hk
            apply le_iSup_of_le β
            apply le_iSup_of_le hβ
            exact le_biSup (f := fam) hk'
          · apply iSup₂_le
            intro β hβ
            apply iSup₂_le
            intro k hk
            apply le_biSup (f := fam)
            simp only [Set.mem_iUnion]
            exact ⟨β, hβ, hk⟩
        rw [hMseq_eq]
        have hdir : Directed (· ≤ ·) (fun β : Set.Iio α => Mseq β.val) := by
          intro ⟨β₁, hβ₁⟩ ⟨β₂, hβ₂⟩
          simp only [Set.mem_Iio] at hβ₁ hβ₂
          refine ⟨⟨max β₁ β₂, Set.mem_Iio.mpr (max_lt hβ₁ hβ₂)⟩, ?_, ?_⟩
          · exact Mseq_mono β₁ (max β₁ β₂) (le_max_left _ _)
          · exact Mseq_mono β₂ (max β₁ β₂) (le_max_right _ _)
        have hne : Nonempty (Set.Iio α) := ⟨⟨0, pos_iff_ne_zero.mpr h0⟩⟩
        have hMseq_eq' : (⨆ (β : Ordinal.{w}) (hβ : β < α), ⨆ i ∈ consumed β, fam i) =
                        ⨆ (β : Set.Iio α), Mseq β.val := by
          apply le_antisymm
          · apply iSup₂_le
            intro β hβ
            exact le_iSup (fun β : Set.Iio α => Mseq β.val) ⟨β, hβ⟩
          · apply iSup_le
            intro ⟨β, hβ⟩
            apply le_iSup_of_le β
            apply le_iSup_of_le hβ
            exact le_refl _
        rw [hMseq_eq']
        constructor
        · intro x hx
          rw [Submodule.mem_iSup_of_directed _ hdir] at hx ⊢
          obtain ⟨⟨β, hβ⟩, hxβ⟩ := hx
          exact ⟨⟨β, hβ⟩, (ih β hβ).1 x hxβ⟩
        · intro x hx
          rw [Submodule.mem_iSup_of_directed _ hdir] at hx ⊢
          obtain ⟨⟨β, hβ⟩, hxβ⟩ := hx
          exact ⟨⟨β, hβ⟩, (ih β hβ).2 x hxβ⟩

      · have : ¬ IsMin α := by exact not_isMin_iff_ne_bot.mpr h0
        have : ¬ Order.IsSuccPrelimit α := by
          rw[Order.IsSuccLimit] at hLim
          push_neg at hLim
          apply hLim this
        rw[Order.IsSuccPrelimit] at this
        push_neg at this
        obtain ⟨b,bprop⟩ := this
        simp only [Mseq]
        have hα : α = Order.succ b := (Order.succ_eq_of_covBy bprop).symm
        subst hα
        have hcons :
          consumed (Order.succ b) =
            if h : consumed b = Set.univ then Set.univ
            else consumed b ∪ computeBinf
              (WellFounded.min (IsWellFounded.wf (r := WellOrderingRel))
                (consumed b)ᶜ (compl_nonempty_of_ne_univ (consumed b) h))
              (consumed b) := by
          simp [consumed, Ordinal.limitRecOn_succ]
        rw [hcons]
        by_cases h : consumed b = Set.univ
        · rw[h]
          simp only [↓reduceDIte, mem_univ, iSup_pos]
          have : (⨆ i, fam i) = ⊤ := by
            apply DirectSum.IsInternal.submodule_iSup_eq_top interFam
          rw[this]
          simp only [PQ]
          constructor
          · intro x; exact fun a ↦ a
          · intro x; exact fun a ↦ a
        · simp only [h]
          simp only [↓reduceDIte]
          rw [iSup_union]
          -- PQ is preserved by sup (each summand is PQ-stable)
          have PQ_sup : ∀ U V : Submodule R M, PQ U → PQ V → PQ (U ⊔ V) := by
            intro U V hU hV
            constructor
            · intro x hx
              rw [Submodule.mem_sup] at hx ⊢
              obtain ⟨u, hu, v, hv, rfl⟩ := hx
              exact ⟨p u, hU.1 u hu, p v, hV.1 v hv, by simp [map_add]⟩
            · intro x hx
              rw [Submodule.mem_sup] at hx ⊢
              obtain ⟨u, hu, v, hv, rfl⟩ := hx
              exact ⟨q u, hU.2 u hu, q v, hV.2 v hv, by simp [map_add]⟩
          apply PQ_sup
          · exact ih b (Order.lt_succ b)
          · -- Show ⨆ k ∈ computeBinf j₀ (consumed b), fam k is PQ-stable
            -- by span induction on the Binf structure
            let j₀ := WellFounded.min (IsWellFounded.wf (r := WellOrderingRel))
               (consumed b)ᶜ (compl_nonempty_of_ne_univ (consumed b) h)
            let Binf := computeBinf j₀ (consumed b)

            let Bstep : Set ι → Set ι := fun B =>
              B ∪ {k : ι | ∃ i ∈ B, ∃ x ∈ fam i, comp k (p x) ≠ 0 ∨ comp k (q x) ≠ 0}

            let B0 : Set ι := {j₀}
            let B : ℕ → Set ι := Nat.rec B0 (fun _n Bn => Bstep Bn)

            have hBinf_eq : Binf = ⋃ n, B n := rfl

            have hBinf_closed : ∀ i ∈ Binf, ∀ x ∈ fam i, ∀ k : ι,
                (comp k (p x) ≠ 0 ∨ comp k (q x) ≠ 0) → k ∈ Binf := by
              intro i hi x hx k hk
              simp only [hBinf_eq, Set.mem_iUnion] at hi ⊢
              obtain ⟨n, hin⟩ := hi
              exact ⟨n + 1, Or.inr ⟨i, hin, x, hx, hk⟩⟩

            -- If i ∈ Binf and x ∈ fam i, then p x lies in ⨆ k ∈ Binf, fam k
            have hp_mem : ∀ i ∈ Binf, ∀ x ∈ fam i, p x ∈ ⨆ k ∈ Binf, fam k := by
              intro i hi x hx
              rw [hsupp (p x)]
              apply Submodule.sum_mem
              intro k hk
              have hcomp_mem_k : comp k (p x) ∈ fam k := hcomp_mem k (p x)
              by_cases hzero : comp k (p x) = 0
              · simp only [hzero, Submodule.zero_mem]
              · have hk_in : k ∈ Binf := hBinf_closed i hi x hx k (Or.inl hzero)
                exact le_biSup (f := fam) hk_in hcomp_mem_k

            -- Similarly for q x
            have hq_mem : ∀ i ∈ Binf, ∀ x ∈ fam i, q x ∈ ⨆ k ∈ Binf, fam k := by
              intro i hi x hx
              rw [hsupp (q x)]
              apply Submodule.sum_mem
              intro k hk
              have hcomp_mem_k : comp k (q x) ∈ fam k := hcomp_mem k (q x)
              by_cases hzero : comp k (q x) = 0
              · simp only [hzero, Submodule.zero_mem]
              · have hk_in : k ∈ Binf := hBinf_closed i hi x hx k (Or.inr hzero)
                exact le_biSup (f := fam) hk_in hcomp_mem_k

            constructor
            · intro x hx
              have hBinf_def : Binf = computeBinf j₀ (consumed b) := rfl
              rw [← hBinf_def] at hx ⊢
              rw [Submodule.iSup_eq_span' fam (· ∈ Binf)] at hx ⊢
              refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
              · intro y hy
                simp only [Set.mem_iUnion] at hy
                obtain ⟨i, hi, hyi⟩ := hy
                have := hp_mem i hi y hyi
                rw [Submodule.iSup_eq_span' fam (· ∈ Binf)] at this
                exact this
              · simp only [map_zero]; exact Submodule.zero_mem _
              · intro a b _ _ ha hb
                simp only [map_add]; exact Submodule.add_mem _ ha hb
              · intro r a _ ha
                simp only [map_smul]; exact Submodule.smul_mem _ r ha

            · intro x hx
              have hBinf_def : Binf = computeBinf j₀ (consumed b) := rfl
              rw [← hBinf_def] at hx ⊢
              rw [Submodule.iSup_eq_span' fam (· ∈ Binf)] at hx ⊢
              refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
              · intro y hy
                simp only [Set.mem_iUnion] at hy
                obtain ⟨i, hi, hyi⟩ := hy
                have := hq_mem i hi y hyi
                rw [Submodule.iSup_eq_span' fam (· ∈ Binf)] at this
                exact this
              · simp only [map_zero]; exact Submodule.zero_mem _
              · intro a b _ _ ha hb
                simp only [map_add]; exact Submodule.add_mem _ ha hb
              · intro r a _ ha
                simp only [map_smul]; exact Submodule.smul_mem _ r ha


-- At each successor step, the minimum unconsumed index j is in consumed(succ α)
have succ_consumes_min : ∀ (α : Ordinal.{w}) (hne : consumed α ≠ Set.univ),
    let Unc := (consumed α)ᶜ
    let hUnc := compl_nonempty_of_ne_univ (consumed α) hne
    let j := WellFounded.min (IsWellFounded.wf (r := WellOrderingRel)) Unc hUnc
    j ∈ consumed (Order.succ α) := by
  intro α hne
  simp only
  have hsucc : consumed (Order.succ α) =
      if h : consumed α = Set.univ then Set.univ
      else consumed α ∪ computeBinf (WellFounded.min (IsWellFounded.wf (r := WellOrderingRel))
           (consumed α)ᶜ (compl_nonempty_of_ne_univ (consumed α) h)) (consumed α) := by
    unfold consumed
    rw [Ordinal.limitRecOn_succ]
  rw [hsucc, dif_neg hne]
  right
  -- j ∈ B 0 = {j} ⊆ computeBinf j (consumed α)
  apply Set.mem_iUnion.mpr
  use 0
  simp only [ne_eq, Nat.rec_zero, mem_singleton_iff]

-- Every index i is eventually consumed: i ∈ consumed(succ(typein i)).
-- Proved by well-founded induction on i using the well-ordering on ι:
-- if i is not yet consumed at its own ordinal level, then the minimum unconsumed
-- index j is smaller (in the well-ordering) and by IH is consumed earlier, contradicting
-- its membership in the unconsumed complement.
have all_eventually_consumed : ∀ i : ι,
  i ∈ consumed (Order.succ (Ordinal.typein WellOrderingRel i)) := by
  intro i
  have wf := IsWellFounded.wf (r := WellOrderingRel (α := ι))
  induction i using wf.induction with
  | h i ih =>
    let ord_i := Ordinal.typein WellOrderingRel i

    by_cases hi : i ∈ consumed ord_i
    · exact consumed_mono ord_i (Order.succ ord_i) (Order.le_succ ord_i) hi
    · have hne : consumed ord_i ≠ Set.univ := by
        intro heq
        rw [heq] at hi
        exact hi (Set.mem_univ i)

      let Unc := (consumed ord_i)ᶜ
      let hUnc := compl_nonempty_of_ne_univ (consumed ord_i) hne
      let j := WellFounded.min wf Unc hUnc

      have hi_unc : i ∈ Unc := hi
      have hj_le_i : ¬ WellOrderingRel i j := WellFounded.not_lt_min wf Unc hUnc hi_unc

      by_cases hji : j = i
      · have hsucc := succ_consumes_min ord_i hne
        simp only at hsucc
        convert hsucc using 2
        exact hji.symm
      · have hjWi : WellOrderingRel j i := by
          have htri := @trichotomous _ WellOrderingRel _ j i
          cases htri with
          | inl h => exact h
          | inr h =>
            cases h with
            | inl heq => exact (hji heq).elim
            | inr h => exact (hj_le_i h).elim

        have hj_cons := ih j hjWi

        have hord_j : Ordinal.typein WellOrderingRel j < ord_i :=
          Ordinal.typein_lt_typein WellOrderingRel |>.mpr hjWi
        have hsucc_le : Order.succ (Ordinal.typein WellOrderingRel j) ≤ ord_i :=
          Order.succ_le_of_lt hord_j

        -- By monotonicity, j ∈ consumed ord_i
        have hj_in : j ∈ consumed ord_i :=
          consumed_mono (Order.succ (Ordinal.typein WellOrderingRel j)) ord_i hsucc_le hj_cons

        -- But j is unconsumed at ord_i, contradiction
        have hj_unc : j ∈ Unc := WellFounded.min_mem wf Unc hUnc
        exact (hj_unc hj_in).elim

have all_eventually_consumed' : ∀ i : ι, ∃ α : Ordinal.{w}, α < Order.succ T ∧ i ∈ consumed α := by
  intro i
  use Order.succ (Ordinal.typein WellOrderingRel i)
  constructor
  · exact Order.succ_lt_succ (Ordinal.typein_lt_type WellOrderingRel i)
  · exact all_eventually_consumed i

-- The union of consumed over all α < S covers everything
have consumed_eventually_univ : (⋃ α : Set.Iio (Order.succ T), consumed α.val) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro i
  have ⟨α, hα, hi⟩ := all_eventually_consumed' i
  simp only [Set.mem_iUnion]
  exact ⟨⟨α, hα⟩, hi⟩

-- The union of Mseq over all α < S equals ⊤ (M is exhausted)
have union_eq_top : (⨆ α : Set.Iio S, Mseq α.val) = ⊤ := by
  apply eq_top_iff.mpr
  rw [← DirectSum.IsInternal.submodule_iSup_eq_top interFam]
  apply iSup_le
  intro i
  obtain ⟨α, hα, hi⟩ := all_eventually_consumed' i
  apply le_iSup_of_le ⟨α, hα⟩
  apply le_biSup (f := fam) hi

-- Nseq: the filtration of N, obtained by restricting Mseq to N via comap i
let Nseq : Set.Iio S → Submodule R N := fun α => (Mseq α.val).comap i

-- computeBinf produces countable sets (same proof as in succCase above, extracted for reuse)
have computeBinf_countable :
        ∀ (j₀ : ι) (C₀ : Set ι),
        (computeBinf j₀ C₀).Countable := by
      intro j₀ C₀
      simp only [computeBinf]
      let Bstep : Set ι → Set ι := fun B =>
        B ∪ {k : ι | ∃ i ∈ B, ∃ x ∈ fam i,
          comp k (p x) ≠ 0 ∨ comp k (q x) ≠ 0}
      let B0 : Set ι := {j₀}
      let B : ℕ → Set ι :=
        Nat.rec B0 (fun _n Bn => Bstep Bn)
      change (⋃ n, B n).Countable
      apply Set.countable_iUnion
      intro n
      induction n with
      | zero => exact Set.countable_singleton j₀
      | succ n ih =>
        apply Set.Countable.union ih
        have heq :
          {k | ∃ i ∈ B n, ∃ x ∈ fam i,
            comp k (p x) ≠ 0 ∨
            comp k (q x) ≠ 0} =
          ⋃ (i : ι) (_ : i ∈ B n),
            {k | ∃ x ∈ fam i,
              comp k (p x) ≠ 0 ∨
              comp k (q x) ≠ 0} := by
          ext k
          simp only [Set.mem_setOf_eq,
            Set.mem_iUnion, exists_prop]
        rw [heq]
        apply Set.Countable.biUnion ih
        intro i _hi
        obtain ⟨genI, hgenI_count, hgenI_span⟩ :=
          allCount i
        have hsubset :
          {k | ∃ x ∈ fam i,
            comp k (p x) ≠ 0 ∨
            comp k (q x) ≠ 0} ⊆
          ⋃ (g : fam i) (_ : g ∈ genI),
            ((supp (p g.val) ∪ supp (q g.val)) :
              Set ι) := by
          intro k hk
          simp only [Set.mem_setOf_eq] at hk
          obtain ⟨x, hx, hkx⟩ := hk
          simp only [Set.mem_iUnion, Set.mem_union,
            Finset.mem_coe]
          have hx_span :
              (⟨x, hx⟩ : fam i) ∈
                Submodule.span R genI := by
            rw [hgenI_span]
            exact Submodule.mem_top
          rcases hkx with hkp | hkq
          · have : ∃ g ∈ genI,
                comp k (p g.val) ≠ 0 := by
              refine Submodule.span_induction
                (p := fun y _ =>
                  comp k (p y.val) ≠ 0 →
                  ∃ g ∈ genI,
                    comp k (p g.val) ≠ 0)
                ?_ ?_ ?_ ?_ hx_span hkp
              · exact fun g hg hne =>
                  ⟨g, hg, hne⟩
              · intro h; simp at h
              · intro a b _ _ iha ihb hne
                by_cases ha :
                    comp k (p a.val) = 0
                · exact ihb (fun hb =>
                    hne (by simp [ha, hb]))
                · exact iha ha
              · intro r a _ iha hne
                simp only [SetLike.val_smul,
                  map_smul] at hne
                exact iha (fun ha =>
                  hne (by simp [ha]))
            obtain ⟨g, hg, hgne⟩ := this
            exact ⟨g, hg, Or.inl
              (hsupp_complete (p g.val) k hgne)⟩
          · have : ∃ g ∈ genI,
                comp k (q g.val) ≠ 0 := by
              refine Submodule.span_induction
                (p := fun y _ =>
                  comp k (q y.val) ≠ 0 →
                  ∃ g ∈ genI,
                    comp k (q g.val) ≠ 0)
                ?_ ?_ ?_ ?_ hx_span hkq
              · exact fun g hg hne =>
                  ⟨g, hg, hne⟩
              · intro h; simp at h
              · intro a b _ _ iha ihb hne
                by_cases ha :
                    comp k (q a.val) = 0
                · exact ihb (fun hb =>
                    hne (by simp [ha, hb]))
                · exact iha ha
              · intro r a _ iha hne
                simp only [SetLike.val_smul,
                  map_smul] at hne
                exact iha (fun ha =>
                  hne (by simp [ha]))
            obtain ⟨g, hg, hgne⟩ := this
            exact ⟨g, hg, Or.inr
              (hsupp_complete (q g.val) k hgne)⟩
        apply Set.Countable.mono hsubset
        apply Set.Countable.biUnion hgenI_count
        intro g _hg
        exact Set.Countable.union
          (Finset.countable_toSet _)
          (Finset.countable_toSet _)


-- Now assemble the KaplanskyDevissage for N using Nseq
refine ⟨⟨Nseq, ?monotone, ?zero_eq_bot, ?union_eq_top, ?limit_continuity, ?succ_step⟩⟩

case monotone =>
  intro α β hαβ
  apply Submodule.comap_mono
  exact Mseq_mono α.val β.val hαβ

case zero_eq_bot =>
  intro h
  simp only [Nseq, Mseq]
  -- consumed 0 = ∅, so Mseq 0 = ⊥, and comap i ⊥ = ker i = ⊥ (since π ∘ i = id)
  have hcons0 : consumed 0 = ∅ := by
    unfold consumed
    rw [Ordinal.limitRecOn_zero]
  simp only [hcons0, Set.mem_empty_iff_false, iSup_false, iSup_bot, Submodule.comap_bot]
  rw [LinearMap.ker_eq_bot]
  exact Function.LeftInverse.injective (fun n => congrFun (congrArg DFunLike.coe hπi) n)


case union_eq_top =>
  rw [eq_top_iff]
  intro n _
  -- i n ∈ ⨆ α, Mseq α = ⊤, so n ∈ ⨆ α, Nseq α
  have hi_n : i n ∈ (⨆ α : Set.Iio S, Mseq α.val) := by
    rw [union_eq_top]; exact Submodule.mem_top
  have hdir : Directed (· ≤ ·) (fun α : Set.Iio S => Mseq α.val) := by
    intro α β
    refine ⟨⟨max α.val β.val, ?_⟩, ?_, ?_⟩
    · simp only [Set.mem_Iio]
      exact max_lt (Set.mem_Iio.mp α.prop) (Set.mem_Iio.mp β.prop)
    · exact Mseq_mono α.val _ (le_max_left _ _)
    · exact Mseq_mono β.val _ (le_max_right _ _)
  have hne : Nonempty (Set.Iio S) := ⟨⟨0, Ordinal.succ_pos T⟩⟩
  rw [Submodule.mem_iSup_of_directed _ hdir] at hi_n
  obtain ⟨α, hα⟩ := hi_n
  exact Submodule.mem_iSup_of_mem α (Submodule.mem_comap.mpr hα)

case limit_continuity =>
  intro α hLimit
  apply le_antisymm
  · -- (Mseq α).comap i ≤ ⨆ β < α, (Mseq β).comap i:
    -- Mseq at a limit equals the directed union, so membership lifts to a finite stage
    intro n hn
    have hconsumed_limit : consumed α.val =
        ⋃ (β : Ordinal.{w}) (hβ : β < α.val), consumed β := by
      unfold consumed
      rw [Ordinal.limitRecOn_limit (h := hLimit)]
    have hMseq_limit : Mseq α.val =
        ⨆ (β : Ordinal.{w}) (hβ : β < α.val), Mseq β := by
      simp only [Mseq]
      rw [hconsumed_limit]
      apply le_antisymm
      · apply iSup₂_le
        intro k hk
        simp only [Set.mem_iUnion] at hk
        obtain ⟨β, hβ, hk'⟩ := hk
        exact le_iSup₂_of_le β hβ (le_biSup (f := fam) hk')
      · apply iSup₂_le
        intro β hβ
        apply iSup₂_le
        intro k hk
        exact le_biSup (f := fam) (Set.mem_iUnion.mpr ⟨β, Set.mem_iUnion.mpr ⟨hβ, hk⟩⟩)
    change i n ∈ Mseq ↑α at hn
    rw [hMseq_limit] at hn
    have hα_pos : 0 < α.val := pos_iff_ne_zero.mpr
      (fun h => by simp [h] at hLimit)
    have hne : Nonempty (Set.Iio α.val) := ⟨⟨0, hα_pos⟩⟩
    have hdir : Directed (· ≤ ·) (fun β : Set.Iio α.val => Mseq β.val) := by
      intro ⟨β₁, hβ₁⟩ ⟨β₂, hβ₂⟩
      refine ⟨⟨max β₁ β₂, Set.mem_Iio.mpr (max_lt (Set.mem_Iio.mp hβ₁)
        (Set.mem_Iio.mp hβ₂))⟩, ?_, ?_⟩
      · exact Mseq_mono β₁ (max β₁ β₂) (le_max_left _ _)
      · exact Mseq_mono β₂ (max β₁ β₂) (le_max_right _ _)
    have hMseq_eq : (⨆ (β : Ordinal.{w}) (_ : β < α.val), Mseq β) =
        ⨆ (β : Set.Iio α.val), Mseq β.val := by
      apply le_antisymm
      · apply iSup₂_le
        intro β hβ
        exact le_iSup (fun β : Set.Iio α.val => Mseq β.val) ⟨β, Set.mem_Iio.mpr hβ⟩
      · apply iSup_le
        intro ⟨β, hβ⟩
        exact le_iSup₂_of_le β hβ le_rfl
    rw [hMseq_eq] at hn
    rw [Submodule.mem_iSup_of_directed _ hdir] at hn
    obtain ⟨⟨β, hβ⟩, hn_β⟩ := hn
    have hβS : β < S := hβ.trans α.prop
    exact Submodule.mem_iSup_of_mem ⟨⟨β, hβS⟩, hβ⟩
      (Submodule.mem_comap.mpr hn_β)
  · -- ⨆ β < α, (Mseq β).comap i ≤ (Mseq α).comap i: monotonicity
    apply iSup_le
    intro ⟨⟨β, hβS⟩, hβα⟩
    apply Submodule.comap_mono
    exact Mseq_mono β α.val hβα.le


case succ_step =>
  intro α hSuccS

  by_cases hne : consumed α = Set.univ
  · -- consumed α = Set.univ: Mseq α = ⊤, the complement is ⊥
    use ⊥
    constructor
    · refine ⟨?_, ?_, ?_, ?_⟩
      · apply Submodule.comap_mono
        exact Mseq_mono α (Order.succ α) (Order.le_succ α)
      · exact bot_le
      · exact disjoint_bot_right
      · rw [sup_bot_eq]
        simp only [Nseq]
        congr 1
        have hMseq_α_eq : Mseq α = ⊤ := by
          simp only [Mseq, hne]
          rw [← DirectSum.IsInternal.submodule_iSup_eq_top interFam]
          apply le_antisymm
          · apply iSup₂_le; intro k _; exact le_iSup fam k
          · apply iSup_le; intro k; apply le_biSup (f := fam); exact Set.mem_univ k
        have hMseq_succ_eq : Mseq (Order.succ α) = ⊤ := by
          apply eq_top_iff.mpr; rw [← hMseq_α_eq]
          exact Mseq_mono α (Order.succ α) (Order.le_succ α)
        rw [hMseq_α_eq, hMseq_succ_eq]
    · use ∅; simp only [countable_empty, span_empty, true_and]
      exact Eq.symm eq_bot_of_subsingleton

  · -- consumed α ≠ Set.univ: the new complement C is built from the least unconsumed index
    let j := WellFounded.min (IsWellFounded.wf (r := WellOrderingRel)) (consumed α)ᶜ
            (compl_nonempty_of_ne_univ (consumed α) hne)
    let Binf_α := computeBinf j (consumed α)

    -- D_α: the genuinely new indices added at this step
    let D_α := Binf_α \ consumed α

    -- Cₘ': direct sum of fam over the new indices D_α
    let Cₘ' : Submodule R M := ⨆ k ∈ D_α, fam k

    -- consumed(succ α) = consumed α ∪ Binf_α = consumed α ∪ D_α
    have hconsumed_succ : consumed (Order.succ α) = consumed α ∪ Binf_α := by
      simp only [consumed]
      rw [Ordinal.limitRecOn_succ]
      have hfold : (Ordinal.limitRecOn α ∅
        (fun α C ↦ if h : C = Set.univ then Set.univ else C ∪
        computeBinf (WellFounded.min IsWellFounded.wf Cᶜ (compl_nonempty_of_ne_univ C h)) C)
        fun α _hLim f ↦ ⋃ β, ⋃ (hβ : β < α), f β hβ) = consumed α := rfl
      simp only [hfold]
      rw [dif_neg hne]

    have hconsumed_succ' : consumed α ∪ Binf_α = consumed α ∪ D_α := by
      ext k
      simp only [Set.mem_union, Set.mem_diff, D_α]
      tauto

    -- Mseq(succ α) = Mseq α ⊔ Cₘ' (direct sum of old and new summands)
    have hMseq_succ : Mseq (Order.succ α) = Mseq α ⊔ Cₘ' := by
      simp only [Mseq, Cₘ']
      rw [hconsumed_succ, hconsumed_succ']
      rw [Set.union_comm, iSup_union, sup_comm]

    -- Mseq α and Cₘ' are disjoint (disjoint indices from the original direct sum)
    have hDisj_M : Disjoint (Mseq α) Cₘ' := by
      have indep : iSupIndep fam := DirectSum.IsInternal.submodule_iSupIndep interFam
      simp only [Mseq, Cₘ']
      simp only [disjoint_iff, eq_bot_iff]
      intro x ⟨hx1, hx2⟩
      -- Reduce to showing comp k x = 0 for all k using the disjointness of consumed α and D_α
      have hx_eq : x = ∑ k ∈ supp x, comp k x := hsupp x
      suffices h : ∀ k ∈ supp x, comp k x = 0 by
        rw [hx_eq, Finset.sum_eq_zero h]
        simp only [zero_mem]
      intro k hk
      have hck : comp k x ∈ fam k := hcomp_mem k x
      by_cases hkC : k ∈ consumed α
      · -- k ∈ consumed α ⇒ k ∉ D_α ⇒ fam k ⊥ Cₘ'
        have hk_not_D : k ∉ D_α := fun h => h.2 hkC

        have hd : Disjoint (fam k) (⨆ j ∈ D_α, fam j) := indep.disjoint_biSup hk_not_D
        have : comp k x = 0 := by
          have hx_span := Submodule.iSup_eq_span (fun j => ⨆ (_ : j ∈ D_α), fam j) ▸ hx2
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hx_span
          · intro y hy
            simp only [Set.mem_iUnion, SetLike.mem_coe] at hy
            obtain ⟨j, hj⟩ := hy
            by_cases hjD : j ∈ D_α
            · simp only [iSup_pos hjD] at hj
              have hkj : k ≠ j := fun h => hk_not_D (h ▸ hjD)
              exact hcomp_proj k j hkj y hj
            · simp only [iSup_neg hjD] at hj
              rw [hj, map_zero]
          · exact map_zero _
          · intro a b _ _ ha hb; rw [map_add, ha, hb, add_zero]
          · intro r a _ ha; rw [map_smul, ha, smul_zero]
        exact this
      · -- k ∉ consumed α ⇒ fam k ⊥ Mseq α (symmetric argument)
        have hk_not_C : k ∉ consumed α := hkC
        have : comp k x = 0 := by
          have hx_span := Submodule.iSup_eq_span (fun j => ⨆ (_ : j ∈ consumed α), fam j) ▸ hx1
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hx_span
          · intro y hy
            simp only [Set.mem_iUnion, SetLike.mem_coe] at hy
            obtain ⟨j, hj⟩ := hy
            by_cases hjC : j ∈ consumed α
            · simp only [iSup_pos hjC] at hj
              have hkj : k ≠ j := fun h => hk_not_C (h ▸ hjC)
              exact hcomp_proj k j hkj y hj
            · simp only [iSup_neg hjC] at hj
              rw [hj, map_zero]
          · exact map_zero _
          · intro a b _ _ ha hb; rw [map_add, ha, hb, add_zero]
          · intro r a _ ha; rw [map_smul, ha, smul_zero]
        exact this


  -- Work inside ↥(Mseq(succ α)) using the internal direct sum Mseq α ⊕ Cₘ'
    let Msucc := Mseq (Order.succ α)
    let Mα_sub : Submodule R Msucc := (Mseq α).comap Msucc.subtype
    let Cₘ'_sub : Submodule R Msucc := Cₘ'.comap Msucc.subtype

    -- Mα_sub and Cₘ'_sub are complementary inside Msucc
    have hIsCompl : IsCompl Mα_sub Cₘ'_sub := by
      constructor
      · rw [disjoint_iff, eq_bot_iff]
        intro ⟨x, hxMsucc⟩ hx
        simp only [Submodule.mem_inf] at hx
        have : x ∈ Mseq α ⊓ Cₘ' := ⟨hx.1, hx.2⟩
        rw [hDisj_M.eq_bot] at this
        simp only [Submodule.mem_bot] at this
        simp only[this]
        simp only [mem_bot, mk_eq_zero]
      · rw [codisjoint_iff, eq_top_iff]
        intro ⟨x, hxMsucc⟩ _
        rw [Submodule.mem_sup]
        have hxsup : x ∈ Mseq α ⊔ Cₘ' := hMseq_succ ▸ hxMsucc
        rw [Submodule.mem_sup] at hxsup
        obtain ⟨a, ha, c, hc, hac⟩ := hxsup
        have haMsucc : a ∈ Msucc := by
          change a ∈ Mseq (Order.succ α)
          rw [hMseq_succ]; exact Submodule.mem_sup_left ha
        have hcMsucc : c ∈ Msucc := by
          change c ∈ Mseq (Order.succ α)
          rw [hMseq_succ]; exact Submodule.mem_sup_right hc
        exact ⟨⟨a, haMsucc⟩, ha, ⟨c, hcMsucc⟩, hc, Subtype.ext hac⟩

    -- ρ: the projection Msucc → Mα_sub given by the internal complement decomposition
    let ρ := Submodule.linearProjOfIsCompl Mα_sub Cₘ'_sub hIsCompl

    have hi_inj : Function.Injective i := by
      exact Function.LeftInverse.injective (fun n => congrFun (congrArg DFunLike.coe hπi) n)

    let Nsucc := Nseq ⟨Order.succ α, hSuccS⟩

    have hi_maps : ∀ n : Nsucc, i n.val ∈ Msucc := by
      intro ⟨n, hn⟩; exact hn

    -- i_restrict: lift i to a map Nsucc → Msucc (well-typed since Nsucc = Msucc.comap i)
    let i_restrict : Nsucc →ₗ[R] Msucc := by
      refine LinearMap.codRestrict Msucc (i.domRestrict Nsucc) ?_
      intro ⟨n, hn⟩; exact hn

    -- σ'_N: the retraction Nsucc → N defined as π ∘ subtype ∘ subtype ∘ ρ ∘ i_restrict.
    -- For n ∈ Nseq α, σ'_N(n) = n (it fixes the "old" part).
    -- Its image lands in Nseq α (since ρ projects to Mα_sub ≤ Mseq α).
    let σ'_N : Nsucc →ₗ[R] N :=
      π.comp (Msucc.subtype.comp (Mα_sub.subtype.comp (ρ.comp i_restrict)))

    -- σ'_N fixes elements of Nseq α ∩ Nsucc
    have hRetract : ∀ (n : N) (hn : n ∈ Nsucc) (hn' : n ∈ Nseq ⟨α, (Order.lt_succ α).trans hSuccS⟩),
        σ'_N ⟨n, hn⟩ = n := by
      intro n hn hn'
      have hin_Mα : i n ∈ Mseq α := hn'
      have hin_Msucc : i n ∈ Msucc := hi_maps ⟨n, hn⟩
      have h_in_Mα_sub : (⟨i n, hin_Msucc⟩ : ↥Msucc) ∈ Mα_sub := hin_Mα
      have h_ir : i_restrict ⟨n, hn⟩ = ⟨i n, hin_Msucc⟩ := rfl
      -- ρ fixes elements of Mα_sub
      have h_rho : ρ ⟨i n, hin_Msucc⟩ = ⟨⟨i n, hin_Msucc⟩, h_in_Mα_sub⟩ := by
        exact Submodule.linearProjOfIsCompl_apply_left hIsCompl ⟨⟨i n, hin_Msucc⟩, h_in_Mα_sub⟩
      simp only [σ'_N, LinearMap.comp_apply, h_ir, h_rho]
      have hπi_n : π (i n) = n := by
        have := congrFun (congrArg DFunLike.coe hπi) n
        simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
        exact this
      simp only [Submodule.subtype_apply, hπi_n]

    -- σ'_N maps into Nseq α: the retraction value always lies in the old filtration level
    have hσ_range : ∀ (n : Nsucc), σ'_N n ∈ Nseq ⟨α, (Order.lt_succ α).trans hSuccS⟩ := by
      intro n
      change i (σ'_N n) ∈ Mseq α
      let ρ_val := ρ (i_restrict n)
      let m_sub := Mα_sub.subtype ρ_val
      let m := Msucc.subtype m_sub
      have hm_Mα : m ∈ Mseq α := ρ_val.property
      have hσ_eq : σ'_N n = π m := rfl
      rw [hσ_eq]
      have hip : i (π m) = p m := rfl
      rw [hip]
      exact (PQ_Mseq α).1 m hm_Mα

    -- C: the complement submodule of Nseq α in Nseq(succ α), defined as image of ker(σ'_N)
    let C : Submodule R N := (LinearMap.ker σ'_N).map Nsucc.subtype

    use C
    constructor
    · refine ⟨?_, ?_, ?_, ?_⟩
      · -- Nseq α ≤ Nseq(succ α)
        apply Submodule.comap_mono
        exact Mseq_mono α (Order.succ α) (Order.le_succ α)

      · -- C ≤ Nseq(succ α)
        apply Submodule.map_le_iff_le_comap.mpr
        intro ⟨n, hn⟩ _; exact hn

      · -- Disjoint (Nseq α) C: σ'_N fixes elements of Nseq α, so ker σ'_N ∩ Nseq α = 0
        rw [disjoint_iff, eq_bot_iff]
        intro n ⟨hn_α, hn_C⟩
        simp only [Submodule.mem_bot]
        obtain ⟨⟨n', hn'_mem⟩, hn'_ker, hn'_eq⟩ := hn_C
        simp only [Submodule.subtype_apply] at hn'_eq
        have hn_Nsucc : n ∈ Nsucc :=
          Submodule.comap_mono (Mseq_mono α (Order.succ α) (Order.le_succ α)) hn_α
        have h1 : σ'_N ⟨n, hn_Nsucc⟩ = n := hRetract n hn_Nsucc hn_α
        have h3 : σ'_N ⟨n, hn_Nsucc⟩ = 0 := by
          have : (⟨n', hn'_mem⟩ : ↥Nsucc) = ⟨n, hn_Nsucc⟩ := Subtype.ext hn'_eq
          rw [this] at hn'_ker; exact hn'_ker
        exact h1.symm.trans h3
      · -- Nseq α ⊔ C = Nseq(succ α): every n ∈ Nsucc decomposes as σ'_N(n) + (n - σ'_N(n))
        apply le_antisymm
        · apply sup_le
          · apply Submodule.comap_mono; exact Mseq_mono α (Order.succ α) (Order.le_succ α)
          · apply Submodule.map_le_iff_le_comap.mpr
            intro ⟨n, hn⟩ _; exact hn
        · intro n hn
          let n_sub : Nsucc := ⟨n, hn⟩
          let s := σ'_N n_sub
          have hs_Nα : s ∈ Nseq ⟨α, (Order.lt_succ α).trans hSuccS⟩ := hσ_range n_sub
          have hs_Nsucc : s ∈ Nsucc :=
            Submodule.comap_mono (Mseq_mono α (Order.succ α) (Order.le_succ α)) hs_Nα
          -- n - s ∈ ker σ'_N since σ'_N(s) = s by hRetract
          have hσ_s : σ'_N ⟨s, hs_Nsucc⟩ = s := hRetract s hs_Nsucc hs_Nα
          have hns_Nsucc : n - s ∈ Nsucc := Nsucc.sub_mem hn hs_Nsucc
          have hker : ⟨n - s, hns_Nsucc⟩ ∈ LinearMap.ker σ'_N := by
            simp only [LinearMap.mem_ker]
            have : σ'_N ⟨n - s, hns_Nsucc⟩ = σ'_N n_sub - σ'_N ⟨s, hs_Nsucc⟩ := by
              have : (⟨n - s, hns_Nsucc⟩ : ↥Nsucc) = n_sub - ⟨s, hs_Nsucc⟩ := by
                ext; simp only [AddSubgroupClass.coe_sub, sub_left_inj]; rfl
              rw [this, map_sub]
            rw [this, hσ_s]; rw [sub_eq_zero]
          have hns_C : n - s ∈ C := ⟨⟨n - s, hns_Nsucc⟩, hker, rfl⟩
          have hdecomp : n = s + (n - s) := by simp only [_root_.add_sub_cancel]
          rw [hdecomp]
          exact Submodule.mem_sup.mpr ⟨s, hs_Nα, n - s, hns_C, rfl⟩

    · -- C is countably generated:
      -- C ≤ Cₘ'.map π (the image of the new summands under π),
      -- and Cₘ' is countably generated (since D_α is countable).
      -- We then surject Cₘ' onto C via Φ = π - σ'_N ∘ π_r and pull back the generation.
      have hC_le : C ≤ Cₘ'.map π := by
        intro n hn
        obtain ⟨⟨n', hn'_mem⟩, hn'_ker, rfl⟩ := hn
        have hin : i n' ∈ Msucc := hn'_mem
        have hin' : i n' ∈ Mseq α ⊔ Cₘ' := hMseq_succ ▸ hin
        rw [Submodule.mem_sup] at hin'
        obtain ⟨a, ha, c, hc, hac⟩ := hin'
        have hπi_n : n' = π (i n') := by
          have := congrFun (congrArg DFunLike.coe hπi) n'
          simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
          exact this.symm

        have hπa_zero : π a = 0 := by
          have haMsucc : a ∈ Msucc := by
            change a ∈ Mseq (Order.succ α); rw [hMseq_succ]; exact Submodule.mem_sup_left ha
          have hcMsucc : c ∈ Msucc := by
            change c ∈ Mseq (Order.succ α); rw [hMseq_succ]; exact Submodule.mem_sup_right hc
          have ha_sub : (⟨a, haMsucc⟩ : ↥Msucc) ∈ Mα_sub := ha
          have hc_sub : (⟨c, hcMsucc⟩ : ↥Msucc) ∈ Cₘ'_sub := hc
          have hsum_sub : (⟨i n', hin⟩ : ↥Msucc) =
              ⟨a, haMsucc⟩ + ⟨c, hcMsucc⟩ := Subtype.ext hac.symm
          -- σ'_N applied to n' extracts the Mα_sub-component, which is π a
          have : σ'_N ⟨n', hn'_mem⟩ = π a := by
            simp only [σ'_N, LinearMap.comp_apply]
            congr 1
            change (Msucc.subtype (Mα_sub.subtype
              (ρ (i_restrict ⟨n', hn'_mem⟩)))) = a
            have h_ir : (i_restrict ⟨n', hn'_mem⟩ : ↥Msucc) =
                ⟨i n', hin⟩ := rfl
            rw [h_ir, hsum_sub, map_add,
              Submodule.linearProjOfIsCompl_apply_left hIsCompl ⟨_, ha_sub⟩,
              Submodule.linearProjOfIsCompl_apply_right hIsCompl ⟨_, hc_sub⟩,
              add_zero, Submodule.subtype_apply, Submodule.subtype_apply]
          rw [← this, hn'_ker]
        change n' ∈ Cₘ'.map π
        have : n' = π c := by
          rw [hπi_n, ← hac, map_add, hπa_zero, zero_add]
        rw [this]
        exact Submodule.mem_map_of_mem hc

      -- Cₘ' is countably generated since D_α ⊆ Binf_α is countable
      have hCₘ'_cg : Cₘ'.IsCountablyGenerated := by
        have hD_count : D_α.Countable :=
          (computeBinf_countable j (consumed α)).mono Set.diff_subset

        have hfam_cg : ∀ k : ι, ∃ s : Set ↥(fam k),
            s.Countable ∧ Submodule.span R s = ⊤ := allCount
        choose sf hsf_count hsf_span using hfam_cg
        have hfam_le : ∀ k ∈ D_α, fam k ≤ Cₘ' :=
          fun k hk => le_iSup₂ (f := fun k _ => fam k) k hk
        let ι_incl (k : ι) (hk : k ∈ D_α) :
            ↥(fam k) → ↥Cₘ' :=
          fun x => ⟨x.1, hfam_le k hk x.2⟩
        -- S: the union of images of the generating sets sf k for k ∈ D_α
        let S : Set ↥Cₘ' :=
          ⋃ (p : D_α), (ι_incl p.1 p.2) '' (sf p.1)

        have hS_count : S.Countable := by
          have : Countable D_α := Set.countable_coe_iff.mpr hD_count
          exact Set.countable_iUnion
            (fun p => Set.Countable.image (hsf_count p.1) _)

        refine ⟨S, hS_count, ?_⟩
        rw [eq_top_iff]
        intro ⟨x, hx⟩ _

        have hle : ∀ (p : D_α), ∀ y ∈ sf p.1,
            ι_incl p.1 p.2 y ∈ Submodule.span R S :=
          fun p y hy => Submodule.subset_span
            (Set.mem_iUnion.mpr ⟨p, Set.mem_image_of_mem _ hy⟩)
        have hfam_in_span : ∀ (p : D_α) (z : ↥(fam p.1)),
            ι_incl p.1 p.2 z ∈ Submodule.span R S := by
          intro p z
          have hz : z ∈ Submodule.span R (sf p.1) :=
            hsf_span p.1 ▸ Submodule.mem_top
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
          · intro y hy; exact hle p y hy
          · change ι_incl p.1 p.2 0 ∈ _
            have : ι_incl p.1 p.2 0 = 0 := Subtype.ext rfl
            rw [this]; exact Submodule.zero_mem _
          · intro a b _ _ ha hb
            change ι_incl p.1 p.2 (a + b) ∈ _
            simp only [ι_incl]; exact Submodule.add_mem _ ha hb
          · intro r a _ ha
            change ι_incl p.1 p.2 (r • a) ∈ _
            simp only [ι_incl]; exact Submodule.smul_mem _ r ha
        have hx' : x ∈ ⨆ k ∈ D_α, fam k := hx

        suffices h : Cₘ' ≤ Submodule.map Cₘ'.subtype
            (Submodule.span R S) by
          obtain ⟨v, hv, hveq⟩ := h hx
          rwa [show (⟨x, hx⟩ : ↥Cₘ') = v
            from Subtype.ext hveq.symm]

        apply iSup₂_le
        intro k hk y hy
        exact ⟨ι_incl k hk ⟨y, hy⟩,
          hfam_in_span ⟨k, hk⟩ ⟨y, hy⟩, rfl⟩

      have hπc_Nsucc : ∀ c ∈ Cₘ', π c ∈ Nsucc := by
        intro c hc
        exact (PQ_Mseq (Order.succ α)).1 c
          (hMseq_succ ▸ Submodule.mem_sup_right hc)

      let πr : ↥Cₘ' →ₗ[R] ↥Nsucc := by
        refine LinearMap.codRestrict Nsucc (π.comp Cₘ'.subtype) ?_
        intro ⟨c, hc⟩; exact hπc_Nsucc c hc

      -- Φ: the map Cₘ' → N combining π and the retraction correction
      let Φ : ↥Cₘ' →ₗ[R] N :=
        (π.comp Cₘ'.subtype) - (σ'_N.comp πr)

      -- Φ maps into C (every Φ(c) is in the kernel complement)
      have hΦ_mem : ∀ c : ↥Cₘ', Φ c ∈ C := by
        intro c
        have hσ_Nα : σ'_N (πr c) ∈ Nseq ⟨α, _⟩ := hσ_range (πr c)
        have hσ_Nsucc : σ'_N (πr c) ∈ Nsucc :=
          Submodule.comap_mono
            (Mseq_mono α (Order.succ α) (Order.le_succ α)) hσ_Nα
        let w : ↥Nsucc := πr c - ⟨σ'_N (πr c), hσ_Nsucc⟩
        have hw_ker : w ∈ LinearMap.ker σ'_N := by
          simp only [LinearMap.mem_ker]
          change σ'_N (πr c - ⟨σ'_N (πr c), hσ_Nsucc⟩) = 0
          rw [map_sub]
          have : σ'_N ⟨σ'_N (πr c), hσ_Nsucc⟩ = σ'_N (πr c) :=
            hRetract _ hσ_Nsucc hσ_Nα
          rw [this]; simp only [_root_.sub_self]
        have hw_eq : Nsucc.subtype w = Φ c := by
          simp only [w, Φ, πr, LinearMap.sub_apply,
            Submodule.subtype_apply,
            LinearMap.comp_apply]
          simp only [AddSubgroupClass.coe_sub, codRestrict_apply, coe_comp, coe_subtype,
            Function.comp_apply]
        exact ⟨w, hw_ker, hw_eq⟩

      -- Φ surjects onto C
      have hΦ_surj : ∀ n ∈ C, ∃ c : ↥Cₘ', Φ c = n := by
        intro n hn
        have hn_map := hC_le hn
        obtain ⟨c, hc, hcn⟩ := hn_map
        refine ⟨⟨c, hc⟩, ?_⟩
        change π c - σ'_N (πr ⟨c, hc⟩) = n
        obtain ⟨⟨n', hn'_mem⟩, hn'_ker, hn'_eq⟩ := hn
        simp only [Submodule.subtype_apply] at hn'_eq
        have hπr_eq : (πr ⟨c, hc⟩ : ↥Nsucc) = ⟨n, hn'_eq ▸ hn'_mem⟩ := by
          ext; simp [πr, hcn]
        have hσ_zero : σ'_N ⟨n, hn'_eq ▸ hn'_mem⟩ = 0 := by
          have : (⟨n', hn'_mem⟩ : ↥Nsucc) = ⟨n, hn'_eq ▸ hn'_mem⟩ :=
            Subtype.ext hn'_eq
          rw [← this]; exact hn'_ker
        rw [hcn, hπr_eq, hσ_zero]; simp only [_root_.sub_zero]

      -- Φ lifts to a surjection Φ' : ↥Cₘ' → ↥C, which we use to pull back countable generation
      let Φ' : ↥Cₘ' →ₗ[R] ↥C :=
        LinearMap.codRestrict C Φ hΦ_mem
      have hΦ'_surj : Function.Surjective Φ' := by
        intro ⟨n, hn⟩
        obtain ⟨c, hc_eq⟩ := hΦ_surj n hn
        exact ⟨c, Subtype.ext hc_eq⟩
      have hΦ'_range : LinearMap.range Φ' = ⊤ :=
        LinearMap.range_eq_top.mpr hΦ'_surj
      obtain ⟨s, hs_count, hs_span⟩ := hCₘ'_cg

      -- The image of the countable generating set of Cₘ' under Φ' generates C
      refine ⟨Φ' '' s, Set.Countable.image hs_count _, ?_⟩
      rw [eq_top_iff]
      intro x _
      obtain ⟨c, rfl⟩ := hΦ'_surj x
      have hc_mem : c ∈ Submodule.span R s := hs_span ▸ Submodule.mem_top

      refine Submodule.span_induction ?_ ?_ ?_ ?_ hc_mem
      · intro x hx
        exact Submodule.subset_span (Set.mem_image_of_mem Φ' hx)
      · change Φ' 0 ∈ span R (⇑Φ' '' s)
        rw [map_zero]; exact (span R (⇑Φ' '' s)).zero_mem
      · intro a b _ _ ha hb
        change Φ' (a + b) ∈ span R (⇑Φ' '' s)
        rw [map_add]; exact Submodule.add_mem _ ha hb
      · intro r a _ ha
        change Φ' (r • a) ∈ span R (⇑Φ' '' s)
        rw [map_smul]; exact Submodule.smul_mem _ r ha



variable
  {R : Type u} [Ring R] {P : Type u} [AddCommGroup P] [Module R P]
  {γ : Ordinal.{u}}
  {Psub : Ordinal → Submodule R P}
  {C : (α : Ordinal) → α < γ → Submodule R P}

/-- Auxiliary lemma: if C β ≤ Psub(succ β) and Psub is monotone, then for any β < α,
C β ≤ Psub α. This is used repeatedly in `isInternal_of_filtration`. -/

theorem C_le_Psub
    (hPsub_mono : ∀ α β, α ≤ β → Psub α ≤ Psub β)
    (hC : ∀ (α : Ordinal) (hα : α < γ),
      IsRelativeComplement (Psub α) (Psub (Order.succ α)) (C α hα))
    {β α : Ordinal} (hβ : β < γ) (hβα : β < α) :
    C β hβ ≤ Psub α :=
  ((hC β hβ).2.1).trans (hPsub_mono _ _ (Order.succ_le_of_lt hβα))

/-- If Psub is a filtration starting at ⊥ with complements C at each successor step,
then Psub α ≤ ⨆ (β < γ), C β for all α ≤ γ. This allows the iSup = ⊤ conclusion
in `isInternal_of_filtration` to follow from Psub γ = ⊤. -/
theorem filtration_Psub_le_iSup
    (hPsub_zero : Psub 0 = ⊥)
    (hPsub_limit : ∀ o, Order.IsSuccLimit o →
      Psub o = ⨆ β, ⨆ (_ : β < o), Psub β)
    (hC : ∀ (α : Ordinal) (hα : α < γ),
      IsRelativeComplement (Psub α) (Psub (Order.succ α)) (C α hα))
    (α : Ordinal) (hαγ : α ≤ γ) :
    Psub α ≤ ⨆ (β : Ordinal) (_ : β < γ), C β ‹_› := by
  induction α using Ordinal.induction with
  | h α ih =>
    by_cases h0 : α = 0
    · rw [h0, hPsub_zero]; exact bot_le
    · by_cases hLim : Order.IsSuccLimit α
      · rw [hPsub_limit α hLim]
        exact iSup₂_le fun β hβα => ih β hβα (hβα.le.trans hαγ)
      · have hNotMin : ¬IsMin α := not_isMin_iff_ne_bot.mpr h0
        have hNotPrelimit : ¬Order.IsSuccPrelimit α := fun hp => hLim ⟨hNotMin, hp⟩
        simp only [Order.IsSuccPrelimit, not_forall, not_not] at hNotPrelimit
        obtain ⟨β, hβ⟩ := hNotPrelimit
        have hα_eq : α = Order.succ β := (Order.succ_eq_of_covBy hβ).symm
        subst hα_eq
        have hβγ : β < γ := by
          rcases hαγ.lt_or_eq with h | h
          · exact (Order.lt_succ β).trans h
          · rw [← h]; exact Order.lt_succ β
        rw [← (hC β hβγ).2.2.2]
        exact sup_le (ih β (Order.lt_succ β) hβγ.le)
          (le_iSup₂ (f := fun β (hβ : β < γ) => C β hβ) β hβγ)


/-- Elements of ⨆ (β < γ, α₀ < β < δ) C β that lie in Psub(succ α₀) must already lie in
Psub α₀. This is the key inductive step for the independence proof in `isInternal_of_filtration`:
contributions from "above" α₀ in the filtration cannot escape into the complement C α₀ unless
they are already in the lower level. The proof is by transfinite induction on δ. -/
theorem filtration_above_cap
    (hPsub_mono : ∀ α β, α ≤ β → Psub α ≤ Psub β)
    (hC : ∀ (α : Ordinal) (hα : α < γ),
      IsRelativeComplement (Psub α) (Psub (Order.succ α)) (C α hα))
    (α₀ : Ordinal)
    (δ : Ordinal) :
    ∀ (x : P),
    x ∈ ⨆ (β : Ordinal) (_ : β < γ) (_ : α₀ < β) (_ : β < δ), C β ‹β < γ› →
    x ∈ Psub (Order.succ α₀) →
    x ∈ Psub α₀ := by
  induction δ using Ordinal.induction with
  | h δ ih =>
    intro x hx hx_succ
    by_cases hδ_le : δ ≤ Order.succ α₀
    · -- Range α₀ < β < δ is empty when δ ≤ succ α₀
      have hempty : (⨆ (β : Ordinal) (_ : β < γ) (_ : α₀ < β) (_ : β < δ), C β ‹_›) = ⊥ := by
        apply eq_bot_iff.mpr
        apply iSup_le; intro β; apply iSup_le; intro _
        apply iSup_le; intro hαβ; apply iSup_le; intro hβδ
        exfalso
        exact not_lt.mpr (Order.succ_le_of_lt hαβ) (lt_of_lt_of_le hβδ hδ_le)
      rw [hempty] at hx
      rw [← @Quotient.mk_eq_zero]
      simp only [mem_bot] at hx
      rw[hx]
      rfl
    · push_neg at hδ_le
      by_cases hLim : Order.IsSuccLimit δ
      · -- Limit case: x lies in the directed union, so find a smaller cutoff
        have hdir : Directed (· ≤ ·) (fun δ' : Set.Iio δ =>
            ⨆ (β : Ordinal) (_ : β < γ) (_ : α₀ < β) (_ : β < δ'.val), C β ‹_›) := by
          intro ⟨a, ha⟩ ⟨b, hb⟩
          refine ⟨⟨max a b, by exact max_lt (mem_Iio.mp ha) (mem_Iio.mp hb)⟩, ?_, ?_⟩ <;> {
            apply iSup_le; intro β; apply iSup_le; intro hβγ
            apply iSup_le; intro hαβ; apply iSup_le; intro hβ
            apply le_iSup_of_le β; apply le_iSup_of_le hβγ
            apply le_iSup_of_le hαβ
            first
            | exact le_iSup_of_le (hβ.trans_le (le_max_left a b)) le_rfl
            | exact le_iSup_of_le (hβ.trans_le (le_max_right a b)) le_rfl }
        have hne : Nonempty (Set.Iio δ) :=
          ⟨⟨0, lt_of_le_of_lt (zero_le _) hδ_le⟩⟩
        have h_eq : (⨆ (β : Ordinal) (_ : β < γ) (_ : α₀ < β) (_ : β < δ), C β ‹_›) =
            ⨆ (δ' : Set.Iio δ),
              ⨆ (β : Ordinal) (_ : β < γ) (_ : α₀ < β) (_ : β < δ'.val), C β ‹_› := by
          apply le_antisymm
          · apply iSup_le; intro β; apply iSup_le; intro hβγ
            apply iSup_le; intro hαβ; apply iSup_le; intro hβδ
            have hsucc_β_lt : Order.succ β < δ := hLim.succ_lt hβδ
            exact le_iSup_of_le ⟨Order.succ β, hsucc_β_lt⟩
              (le_iSup_of_le β (le_iSup_of_le hβγ (le_iSup_of_le hαβ
                (le_iSup_of_le (Order.lt_succ β) le_rfl))))
          · apply iSup_le; intro ⟨δ', hδ'⟩
            apply iSup_le; intro β; apply iSup_le; intro hβγ
            apply iSup_le; intro hαβ; apply iSup_le; intro hβδ'
            exact le_iSup_of_le β (le_iSup_of_le hβγ (le_iSup_of_le hαβ
              (le_iSup_of_le (hβδ'.trans hδ') le_rfl)))
        rw [h_eq, Submodule.mem_iSup_of_directed _ hdir] at hx
        obtain ⟨⟨δ', hδ'⟩, hx'⟩ := hx
        exact ih δ' hδ' x hx' hx_succ

      · -- Successor case: δ = succ δ'
        have hδ_ne_zero : δ ≠ 0 := by
          intro h; rw [h] at hδ_le; exact not_lt.mpr (zero_le _) hδ_le
        have hNotMin : ¬IsMin δ := not_isMin_iff_ne_bot.mpr hδ_ne_zero
        have hNotPrelimit : ¬Order.IsSuccPrelimit δ := fun hp => hLim ⟨hNotMin, hp⟩
        simp only [Order.IsSuccPrelimit, not_forall, not_not] at hNotPrelimit
        obtain ⟨δ', hδ'⟩ := hNotPrelimit
        have hδ_eq : δ = Order.succ δ' := (Order.succ_eq_of_covBy hδ').symm
        subst hδ_eq

        by_cases hαδ' : α₀ < δ'
        ·
          by_cases hδ'γ : δ' < γ
          · -- Split the iSup: β < succ δ' means β < δ' or β = δ'
            have h_split : (⨆ (β : Ordinal) (_ : β < γ) (_ : α₀ < β) (_ : β < Order.succ δ'),
                C β ‹_›) =
              (⨆ (β : Ordinal) (_ : β < γ) (_ : α₀ < β) (_ : β < δ'), C β ‹_›) ⊔ C δ' hδ'γ := by
              apply le_antisymm
              · apply iSup_le; intro β; apply iSup_le; intro hβγ
                apply iSup_le; intro hαβ; apply iSup_le; intro hβsucc
                rcases (Order.lt_succ_iff.mp hβsucc).lt_or_eq with hβδ' | hβδ'
                · exact le_sup_of_le_left
                    (le_iSup_of_le β (le_iSup_of_le hβγ (le_iSup_of_le hαβ
                      (le_iSup_of_le hβδ' le_rfl))))
                · subst hβδ'; exact le_sup_right
              · apply sup_le
                · apply iSup_le; intro β; apply iSup_le; intro hβγ
                  apply iSup_le; intro hαβ; apply iSup_le; intro hβδ'
                  exact le_iSup_of_le β (le_iSup_of_le hβγ (le_iSup_of_le hαβ
                    (le_iSup_of_le (hβδ'.trans (Order.lt_succ δ')) le_rfl)))
                · exact le_iSup_of_le δ' (le_iSup_of_le hδ'γ (le_iSup_of_le hαδ'
                    (le_iSup_of_le (Order.lt_succ δ') le_rfl)))

            rw [h_split, Submodule.mem_sup] at hx
            obtain ⟨y_below, hy_below, y_top, hy_top, hy_eq⟩ := hx

            -- y_below lands in Psub δ' (all β-contributions are below δ')
            have hy_below_δ' : y_below ∈ Psub δ' := by
              have hle : (⨆ (β : Ordinal) (_ : β < γ) (_ : α₀ < β) (_ : β < δ'),
                  C β ‹_›) ≤ Psub δ' := by
                apply iSup_le; intro β; apply iSup_le; intro hβγ
                apply iSup_le; intro _; apply iSup_le; intro hβδ'
                exact C_le_Psub hPsub_mono hC hβγ hβδ'
              exact hle hy_below

            have hx_δ' : x ∈ Psub δ' :=
              hPsub_mono _ _ (Order.succ_le_of_lt hαδ') hx_succ

            -- y_top = x - y_below ∈ Psub δ'
            have hy_top_δ' : y_top ∈ Psub δ' := by
              have : y_top = x - y_below := by exact eq_sub_of_add_eq' hy_eq
              rw [show y_top = x - y_below from by exact this]
              exact (Psub δ').sub_mem hx_δ' hy_below_δ'

            -- C δ' is disjoint from Psub δ' by the devissage hypothesis, so y_top = 0
            have hy_top_zero : y_top = 0 := by
              have hDisj := (hC δ' hδ'γ).2.2.1
              rw [Submodule.disjoint_def] at hDisj
              exact hDisj y_top hy_top_δ' hy_top

            have : x = y_below := by
              rw[hy_top_zero] at hy_eq
              simp only [add_zero] at hy_eq
              exact id (Eq.symm hy_eq)
            rw [this]
            have hy_below_succ : y_below ∈ Psub (Order.succ α₀) := this ▸ hx_succ
            exact ih δ' (Order.lt_succ δ') y_below hy_below hy_below_succ

          · -- δ' ≥ γ: the β = δ' term is filtered out, so same as the β < δ' case
            have h_same : (⨆ (β : Ordinal) (_ : β < γ) (_ : α₀ < β) (_ : β < Order.succ δ'),
                C β ‹_›) =
              (⨆ (β : Ordinal) (_ : β < γ) (_ : α₀ < β) (_ : β < δ'), C β ‹_›) := by
              apply le_antisymm
              · apply iSup_le; intro β; apply iSup_le; intro hβγ
                apply iSup_le; intro hαβ; apply iSup_le; intro hβsucc
                have hβδ' : β < δ' := by
                  rcases (Order.lt_succ_iff.mp hβsucc).lt_or_eq with h | h
                  · exact h
                  · exfalso; exact hδ'γ (h ▸ hβγ)
                exact le_iSup_of_le β (le_iSup_of_le hβγ (le_iSup_of_le hαβ
                  (le_iSup_of_le hβδ' le_rfl)))
              · apply iSup_le; intro β; apply iSup_le; intro hβγ
                apply iSup_le; intro hαβ; apply iSup_le; intro hβδ'
                exact le_iSup_of_le β (le_iSup_of_le hβγ (le_iSup_of_le hαβ
                  (le_iSup_of_le (hβδ'.trans (Order.lt_succ δ')) le_rfl)))
            rw [h_same] at hx
            exact ih δ' (Order.lt_succ δ') x hx hx_succ

        · -- δ' ≤ α₀: the range α₀ < β < succ δ' is empty
          push_neg at hαδ'
          have hempty : (⨆ (β : Ordinal) (_ : β < γ) (_ : α₀ < β) (_ : β < Order.succ δ'),
              C β ‹_›) = ⊥ := by
            apply eq_bot_iff.mpr
            apply iSup_le; intro β; apply iSup_le; intro _
            apply iSup_le; intro hαβ; apply iSup_le; intro hβ
            exfalso
            exact not_lt.mpr ((Order.lt_succ_iff.mp hβ).trans hαδ') hαβ
          rw [hempty] at hx
          simp only [mem_bot] at hx
          exact (Quotient.mk_eq_zero (Psub α₀)).mp (congrArg Submodule.Quotient.mk hx)


/-- Given an ordinal-indexed filtration Psub of P with:
- `Psub 0 = ⊥`, `Psub γ = ⊤`;
- Psub monotone and continuous at limits;
- a direct complement C α at each successor step (i.e., Psub(succ α) = Psub α ⊕ C α);

the family `(C α)_{α < γ}` is an internal direct sum decomposition of P.

This is the abstract version of Kaplansky's devissage theorem that is used in the
proof of `kaplansky_devissage_iff_direct_sum` and more generally to assemble
filtration-based arguments into direct sum conclusions. -/
theorem isInternal_of_filtration
    {R : Type u} [Ring R] {P : Type u} [AddCommGroup P] [Module R P]
    {γ : Ordinal.{u}}
    (Psub : Ordinal → Submodule R P)
    (hPsub_zero : Psub 0 = ⊥)
    (hPsub_top : Psub γ = ⊤)
    (hPsub_mono : ∀ α β, α ≤ β → Psub α ≤ Psub β)
    (hPsub_limit : ∀ o, Order.IsSuccLimit o →
      Psub o = ⨆ β, ⨆ (_ : β < o), Psub β)
    (C : (α : Ordinal) → α < γ → Submodule R P)
    (hC : ∀ (α : Ordinal) (hα : α < γ),
      IsRelativeComplement (Psub α) (Psub (Order.succ α)) (C α hα)) :
    DirectSum.IsInternal (fun (p : {α // α < γ}) => C p.val p.prop) := by
  classical
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor

  · -- Independence of C:
    -- For each α₀ < γ, show C α₀ is disjoint from ⨆ (j ≠ α₀) C j.
    -- Split the complement into "below α₀" and "above α₀" contributions.
    -- Below: lands in Psub α₀ by C_le_Psub. Above: lands in Psub α₀ by filtration_above_cap.
    -- Then disjointness from C α₀ gives x = 0.
    rw [iSupIndep_def]
    intro ⟨α₀, hα₀⟩
    rw [Submodule.disjoint_def]
    intro x hx_C hx_rest

    have hx_succ : x ∈ Psub (Order.succ α₀) := (hC α₀ hα₀).2.1 hx_C

    suffices hx_Psub : x ∈ Psub α₀ by
      exact Submodule.disjoint_def.mp (hC α₀ hα₀).2.2.1 x hx_Psub hx_C

    have h_split : (⨆ (j : {α // α < γ}) (_ : j ≠ ⟨α₀, hα₀⟩), C j.val j.prop) ≤
        (⨆ (β : Ordinal) (_ : β < γ) (_ : β < α₀), C β ‹_›) ⊔
        (⨆ (β : Ordinal) (_ : β < γ) (_ : α₀ < β), C β ‹_›) := by
      apply iSup_le; intro ⟨β, hβ⟩; apply iSup_le; intro hne
      have hne' : β ≠ α₀ := fun h => hne (Subtype.ext h)
      rcases hne'.lt_or_gt with hlt | hlt
      · exact le_sup_of_le_left
          (le_iSup_of_le β (le_iSup_of_le hβ (le_iSup_of_le hlt le_rfl)))
      · exact le_sup_of_le_right
          (le_iSup_of_le β (le_iSup_of_le hβ (le_iSup_of_le hlt le_rfl)))

    obtain ⟨x_below, hx_below, x_above, hx_above, hx_eq⟩ :=
      Submodule.mem_sup.mp (h_split hx_rest)

    have hx_below_Psub : x_below ∈ Psub α₀ := by
      have hle : (⨆ (β : Ordinal) (_ : β < γ) (_ : β < α₀), C β ‹_›) ≤ Psub α₀ :=
        iSup_le fun β => iSup_le fun hβγ => iSup_le fun hβα₀ =>
          C_le_Psub hPsub_mono hC hβγ hβα₀
      exact hle hx_below

    have hx_above_succ : x_above ∈ Psub (Order.succ α₀) := by
      have : x_above = x - x_below := by exact eq_sub_of_add_eq' hx_eq
      rw [show x_above = x - x_below from by exact this]
      exact (Psub (Order.succ α₀)).sub_mem hx_succ
        (hPsub_mono _ _ (Order.le_succ α₀) hx_below_Psub)

    -- x_above ∈ Psub α₀ by filtration_above_cap (transfinite induction on γ)
    have hx_above_Psub : x_above ∈ Psub α₀ := by
      have hx_above' : x_above ∈ ⨆ (β : Ordinal) (_ : β < γ) (_ : α₀ < β) (_ : β < γ),
          C β ‹_› := by
        have hle : (⨆ (β : Ordinal) (_ : β < γ) (_ : α₀ < β), C β ‹_›) ≤
            ⨆ (β : Ordinal) (_ : β < γ) (_ : α₀ < β) (_ : β < γ), C β ‹_› :=
          iSup_le fun β => iSup_le fun hβγ => iSup_le fun hαβ =>
            le_iSup_of_le β (le_iSup_of_le hβγ (le_iSup_of_le hαβ
              (le_iSup_of_le hβγ le_rfl)))
        exact hle hx_above
      exact filtration_above_cap hPsub_mono hC α₀ γ
        x_above hx_above' hx_above_succ

    rw [← hx_eq]
    exact (Psub α₀).add_mem hx_below_Psub hx_above_Psub

  · -- iSup C = ⊤: follows from Psub γ = ⊤ and filtration_Psub_le_iSup
    rw [eq_top_iff, ← hPsub_top]
    exact (filtration_Psub_le_iSup hPsub_zero hPsub_limit hC γ le_rfl).trans
      (iSup₂_le fun β hβγ =>
        le_iSup (fun (p : {α // α < γ}) => C p.val p.prop) ⟨β, hβγ⟩)
