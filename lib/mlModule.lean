/-
Copyright (c) 2026 Liran Shaul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Liran Shaul

This file is part of the formalization project accompanying the paper:
  "Formalization in Lean of faithfully flat descent of projectivity"
  by Liran Shaul, Charles University in Prague.

We define and study Mittag-Leffler modules over a commutative ring R, following
Section 7 of the paper and the Stacks Project (Tag 0599). The central definition is:

  Module.IsMittagLeffler R M

which asserts that for every finitely presented R-module P and R-linear map f : P → M,
there exists a finitely presented R-module Q and a map g : P → Q such that f and g
mutually dominate each other (in the sense of LinearMap.MutuallyDominate from
lib.Domination).

We establish four equivalent characterizations of this property (corresponding to
Proposition 88.6 / Tag 0599 of the Stacks Project and Proposition 6.11 of Perry):

  (1) IsMittagLeffler   — the direct definition above.
  (2) IsMittagLeffler'  — for a fixed presentation M = colim Mᵢ of finitely presented
                          modules, each inclusion Mᵢ → M is dominated by some transition
                          map fᵢⱼ.
  (3) IsMittagLeffler'' — for each i, some fᵢⱼ factors through every fᵢₖ with k ≥ i.
  (4) IsMittagLeffler'''— for every R-module N, the inverse system (Hom(Mᵢ, N)) is
                          Mittag-Leffler in the sense of InverseSystem.IsMittagLeffler.

We note that the equivalence (1) ↔ (2) requires an argument not fully spelled out in
the Stacks Project or Perry; we provide a corrected proof.

The main structural results proved here are:

  finitePresentation_isMittagLeffler  — finitely presented modules are Mittag-Leffler
                                        (Section 7 of the paper).
  free_isMittagLeffler                — free modules are Mittag-Leffler.
  IsMittagLeffler.of_direct_summand  — direct summands of Mittag-Leffler modules are
                                        Mittag-Leffler.
  proj_is_Mittag_Leffler             — projective modules are Mittag-Leffler (Section 7).
  mittagLeffler_countablyGenerated_has_countable_colimit
                                     — a countably generated Mittag-Leffler module admits
                                       a presentation over a countable directed index set
                                       (Lemma 10.92.1 / Tag 059W of the Stacks Project,
                                       Lemma 7.1 of Perry). This is the key structural
                                       lemma used in the proof of both main theorems of
                                       the paper.
-/

import Mathlib.Algebra.Module.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Colimit.Module
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Order.Iterate
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.Order.Directed
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.LinearAlgebra.Prod
import lib.mlSystem
import lib.Domination
import lib.fpLemma
import lib.Lazard

universe u

variable {R : Type u} [CommRing R]

namespace Module

section MittagLefflerDef

/-- A module `M` over a commutative ring `R` is Mittag-Leffler if for every finitely
presented R-module `P` and every R-linear map `f : P →ₗ[R] M`, there exists a finitely
presented R-module `Q` and a map `g : P →ₗ[R] Q` such that `f` and `g` mutually dominate
each other (i.e., ker(f ⊗ id_T) = ker(g ⊗ id_T) for every R-module T).

This is Definition 88.7 of the Stacks Project (Tag 0599) and Definition 6.1 / Definition 7
of Perry's paper, stated here in the equivalent form given by Proposition 88.6 (1). -/
def IsMittagLeffler (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  ∀ (P : Type u) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.FinitePresentation R P),
    ∀ f : P →ₗ[R] M,
      ∃ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q) (_ : Module.FinitePresentation R Q),
        ∃ g : P →ₗ[R] Q, LinearMap.MutuallyDominate f g

variable (R : Type u) [CommRing R]

/-- Second characterization of the Mittag-Leffler property (Proposition 88.6 (2) of the
Stacks Project / Tag 0599): given a presentation M = colim_{i ∈ ι} Mᵢ of M as a directed
colimit of finitely presented modules with transition maps f, the module M is Mittag-Leffler
if and only if for each index i there exists j ≥ i such that the transition map fᵢⱼ : Mᵢ → Mⱼ
dominates the canonical inclusion of R ι F f i : Mᵢ → M. -/
def IsMittagLeffler' {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] [DecidableEq ι]
    (F : ι → Type u) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
    [∀ i, Module.FinitePresentation R (F i)]
    (f : ∀ i j, i ≤ j → F i →ₗ[R] F j)
    [DirectedSystem F (fun i j h => f i j h)] : Prop :=
  ∀ i : ι, ∃ j : ι, ∃ (hij : i ≤ j),
    LinearMap.Dominates (Module.DirectLimit.of R ι F f i) (f i j hij)

/-- Third characterization of the Mittag-Leffler property (Proposition 88.6 (3) of the
Stacks Project / Tag 0599): for each index i there exists j ≥ i such that for all k ≥ i,
the transition map fᵢⱼ : Mᵢ → Mⱼ factors through fᵢₖ : Mᵢ → Mₖ. -/
def IsMittagLeffler'' {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (F : ι → Type u) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
    [∀ i, Module.FinitePresentation R (F i)]
    (f : ∀ i j, i ≤ j → F i →ₗ[R] F j) : Prop :=
  ∀ i : ι, ∃ j : ι, ∃ (hij : i ≤ j), ∀ k : ι, ∀ (hik : i ≤ k),
    ∃ (h : F k →ₗ[R] F j), f i j hij = h.comp (f i k hik)

/-- The contravariant Hom functor applied to the directed system (F, f): for each pair
i ≤ j and target module N, precomposition with fᵢⱼ gives a map Hom(Fⱼ, N) → Hom(Fᵢ, N).
These maps assemble into an inverse system, which is used in the fourth characterization
of the Mittag-Leffler property. -/
def HomInverseSystemMap {ι : Type u} [Preorder ι]
    (F : ι → Type u) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
    (f : ∀ i j, i ≤ j → F i →ₗ[R] F j)
    (N : Type u) [AddCommGroup N] [Module R N]
    (i j : ι) (hij : i ≤ j) : (F j →ₗ[R] N) → (F i →ₗ[R] N) :=
  fun g => g.comp (f i j hij)

/-- The family of precomposition maps `HomInverseSystemMap R F f N` satisfies the axioms
of an inverse system: it is compatible with identities (using the identity axiom for the
directed system F) and with composition (using the composition axiom for F). -/
theorem HomInverseSystem {ι : Type u} [Preorder ι]
    (F : ι → Type u) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
    (f : ∀ i j, i ≤ j → F i →ₗ[R] F j)
    (hf : ∀ i, f i i (le_refl i) = LinearMap.id)
    (hcomp : ∀ i j k (hij : i ≤ j)
    (hjk : j ≤ k), f i k (hij.trans hjk) = (f j k hjk).comp (f i j hij))
    (N : Type u) [AddCommGroup N] [Module R N] :
    InverseSystem (fun {i j} (hij : i ≤ j) => HomInverseSystemMap R F f N i j hij) where
  map_self i x := by
    simp only [HomInverseSystemMap]
    rw [hf i]
    simp
  map_map i j k hij hjk x := by
    simp only [HomInverseSystemMap]
    rw [hcomp i j k hij hjk]
    simp only [LinearMap.comp_assoc]

/-- Fourth characterization of the Mittag-Leffler property (Proposition 88.6 (4) of the
Stacks Project / Tag 0599): for every R-module N, the inverse system of Hom-modules
(Hom(Fᵢ, N), precomposition with fᵢⱼ) is Mittag-Leffler in the sense of
InverseSystem.IsMittagLeffler (defined in mlSystem.lean). This condition connects the
module-theoretic definition to the inverse system theory used in the proof of the main
projectivity theorem. -/
def IsMittagLeffler''' {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (F : ι → Type u) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
    [∀ i, Module.FinitePresentation R (F i)]
    (f : ∀ i j, i ≤ j → F i →ₗ[R] F j)
    (hf : ∀ i, f i i (le_refl i) = LinearMap.id)
    (hcomp : ∀ i j k (hij : i ≤ j)
    (hjk : j ≤ k), f i k (hij.trans hjk) = (f j k hjk).comp (f i j hij)) : Prop :=
  ∀ (N : Type u) [AddCommGroup N] [Module R N],
    ∀ _ : ∀ i, Nonempty (F i →ₗ[R] N),
    @InverseSystem.IsMittagLeffler ι _
      (fun i => F i →ₗ[R] N)
      (fun _ => ⟨0⟩)
      (fun {i j} (hij : i ≤ j) => HomInverseSystemMap R F f N i j hij)
      (HomInverseSystem R F f hf hcomp N)

/-- Unfolding lemma for `IsMittagLeffler'''`: the fourth characterization is equivalent to
the explicit image-stabilization condition on the inverse system of Hom-modules, namely
that for each i there exists j ≥ i such that for all k ≥ j, the image of
(g ↦ g ∘ fᵢₖ) : Hom(Fₖ, N) → Hom(Fᵢ, N) equals that of
(g ↦ g ∘ fᵢⱼ) : Hom(Fⱼ, N) → Hom(Fᵢ, N). -/
theorem isMittagLeffler'''_iff {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (F : ι → Type u) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
    [∀ i, Module.FinitePresentation R (F i)]
    (f : ∀ i j, i ≤ j → F i →ₗ[R] F j)
    (hf : ∀ i, f i i (le_refl i) = LinearMap.id)
    (hcomp : ∀ i j k (hij : i ≤ j)
    (hjk : j ≤ k), f i k (hij.trans hjk) = (f j k hjk).comp (f i j hij)) :
    IsMittagLeffler''' R F f hf hcomp ↔
    ∀ (N : Type u) [AddCommGroup N] [Module R N],
      ∀ i : ι, ∃ j : ι, ∃ (hij : i ≤ j), ∀ k : ι, ∀ (hjk : j ≤ k),
        Set.range (fun (g : F k →ₗ[R] N) => g.comp (f i k (hij.trans hjk))) =
        Set.range (fun (g : F j →ₗ[R] N) => g.comp (f i j hij)) := by
  constructor
  · intro h N _ _ i
    have hne : ∀ i, Nonempty (F i →ₗ[R] N) := fun _ => ⟨0⟩
    obtain ⟨j, hij, hstab⟩ := @InverseSystem.IsMittagLeffler.stabilization ι _
      (fun i => F i →ₗ[R] N) (fun _ => ⟨0⟩)
      (fun {i j} (hij : i ≤ j) => HomInverseSystemMap R F f N i j hij)
      (HomInverseSystem R F f hf hcomp N)
      (h N hne) i
    use j, hij
    intro k hjk
    have := hstab k hjk
    unfold HomInverseSystemMap at this
    exact this
  · intro h N _ _ hne
    exact @InverseSystem.IsMittagLeffler.mk ι _
      (fun i => F i →ₗ[R] N) (fun _ => ⟨0⟩)
      (fun {i j} (hij : i ≤ j) => HomInverseSystemMap R F f N i j hij)
      (HomInverseSystem R F f hf hcomp N)
      (fun i => by
        obtain ⟨j, hij, hstab⟩ := h N i
        use j, hij
        intro k hjk
        unfold HomInverseSystemMap
        exact hstab k hjk)

end MittagLefflerDef




section Equivalences

variable {R : Type u} [CommRing R]
variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] [DecidableEq ι]
variable (F : ι → Type u) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
variable (f : ∀ i j, i ≤ j → F i →ₗ[R] F j)


open CategoryTheory CategoryTheory.Limits


/-- The Mittag-Leffler property is preserved under R-linear isomorphisms of modules.
This allows us to transfer the property between isomorphic presentations without
re-establishing it from scratch. -/
theorem IsMittagLeffler.of_iso (R : Type u) [CommRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (h : IsMittagLeffler R M) (e : M ≃ₗ[R] N) :
    IsMittagLeffler R N := by
  rw[IsMittagLeffler]
  rw[IsMittagLeffler] at h
  intro P x1 x2 pFP f
  let f' := (e.symm).comp f
  obtain ⟨Q, Qab , Qmod , Qfp , g, f'gDomMut ⟩ := h P x1 x2 pFP f'
  use Q, Qab, Qmod, Qfp, g
  rw[LinearMap.MutuallyDominate] at f'gDomMut
  let f'domg := f'gDomMut.1
  let gdomf' := f'gDomMut.2
  have feq : f = e.comp f' := by
    simp only [f']
    rw[←LinearMap.comp_assoc]
    rw [@LinearEquiv.comp_symm]
    rw [@LinearMap.id_comp]
  rw[feq]
  rw[LinearMap.MutuallyDominate]

  constructor
  · rw[LinearMap.Dominates]
    intro Q Qab QMod x hx
    rw[←feq] at hx
    let Qid : Q →ₗ[R] Q := LinearMap.id
    have qidid : Qid = Qid.comp Qid := by
      ext x
      rw[LinearMap.comp_apply]
      simp only [Qid]
      simp only [LinearMap.id_coe, id_eq]
    have : TensorProduct.map f' Qid x = 0 := by
      simp only [f']
      rw[qidid]
      have tensId : TensorProduct.map (↑e.symm ∘ₗ f) (Qid ∘ₗ Qid) =
        (TensorProduct.map (e.symm).toLinearMap Qid).comp (TensorProduct.map f Qid) := by
        rw [@TensorProduct.map_comp]
      rw[tensId]
      rw[LinearMap.comp_apply]
      rw[hx]
      rw[map_zero]
    rw[LinearMap.Dominates] at f'domg
    let T := f'domg Q Qab QMod x this
    exact T
  · rw[LinearMap.Dominates]
    intro Q Qab QMod x hx
    let T := gdomf' Q Qab QMod x hx
    let Qid : Q →ₗ[R] Q := LinearMap.id
    have qidid : Qid = Qid.comp Qid := by
      ext x
      rw[LinearMap.comp_apply]
      simp only [Qid]
      simp only [LinearMap.id_coe, id_eq]
    have tensId : TensorProduct.map (e ∘ₗ f') (Qid) =
      (TensorProduct.map (e).toLinearMap Qid).comp (TensorProduct.map f' Qid) := by
      rw [←@TensorProduct.map_comp]
      nth_rw 1[qidid]
    rw[tensId]
    rw[LinearMap.comp_apply]
    rw[T]
    rw[map_zero]


/-- Any map from a finitely presented module P into a directed colimit M = colim Fᵢ
factors through one of the components: there exists an index j and a map h : P →ₗ[R] Fⱼ
such that g = (of j) ∘ h. This follows from the categorical finite presentability of P
(established in fpLemma.lean) applied to the colimit cocone of the direct limit. -/
theorem FinitePresentation.exists_factorization_of_colimit
    [DirectedSystem F (fun i j h => f i j h)]
    {P : Type u} [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
    (g : P →ₗ[R] Module.DirectLimit F f) :
    ∃ j, ∃ h : P →ₗ[R] F j, g = (Module.DirectLimit.of R ι F f j) ∘ₗ h := by
  let D := ModuleCat.directLimitDiagram F f
  let c := ModuleCat.directLimitCocone F f
  have hc : IsColimit c := ModuleCat.directLimitIsColimit F f

  haveI : IsFinitelyPresentable.{u} (ModuleCat.of R P) := by infer_instance
  let g' : ModuleCat.of R P ⟶ c.pt := ModuleCat.ofHom g
  obtain ⟨j, p, hp⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc g'
  refine ⟨j, p.hom, ?_⟩
  ext x
  have := congrArg ModuleCat.Hom.hom hp
  simp only [ModuleCat.hom_comp] at this
  exact congrFun (congrArg DFunLike.coe this.symm) x


variable [∀ i, Module.FinitePresentation R (F i)]
variable [DirectedSystem F (fun i j h => f i j h)]

/-- The equivalence of characterizations (1) and (2) of Mittag-Leffler modules:
`IsMittagLeffler'` (condition (2) of Proposition 88.6 / Tag 0599 of the Stacks Project)
is equivalent to `IsMittagLeffler` (condition (1), the intrinsic definition).

The proof of (2) ⟹ (1): given f : P → M, use
`FinitePresentation.exists_factorization_of_colimit` to factor f through some Fᵢ, then
apply the stabilization index j from condition (2). The mutual domination is established
by combining the transitivity and factorization lemmas from lib.Domination.

The proof of (1) ⟹ (2): apply condition (1) to the inclusion Fᵢ → M, obtaining a
finitely presented Q and a mutually dominating map g : Fᵢ → Q. The Mittag-Leffler
condition gives a factorization of the colimit map through some Fⱼ; the argument then
uses directedness to find a common index k and a finite generation argument to propagate
the required equation from generators to all of Fᵢ. This step goes beyond what is
explicitly proved in the Stacks Project or Perry, and provides the corrected argument
mentioned in Section 7 of the paper. -/
theorem isMittagLeffler_iff_isMittagLeffler' :
    IsMittagLeffler' R F f ↔ IsMittagLeffler R (Module.DirectLimit F f) := by
  constructor
  · intro ML'
    rw [IsMittagLeffler'] at ML'
    rw [IsMittagLeffler]
    intro P _ PModule PFP fPM
    obtain ⟨i, g', g'fact⟩ := FinitePresentation.exists_factorization_of_colimit F f fPM
    obtain ⟨j, hij, domin ⟩ := ML' i
    use (F j)
    refine ⟨inferInstance,inferInstance,inferInstance,?_⟩
    let g := (f i j hij).comp g'
    use g
    rw[LinearMap.MutuallyDominate]
    constructor
    · simp only [g]
      rw [g'fact]
      exact LinearMap.Dominates.comp_right g' domin
    · have factorization : fPM = (DirectLimit.of R ι F f j) ∘ₗ g := by
        rw [g'fact]
        simp only [g]
        rw [← LinearMap.comp_assoc]
        congr 1
        ext x
        exact (Module.DirectLimit.of_f (hij := hij)).symm
      exact LinearMap.Dominates.of_factors (DirectLimit.of R ι F f j) factorization
  · intro ML
    rw [IsMittagLeffler']
    intro i
    rw [IsMittagLeffler] at ML
    have FIFp : Module.FinitePresentation R (F i) := inferInstance
    let FMitoM := Module.DirectLimit.of R ι F f i
    obtain ⟨Q, _, _, QFP, g, fdomg, gdomf⟩ := ML (F i) inferInstance inferInstance FIFp FMitoM
    have cokerFP : Module.FinitePresentation R (Q ⧸ LinearMap.range g) := by
      apply Module.finitePresentation_of_surjective (LinearMap.range g).mkQ
      · exact Submodule.mkQ_surjective (LinearMap.range g)
      · rw [Submodule.ker_mkQ]
        rw [← Submodule.map_top g]
        exact Submodule.FG.map g Module.Finite.fg_top
    have fact : ∃ (h : Q →ₗ[R] Module.DirectLimit F f), FMitoM = h.comp g :=
      LinearMap.dominates_iff_factors_through g FMitoM |>.mp gdomf
    obtain ⟨h, hfact⟩ := fact
    -- Factor h : Q → DirectLimit F f through some component F j
    obtain ⟨j, h', h'fact⟩ := FinitePresentation.exists_factorization_of_colimit F f h
    -- Use directedness to find a common upper bound k for i and j
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j

    have fjFactfk :
      Module.DirectLimit.of R ι F f j = (Module.DirectLimit.of R ι F f k).comp (f j k hjk) := by
      ext x
      simp only [LinearMap.comp_apply]
      exact (Module.DirectLimit.of_f (hij := hjk) (x := x)).symm

    let h'' := (f j k hjk).comp h'

    have fiFactfk :
      DirectLimit.of R ι F f i = (DirectLimit.of R ι F f k).comp (f i k hik) := by
      ext x
      simp only [LinearMap.comp_apply]
      exact (Module.DirectLimit.of_f (hij := hik) (x := x)).symm

    -- After base-changing to F k, the two composite maps (of k) ∘ (h'' ∘ g) and (of k) ∘ fᵢₖ
    -- agree, so by the zero-exact property of direct limits they agree after further
    -- postcomposing with some transition map f k l.
    have keyFact : (DirectLimit.of R ι F f k) ∘ₗ (h'' ∘ₗ g) =
      (DirectLimit.of R ι F f k) ∘ₗ (f i k hik) := by
      simp only [h'']
      rw[←LinearMap.comp_assoc]
      rw[←LinearMap.comp_assoc]
      rw[←fjFactfk]
      rw[←h'fact]
      rw[←fiFactfk]
      exact id (Eq.symm hfact)
    -- Use finite generation of Fᵢ to find a single index l at which the equation holds
    have : ∃ (l : ι) (hkl : k ≤ l), (f k l hkl).comp (h''.comp g) =
      (f k l hkl).comp (f i k hik) := by
          have h_ptwise : ∀ x : F i, (DirectLimit.of R ι F f k) ((h'' ∘ₗ g) x) =
                                (DirectLimit.of R ι F f k) ((f i k hik) x) :=
            fun x => congrFun (congrArg DFunLike.coe keyFact) x
          haveI : Module.Finite R (F i) := inferInstance
          obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := R) (M := F i)
          have h_stage : ∀ t ∈ T, ∃ l, ∃ hkl : k ≤ l,
            f k l hkl ((h'' ∘ₗ g) t) = f k l hkl ((f i k hik) t) :=
              fun t _ => Module.DirectLimit.exists_eq_of_of_eq (h_ptwise t)
          choose! l_fun hkl_fun heq_fun using h_stage

          obtain ⟨l, hkl, hl_all⟩ : ∃ l, k ≤ l ∧ ∀ t ∈ T, l_fun t ≤ l := by
            have h_upper : ∀ S : Finset (F i), ∃ l, ∀ t ∈ S, l_fun t ≤ l := by
              classical
              intro S
              induction S using Finset.induction_on with
                | empty => exact ⟨k, fun _ h => (Finset.notMem_empty _ h).elim⟩
                | @insert a s ha ih =>
                  obtain ⟨l', hl'⟩ := ih
                  obtain ⟨l, hl_fun_a, hl'_l⟩ := exists_ge_ge (l_fun a) l'
                  exact ⟨l, fun t ht => by
                    simp only [Finset.mem_insert] at ht
                    rcases ht with rfl | ht
                    · exact hl_fun_a
                    · exact le_trans (hl' t ht) hl'_l⟩
            obtain ⟨l', hl'⟩ := h_upper T
            obtain ⟨l, hkl, hl'l⟩ := exists_ge_ge k l'
            exact ⟨l, hkl, fun t ht => le_trans (hl' t ht) hl'l⟩

          have h_agree_gens : ∀ t ∈ T, (f k l hkl ∘ₗ h'' ∘ₗ g) t = (f k l hkl ∘ₗ f i k hik) t := by
            intro t ht
            simp only [LinearMap.coe_comp, Function.comp_apply]
            have hkl_t := hkl_fun t ht
            have hl_t_l := hl_all t ht
            rw [← DirectedSystem.map_map (f := fun i j h => f i j h) hkl_t hl_t_l (h'' (g t)),
              ← DirectedSystem.map_map (f := fun i j h => f i j h) hkl_t hl_t_l ((f i k hik) t)]
            congr 1
            exact heq_fun t ht

          have h_maps_eq : f k l hkl ∘ₗ h'' ∘ₗ g = f k l hkl ∘ₗ f i k hik := by
            apply LinearMap.ext
            intro x
            have hx_mem : x ∈ Submodule.span R (T : Set (F i)) := by rw [hT]; trivial
            refine Submodule.span_induction ?_ ?_ ?_ ?_ hx_mem
            · exact fun t ht => h_agree_gens t ht
            · simp only [map_zero]
            · intro a b _ _ ha hb
              simp only [LinearMap.coe_comp, Function.comp_apply, map_add,ha,hb]
            · intro r a _ ha
              simp only [LinearMap.coe_comp, Function.comp_apply, map_smul,ha]
          exact ⟨l, hkl, h_maps_eq⟩

    obtain ⟨l,hkl,lfact⟩ := this
    have hil : i≤ l := by exact Std.IsPreorder.le_trans i k l hik hkl
    use l
    refine ⟨hil,?_⟩
    -- The domination at l is obtained by transitivity from fdomg and a factorization argument
    apply LinearMap.Dominates.trans fdomg
    have : (f k l hkl) ∘ₗ (f i k hik) = (f i l hil) := by
        ext x
        rw [← DirectedSystem.map_map (f := f) hik hkl]
        rw [@LinearMap.comp_apply]
    rw[this] at lfact
    apply LinearMap.Dominates.of_factors
    · rw [←lfact]
      rw [← @LinearMap.comp_assoc]


/-- The equivalence of characterizations (2) and (3) of Mittag-Leffler modules
(Proposition 88.6 (2) ↔ (3) of the Stacks Project / Tag 0599).

The direction (2) ⟹ (3): given domination of the inclusion Fᵢ → M by fᵢⱼ, apply
`LinearMap.dominates_iff_factors_through` (Theorem 6.1 of Perry / Tag 059D) to the
cokernel of fᵢₖ, which is finitely presented because each Fᵢ is finitely presented.

The direction (3) ⟹ (2): given the explicit factorization condition, use the natural
isomorphism between the direct limit of (Fᵢ ⊗ Q) and (DirectLimit Fᵢ) ⊗ Q
(from lib.TensorDirectLimit) to reduce the domination condition to a finite stage. -/
theorem isMittagLeffler'_iff_isMittagLeffler''
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] [DecidableEq ι]
    (F : ι → Type u) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
    [∀ i, Module.FinitePresentation R (F i)]
    (f : ∀ i j, i ≤ j → F i →ₗ[R] F j)
    [DirectedSystem F (fun i j h => f i j h)] :
    IsMittagLeffler' R F f ↔ IsMittagLeffler'' R F f := by
  constructor
  · intro ML'
    rw[IsMittagLeffler'] at ML'
    rw[IsMittagLeffler'']
    intro i
    obtain ⟨j,hij,domRel⟩ := ML' i
    use j,hij
    intro k hik
    -- The cokernel of fᵢₖ is finitely presented since Fₖ is finitely presented
    have fpCoker : Module.FinitePresentation R (F k ⧸ LinearMap.range (f i k hik)) := by
      apply Module.finitePresentation_of_surjective (LinearMap.range (f i k hik)).mkQ
      · exact Submodule.mkQ_surjective (LinearMap.range (f i k hik))
      · rw [Submodule.ker_mkQ]
        rw [← Submodule.map_top (f i k hik)]
        exact Submodule.FG.map (f i k hik) Module.Finite.fg_top

    -- The inclusion of R ι F f i factors through of R ι F f k via fᵢₖ
    have fikRel : (DirectLimit.of R ι F f i) = (DirectLimit.of R ι F f k).comp (f i k hik) := by
      ext x
      simp only [LinearMap.comp_apply]
      exact (Module.DirectLimit.of_f (hij := hik) (x := x)).symm
    -- Transitivity of domination gives that fᵢⱼ dominates fᵢₖ
    have domfik : (f i k hik).Dominates (f i j hij) := by
      exact LinearMap.Dominates.trans
        (LinearMap.Dominates.of_factors (DirectLimit.of R ι F f k) fikRel) domRel
    -- Apply dominates_iff_factors_through to extract the explicit factorization
    have : ∃ (h : F k →ₗ[R] F j), f i j hij = h.comp (f i k hik)  := by
      apply LinearMap.dominates_iff_factors_through (f i k hik) (f i j hij) |>.mp domfik
    exact this
  · intro ML''
    rw[IsMittagLeffler''] at ML''
    rw[IsMittagLeffler']
    intro i
    obtain ⟨j,hij,cond⟩ := ML'' i
    use j,hij
    intro Q _ _ x hx
    -- Reduce domination to a finite stage using the tensor-commutes-with-colimit isomorphism
    have key : ∃ k:ι, ∃(hik: k≥ i),  (TensorProduct.map (f i k hik) LinearMap.id) x = 0 := by
      let iso := TensorProduct.directLimitLeft f Q
      let G : ι → Type u := fun k => TensorProduct R (F k)  Q
      let g : ∀ i j, i ≤ j → G i →ₗ[R] G j := fun i j hij => (f i j hij).rTensor Q
      have hx' : Module.DirectLimit.of R ι G g i x = 0 := by
        have comm : Module.DirectLimit.of R ι G g i =
          iso ∘ₗ (DirectLimit.of R ι F f i).rTensor Q := by
          ext y q
          change Module.DirectLimit.of R ι G g i (y ⊗ₜ q) = iso ((DirectLimit.of R ι F f i y) ⊗ₜ q)
          have h := TensorProduct.directLimitLeft_tmul_of f Q y q
          convert h.symm using 1
        rw [comm, LinearMap.comp_apply]
        have eq1 : (DirectLimit.of R ι F f i).rTensor Q =
          TensorProduct.map (DirectLimit.of R ι F f i) LinearMap.id := rfl
        rw[eq1, hx, map_zero]
      obtain ⟨k, hik, hzero⟩ := Module.DirectLimit.of.zero_exact hx'
      exact ⟨k, hik, hzero⟩
    obtain ⟨k,hik, keq⟩ := key
    -- Use the factorization from condition (3) to conclude fᵢⱼ ⊗ id also vanishes on x
    obtain ⟨h,hrel⟩ := cond k hik
    rw[hrel]
    have idrel : (LinearMap.id : Q →ₗ[R] Q) ∘ₗ LinearMap.id = LinearMap.id := by
      ext; simp only [LinearMap.comp_id, LinearMap.id_coe, id_eq]
    rw[←idrel]
    rw[TensorProduct.map_comp,LinearMap.comp_apply]
    rw[keq]
    exact rfl


omit [DirectedSystem F fun i j h => f i j h] in
/-- The equivalence of characterizations (3) and (4) of Mittag-Leffler modules
(Proposition 88.6 (3) ↔ (4) of the Stacks Project / Tag 0599).

The direction (3) ⟹ (4): given the factorization condition, show that the images of the
precomposition maps stabilize by using the composition axiom for the directed system and
the explicit factorization maps.

The direction (4) ⟹ (3): take N = ∏ᵢ Fᵢ with the projection incl_j and proj_j maps.
The stabilization of image ranges in the Hom system allows us to extract the required
factorization map h : Fₖ → Fⱼ by projecting an appropriate element of the stabilized image. -/
theorem isMittagLeffler''_iff_isMittagLeffler'''
    (hf : ∀ i, f i i (le_refl i) = LinearMap.id)
    (hcomp : ∀ i j k (hij : i ≤ j)
    (hjk : j ≤ k), f i k (hij.trans hjk) = (f j k hjk).comp (f i j hij)) :
    IsMittagLeffler'' R F f ↔ IsMittagLeffler''' R F f hf hcomp := by
  constructor
  · rw [isMittagLeffler'''_iff]
    intro h N _ _ i
    obtain ⟨j, hij, hfac⟩ := h i
    use j, hij
    intro k hjk
    ext φ
    constructor
    · rintro ⟨g, rfl⟩
      use g.comp (f j k hjk)
      simp only [LinearMap.comp_assoc]
      rw [← hcomp i j k hij hjk]
    · rintro ⟨g, rfl⟩
      obtain ⟨hmap, hfac_eq⟩ := hfac k (hij.trans hjk)
      use g.comp hmap
      simp only [LinearMap.comp_assoc]
      rw [← hfac_eq]


  · rw [isMittagLeffler'''_iff]
    rw [IsMittagLeffler'']
    intro ML''' i
    -- Take N = ∏ᵢ Fᵢ and use projection/inclusion maps to extract the factorization
    let N := (i : ι) → F i
    obtain ⟨j, hij, cond⟩ := ML''' N i
    use j, hij
    intro k hik
    obtain ⟨l, hjl, hkl⟩ := directed_of (· ≤ ·) j k

    let incl_j : F j →ₗ[R] N := LinearMap.single R (fun i => F i) j

    have h_in_range_j : incl_j.comp (f i j hij) ∈
                        Set.range (fun g : F j →ₗ[R] N => g.comp (f i j hij)) := ⟨incl_j, rfl⟩

    have h_range_eq := cond l hjl
    rw [←h_range_eq] at h_in_range_j

    obtain ⟨g, hg⟩ := h_in_range_j

    let proj_j : N →ₗ[R] F j := LinearMap.proj j
    let h : F k →ₗ[R] F j := proj_j.comp (g.comp (f k l hkl))

    use h
    ext x
    simp only [h, LinearMap.comp_apply]
    have hfil : f i l (hij.trans hjl) = (f k l hkl).comp (f i k hik) := by
      rw [hcomp i k l hik hkl]
    have hx : g (f i l (hij.trans hjl) x) = incl_j (f i j hij x) := by
      exact congrFun (congrArg DFunLike.coe hg) x
    rw [hfil, LinearMap.comp_apply] at hx
    have := congrArg (fun y => proj_j y) hx
    simp only [proj_j, incl_j] at this
    rw [LinearMap.proj_apply, LinearMap.proj_apply] at this
    rw [LinearMap.single_apply, Pi.single_eq_same] at this
    exact this.symm



end Equivalences


section Properties

variable {R : Type u} [CommRing R]

/-- Every finitely presented R-module is Mittag-Leffler. This is immediate from the
definition: given any map f : P → M from a finitely presented module, take Q = M and
g = f; then f and g trivially mutually dominate each other. -/
theorem finitePresentation_isMittagLeffler (M : Type u) [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] : IsMittagLeffler R M := by
  intro P _ _ _ f
  refine ⟨M, inferInstance, inferInstance, inferInstance, f, ?_⟩
  constructor
  · intro Q instAG instMod x hx
    exact hx
  · intro Q instAG instMod x hx
    exact hx

/-- Every free R-module is Mittag-Leffler. Given f : P → M with M free and P finitely
presented, we restrict f to a finite set of basis indices basisIndices (the union of the
supports of b.repr(f(s)) over the generators s of P), obtaining a finitely presented
module Q = basisIndices →₀ R and a mutually dominating pair: f factors through g via
the natural inclusion ι : Q → M, and g factors through f via the restriction map. -/
theorem free_isMittagLeffler (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Free R M] : IsMittagLeffler R M := by
  intro P _ _ PFP f
  rcases PFP with ⟨S, sGenP, relS, relSgenRel⟩
  let b := Module.Free.chooseBasis R M
  let basisIndices : Finset (Module.Free.ChooseBasisIndex R M) :=
    Finset.biUnion S (fun s => (b.repr (f s)).support)
  let Q := (↥basisIndices) →₀ R
  use Q, inferInstance, inferInstance, inferInstance
  let restrictToIndices : (Module.Free.ChooseBasisIndex R M →₀ R) →ₗ[R] Q :=
    Finsupp.lsubtypeDomain (· ∈ basisIndices)
  let g : P →ₗ[R] Q := restrictToIndices.comp (b.repr.toLinearMap.comp f)
  use g
  let ι : Q →ₗ[R] M := Finsupp.linearCombination R (fun j => b j.val)
  -- Show by induction on span that the support of b.repr(f p) lies in basisIndices
  have support_subset : ∀ p : P, (b.repr (f p)).support ⊆ basisIndices := by
    intro p
    have hp : p ∈ (⊤ : Submodule R P) := Submodule.mem_top
    rw [← sGenP] at hp
    refine Submodule.span_induction
      (mem := fun s hs => ?_)
      (zero := ?_)
      (add := fun x y hx hy hpx hpy => ?_)
      (smul := fun r x hx hpx => ?_)
      hp
    · intro idx hidx
      exact Finset.mem_biUnion.mpr ⟨s, hs, hidx⟩
    · simp only [map_zero, Finsupp.support_zero, Finset.empty_subset]
    · intro idx hidx
      simp only [map_add] at hidx
      have := Finsupp.support_add hidx
      rcases Finset.mem_union.mp this with h | h
      · exact hpx h
      · exact hpy h
    · intro idx hidx
      simp only [map_smul] at hidx
      have := Finsupp.support_smul hidx
      exact hpx this
  -- Establish f = ι ∘ g by comparing the basis expansions
  have hfac : f = ι.comp g := by
    ext p
    dsimp only [ι, g, restrictToIndices]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [Finsupp.linearCombination_apply]
    conv_lhs => rw [← b.linearCombination_repr (f p), Finsupp.linearCombination_apply]
    rw [← Finsupp.sum_subtypeDomain_index (support_subset p)]
    rfl

  constructor
  · exact LinearMap.Dominates.of_factors (restrictToIndices.comp b.repr.toLinearMap) rfl
  · exact LinearMap.Dominates.of_factors ι hfac


/-- A direct summand of a Mittag-Leffler module is Mittag-Leffler. Given N a direct
summand of M via ι : N → M and π : M → N with π ∘ ι = id, we apply the Mittag-Leffler
property of M to the composed map ι ∘ f : P → M, obtaining a mutually dominating pair.
The domination for N is then deduced using the injectivity of ι ⊗ id (which follows from
π ⊗ id being a left inverse) and the functoriality of tensor products. -/
theorem IsMittagLeffler.of_direct_summand {R : Type u} [CommRing R]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (hM : IsMittagLeffler R M)
    (ι : N →ₗ[R] M) (π : M →ₗ[R] N) (hπι : π.comp ι = LinearMap.id) :
    IsMittagLeffler R N := by
  intro P _ _ hP f
  obtain ⟨Q, _, _, hQ, g, hfg⟩ := hM P _ _ hP (ι.comp f)
  refine ⟨Q, _, _, hQ, g, ?_⟩
  obtain ⟨h_g_dom_ιf, h_ιf_dom_g⟩ := hfg
  constructor
  · intro Q' _ _ x hx
    apply h_g_dom_ιf
    have h_eq : TensorProduct.map (ι.comp f) (LinearMap.id : Q' →ₗ[R] Q') =
        (TensorProduct.map ι LinearMap.id).comp (TensorProduct.map f LinearMap.id) := by
      rw [← TensorProduct.map_comp]
      simp only [LinearMap.comp_id]
    rw [h_eq, LinearMap.comp_apply, hx, map_zero]
  · intro Q' _ _ x hx
    have h_ιf_zero := h_ιf_dom_g Q' _ _ x hx
    have h_eq : TensorProduct.map (ι.comp f) (LinearMap.id : Q' →ₗ[R] Q') =
        (TensorProduct.map ι LinearMap.id).comp (TensorProduct.map f LinearMap.id) := by
      rw [← TensorProduct.map_comp]
      simp only [LinearMap.comp_id]
    rw [h_eq, LinearMap.comp_apply] at h_ιf_zero
    -- ι ⊗ id is injective because π ⊗ id ∘ ι ⊗ id = id
    have h_inj : Function.Injective (TensorProduct.map ι (LinearMap.id : Q' →ₗ[R] Q')) := by
      have h_left_inv : (TensorProduct.map π (LinearMap.id : Q' →ₗ[R] Q')).comp
        (TensorProduct.map ι LinearMap.id) =
          LinearMap.id := by
        rw [← TensorProduct.map_comp]
        simp only [hπι, LinearMap.comp_id, TensorProduct.map_id]
      exact Function.HasLeftInverse.injective ⟨TensorProduct.map π LinearMap.id,
        fun x => by rw [← LinearMap.comp_apply, h_left_inv, LinearMap.id_apply]⟩
    exact h_inj h_ιf_zero


/-- Every projective R-module is Mittag-Leffler (Section 7 of the paper). The proof
proceeds by expressing P as a direct summand of the free module F = P →₀ R via the
canonical surjection π : F → P together with a section ι obtained from the projective
lifting property. Since free modules are Mittag-Leffler by `free_isMittagLeffler`, and
direct summands of Mittag-Leffler modules are Mittag-Leffler by
`IsMittagLeffler.of_direct_summand`, the result follows.

This proof is simpler than the arguments in the Stacks Project and Perry, which use a
characterization of Mittag-Leffler via tensoring with direct products. -/
theorem proj_is_Mittag_Leffler {R : Type u} {P : Type u} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P] : Module.IsMittagLeffler R P := by
  let F := P →₀ R
  let π : F →ₗ[R] P := Finsupp.linearCombination R id
  have hπ : Function.Surjective π := Finsupp.linearCombination_id_surjective R P
  obtain ⟨ι, hιπ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hFree : IsMittagLeffler R F := free_isMittagLeffler F
  exact IsMittagLeffler.of_direct_summand hFree ι π hιπ


/-- A module M over R is countably generated if there exists a countable subset S ⊆ M
whose R-span equals M. -/
def IsCountablyGenerated (R : Type u) [CommRing R] (M : Type u)
[AddCommGroup M] [Module R M] : Prop :=
  ∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤


/-- Any countable subset I of a directed preorder ι can be enlarged to a countable directed
subset I' ⊇ I. The construction proceeds by iterating the operation of adding pairwise
upper bounds: starting from the insert of a chosen base point into I, each step takes the
union of the current set with the image of all pairwise upper bounds ub(x, y). The union
I' = ⋃ₙ Iₙ is then countable (as a countable union of countable sets), directed (since
any two elements land in the same Iₙ for large enough n, and Iₙ is built to contain their
upper bound), and nonempty. -/
lemma countable_subset_directed_closure
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (I : Set ι) (hI : I.Countable) :
    ∃ I' : Set ι, I ⊆ I' ∧ I'.Countable ∧ DirectedOn (· ≤ ·) I' ∧ I'.Nonempty := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  choose ub hub using fun (x y : ι) => directed_of (· ≤ ·) x y
  let step : Set ι → Set ι := fun S => S ∪ Set.image2 ub S S
  let I_n : ℕ → Set ι := fun n => step^[n] (insert i₀ I)
  let I' := ⋃ n, I_n n
  refine ⟨I', ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact Set.mem_iUnion.mpr ⟨0, by simp [I_n, Set.mem_insert_iff, hx]⟩
  · apply Set.countable_iUnion
    intro n
    induction n with
    | zero => exact (hI.insert i₀)
    | succ n ih =>
      simp only [I_n, Function.iterate_succ', Function.comp_apply] at ih ⊢
      apply Set.Countable.union ih
      exact Set.Countable.image2 ih ih ub
  · intro x hx y hy
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hy
    let k := max n m
    have mono : ∀ a b, a ≤ b → I_n a ⊆ I_n b := fun a b hab => by
      have h : id ≤ step := fun S => Set.subset_union_left
      exact Function.monotone_iterate_of_id_le h hab (insert i₀ I)
    have hxk : x ∈ I_n k := mono n k (le_max_left n m) hn
    have hyk : y ∈ I_n k := mono m k (le_max_right n m) hm
    refine ⟨ub x y, ?_, (hub x y).1, (hub x y).2⟩
    apply Set.mem_iUnion.mpr
    use k + 1
    simp only [I_n, Function.iterate_succ', Function.comp_apply, step]
    right
    exact Set.mem_image2_of_mem hxk hyk
  · exact ⟨i₀, Set.mem_iUnion.mpr ⟨0, by simp [I_n]⟩⟩


/-- If M is a Mittag-Leffler module that is also countably generated, and M is presented
as a directed colimit M = colim_{i ∈ ι} Mᵢ of finitely presented modules, then there
exists a countable directed subset I' ⊆ ι such that M ≅ colim_{i ∈ I'} Mᵢ.

This is Lemma 10.92.1 (Tag 059W) of the Stacks Project and Lemma 7.1 of Perry. It is
the key structural result used in the proofs of both main theorems of the paper:
  - In the proof of Theorem II (proj_iff_Mittag_Leffler), it allows reducing the
    projectivity lifting problem to a countable index set, where the surjectivity theorem
    for Mittag-Leffler inverse systems (Theorem 5.2 of the paper) applies.
  - In the proof of Theorem I (proj_faithfully_flat), it is applied after descending the
    Mittag-Leffler property along the faithfully flat map R → S.

The construction proceeds in two main steps:
  (1) Extract a countable initial set I₀ ⊆ ι by choosing, for each generator of M, a
      representing index in ι.
  (2) Iteratively enlarge I₀ using `countable_subset_directed_closure` and the
      Mittag-Leffler stabilization indices (from condition (3)) to produce a sequence
      buildSeq of countable directed sets whose union I' satisfies the required properties.
The isomorphism M ≅ colim_{I'} Mᵢ is then established by showing the canonical map
from the restricted colimit is both injective (using the zero-exact property of direct
limits and the Mittag-Leffler condition on I') and surjective (since I' contains
representatives of all generators of M). -/
theorem mittagLeffler_countablyGenerated_has_countable_colimit
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] [DecidableEq ι]
    (F : ι → Type u) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
    [∀ i, Module.FinitePresentation R (F i)]
    (f : ∀ i j, i ≤ j → F i →ₗ[R] F j)
    [DirectedSystem F (fun i j h => f i j h)]
    (hML : IsMittagLeffler R (Module.DirectLimit F f))
    (hCountGen : Module.IsCountablyGenerated R (Module.DirectLimit F f)) :
    ∃ (I' : Set ι) (_ : I'.Countable) (_ : DirectedOn (· ≤ ·) I') (_ : I'.Nonempty),
      Nonempty (Module.DirectLimit F f ≃ₗ[R] Module.DirectLimit (fun i : I' => F i.val)
        (fun i j (hij : i ≤ j) => f i.val j.val hij)) := by
  let M := Module.DirectLimit F f
  -- Convert the ML hypothesis to condition (3) for use in constructing I'
  have ML'' : IsMittagLeffler'' R F f := by
    rw [← isMittagLeffler'_iff_isMittagLeffler'']
    rw [isMittagLeffler_iff_isMittagLeffler']
    exact hML
  rw[IsMittagLeffler''] at ML''

  obtain ⟨S, hS_countable, hS_span⟩ := hCountGen

  -- Step 1: for each generator of M, pick a representing index in ι
  have hgen_rep : ∀ x : Module.DirectLimit F f, ∃ i : ι, ∃ y : F i,
    Module.DirectLimit.of R ι F f i y = x := fun x => Module.DirectLimit.exists_of x
  choose i_of y_of hy_of using fun x : S => hgen_rep x.val
  let I_0 : Set ι := Set.range i_of
  have hI_0_countable : I_0.Countable := by
    haveI : Countable ↑S := hS_countable.to_subtype
    apply Set.countable_range
  -- For each index i, record its ML stabilization index j_of i ≥ i
  choose j_of hj_of_ge hj_of_cond using ML''
  let addML : Set ι → Set ι := fun S => S ∪ (j_of '' S)

  -- Step 2: iteratively enlarge to a sequence of countable directed sets
  let buildSeq : ℕ → {S : Set ι // S.Countable ∧ DirectedOn (· ≤ ·) S ∧ S.Nonempty} :=
    Nat.rec
      (let S' := (countable_subset_directed_closure I_0 hI_0_countable).choose
       let hS' := (countable_subset_directed_closure I_0 hI_0_countable).choose_spec
       ⟨S', hS'.2.1, hS'.2.2.1, hS'.2.2.2⟩)
      (fun n prev =>
        let S_with_ML := addML prev.val
        let hS_count : S_with_ML.Countable :=
          Set.Countable.union prev.prop.1 (prev.prop.1.image j_of)
        let S' := (countable_subset_directed_closure S_with_ML hS_count).choose
        let hS' := (countable_subset_directed_closure S_with_ML hS_count).choose_spec
        ⟨S', hS'.2.1, hS'.2.2.1, hS'.2.2.2⟩)

  have hSeq_subset_succ : ∀ n, (buildSeq n).val ⊆ (buildSeq (n + 1)).val := by
    intro n
    have h1 : (buildSeq n).val ⊆ addML (buildSeq n).val := Set.subset_union_left
    have h2 : addML (buildSeq n).val ⊆ (buildSeq (n + 1)).val :=
        (countable_subset_directed_closure (addML (buildSeq n).val)
          (Set.Countable.union (buildSeq n).prop.1 ((buildSeq n).prop.1.image j_of))).choose_spec.1
    exact Set.Subset.trans h1 h2

  have hSeq_mono : ∀ n m, n ≤ m → (buildSeq n).val ⊆ (buildSeq m).val := by
    intro n m hnm
    induction m with
    | zero =>
        simp only [Nat.le_zero] at hnm
        rw [hnm]
    | succ m ih =>
        rcases Nat.eq_or_lt_of_le hnm with h | h
        · rw [h]
        · exact Set.Subset.trans (ih (Nat.lt_succ_iff.mp h)) (hSeq_subset_succ m)

  -- Take I' to be the union of the sequence
  let I' : Set ι := ⋃ n, (buildSeq n).val
  have hI'_countable : I'.Countable := by
    apply Set.countable_iUnion
    intro n
    exact (buildSeq n).prop.1
  have hI'_directed : DirectedOn (· ≤ ·) I' := by
    rw[DirectedOn]
    intro x xin y yin
    simp only[I'] at xin
    simp only[I'] at yin
    have : ∃ n : ℕ, x ∈ (buildSeq n).val := by exact Set.mem_iUnion.mp xin
    obtain ⟨n,nprop⟩ := this
    have : ∃ n : ℕ, y ∈ (buildSeq n).val := by exact Set.mem_iUnion.mp yin
    obtain ⟨m,mprop⟩ := this
    let k := max n m
    have hxk : x ∈ (buildSeq k).val := hSeq_mono n k (le_max_left n m) nprop
    have hyk : y ∈ (buildSeq k).val := hSeq_mono m k (le_max_right n m) mprop
    have hk_directed : DirectedOn (· ≤ ·) (buildSeq k).val := (buildSeq k).prop.2.1
    obtain ⟨z, zin, hxz, hyz⟩ := hk_directed x hxk y hyk
    exact ⟨z, Set.mem_iUnion.mpr ⟨k, zin⟩, hxz, hyz⟩

  have hI'_nonempty : I'.Nonempty := by
    have h0 := (buildSeq 0).prop.2.2
    obtain ⟨x, hx⟩ := h0
    exact ⟨x, Set.mem_iUnion.mpr ⟨0, hx⟩⟩
  refine ⟨I', hI'_countable, hI'_directed, hI'_nonempty,?_⟩

  have hI'_iso : Nonempty (Module.DirectLimit F f ≃ₗ[R]
      Module.DirectLimit (fun i : I' => F i.val) (fun i j hij => f i.val j.val hij)) := by
    let F' : I' → Type u := fun i => F i.val
    let f' : ∀ (i j : I'), i ≤ j → F' i →ₗ[R] F' j := fun i j hij => f i.val j.val hij

    haveI : DirectedSystem F' (fun i j h => f' i j h) := by
      constructor
      · intro i x
        simp only [F', f']
        exact DirectedSystem.map_self (f := fun i j h => f i j h) x
      · intro i j k hij hjk x
        simp only [F', f']
        exact DirectedSystem.map_map (f := fun i j h => f i j h) hij hjk x

    -- The canonical map from the restricted colimit to the full colimit
    let φ : Module.DirectLimit F' f' →ₗ[R] Module.DirectLimit F f :=
      Module.DirectLimit.lift R I' F' f'
        (fun i => (Module.DirectLimit.of R ι F f i.val : F i.val →ₗ[R] Module.DirectLimit F f))
        (fun i j hij x => by
          change (Module.DirectLimit.of R ι F f j.val) (f i.val j.val hij x) =
               (Module.DirectLimit.of R ι F f i.val) x
          exact Module.DirectLimit.of_f)

    -- Surjectivity: every generator of M has its representing index in I'
    have hsurj : Function.Surjective φ := by
      rw [← LinearMap.range_eq_top]
      have hS_sub_range : S ⊆ LinearMap.range φ := by
        intro x hx
        have hx' : x = Module.DirectLimit.of R ι F f (i_of ⟨x, hx⟩) (y_of ⟨x, hx⟩) :=
          (hy_of ⟨x, hx⟩).symm
        rw [hx']
        have hi : i_of ⟨x, hx⟩ ∈ I' := by
          apply Set.mem_iUnion.mpr
          use 0
          have hI0_sub : I_0 ⊆ (buildSeq 0).val :=
            (countable_subset_directed_closure I_0 hI_0_countable).choose_spec.1
          exact hI0_sub (Set.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩)
        rw [SetLike.mem_coe, LinearMap.mem_range]
        use Module.DirectLimit.of R I' F' f' ⟨i_of ⟨x, hx⟩, hi⟩ (y_of ⟨x, hx⟩)
        simp only [φ]
        rw [Module.DirectLimit.lift_of]
      have h1 : Submodule.span R S ≤ LinearMap.range φ := Submodule.span_le.mpr hS_sub_range
      rw [hS_span] at h1
      exact top_le_iff.mp h1

    -- Injectivity: use the zero-exact property and the ML condition on I'
    have hinj : Function.Injective φ := by
      rw [← LinearMap.ker_eq_bot]
      apply eq_bot_iff.mpr
      intro z hz
      rw [LinearMap.mem_ker] at hz
      haveI : Nonempty I' := hI'_nonempty.to_subtype
      haveI : IsDirected I' (· ≤ ·) := by
        constructor
        intro ⟨a, ha⟩ ⟨b, hb⟩
        obtain ⟨c, hc, hac, hbc⟩ := hI'_directed a ha b hb
        exact ⟨⟨c, hc⟩, hac, hbc⟩

      obtain ⟨i, x, hx⟩ := Module.DirectLimit.exists_of z
      -- φ(z) = 0 means the inclusion of x into the full colimit vanishes
      have hφz : Module.DirectLimit.of R ι F f i.val x = 0 := by
        rw [← hx] at hz
        simp only [φ, Module.DirectLimit.lift_of] at hz
        exact hz
      -- By zero-exact, some transition map kills x in the full system
      obtain ⟨k, hik, hzero⟩ := Module.DirectLimit.of.zero_exact hφz
      -- The ML stabilization index j_of i.val is in I' (added at step n+1)
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp i.prop
      have hj_in_I' : j_of i.val ∈ I' := by
        apply Set.mem_iUnion.mpr
        use n + 1
        have h_addML_sub : addML (buildSeq n).val ⊆ (buildSeq (n + 1)).val :=
          (countable_subset_directed_closure (addML (buildSeq n).val)
           (Set.Countable.union (buildSeq n).prop.1 ((buildSeq n).prop.1.image j_of))).choose_spec.1
        apply h_addML_sub
        apply Set.mem_union_right
        exact Set.mem_image_of_mem j_of hn
      -- The ML condition gives a factorization that forces fᵢⱼ(x) = 0 in the restricted system
      obtain ⟨h, hfac⟩ := hj_of_cond i.val k hik
      have hzero' : f i.val (j_of i.val) (hj_of_ge i.val) x = 0 := by
        rw [hfac, LinearMap.comp_apply, hzero, map_zero]
      -- Hence z = 0 in the restricted colimit
      rw [← hx, Submodule.mem_bot]
      let j' : I' := ⟨j_of i.val, hj_in_I'⟩
      have hij' : i ≤ j' := hj_of_ge i.val
      rw [← Module.DirectLimit.of_f (f := f') (hij := hij')]
      simp only [j']
      rw[hzero',map_zero]
    exact ⟨(LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩
  exact hI'_iso



end Properties



end Module
