/-
Copyright (c) 2026 Liran Shaul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Liran Shaul

This file is part of the formalization project accompanying the paper:
  "Formalization in Lean of faithfully flat descent of projectivity"
  by Liran Shaul, Charles University in Prague.

We develop the theory of domination of linear maps, which is a key technical notion
underlying the theory of Mittag-Leffler modules (Section 6 of the paper). Given
R-linear maps f : M → N and g : M → M', we say g dominates f if for every R-module Q,
ker(f ⊗ id_Q) ⊆ ker(g ⊗ id_Q). The main result of this file is:

  dominates_iff_factors_through (Theorem 6.10 of Perry / Tag 059D of the Stacks Project):
  If N/im(f) is finitely presented, then g dominates f if and only if g factors through f.

The proof proceeds by first establishing the equivalence between domination and
universal injectivity of the canonical map Pushout.inr : M' → Pushout(f,g)
(dominates_iff_pushout_inr_universallyInjective, corresponding to Tag 059C of the
Stacks Project), and then applying the splitting criterion for short exact sequences
of finitely presented modules via shortExact_universally_injective_iff_splitting.
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
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.TensorProduct.Pi
import lib.mlSystem
import lib.Pushout
import lib.UnivInj


universe u

variable {R : Type u} [CommRing R]

namespace LinearMap

section Domination

variable {M : Type u} {N : Type u} {M' : Type u}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup M']
variable [Module R M] [Module R N] [Module R M']

/-- Given `f : M →ₗ[R] N` and `g : M →ₗ[R] M'`, we say `g` dominates `f` if for every
R-module Q, ker(f ⊗ id_Q) ⊆ ker(g ⊗ id_Q). This is Definition 6.1 of Perry and
Tag 088.2 of the Stacks Project. Note that in the Lean code, `Dominates f g` means
that g dominates f. -/
def Dominates (f : M →ₗ[R] N) (g : M →ₗ[R] M') : Prop :=
  ∀ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q),
    ∀ x : TensorProduct R M Q, (TensorProduct.map f LinearMap.id) x = 0 →
      (TensorProduct.map g LinearMap.id) x = 0

/-- Two maps `f : M → N` and `g : M → M'` mutually dominate each other if
ker(f ⊗ id_Q) = ker(g ⊗ id_Q) for every R-module Q. This is the equivalence relation
used to define the Mittag-Leffler property; see Proposition 6.11 of Perry and
Tag 0599 of the Stacks Project. -/
def MutuallyDominate (f : M →ₗ[R] N) (g : M →ₗ[R] M') : Prop :=
  Dominates f g ∧ Dominates g f

/-- Domination is reflexive. -/
theorem Dominates.refl (f : M →ₗ[R] N) : Dominates f f := by
  intro Q _ _ x hx
  exact hx

/-- Domination is transitive. -/
theorem Dominates.trans {P : Type u} [AddCommGroup P] [Module R P]
    {f : M →ₗ[R] N} {g : M →ₗ[R] M'} {h : M →ₗ[R] P}
    (hfg : Dominates f g) (hgh : Dominates g h) : Dominates f h := by
  intro Q instAG instMod x hx
  exact hgh Q instAG instMod x (hfg Q instAG instMod x hx)

/-- If f factors through g (i.e., f = h ∘ g for some h), then g dominates f.
This is one direction of `dominates_iff_factors_through` and holds without any
finite presentation hypothesis. -/
theorem Dominates.of_factors {f : M →ₗ[R] N} {g : M →ₗ[R] M'}
    (h : M' →ₗ[R] N) (hfac : f = h.comp g) : Dominates g f := by
  intro Q instAG instMod x hx
  simp only [hfac]
  have key : (TensorProduct.map (h ∘ₗ g) (LinearMap.id (R := R) (M := Q))) =
             (TensorProduct.map h (LinearMap.id (R := R) (M := Q))) ∘ₗ
             (TensorProduct.map g (LinearMap.id (R := R) (M := Q))) := by
    rw [← TensorProduct.map_comp]
    simp only [LinearMap.id_comp]
  rw [key, LinearMap.comp_apply, hx, map_zero]

/-- Domination is compatible with precomposition: if f dominates g, then f ∘ h dominates g ∘ h. -/
theorem Dominates.comp_right {P : Type u} [AddCommGroup P] [Module R P]
    {f : M →ₗ[R] N} {g : M →ₗ[R] M'} (h : P →ₗ[R] M)
    (hdom : f.Dominates g) : (f.comp h).Dominates (g.comp h) := by
  intro Q _ _ x hx
  have key1 : TensorProduct.map (f.comp h) (LinearMap.id (R := R) (M := Q)) =
              (TensorProduct.map f (LinearMap.id (R := R) (M := Q))).comp
              (TensorProduct.map h (LinearMap.id (R := R) (M := Q))) := by
    rw [← TensorProduct.map_comp]; simp
  have key2 : TensorProduct.map (g.comp h) (LinearMap.id (R := R) (M := Q)) =
              (TensorProduct.map g (LinearMap.id (R := R) (M := Q))).comp
              (TensorProduct.map h (LinearMap.id (R := R) (M := Q))) := by
    rw [← TensorProduct.map_comp]; simp
  rw [key1] at hx
  rw [key2]
  simp only [LinearMap.comp_apply] at hx ⊢
  exact hdom Q _ _ _ hx

/-- The restriction of g to ker(f), viewed as a map ker(f) → M'. This is an auxiliary
definition used to construct the map `kerFToKerInr` below. -/
def gRestrictKerF (f : M →ₗ[R] N) (g : M →ₗ[R] M') : LinearMap.ker f →ₗ[R] M' :=
  g.domRestrict (LinearMap.ker f)

/-- The map ker(f) → ker(Pushout.inr f g) induced by g. For x ∈ ker(f), the pushout
condition inl(f(x)) = inr(g(x)) together with f(x) = 0 gives inr(g(x)) = 0, so g(x)
lands in ker(Pushout.inr f g). This map is used in the proof of
`dominates_iff_pushout_inr_universallyInjective`. -/
def kerFToKerInr (f : M →ₗ[R] N) (g : M →ₗ[R] M') :
    LinearMap.ker f →ₗ[R] LinearMap.ker (Pushout.inr f g) :=
  LinearMap.codRestrict (LinearMap.ker (Pushout.inr f g)) (gRestrictKerF f g) (by
    intro ⟨x, hx⟩
    simp only [LinearMap.mem_ker, gRestrictKerF, LinearMap.domRestrict_apply]
    have h := Pushout.condition_apply f g x
    simp only [LinearMap.mem_ker] at hx
    rw [hx, map_zero] at h
    exact h.symm
  )

/-- The kernel of `kerFToKerInr f g` is ker(f) ∩ ker(g), pulled back along the inclusion
ker(f) ↪ M. -/
theorem ker_kerFToKerInr (f : M →ₗ[R] N) (g : M →ₗ[R] M') :
    LinearMap.ker (kerFToKerInr f g) =
    (LinearMap.ker f ⊓ LinearMap.ker g).comap (Submodule.subtype (LinearMap.ker f)) := by
  ext ⟨x, hx⟩
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.mem_inf]
  change kerFToKerInr f g ⟨x, hx⟩ = 0 ↔ x ∈ LinearMap.ker f ∧ x ∈ LinearMap.ker g
  rw [show (x ∈ LinearMap.ker f) = True from eq_true hx, true_and]
  simp only [LinearMap.mem_ker]
  constructor
  · intro h
    have : (kerFToKerInr f g ⟨x, hx⟩).val = (0 : LinearMap.ker (Pushout.inr f g)).val := by
      rw [h]
    simp only [kerFToKerInr, LinearMap.codRestrict_apply, gRestrictKerF,
               LinearMap.domRestrict_apply, Submodule.coe_zero] at this
    exact this
  · intro h
    apply Subtype.ext
    simp only [kerFToKerInr, LinearMap.codRestrict_apply, gRestrictKerF,
               LinearMap.domRestrict_apply, Submodule.coe_zero]
    exact h

/-- The map `kerFToKerInr f g` is surjective. This uses the explicit description of the
pushout as (N ⊕ M') / span{(f(a), -g(a)) : a ∈ M}: an element m' ∈ ker(Pushout.inr f g)
satisfies [(0, m')] = 0 in the quotient, which means (0, m') = (f(a), -g(a)) for some a,
giving a ∈ ker(f) with g(a) = -m'. -/
theorem kerFToKerInr_surjective (f : M →ₗ[R] N) (g : M →ₗ[R] M') :
    Function.Surjective (kerFToKerInr f g) := by
  intro ⟨m', hm'⟩
  simp only [LinearMap.mem_ker] at hm'
  simp only [Pushout.inr] at hm'
  change Submodule.Quotient.mk (0, m') = 0 at hm'
  rw [Submodule.Quotient.mk_eq_zero, mem_pushoutSubmodule_iff] at hm'
  obtain ⟨a, ha⟩ := hm'
  simp only [Prod.mk.injEq] at ha
  use ⟨-a, by simp [LinearMap.mem_ker, ha.1]⟩
  ext
  simp only [kerFToKerInr, LinearMap.codRestrict_apply, gRestrictKerF,
             LinearMap.domRestrict_apply]
  simp [ha.2]

/-- The natural map Pushout(f,g) ⊗ Q → Pushout(f ⊗ id_Q, g ⊗ id_Q), constructed using
the universal properties of the tensor product and the pushout. This comparison map
is used in the proof of `dominates_iff_pushout_inr_universallyInjective` to transfer
injectivity statements between the two sides. -/
def pushoutTensorToTensorPushout (f : M →ₗ[R] N) (g : M →ₗ[R] M')
    (Q : Type u) [AddCommGroup Q] [Module R Q] :
    TensorProduct R (Pushout f g) Q →ₗ[R] Pushout (f.rTensor Q) (g.rTensor Q) := by
  refine TensorProduct.lift ?_
  refine Pushout.desc f g ?_ ?_ ?_
  · exact (TensorProduct.mk R N Q).compr₂ (Pushout.inl (f.rTensor Q) (g.rTensor Q))
  · exact (TensorProduct.mk R M' Q).compr₂ (Pushout.inr (f.rTensor Q) (g.rTensor Q))
  · ext a q
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.comp_apply]
    exact Pushout.condition_apply (f.rTensor Q) (g.rTensor Q) (a ⊗ₜ q)

/-- The comparison map `pushoutTensorToTensorPushout` intertwines the two versions of
Pushout.inr: the rTensor of the original inr, and the inr of the tensored pushout. -/
theorem pushoutTensorToTensorPushout_comp_inr (f : M →ₗ[R] N) (g : M →ₗ[R] M')
    (Q : Type u) [AddCommGroup Q] [Module R Q] :
    pushoutTensorToTensorPushout f g Q ∘ₗ (Pushout.inr f g).rTensor Q =
    Pushout.inr (f.rTensor Q) (g.rTensor Q) := by
  apply TensorProduct.ext
  ext m' q
  simp only [LinearMap.compr₂ₛₗ_apply, LinearMap.comp_apply]
  unfold pushoutTensorToTensorPushout
  simp only [TensorProduct.mk_apply, rTensor_tmul, TensorProduct.lift.tmul]
  rw [← LinearMap.comp_apply, Pushout.inr_desc]
  simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply]

/-- The key equivalence connecting domination and universal injectivity: g dominates f
if and only if the canonical map Pushout.inr f g : M' → Pushout(f,g) is universally
injective. This corresponds to Tag 059C of the Stacks Project and is the central
technical tool used in the proof of `dominates_iff_factors_through`. -/
theorem dominates_iff_pushout_inr_universallyInjective (f : M →ₗ[R] N) (g : M →ₗ[R] M') :
    Dominates f g ↔ UniversallyInjective (Pushout.inr f g) := by
  constructor
  · intro hdom Q _ _ x y hxy
    have hzero : (Pushout.inr f g).rTensor Q (x - y) = 0 := by
      simp only [map_sub, hxy, sub_self]
    have hcompat := pushoutTensorToTensorPushout_comp_inr f g Q
    -- Transfer the vanishing from the original pushout to the tensored pushout
    -- using the compatibility of the comparison map with inr.
    have hzero' : Pushout.inr (f.rTensor Q) (g.rTensor Q) (x - y) = 0 := by
      have : (pushoutTensorToTensorPushout f g Q) ((Pushout.inr f g).rTensor Q (x - y)) =
             Pushout.inr (f.rTensor Q) (g.rTensor Q) (x - y) := by
        rw [← LinearMap.comp_apply, hcompat]
      rw [← this, hzero, map_zero]
    -- Use surjectivity of kerFToKerInr to lift x - y to an element a ∈ ker(f ⊗ id_Q).
    have hsurj := kerFToKerInr_surjective (f.rTensor Q) (g.rTensor Q)
    obtain ⟨⟨a, ha⟩, hab⟩ := hsurj ⟨x - y, hzero'⟩
    simp only [kerFToKerInr, gRestrictKerF] at hab
    have hga : (g.rTensor Q) a = x - y := congrArg Subtype.val hab
    have hfa : (f.rTensor Q) a = 0 := ha
    simp only [LinearMap.rTensor] at hfa
    -- Apply the domination hypothesis to conclude g ⊗ id_Q also vanishes on a.
    have hga_zero := hdom Q _ _ a hfa
    simp only [LinearMap.rTensor] at hga hga_zero
    have : x - y = 0 := by rw [← hga, hga_zero]
    exact sub_eq_zero.mp this
  · intro huniv Q _ _ x hx
    have h := Pushout.condition f g
    -- The pushout condition tensored with Q gives a commutative square of tensor maps.
    have htensor : TensorProduct.map (Pushout.inl f g) (LinearMap.id (R := R) (M := Q)) ∘ₗ
                   TensorProduct.map f (LinearMap.id (R := R) (M := Q)) =
                   TensorProduct.map (Pushout.inr f g) (LinearMap.id (R := R) (M := Q)) ∘ₗ
                   TensorProduct.map g (LinearMap.id (R := R) (M := Q)) := by
      rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
      simp only [LinearMap.id_comp]
      rw [h]
    -- Since f ⊗ id_Q kills x, the pushout condition forces (inr ⊗ id_Q)(g ⊗ id_Q)(x) = 0.
    have hcond : TensorProduct.map (Pushout.inr f g) (LinearMap.id (R := R) (M := Q))
                 (TensorProduct.map g (LinearMap.id (R := R) (M := Q)) x) = 0 := by
      rw [← LinearMap.comp_apply, ← htensor, LinearMap.comp_apply, hx, map_zero]
    unfold UniversallyInjective at huniv
    have hinj := huniv Q
    change Function.Injective (TensorProduct.map (Pushout.inr f g)
                               (LinearMap.id (R := R) (M := Q))) at hinj
    exact hinj hcond

open CategoryTheory
open ShortComplex

/-- A short exact sequence of R-modules 0 → X₁ → X₂ → X₃ → 0 is universally exact
(i.e., remains exact after tensoring with any R-module) if and only if it splits,
provided X₃ is finitely presented. The forward direction uses `univ_exact_lift_fp`
to produce a section of the surjection X₂ → X₃; the backward direction is immediate
from the splitting. -/
theorem shortExact_universally_injective_iff_splitting
    {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact)
    (fph : Module.FinitePresentation R S.X₃) :
    ShortComplex.UniversallyExact S ↔ Nonempty S.Splitting := by
  constructor
  · intro hUniv
    have : ∃ ψ : S.X₃ →ₗ[R] S.X₂, ((S.g).hom).comp ψ = LinearMap.id := by
      apply univ_exact_lift_fp (S := S) (hS := hS) (hSUniv := hUniv) (P := S.X₃) (PfP := fph)
    obtain ⟨ψ,psiprop⟩ := this
    refine ⟨Splitting.ofExactOfSection S hS.exact ?s ?s_g hS.mono_f⟩
    · exact ModuleCat.ofHom ψ
    · ext x
      simp only [ModuleCat.comp_apply, ModuleCat.id_apply]
      exact congr_fun (congrArg DFunLike.coe psiprop) x
  · intro sSplits
    rcases sSplits with ⟨r1,r2,fr1isId,r2gisId,_⟩
    simp only [UniversallyExact]
    intro Q _ _ x y xeqy
    -- The retraction r1 of S.f gives a left inverse of S.f ⊗ id_Q,
    -- which forces S.f ⊗ id_Q to be injective.
    let phitens := rTensor Q r1.hom
    have : phitens ∘ₗ (rTensor Q S.f.hom) = LinearMap.id := by
      simp only [rTensor, phitens]
      rw [← TensorProduct.map_comp]
      have h : r1.hom ∘ₗ S.f.hom = LinearMap.id := by
        have := congr_arg ModuleCat.Hom.hom fr1isId
        simp only [ModuleCat.hom_comp, ModuleCat.hom_id] at this
        exact this
      rw[h]
      simp only [comp_id, TensorProduct.map_id]
    have xyeq2 : phitens (rTensor Q S.f.hom x) = phitens (rTensor Q S.f.hom y) := by rw[xeqy]
    have h1 : (phitens ∘ₗ rTensor Q S.f.hom) x = (phitens ∘ₗ rTensor Q S.f.hom) y := by simp [xyeq2]
    rw [this] at h1
    simp only [id_coe, id_eq] at h1
    exact h1

/-- The domination criterion (Lemma 6.10 of Perry, Tag 059D of the Stacks Project):
if N/im(f) is finitely presented, then g dominates f if and only if g factors through f,
i.e., there exists h : N → M' such that g = h ∘ f.

The proof of the nontrivial direction proceeds by:
  (1) Rewriting domination as universal injectivity of Pushout.inr f g via
      `dominates_iff_pushout_inr_universallyInjective`.
  (2) Constructing a short exact sequence M' → Pushout(f,g) → Pushout(f,g)/im(inr) → 0
      and verifying it is short exact.
  (3) Noting that Pushout(f,g)/im(inr) ≅ N/im(f) is finitely presented
      (via `Pushout.quotientInrEquiv`), so the short exact sequence splits by
      `shortExact_universally_injective_iff_splitting`.
  (4) Extracting the desired factorization h from the splitting retraction. -/
theorem dominates_iff_factors_through (f : M →ₗ[R] N) (g : M →ₗ[R] M')
    [Module.FinitePresentation R (N ⧸ LinearMap.range f)] :
    Dominates f g ↔ ∃ (h : N →ₗ[R] M'), g = h.comp f := by
   constructor
   · rw[dominates_iff_pushout_inr_universallyInjective]
     -- Construct the short exact sequence M' → Pushout(f,g) → Pushout(f,g)/im(inr) → 0.
     let surjmap := Submodule.mkQ (range (Pushout.inr f g))
     have iscomplex : ModuleCat.ofHom (Pushout.inr f g) ≫ (ModuleCat.ofHom surjmap) = 0 := by
       ext x
       simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, coe_comp, Function.comp_apply,
         ModuleCat.hom_zero, zero_apply]
       rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
       simp only [mem_range, exists_apply_eq_apply]
     let S : ShortComplex (ModuleCat.{u} R) :=  {
         X₁ := ModuleCat.of R M'
         X₂ := ModuleCat.of R (Pushout f g)
         X₃ := ModuleCat.of R ((Pushout f g) ⧸ range (Pushout.inr f g))
         f := ModuleCat.ofHom (Pushout.inr f g)
         g := ModuleCat.ofHom surjmap
         zero := iscomplex }
     intro pushoutUnInj
     -- Verify that S is short exact using injectivity of inr and surjectivity of the quotient map.
     have hS : S.ShortExact := {
       mono_f := by
         have : Function.Injective (Pushout.inr f g) := by exact pushoutUnInj.injective
         rw [ModuleCat.mono_iff_injective]
         exact this
       epi_g := by
         have : Function.Surjective surjmap :=
           by exact Submodule.mkQ_surjective (range (Pushout.inr f g))
         rw [ModuleCat.epi_iff_surjective]
         exact this
       exact := by
         rw [ShortComplex.moduleCat_exact_iff]
         intro x xinker
         have : x ∈ (LinearMap.range) (Pushout.inr f g) := by
           exact (Submodule.Quotient.mk_eq_zero (range (Pushout.inr f g))).mp xinker
         simp only [mem_range] at this
         rcases this with ⟨y,yin⟩
         use y
         rw[←yin]
         rfl
     }
     -- The third term Pushout(f,g)/im(inr) ≅ N/im(f) is finitely presented by hypothesis.
     have FP : Module.FinitePresentation R S.X₃ := by
       let FPIso := Pushout.quotientInrEquiv f g
       apply Module.FinitePresentation.of_equiv (FPIso.symm)
     -- Universal injectivity of inr implies the short exact sequence S splits.
     have splitS : Nonempty S.Splitting := by
       apply (shortExact_universally_injective_iff_splitting S hS FP).mp
       exact pushoutUnInj
     -- Extract the retraction h' : Pushout(f,g) → M' from the splitting.
     let split := Classical.choice splitS
     rcases split with ⟨h',k,hcond,kcond,_⟩
     -- Define h : N → M' by composing h' with inl : N → Pushout(f,g).
     let h := h'.hom ∘ₗ (Pushout.inl f g)
     use h
     simp only [h]
     rw[LinearMap.comp_assoc]
     -- Use the pushout condition inl ∘ f = inr ∘ g to rewrite.
     have : (Pushout.inl f g).comp f = (Pushout.inr f g).comp g := by apply Pushout.condition
     rw[this]
     rw[←LinearMap.comp_assoc]
     -- The splitting condition gives h' ∘ inr = id, so h' ∘ inr ∘ g = g.
     have : (ModuleCat.Hom.hom h' ∘ₗ Pushout.inr f g) = LinearMap.id := by
       have hcond' := congrArg ModuleCat.Hom.hom hcond
       simp only [ModuleCat.hom_comp, ModuleCat.hom_id] at hcond'
       exact hcond'
     simp only [this, id_comp]
   · intro hc
     rcases hc with ⟨h,hcond⟩
     rw[hcond]
     exact Dominates.of_factors h rfl

end Domination

end LinearMap
