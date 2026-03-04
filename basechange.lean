/-
Copyright (c) 2026 Liran Shaul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Liran Shaul

This file is part of the formalization project accompanying the paper:
  "Formalization in Lean of faithfully flat descent of projectivity"
  by Liran Shaul, Charles University in Prague.

This is the main file of the project. It contains the formalization of the
two central theorems:

  Theorem I  (proj_faithfully_flat):
    Let R → S be a faithfully flat map of commutative rings and P an R-module.
    Then P is projective over R if and only if S ⊗[R] P is projective over S.

  Theorem II (proj_iff_Mittag_Leffler):
    Let R be a commutative ring and P an R-module. Then P is projective if and
    only if it is flat, Mittag-Leffler, and a direct sum of countably generated
    R-modules.

Along the way the file establishes a number of auxiliary results that are of
independent interest, including:

  * Base change preserves projectivity (proj_base_change).
  * A projective module is a direct sum of countably generated modules
    (proj_is_dirSumCountable), via Kaplansky's theorem.
  * A flat, Mittag-Leffler, countably generated module is projective
    (proj_if_countable_flat_Mittag_Leffler), the key step toward Theorem II.
  * Faithful flatness reflects the Mittag-Leffler property
    (ML_of_faithfullyFlat_tensorProduct) and countable generation
    (countably_generated_faithfully_flat).
  * The countably generated case of Theorem I
    (proj_countable_faithfully_flat).
  * A lift lemma for the transfinite induction in Theorem I
    (countably_generated_lift).
  * The full transfinite devissage proving Theorem I (proj_faithfully_flat).

The proof of Theorem I requires the auxiliary files lib/mlModule (Mittag-Leffler
modules), lib/Lazard (Lazard's theorem), lib/dirlimitchange (change of index
for direct limits), lib/Pushout (pushouts of modules), lib/Domination
(domination of linear maps), lib/UnivInj (universally injective maps), and
lib/Kap (Kaplansky devissage and the equivalence with direct sums of countably
generated modules).
-/

import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Data.Set.Countable
import Mathlib.Tactic

import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Module.Shrink

import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

import Mathlib.RingTheory.TensorProduct.Free

import Mathlib.Algebra.Category.ModuleCat.Basic

import Mathlib.Algebra.Module.FinitePresentation

import lib.mlModule
import lib.Lazard
import lib.dirlimitchange
import lib.Pushout
import lib.Domination
import lib.UnivInj
import lib.Kap

open Ordinal Submodule DirectSum Set
open scoped TensorProduct


open LinearMap hiding id
open Finsupp
universe u v w


variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The tensor product S ⊗[R] (P →₀ R) is projective over S for any R-algebra S and
any type P. This is because S ⊗[R] (P →₀ R) carries an S-basis indexed by P (via
Algebra.TensorProduct.basis), so it is a free, hence projective, S-module. -/
lemma free_base_change {R : Type u} {S : Type u} {P : Type u} [CommRing R] [CommRing S]
[Algebra R S] : Module.Projective S (TensorProduct R S (P →₀ R)) := by
  have rBasis : Module.Basis P R (P →₀ R) := by exact Finsupp.basisSingleOne
  have rLinear : S ⊗[R] (P →₀ R) ≃ₗ[R] P →₀ S := by
    apply Algebra.TensorProduct.basisAux (R:=R) (A:=S) (M := (P →₀ R)) rBasis

  have sBasis : Module.Basis P S (S ⊗[R] (P →₀ R)) :=
    Algebra.TensorProduct.basis S rBasis
  have sLinear : S ⊗[R] (P →₀ R) ≃ₗ[S] P →₀ S := sBasis.repr
  apply Module.Projective.of_equiv sLinear.symm


/-- Base change preserves projectivity: if P is projective over R and S is an R-algebra,
then S ⊗[R] P is projective over S.

The proof uses the projectivity of P to split the identity on P through a free module
F = (P →₀ R), producing a retraction s : P → F with linearCombination ∘ s = id.
Tensoring this retraction with S gives a split S ⊗[R] P → S ⊗[R] F → S ⊗[R] P,
and since S ⊗[R] F is projective over S by free_base_change, the retract S ⊗[R] P
is also projective. -/
theorem proj_base_change {R : Type u} {S : Type u} {P : Type u} [CommRing R] [CommRing S]
[Algebra R S] [AddCommGroup P] [Module R P] (pproj : Module.Projective R P) :
Module.Projective S (TensorProduct R S P) := by

  have : ∃ s : P →ₗ[R] P →₀ R, Function.LeftInverse (linearCombination R id) s :=
    by apply Module.projective_def.mp pproj
  rcases this with ⟨s,t⟩

  let F := P →₀ R
  let φ: F →ₗ[R] P := Finsupp.linearCombination R id
  let idS : S →ₗ[S] S := LinearMap.id
  let idP : P →ₗ[R] P := LinearMap.id
  let idStenP :TensorProduct R S P →ₗ[S] TensorProduct R S P := LinearMap.id

  have phisid: φ∘ₗs = idP := by ext x;apply t

  let tenmap1 : TensorProduct R S F →ₗ[S] TensorProduct R S P :=
    TensorProduct.AlgebraTensorModule.map idS φ
  let tenmap2 : TensorProduct R S P →ₗ[S] TensorProduct R S F :=
    TensorProduct.AlgebraTensorModule.map idS s

  have tensorIdentity : tenmap1∘ₗtenmap2 = idStenP := by
    rw [← @TensorProduct.AlgebraTensorModule.map_comp]
    rw[phisid]
    have : idS∘ₗidS = idS := by ext;simp[idS]
    rw[this]
    ext
    simp[idP,idS,idStenP]

  have projTens : Module.Projective S (TensorProduct R S F) := by apply free_base_change
  exact Module.Projective.of_split tenmap2 tenmap1 tensorIdentity




/-- An R-module P is a direct sum of countably generated modules if there exists an
internal direct sum decomposition P = ⨁ᵢ Mᵢ where each Mᵢ is countably generated.
This is used as the third condition in the characterization of projective modules
(Theorem II / proj_iff_Mittag_Leffler). -/
class IsDirectSumOfCountablyGenerated (R : Type u) [Ring R] (P : Type u)
[AddCommMonoid P] [Module R P] :
Prop where out : (∃ (ι : Type u) (_ : DecidableEq ι) (fam : ι → Submodule R P),
    DirectSum.IsInternal fam ∧ ∀ i, ∃ s : Set (fam i), s.Countable ∧ span R s = ⊤)




open Classical in
/-- Any projective R-module is a direct sum of countably generated R-modules.

This is the formalization of Kaplansky's theorem [Kaplansky, 1958, Theorem 1]: since P is
projective it embeds as a direct summand of a free module F = (P →₀ R), and F is an
internal direct sum of cyclic (hence countably generated) submodules. The auxiliary
theorem dirsummand_of_dirSumCountable from lib/Kap then transfers the decomposition
from F to the retract P. -/
theorem proj_is_dirSumCountable {R : Type u} {P : Type u} [Ring R] [AddCommGroup P]
[Module R P] (pproj : Module.Projective R P) : IsDirectSumOfCountablyGenerated R P:=
by
  have : ∃ s : P →ₗ[R] P →₀ R, Function.LeftInverse (linearCombination R id) s :=
      by apply Module.projective_def.mp pproj
  rcases this with ⟨s,t⟩
  let F := P →₀ R
  have ffree: Module.Free R F := by infer_instance

  have FBasis: ∃ (ι : Type u) (fam : ι → Submodule R F) ,
      DirectSum.IsInternal fam ∧ ∀ i, (fam i).IsCountablyGenerated := by
    have b := Finsupp.basisSingleOne (ι := P) (R := R)
    refine ⟨P, fun p => R ∙ b p, ?_, ?_⟩
    · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
      exact ⟨b.linearIndependent.iSupIndep_span_singleton,
            by rw [← Submodule.span_range_eq_iSup]; exact b.span_eq⟩
    · intro i
      refine ⟨{⟨b i, Submodule.subset_span rfl⟩}, Set.countable_singleton _, ?_⟩
      rw [eq_top_iff]
      rintro ⟨x, hx⟩ -
      rw [Submodule.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      let gen : ↥((fun p ↦ span R {b p}) i) := ⟨b i, Submodule.subset_span rfl⟩
      have : (⟨c • b i, hx⟩ : ↥((fun p ↦ span R {b p}) i)) = c • gen := by
        ext; simp [gen]
      rw [this]
      exact Submodule.smul_mem _ c (Submodule.subset_span rfl)

  have hπs : (Finsupp.linearCombination R id).comp s = LinearMap.id :=
    LinearMap.ext (fun x => t x)
  have countBas := dirsummand_of_dirSumCountable FBasis s (Finsupp.linearCombination R id) hπs
  refine IsDirectSumOfCountablyGenerated.mk ?_
  obtain ⟨k,fam',intFam, countj⟩ := countBas
  simp only[IsCountablyGenerated] at countj
  use k, Classical.decEq k, fam', intFam, countj



/-- A flat, Mittag-Leffler, countably generated R-module is projective.

This is the key step in the proof of Theorem II. The argument proceeds as follows:
  1. By Lazard's theorem, P = DirectLimit G f where each G i is finitely presented and free.
  2. By mittagLeffler_countablyGenerated_has_countable_colimit, we may assume the index
     set is countable.
  3. Projectivity is verified via the lifting property: given a surjection f : N₂ → N₃
     and a map g : P → N₃, the maps g ∘ (of i) form an element of lim← Hom(Gᵢ, N₃).
  4. Since P is Mittag-Leffler, the inverse systems Hom(Gᵢ, N) are Mittag-Leffler for
     every N (by the equivalence of conditions (1) and (4) in Theorem 7.1 of the paper).
  5. The surjectivity theorem for Mittag-Leffler inverse systems (Theorem 5.2 of the
     paper, surjective_limit_of_mittagLeffler_exact) provides a compatible family of
     lifts in lim← Hom(Gᵢ, N₂), which assembles via DirectLimit.lift into P → N₂. -/
theorem proj_if_countable_flat_Mittag_Leffler {R : Type u} {P : Type u} [CommRing R]
[AddCommGroup P] [Module R P] (PFlat : Module.Flat R P) (PML : Module.IsMittagLeffler R P)
(PCount : ∃ s : Set P, s.Countable ∧ span R s = ⊤) : Module.Projective R P := by

  have PhasLlmit := (Module.Flat.Lazard (R := R) (M := P)).mp PFlat
  obtain ⟨ι, preord, dir, nonempt, deceq, G, addcomm, mod, fp, free, f, ds, iso⟩ := PhasLlmit
  have conIso := iso.some
  suffices P'Proj : Module.Projective R  (Module.DirectLimit G fun x x_1 h ↦ f h) by
    apply Module.Projective.of_equiv conIso
  have P'ML : Module.IsMittagLeffler R (Module.DirectLimit G fun x x_1 h ↦ f h) := by
    apply Module.IsMittagLeffler.of_iso (R:=R) (M:=P)
      (N:=(Module.DirectLimit G fun x x_1 h ↦ f h)) (h:=PML) (e:=conIso.symm)
  have P'Count :
    ∃ s : Set (Module.DirectLimit G fun x x_1 h ↦ f h), s.Countable ∧ span R s = ⊤ := by
      obtain ⟨s, hcount, hspan⟩ := PCount
      use conIso.symm '' s
      constructor
      · exact hcount.image _
      · have h1 : span R (conIso.symm '' s) = Submodule.map conIso.symm.toLinearMap (span R s) := by
          rw [Submodule.map_span]
          exact toSubMulAction_inj.mp rfl
        rw[h1,hspan,Submodule.map_top]
        exact LinearEquiv.range conIso.symm
  let f' : ∀ i j, i ≤ j → G i →ₗ[R] G j := fun i j h => f h
  have ctI := Module.mittagLeffler_countablyGenerated_has_countable_colimit G f' P'ML P'Count
  obtain ⟨I', hI'count, hI'dir, hI'nonempty, hI'iso⟩ := ctI
  let conIso2 := hI'iso.some
  suffices P''Proj : Module.Projective R
    (Module.DirectLimit (fun i : I' => G i.val) (fun i j hij => f' i.val j.val hij)) by
    exact Module.Projective.of_equiv conIso2.symm
  -- Verify projectivity via the lifting property.
  apply Module.Projective.of_lifting_property
  intro N_2 N_3 _ _ _ _ f g fsurj
  let N_1 := (LinearMap.ker f).module
  let inc := (LinearMap.ker f).subtype
  have exact : LinearMap.range inc = LinearMap.ker f := by
    simp only [inc]
    exact range_subtype (ker f)

  -- The map Hom(G i, ker f) → Hom(G i, N_2) induced by the inclusion
  let φ₁ : ∀ i : I', (G i →ₗ[R] ker f) →ₗ[R] (G i →ₗ[R] N_2) :=
  fun i => {
    toFun := fun h => inc.comp h
    map_add' := fun h₁ h₂ => by ext; simp
    map_smul' := fun r h => by ext; simp
  }

  -- The map Hom(G i, N_2) → Hom(G i, N_3) induced by f
  let φ₂ : ∀ i : I', (G i →ₗ[R] N_2) →ₗ[R] (G i →ₗ[R] N_3) :=
  fun i => {
    toFun := fun h => f.comp h
    map_add' := fun h₁ h₂ => by ext; simp
    map_smul' := fun r h => by ext; simp
  }

  -- φ₂ is surjective because G i is free (hence projective) and f is surjective.
  have hφ₂_surj : ∀ i : I', Function.Surjective (φ₂ i) := fun i h => by
    haveI : Module.Free R (G i) := free i
    obtain ⟨lift, hlift⟩ := Module.projective_lifting_property f h fsurj
    refine ⟨lift,?_⟩
    exact hlift

  -- Exactness: range φ₁ = ker φ₂, since the short exact sequence 0 → ker f → N₂ → N₃ → 0
  -- remains exact after applying Hom(G i, -).
  have hexact_φ : ∀ i : I', LinearMap.range (φ₁ i) = LinearMap.ker (φ₂ i) := fun i => by
    ext h
    simp only [LinearMap.mem_range, LinearMap.mem_ker, φ₁, φ₂]
    constructor
    · rintro ⟨h', rfl⟩
      ext x
      simp only [LinearMap.zero_apply]
      exact LinearMap.mem_ker.mp (h' x).property
    · intro hfh
      use {
        toFun := fun x =>
          ⟨h x, by exact LinearMap.mem_ker.mpr (congrFun (congrArg DFunLike.coe hfh) x)⟩
        map_add' := fun x y => by simp [map_add]
        map_smul' := fun r x => by simp [map_smul]
      }
      ext x
      simp [inc]


  -- The transition maps for the Hom inverse systems (precomposition with f').
  let fHom₁ : ∀ ⦃i j : I'⦄, i ≤ j → (G j →ₗ[R] ker f) → (G i →ₗ[R] ker f) :=
    fun i j hij h => h.comp (f' i j hij)

  let fHom₂ : ∀ ⦃i j : I'⦄, i ≤ j → (G j →ₗ[R] N_2) → (G i →ₗ[R] N_2) :=
    fun i j hij h => h.comp (f' i j hij)

  let fHom₃ : ∀ ⦃i j : I'⦄, i ≤ j → (G j →ₗ[R] N_3) → (G i →ₗ[R] N_3) :=
    fun i j hij h => h.comp (f' i j hij)

  -- These form inverse systems (follows from the directed system axioms on f').
  have hInvSys₁ : InverseSystem fHom₁ := by
    constructor
    · intro i h
      simp only [fHom₁]
      ext x
      simp [DirectedSystem.map_self (f := fun i j h => f' i j h)]
    · intro i j k hij hjk h
      simp only [fHom₁]
      ext x
      simp [DirectedSystem.map_map (f := fun i j h => f' i j h) hij hjk]

  have hInvSys₂ : InverseSystem fHom₂ := by
    constructor
    · intro i h
      simp only [fHom₂]
      ext x
      simp [DirectedSystem.map_self (f := fun i j h => f' i j h)]
    · intro i j k hij hjk h
      simp only [fHom₂]
      ext x
      simp [DirectedSystem.map_map (f := fun i j h => f' i j h) hij hjk]

  have hInvSys₃ : InverseSystem fHom₃ := by
    constructor
    · intro i h
      simp only [fHom₃]
      ext x
      simp [DirectedSystem.map_self (f := fun i j h => f' i j h)]
    · intro i j k hij hjk h
      simp only [fHom₃]
      ext x
      simp [DirectedSystem.map_map (f := fun i j h => f' i j h) hij hjk]

  -- The Mittag-Leffler property for the Hom inverse systems follows from the
  -- Mittag-Leffler property of P (equivalence of conditions (1) and (4) in
  -- Theorem 7.1 of the paper).
  haveI : IsDirected I' (· ≤ ·) := by
    constructor
    intro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨c, hc, hac, hbc⟩ := hI'dir a ha b hb
    exact ⟨⟨c, hc⟩, hac, hbc⟩

  haveI : Nonempty I' := hI'nonempty.to_subtype

  haveI : DirectedSystem (fun i : I' => G i.val) (fun i j h => f' i.val j.val h) := by
    constructor
    · intro i x
      exact DirectedSystem.map_self (f := fun i j h => f' i j h) x
    · intro i j k hij hjk x
      exact DirectedSystem.map_map (f := fun i j h => f' i j h) hij hjk x

  have P'_restricted_ML : Module.IsMittagLeffler R
      (Module.DirectLimit (fun i : I' => G i.val) (fun i j hij => f' i.val j.val hij)) := by
    apply Module.IsMittagLeffler.of_iso (R:=R) (M := Module.DirectLimit G f')
    · exact P'ML
    · exact conIso2

  have hML'_restricted : Module.IsMittagLeffler' R
      (fun i : I' => G i.val)
      (fun i j hij => f' i.val j.val hij) := by
    rw [Module.isMittagLeffler_iff_isMittagLeffler']
    exact P'_restricted_ML

  have hML''_restricted : Module.IsMittagLeffler'' R
    (fun i : I' => G i.val)
    (fun i j hij => f' i.val j.val hij) := by
    rw [← Module.isMittagLeffler'_iff_isMittagLeffler'']
    exact hML'_restricted

  have hf_restricted : ∀ i : I', (fun i j hij => f' i.val j.val hij) i i (le_refl i) =
    LinearMap.id := by
    intro i
    ext x
    exact DirectedSystem.map_self (f := fun i j h => f' i j h) x


  have hcomp_restricted : ∀ (i j k : I') (hij : i ≤ j) (hjk : j ≤ k),
    (fun i j hij => f' i.val j.val hij) i k (hij.trans hjk) =
    ((fun i j hij => f' i.val j.val hij) j k hjk).comp
    ((fun i j hij => f' i.val j.val hij) i j hij) := by
    intro i j k hij hjk
    ext x
    exact (DirectedSystem.map_map (f := fun i j h => f' i j h) hij hjk x).symm

  have hML'''_restricted : Module.IsMittagLeffler''' R
      (fun i : I' => G i.val)
      (fun i j hij => f' i.val j.val hij)
      hf_restricted
      hcomp_restricted := by
    exact (Module.isMittagLeffler''_iff_isMittagLeffler'''
      (F := fun i : I' => G i.val)
      (f := fun i j hij => f' i.val j.val hij)
      hf_restricted
      hcomp_restricted).mp hML''_restricted

  have hML_Hom₁ : @InverseSystem.IsMittagLeffler I' _ (fun i => G i.val →ₗ[R] ker f)
      (fun _ => ⟨0⟩) fHom₁ hInvSys₁ := by
    apply hML'''_restricted (N := ker f)
    intro i
    exact ⟨0⟩

  have hML_Hom₂ : @InverseSystem.IsMittagLeffler I' _ (fun i => G i.val →ₗ[R] N_2)
      (fun _ => ⟨0⟩) fHom₂ hInvSys₂ := by
    apply hML'''_restricted (N := N_2)
    intro i
    exact ⟨0⟩

  have hML_Hom₃ : @InverseSystem.IsMittagLeffler I' _ (fun i => G i.val →ₗ[R] N_3)
      (fun _ => ⟨0⟩) fHom₃ hInvSys₃ := by
    apply hML'''_restricted (N := N_3)
    intro i
    exact ⟨0⟩
  let fHom₁_lin : ∀ (i j : I') (hij : i ≤ j), (G j →ₗ[R] ker f) →ₗ[R] (G i →ₗ[R] ker f) :=
      fun i j hij => {
        toFun := fun h => h.comp (f' i.val j.val hij)
        map_add' := fun h₁ h₂ => by ext x; simp
        map_smul' := fun r h => by ext x; simp
      }

  let fHom₂_lin : ∀ (i j : I') (hij : i ≤ j), (G j →ₗ[R] N_2) →ₗ[R] (G i →ₗ[R] N_2) :=
    fun i j hij => {
      toFun := fun h => h.comp (f' i.val j.val hij)
      map_add' := fun h₁ h₂ => by ext x; simp
      map_smul' := fun r h => by ext x; simp
    }

  let fHom₃_lin : ∀ (i j : I') (hij : i ≤ j), (G j →ₗ[R] N_3) →ₗ[R] (G i →ₗ[R] N_3) :=
    fun i j hij => {
      toFun := fun h => h.comp (f' i.val j.val hij)
      map_add' := fun h₁ h₂ => by ext x; simp
      map_smul' := fun r h => by ext x; simp
    }

  haveI : Countable I' := hI'count.to_subtype

  haveI : ∀ i : I', Nonempty (G i.val →ₗ[R] ker f) := fun _ => ⟨0⟩
  haveI : ∀ i : I', Nonempty (G i.val →ₗ[R] N_2) := fun _ => ⟨0⟩
  haveI : ∀ i : I', Nonempty (G i.val →ₗ[R] N_3) := fun _ => ⟨0⟩

  -- Naturality: φ₁ and φ₂ commute with the transition maps.
  have hφ₁_compat : ∀ (i j : I') (hij : i ≤ j) (a : G j.val →ₗ[R] ker f),
      fHom₂_lin i j hij (φ₁ j a) = φ₁ i (fHom₁_lin i j hij a) := by
    intro i j hij a
    ext x
    simp [fHom₁_lin, fHom₂_lin, φ₁]

  have hφ₂_compat : ∀ (i j : I') (hij : i ≤ j) (b : G j.val →ₗ[R] N_2),
      fHom₃_lin i j hij (φ₂ j b) = φ₂ i (fHom₂_lin i j hij b) := by
    intro i j hij b
    ext x
    simp [fHom₂_lin, fHom₃_lin, φ₂]

  -- Apply the surjectivity theorem for Mittag-Leffler inverse systems
  -- (Theorem 5.2 of the paper) to the right-exact sequence of Hom inverse systems.
  have hsurj_limit := InverseSystem.surjective_limit_of_mittagLeffler_exact
    (fA := fun i j hij => fHom₁_lin i j hij)
    (fB := fun i j hij => fHom₂_lin i j hij)
    (fC := fun i j hij => fHom₃_lin i j hij)
    (f := φ₁)
    (g := φ₂)
    hφ₂_surj
    hexact_φ
    hφ₁_compat
    hφ₂_compat


  -- g induces a compatible family in the inverse limit of Hom(G i, N_3).
  let g_family : InverseSystem.InverseLimit (fun i j hij => fHom₃_lin i j hij) := by
    refine ⟨fun i => g.comp (Module.DirectLimit.of R I' (fun i => G i.val)
       (fun i j hij => f' i.val j.val hij) i), ?_⟩
    intro i j hij
    ext x
    simp only [fHom₃_lin]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, coe_comp, Function.comp_apply,
      Module.DirectLimit.of_f]

  -- Apply surjectivity to obtain a compatible family of lifts in lim← Hom(Gᵢ, N₂).
  obtain ⟨h_family, hh_family⟩ := hsurj_limit g_family

  -- Assemble the compatible family into a global lift P → N₂ via DirectLimit.lift.
  let h : (Module.DirectLimit (fun i : I' => G i.val)
  (fun i j hij => f' i.val j.val hij)) →ₗ[R] N_2 :=
    Module.DirectLimit.lift R I' (fun i : I' => G i.val) (fun i j hij => f' i.val j.val hij)
      (fun i => h_family.val i)
      (fun i j hij x => by
        have := h_family.property i j hij
        simp only [fHom₂_lin] at this
        exact congrFun (congrArg DFunLike.coe this) x)

  use h
  ext x
  simp only [LinearMap.comp_apply, h, Module.DirectLimit.lift_of]
  have := congrArg Subtype.val hh_family
  have hi := congrFun this x
  simp only [φ₂, LinearMap.coe_mk, AddHom.coe_mk] at hi
  exact congrFun (congrArg DFunLike.coe hi) _




/-- An internal direct sum of projective modules is projective.

The proof uses the universal property of the direct sum: a lifting problem for ⨁ᵢ Mᵢ
reduces to independent lifting problems for each summand Mᵢ via the inclusions ιᵢ,
and each summand is projective by hypothesis. -/
theorem projective_if_interalsum_is {R : Type u} {P : Type u} [CommRing R]
[AddCommGroup P] [Module R P] (ι : Type u) (_ : DecidableEq ι) (fam : ι → Submodule R P)
    (internalsum : DirectSum.IsInternal fam)
    (eachProj : ∀ i, Module.Projective R (fam i)) : Module.Projective R P :=
    by
    let φ := LinearEquiv.ofBijective (DirectSum.coeLinearMap fam) internalsum
    suffices Module.Projective R (⨁ (i : ι), ↥(fam i)) by
      apply Module.Projective.of_equiv φ
    apply Module.Projective.of_lifting_property'
    intro M N _ _ _ _ f g surjF
    let ιi := DirectSum.lof R ι (fun i => ↥(fam i))
    let gi := fun i => g.comp (ιi i)
    have key : ∀ i : ι, ∃ hi : (fam i) →ₗ[R] M, f ∘ₗ hi = gi i := by
      intro i
      have proji := (eachProj i)
      exact Module.projective_lifting_property f (gi i) surjF
    choose hi hfi using key
    use DirectSum.toModule R ι M hi
    ext i x
    simp only [coe_comp, Function.comp_apply, toModule_lof]
    exact LinearMap.congr_fun (hfi i) x



/-- Characterization of projective modules (Theorem II of the paper):
An R-module P is projective if and only if it is flat, Mittag-Leffler, and a direct sum
of countably generated R-modules.

Forward direction: projectivity implies all three conditions, using standard results and
Kaplansky's theorem (proj_is_dirSumCountable).

Backward direction: The direct sum decomposition P = ⨁ᵢ Mᵢ reduces to showing each
Mᵢ is projective; since each Mᵢ inherits flatness and the Mittag-Leffler property from
P as a direct summand, and is countably generated by hypothesis, the result follows
from proj_if_countable_flat_Mittag_Leffler. -/
theorem proj_iff_Mittag_Leffler {R : Type u} {P : Type u} [CommRing R]
[AddCommGroup P] [Module R P] : Module.Projective R P ↔
(Module.Flat R P) ∧ (Module.IsMittagLeffler R P) ∧ (IsDirectSumOfCountablyGenerated R P)
:= by
  constructor
  · intro PProj
    have : Module.Flat R P := by exact Module.Flat.of_projective
    refine ⟨this,?_⟩
    have : Module.IsMittagLeffler R P := by exact Module.proj_is_Mittag_Leffler
    refine ⟨this,?_⟩
    have : IsDirectSumOfCountablyGenerated R P := by exact proj_is_dirSumCountable PProj
    exact this
  · intro PAssumptions
    rcases PAssumptions with ⟨PFlat, PML, PDirSum⟩
    rcases PDirSum with ⟨IndexSet,ISdec,M,SumMiisP,Miountable⟩

    -- Each summand Mᵢ is a direct summand of P, hence inherits the retraction structure.
    have hRetract : ∀ i : IndexSet, ∃ (incl : (M i) →ₗ[R] P) (proj : P →ₗ[R] (M i)),
        proj.comp incl = LinearMap.id := fun i => by
      let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap M) SumMiisP
      let incl : (M i) →ₗ[R] P := (M i).subtype
      let proj : P →ₗ[R] (M i) :=
        (DirectSum.component R IndexSet (fun i => ↥(M i)) i).comp e.symm.toLinearMap
      have hcomp : proj.comp incl = LinearMap.id := by
        ext ⟨x, hx⟩
        simp only [LinearMap.comp_apply, LinearMap.id_apply, proj, incl]
        have h := DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem SumMiisP hx
        change ↑((e.symm x) i) = x
        rw [h]
      exact ⟨incl, proj, hcomp⟩

    have allflat : ∀ i : IndexSet, Module.Flat R (M i) := fun i => by
      obtain ⟨incl, proj, hcomp⟩ := hRetract i
      exact Module.Flat.of_retract incl proj hcomp

    have allML : ∀ i : IndexSet, Module.IsMittagLeffler R (M i) := fun i => by
      obtain ⟨incl, proj, hcomp⟩ := hRetract i
      exact Module.IsMittagLeffler.of_direct_summand PML incl proj hcomp

    have allCG : ∀ i : IndexSet, ∃ s : Set (M i), s.Countable ∧ span R s = ⊤ := fun i => by
      exact Miountable i

    have allProj : ∀ i :IndexSet, Module.Projective R (M i) := by
      intro i
      have Miflat : Module.Flat R (M i) := by exact allflat i
      have MiML : Module.IsMittagLeffler R (M i) := by exact allML i
      have MiCG : ∃ s : Set (M i), s.Countable ∧ span R s = ⊤ := by exact allCG i
      apply proj_if_countable_flat_Mittag_Leffler Miflat MiML MiCG
    apply projective_if_interalsum_is
      (ι := IndexSet) (internalsum := SumMiisP) (eachProj := allProj)


/-- Faithful flatness reflects the Mittag-Leffler property (Theorem 8.1 of the paper,
[Stacks Project, Tag 05A5]).

If R → S is faithfully flat and S ⊗[R] M is Mittag-Leffler over S, then M is
Mittag-Leffler over R.

The proof writes M as a directed colimit lim→ Gᵢ of finitely presented modules and uses
the equivalence of conditions (1) and (2) in Theorem 7.1 of the paper. The hypothesis
gives a stabilization index for each i in the base-changed system (S ⊗[R] Gᵢ). The
key step transfers this stabilization to the original system using the pushout
characterization of domination (Theorem 6.2) together with
UniversallyInjective.of_baseChange_faithfullyFlat. -/
theorem ML_of_faithfullyFlat_tensorProduct {R : Type u} {S : Type u} {M : Type u}
[CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
[AddCommGroup M] [Module R M]
(h : Module.IsMittagLeffler S (TensorProduct R S M)) :
Module.IsMittagLeffler R M := by

  -- Write M as a direct limit of finitely presented modules.
  have MisLimit := Module.isDirectLimit_of_finitelyPresented (R:=R) (M:=M)
  obtain ⟨ι, preord, dir, directed, deceq, G, addcomm, mod, fp, f, dirSys, iso⟩ := MisLimit
  have coniso := iso.some
  let idS : S →ₗ[S] S := LinearMap.id
  let tenIso : TensorProduct R S (Module.DirectLimit G fun x x_1 h ↦ f h)
    ≃ₗ[S] TensorProduct R S M :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) coniso

  suffices limIsML : Module.IsMittagLeffler R (Module.DirectLimit G fun x x_1 h ↦ f h) by
    apply Module.IsMittagLeffler.of_iso (e:=coniso) (h:=limIsML)

  -- Use TensorProduct.directLimitRightSLinear to transfer the Mittag-Leffler
  -- property from the base-changed direct limit to the original one.
  let iso_lim := TensorProduct.directLimitRight f S
  let iso_map := iso_lim.toLinearMap

  let iso_lim_S_equiv := TensorProduct.directLimitRightSLinear
    (R := R) (S := S) G (fun i j h => f h)

  have limTenML : Module.IsMittagLeffler S (Module.DirectLimit
      (fun i => TensorProduct R S (G i))
      (fun i j hij => TensorProduct.AlgebraTensorModule.map
        (LinearMap.id (R := S) (M := S)) (f hij))) := by
    apply Module.IsMittagLeffler.of_iso S h (tenIso.symm.trans iso_lim_S_equiv)


  let G' : ι → Type u := fun i => S ⊗[R] G i

  letI inst_acg : ∀ i, AddCommGroup (G' i) := fun i => TensorProduct.addCommGroup
  letI inst_mod : ∀ i, Module S (G' i) := fun i => TensorProduct.leftModule

  let f' : ∀ i j, i ≤ j → G' i →ₗ[S] G' j :=
    fun i j hij => TensorProduct.AlgebraTensorModule.map LinearMap.id (f hij)

  haveI : ∀ i, Module.FinitePresentation S (S ⊗[R] G i) := fun i => inferInstance

  haveI hDS : DirectedSystem G' (fun i j h => f' i j h) := by
    constructor
    · intro i x
      simp only [f']
      have h1 : f (le_refl i) = LinearMap.id := by
        ext y
        exact DirectedSystem.map_self (f := fun i j h => f h) y
      simp only [h1, TensorProduct.AlgebraTensorModule.map_id, LinearMap.id_apply]
    · intro i j k hij hjk x
      simp only [f']
      have hcomp : f (hij.trans hjk) = (f hjk).comp (f hij) := by
        ext y
        exact (DirectedSystem.map_map (f := fun i j h => f h) hij hjk y).symm
      simp only [hcomp]
      have hmapcomp : TensorProduct.AlgebraTensorModule.map
        (LinearMap.id : S →ₗ[S] S) (f hjk ∘ₗ f hij) =
          (TensorProduct.AlgebraTensorModule.map LinearMap.id (f hjk)).comp
          (TensorProduct.AlgebraTensorModule.map LinearMap.id (f hij)) := by
        rw [← TensorProduct.AlgebraTensorModule.map_comp]
        simp only [LinearMap.id_comp]
      conv_rhs => rw [hmapcomp, LinearMap.comp_apply]

  -- Transfer the Mittag-Leffler condition to the IsMittagLeffler' reformulation
  -- and extract the stabilization index for each i.
  have limTenML' : @Module.IsMittagLeffler' S _ ι _ _ _ _ G' inst_acg inst_mod _ f' hDS := by
    rw [Module.isMittagLeffler_iff_isMittagLeffler']
    convert limTenML
  rw[Module.IsMittagLeffler'] at limTenML'
  rw [← Module.isMittagLeffler_iff_isMittagLeffler']
  rw[Module.IsMittagLeffler']
  intro i
  obtain ⟨j,hij,keyFact⟩ := limTenML' i
  use j,hij

  -- The domination condition over S is witnessed by the pushout map being universally
  -- injective over S. We descend this along the faithfully flat map R → S using
  -- UniversallyInjective.of_baseChange_faithfullyFlat.
  let map1:=(f hij)
  let map2:= (Module.DirectLimit.of R ι G f i)
  let N := Pushout (f:=map1) (g:=map2)
  let map3 := Pushout.inl (f:=map1) (g:=map2)
  let map4 := Pushout.inr (f:=map1) (g:=map2)

  rw[dominates_iff_pushout_inr_universallyInjective]
  rw[dominates_iff_pushout_inr_universallyInjective] at keyFact
  apply UniversallyInjective.of_baseChange_faithfullyFlat (S := S)

  -- The base-changed pushout map factors through the pushout of the base-changed maps
  -- via the isomorphism Pushout.baseChangeEquiv (Theorem 3.1 of the paper).
  have eq := Pushout.baseChangeEquiv_inr (S := S) (f := map2) (g := map1)

  have eq' : (Pushout.inr map2 map1).baseChange S =
      (Pushout.baseChangeEquiv (S := S) map2 map1).symm.toLinearMap ∘ₗ
      Pushout.inr (map2.baseChange S) (map1.baseChange S) := by
    rw [← eq, ← LinearMap.comp_assoc]
    simp only [LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
      id_comp]

  rw [eq']

  -- Universal injectivity is preserved under precomposition with a linear equivalence.
  have h_equiv_inj : (Pushout.inr (map2.baseChange S) (map1.baseChange S)).UniversallyInjective →
    ((Pushout.baseChangeEquiv (S := S) map2 map1).symm.toLinearMap ∘ₗ
     Pushout.inr (map2.baseChange S) (map1.baseChange S)).UniversallyInjective := by
    intro hf Q _ _
    rw [LinearMap.rTensor_comp]
    have h1 : Function.Injective
      ((Pushout.baseChangeEquiv (S := S) map2 map1).symm.toLinearMap.rTensor Q) := by
      have e : (Pushout.baseChangeEquiv (S := S) map2 map1).symm.toLinearMap.rTensor Q =
              ((Pushout.baseChangeEquiv (S := S) map2 map1).rTensor Q).symm.toLinearMap := by
        ext x
        simp
      rw [e]
      exact LinearEquiv.injective _
    exact h1.comp (hf Q)

  apply h_equiv_inj

  -- Identify the base-changed transition map and base-changed "of i" map in terms of
  -- the S-linear system G', and reduce to keyFact via a pushout equivalence.
  have map1_eq : map1.baseChange S = f' i j hij := by
    simp only [map1, f']
    ext x
    simp [LinearMap.baseChange, TensorProduct.AlgebraTensorModule.map]

  have map2_compat : iso_lim_S_equiv.toLinearMap ∘ₗ map2.baseChange S =
      Module.DirectLimit.of S ι G' f' i := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s g =>
      simp only [LinearMap.comp_apply, map2, LinearMap.baseChange_tmul]
      exact TensorProduct.directLimitRightSLinear_tmul_of G (fun i j h => f h) s i g
    | add x y hx hy => simp only [map_add, hx, hy]


  have map2_eq : LinearMap.baseChange S map2 =
      iso_lim_S_equiv.symm.toLinearMap ∘ₗ Module.DirectLimit.of S ι G' f' i := by
    apply LinearMap.ext
    intro x
    have h : (iso_lim_S_equiv.toLinearMap ∘ₗ LinearMap.baseChange S map2) x =
            (Module.DirectLimit.of S ι G' f' i) x := congrFun (congrArg DFunLike.coe map2_compat) x
    simp only [LinearMap.comp_apply] at h ⊢
    rw [← h]
    exact (iso_lim_S_equiv.symm_apply_apply _).symm

  have pushout_equiv_hg : (LinearEquiv.refl S (G' j)).toLinearMap ∘ₗ (map1.baseChange S)
    = f' i j hij := by
    simp only [LinearEquiv.refl_toLinearMap, LinearMap.id_comp, map1_eq]

  let pushout_equiv : Pushout (map2.baseChange S) (map1.baseChange S) ≃ₗ[S]
      Pushout (Module.DirectLimit.of S ι G' f' i) (f' i j hij) :=
    Pushout.congrEquiv (map2.baseChange S) (map1.baseChange S)
      iso_lim_S_equiv (LinearEquiv.refl S (G' j))
      (Module.DirectLimit.of S ι G' f' i) (f' i j hij) map2_compat pushout_equiv_hg

  have inr_compat : pushout_equiv.toLinearMap ∘ₗ Pushout.inr (map2.baseChange S)
    (map1.baseChange S) =
      Pushout.inr (Module.DirectLimit.of S ι G' f' i) (f' i j hij) := by
      simpa [pushout_equiv, LinearEquiv.refl_toLinearMap] using
      (Pushout.congrEquiv_inr (R := S)
        (f := LinearMap.baseChange S map2) (g := LinearMap.baseChange S map1)
        (eB := iso_lim_S_equiv) (eC := LinearEquiv.refl S (G' j))
        (f' := Module.DirectLimit.of S ι G' f' i) (g' := f' i j hij)
        (hf := map2_compat) (hg := pushout_equiv_hg))


  have inr_compat' : Pushout.inr (map2.baseChange S) (map1.baseChange S) =
    pushout_equiv.symm.toLinearMap ∘ₗ Pushout.inr
      (Module.DirectLimit.of S ι G' f' i) (f' i j hij) := by
    ext x
    have hx := congrFun (congrArg DFunLike.coe inr_compat) x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at hx ⊢
    rw [← hx, pushout_equiv.symm_apply_apply]

  rw [inr_compat']
  intro Q _ _
  rw [LinearMap.rTensor_comp]
  have h1 : Function.Injective ((pushout_equiv.symm.toLinearMap).rTensor Q) :=
    pushout_equiv.symm.rTensor Q |>.injective
  exact h1.comp (keyFact Q)


/-
Faithful flatness reflects countable generation [Stacks Project, Tag 0GVD]:
If R → S is faithfully flat and S ⊗[R] P is countably generated over S,
then P is countably generated over R.
-/

/-- Faithful flatness reflects countable generation (Theorem 8.2 / [Stacks, Tag 0GVD]).

If R → S is faithfully flat and S ⊗[R] P is countably generated over S, then P is
countably generated over R.

The proof enumerates a countable generating set of S ⊗[R] P, expresses each generator
as a finite sum of pure tensors, collects all P-components into a countable subset t ⊆ P,
and then uses faithful flatness to show that t generates P over R. -/
theorem countably_generated_faithfully_flat {R : Type u} {S : Type u} {P : Type u}
[CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S] [AddCommGroup P] [Module R P]
(PSIsCountable : ∃ s : Set (TensorProduct R S P), s.Countable ∧ span S s = ⊤) :
∃ t : Set P, t.Countable ∧ span R t = ⊤ := by

classical
obtain ⟨s,scount,sgen⟩ := PSIsCountable
by_cases h : s.Nonempty
· have surjEx :  ∃ f : ℕ → s, f.Surjective := by
    apply Set.Countable.exists_surjective h scount
  obtain ⟨f,fsurj⟩ := surjEx
  have coll : ∀ i, ∃ t : Finset (S × P), (f i : S ⊗[R] P) = t.sum (fun p => p.1 ⊗ₜ p.2) := by
    intro i
    exact TensorProduct.exists_finset ((f i : S ⊗[R] P))
  choose coll hcoll using coll
  -- Collect all P-components of the finite decompositions into a countable set t.
  let t : Set P := ⋃ i, ((coll i : Finset (S × P)).image Prod.snd : Set P)
  use t
  have tcount : t.Countable := by
    apply Set.countable_iUnion
    intro i
    exact Finset.countable_toSet (Finset.image Prod.snd (coll i))
  refine ⟨tcount,?_ ⟩
  let P' := span R t
  let φ := P'.subtype
  -- Use faithful flatness: φ is surjective iff id ⊗ φ is surjective.
  have φsurj : Function.Surjective φ := by
    suffices h : Function.Surjective (φ.lTensor S) by
      exact (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S φ).mp h
    let idS : S →ₗ[S] S := LinearMap.id
    suffices h : Function.Surjective (TensorProduct.AlgebraTensorModule.map idS φ) by
      intro x
      obtain ⟨y,yprop⟩ := h x
      use y
      rw[lTensor]
      exact yprop
    rw[←LinearMap.range_eq_top]
    suffices h : s ≤  LinearMap.range (TensorProduct.AlgebraTensorModule.map idS φ) by
      have hspan :
        span S s ≤ (LinearMap.range (TensorProduct.AlgebraTensorModule.map idS φ)) := by
        exact Submodule.span_le.2 h
      have htop :
      (⊤ : Submodule S (S ⊗[R] P)) ≤
        (LinearMap.range (TensorProduct.AlgebraTensorModule.map idS φ)) := by
        have : (⊤ : Submodule S (S ⊗[R] P)) = span S s := by
          exact Eq.symm sgen
        rw[this]
        exact hspan

      exact le_antisymm le_top htop

    intro x xins
    let xs : (↑s) := ⟨x, xins⟩
    obtain ⟨n,nprop⟩ := fsurj xs
    let colln := coll n
    let hcolln := hcoll n
    have hfnx : (f n : S ⊗[R] P) = x := by
      have hvals : ((f n : ↑s) : S ⊗[R] P) = (xs : S ⊗[R] P) := congrArg Subtype.val nprop
      apply Eq.trans hvals
      rfl
    have hxsum : x = ∑ p ∈ coll n, p.1 ⊗ₜ[R] p.2 := by
      exact Eq.trans (Eq.symm hfnx) hcolln

    change x ∈ (LinearMap.range (TensorProduct.AlgebraTensorModule.map idS φ) : Set (S ⊗[R] P))
    rw [hxsum]
    refine (LinearMap.range (TensorProduct.AlgebraTensorModule.map idS φ)).sum_mem ?_
    intro p hp

    have hp_t : p.2 ∈ t := by
      refine Set.mem_iUnion.2 ?_
      refine ⟨n, ?_⟩
      change p.2 ∈ (↑(Finset.image Prod.snd (coll n)) : Set P)
      refine (Finset.mem_coe).2 ?_
      exact Finset.mem_image.2 ⟨p, hp, rfl⟩
    have hp_P' : p.2 ∈ P' := by
      change p.2 ∈ (span R t : Submodule R P)
      exact Submodule.subset_span hp_t
    refine ⟨p.1 ⊗ₜ[R] (⟨p.2, hp_P'⟩ : P'), ?_⟩
    simp only [TensorProduct.AlgebraTensorModule.map_tmul, idS, φ, id_coe, id_eq, subtype_apply]
  rw[←LinearMap.range_eq_top] at φsurj
  have hrange : LinearMap.range φ = P' := by
    change LinearMap.range P'.subtype = P'
    exact P'.range_subtype
  have hPtop : (P' : Submodule R P) = ⊤ := by
    calc
      P' = LinearMap.range φ := by exact Eq.symm hrange
      _ = ⊤ := by exact φsurj
  change P' = ⊤
  exact hPtop
· -- Degenerate case: s is empty, so S ⊗[R] P = 0, hence P = 0 by faithful flatness.
  push_neg at h
  rw[h] at sgen
  simp only [span_empty] at sgen
  have singsp : Subsingleton (S ⊗[R] P) := by
    constructor
    intro a b
    have ha : a ∈ (⊤ : Submodule S (S ⊗[R] P)) := trivial
    have hb : b ∈ (⊤ : Submodule S (S ⊗[R] P)) := trivial
    rw [← sgen] at ha hb
    simp only [mem_bot] at ha hb
    rw [ha, hb]
  haveI singp : Subsingleton P := Module.FaithfullyFlat.lTensor_reflects_triviality R S P
  use ∅
  constructor
  · exact countable_empty
  · simp only [span_empty]
    rw [@eq_top_iff']
    intro x
    simp only [mem_bot]
    exact Subsingleton.eq_zero x


/-- The countably generated case of Theorem I: if R → S is faithfully flat, P is an
R-module, S ⊗[R] P is countably generated and projective over S, then P is projective
over R.

The proof combines the two descent lemmas:
  * ML_of_faithfullyFlat_tensorProduct: S ⊗[R] P projective ⟹ S ⊗[R] P Mittag-Leffler
    ⟹ P Mittag-Leffler.
  * Flatness of P follows from flatness of S ⊗[R] P via
    Module.Flat.iff_flat_tensorProduct.
  * Countable generation of P follows from
    countably_generated_faithfully_flat.
  * Projectivity then follows from proj_if_countable_flat_Mittag_Leffler. -/
theorem proj_countable_faithfully_flat {R : Type u} {S : Type u} {P : Type u}
[CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S] [AddCommGroup P] [Module R P]
(PIsCountable : ∃ s : Set (TensorProduct R S P), s.Countable ∧ span S s = ⊤)
(baseChangeProj : Module.Projective S (TensorProduct R S P)) :
Module.Projective R P := by
  classical
  have SPFlat : Module.Flat S (TensorProduct R S P) := Module.Flat.of_projective
  have PFlat : Module.Flat R P := by
    exact (Module.Flat.iff_flat_tensorProduct R P S).mp SPFlat
  have TensML : Module.IsMittagLeffler S (TensorProduct R S P) := by
    exact Module.proj_is_Mittag_Leffler
  have PML : Module.IsMittagLeffler R P := by
    apply ML_of_faithfullyFlat_tensorProduct (S:=S)
    exact TensML
  have PCount : ∃ t : Set P, t.Countable ∧ span R t = ⊤ := by
    apply countably_generated_faithfully_flat (S:=S)
    exact PIsCountable
  exact proj_if_countable_flat_Mittag_Leffler (PFlat := PFlat) (PML := PML) (PCount := PCount)


/-- Given a countably generated S-submodule Q of S ⊗[R] M, there exists an R-submodule
P of M such that P is countably generated and Q is contained in the image of the
base-changed inclusion S ⊗[R] P → S ⊗[R] M.

This lemma allows one to "lift" a countably generated S-submodule of S ⊗[R] M to
an R-submodule of M. It is used in the construction of the filtration in the proof
of Theorem I. -/
lemma count_gen_sub_mod {R : Type u} {S : Type u} {M : Type u}
[CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
(Q : Submodule S (TensorProduct R S M))
(QIsCountable : ∃ s : Set Q, s.Countable ∧ span S s = ⊤)
 :
∃ P : Submodule R M, ∃ t : Set P, (t.Countable ∧ span R t = ⊤)
∧ Q ≤ LinearMap.range
  (TensorProduct.AlgebraTensorModule.map
    (LinearMap.id (R := S) (M := S))
    P.subtype)
 :=
by
classical
obtain ⟨s,scount,sgen⟩ := QIsCountable
by_cases h: s.Nonempty
· have surjEx :  ∃ f : ℕ → s, f.Surjective := by
     apply Set.Countable.exists_surjective h scount
  obtain ⟨f,fsurj⟩ := surjEx
  have coll : ∀ i, ∃ t : Finset (S × M), (f i : S ⊗[R] M) = t.sum (fun p => p.1 ⊗ₜ p.2) := by
    intro i
    exact TensorProduct.exists_finset ((f i : S ⊗[R] M))
  choose coll hcoll using coll
  let t : Set M := ⋃ i, ((coll i : Finset (S × M)).image Prod.snd : Set M)
  let P : Submodule R M := span R t
  use P
  let t : Set P := Subtype.val ⁻¹' t
  use t
  constructor
  · constructor
    · simp only [t]
      apply Set.Countable.preimage
      · apply Set.countable_iUnion
        intro i
        exact Finset.countable_toSet (Finset.image Prod.snd (coll i))
      · exact Subtype.coe_injective
    · exact span_span_coe_preimage
  · have : ∀ x ∈ s, Q.subtype x ∈
          LinearMap.range
      (TensorProduct.AlgebraTensorModule.map
        (LinearMap.id (R := S) (M := S))
        P.subtype) := by
      intro x xins
      let xs : (↑s) := ⟨x, xins⟩
      obtain ⟨n,nprop⟩ := fsurj xs
      let colln := coll n
      let hcolln := hcoll n
      have hfnx : (f n : S ⊗[R] M) = x := by
        have hvals : ((f n : ↑s) : S ⊗[R] M) = (xs : S ⊗[R] M) := by rw[nprop]
        apply Eq.trans hvals
        rfl
      have hxsum : x = ∑ p ∈ coll n, p.1 ⊗ₜ[R] p.2 := by
        exact Eq.trans (Eq.symm hfnx) hcolln
      change (x : S ⊗[R] M) ∈ LinearMap.range
        (TensorProduct.AlgebraTensorModule.map LinearMap.id P.subtype)
      rw [hxsum]

      refine (LinearMap.range
        (TensorProduct.AlgebraTensorModule.map LinearMap.id P.subtype)).sum_mem ?_

      intro p hp
      rw [@LinearMap.mem_range]
      have p2_in_t : p.2 ∈ (⋃ i, ((coll i : Finset (S × M)).image Prod.snd : Set M)) := by
        apply Set.mem_iUnion_of_mem n
        exact Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.snd hp)

      have p2_in_P : p.2 ∈ P := by
        apply Submodule.subset_span
        exact p2_in_t

      let p2P : P := ⟨p.2, p2_in_P⟩
      use p.1 ⊗ₜ[R] p2P
      simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_coe, id_eq]
      rw [Submodule.subtype_apply]

    have : ∀ q : Q, q ∈ s → q.1 ∈
      LinearMap.range (TensorProduct.AlgebraTensorModule.map LinearMap.id P.subtype) :=
      fun q qmem => this q qmem

    suffices ∀ q : Q, q.1 ∈
      LinearMap.range (TensorProduct.AlgebraTensorModule.map LinearMap.id P.subtype) by
      intro x xmem
      exact this ⟨x, xmem⟩

    intro q
    have key : q ∈ (⊤ : Submodule S Q) := Submodule.mem_top
    rw [← sgen] at key
    rw[mem_span_set'] at key


    obtain ⟨n,f, g,h⟩ := key
    rw[←h]

    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, LinearMap.mem_range]

    suffices h : ∀ x : (Fin n), ∃ y : TensorProduct R S P,
     ((TensorProduct.AlgebraTensorModule.map (LinearMap.id (R := S) (M := S))
       P.subtype) y = (g x) ) by
       choose y hy using h
       use ∑ i, f i • y i
       simp only [map_sum, map_smul]
       simp only [hy]
    intro n
    apply this (g n)
    exact Subtype.coe_prop (g n)
· -- Degenerate case: s is empty, so Q = 0.
  push_neg at h
  rw[h] at sgen
  simp only [span_empty] at sgen
  use 0
  use ∅
  constructor
  · simp only [zero_eq_bot, countable_empty, span_empty, true_and]
    exact Eq.symm eq_bot_of_subsingleton
  · intro x xinq
    have : x = 0 := by
      have hx : (⟨x, xinq⟩ : ↥Q) ∈ (⊤ : Submodule S ↥Q) := by
        trivial
      rw[←sgen] at hx
      exact (AddSubmonoid.mk_eq_zero Q.toAddSubmonoid).mp hx
    rw[this]
    simp only [zero_eq_bot, zero_mem]


/-- Given an internal direct sum S ⊗[R] M = ⨁ᵢ famᵢ with each famᵢ countably generated,
and a countably generated R-submodule N of M, there exists a countably generated
R-submodule N' ≥ N and a set of indices I' such that the image of the base-changed
inclusion S ⊗[R] N' → S ⊗[R] M equals ⨆ i ∈ I', famᵢ.

This is the key inductive step used to build the filtration in the proof of Theorem I:
it shows that the correspondence between R-submodules of M and sub-direct-sums of the
decomposition of S ⊗[R] M can be maintained while extending by countably many indices. -/
lemma count_gen_sum_im {R : Type u} {S : Type u} {M : Type u}
[CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
(ι : Type w) [dec : DecidableEq ι]
(fam : ι → Submodule S (TensorProduct R S M))
(h_sum : DirectSum.IsInternal fam)
(h_count_fam : ∀ i, (fam i).IsCountablyGenerated)
(N : Submodule R M)
(hN : N.IsCountablyGenerated)
 :
∃ N' : Submodule R M, N'.IsCountablyGenerated ∧
  N ≤ N' ∧
  ∃ I' : Set ι,
    LinearMap.range (LinearMap.baseChange S N'.subtype) =
      (⨆ i ∈ I', fam i) :=
by
classical

let decomp : (⨁ i, ↥(fam i)) ≃ₗ[S] (TensorProduct R S M) :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap fam) h_sum

-- The support of a submodule P: the set of direct summand indices where P has
-- a nonzero component. This captures "the projection of P onto fam i is nonzero".
let support : Submodule S (TensorProduct R S M) → Set ι :=
  fun P => {i | ∃ x ∈ P, (decomp.symm x) i ≠ 0}

-- Every submodule is contained in the sub-direct-sum indexed by its support.
have support_le :
    ∀ (P : Submodule S (TensorProduct R S M)),
      P ≤ ⨆ i ∈ support P, fam i := by
  intro P x hxP
  have hx_eq : decomp (decomp.symm x) = x :=
    decomp.apply_symm_apply x
  rw [← hx_eq]
  change DirectSum.coeLinearMap fam (decomp.symm x) ∈ _
  set d := decomp.symm x
  suffices h : ∀ i, ↑(d i) ∈ ⨆ j ∈ support P, fam j by
    have := DirectSum.sum_support_of d
    rw [← this]
    rw [map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [DirectSum.coeLinearMap_of]
    exact h i
  intro i
  by_cases hi : d i = 0
  · simp [hi, zero_mem]
  · have hi_supp : i ∈ support P := ⟨x, hxP, hi⟩
    exact le_iSup₂ (f := fun j _ => fam j) i hi_supp (Submodule.coe_mem (d i))




have lemma_cg :
    ∀ (Q : Submodule S (TensorProduct R S M)),
      Q.IsCountablyGenerated →
      ∃ P : Submodule R M, P.IsCountablyGenerated ∧
        Q ≤ LinearMap.range
          (LinearMap.baseChange S P.subtype) := by
  intro Q hQcg
  obtain ⟨s, hs_count, hs_span⟩ := hQcg
  obtain ⟨P, t, ⟨ht_count, ht_span⟩, hle⟩ :=
    count_gen_sub_mod Q ⟨s, hs_count, hs_span⟩
  refine ⟨P, ⟨t, ht_count, ht_span⟩, ?_⟩
  convert hle using 2


-- The support of a countably generated submodule is countable, since each generator
-- has finite DFinsupp support under the decomposition.
have support_countable :
    ∀ (P : Submodule S (TensorProduct R S M)),
        P.IsCountablyGenerated → (support P).Countable := by
  intro P ⟨s, hs_count, hs_span⟩
  apply Set.Countable.mono _ (hs_count.biUnion
    (fun y _ => Set.Finite.countable
      (DFinsupp.support (decomp.symm (y : TensorProduct R S M))).finite_toSet))
  intro i ⟨x, hxP, hi⟩
  simp only [Set.mem_iUnion]
  by_contra h_none
  push_neg at h_none
  apply hi
  have hxP' : (⟨x, hxP⟩ : P) ∈ span S s := by
    rw [hs_span]; trivial
  have : ∀ y ∈ s, (decomp.symm (y : P).val) i = 0 := by
    intro y hy
    simp only [Finset.mem_coe, DFinsupp.mem_support_iff,
      not_not] at h_none
    exact h_none y hy

  have key : ∀ z ∈ span S s,
        (decomp.symm (z : P).val) i = 0 := by
      intro z hz
      exact Submodule.span_induction
        (p := fun z _ => (decomp.symm (z : P).val) i = 0)
        (fun y hy => this y hy)
        (by simp [map_zero, DirectSum.zero_apply])
        (fun a b _ _ ha hb => by
          simp [map_add, DirectSum.add_apply, ha, hb])
        (fun r a _ ha => by
          simp [map_smul, DirectSum.smul_apply, ha,
            smul_zero])
        hz
  exact key ⟨x, hxP⟩ hxP'




have range_baseChange_cg :
      ∀ (Nn : Submodule R M),
        Nn.IsCountablyGenerated →
        (LinearMap.range
          (LinearMap.baseChange S
            Nn.subtype)).IsCountablyGenerated := by
    intro Nn ⟨s, hs_count, hs_span⟩
    let f := LinearMap.baseChange S Nn.subtype
    let gs : Set (LinearMap.range f) :=
      (fun g => ⟨f (1 ⊗ₜ (g : Nn)),
        ⟨1 ⊗ₜ (g : Nn), rfl⟩⟩) '' s
    refine ⟨gs, hs_count.image _, ?_⟩
    rw [eq_top_iff]
    rintro ⟨_, y, rfl⟩ -
    induction y using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero]
      exact (Quotient.mk_eq_zero (span S gs)).mp rfl
    | tmul a m =>
      have ha : f (a ⊗ₜ[R] m) = a • f (1 ⊗ₜ[R] m) := by
        change LinearMap.baseChange S Nn.subtype (a ⊗ₜ[R] m) =
          a • LinearMap.baseChange S Nn.subtype (1 ⊗ₜ[R] m)
        simp only [baseChange_tmul, subtype_apply]
        rw [TensorProduct.smul_tmul']
        simp only [_root_.smul_eq_mul, mul_one]

      suffices hmem : (⟨f (1 ⊗ₜ[R] m), ⟨1 ⊗ₜ m, rfl⟩⟩ :
          LinearMap.range f) ∈ span S gs by
        have : (⟨f (a ⊗ₜ[R] m), ⟨a ⊗ₜ m, rfl⟩⟩ :
            LinearMap.range f) =
            a • ⟨f (1 ⊗ₜ[R] m), ⟨1 ⊗ₜ m, rfl⟩⟩ := by
          ext; exact ha
        rw [this]
        exact Submodule.smul_mem _ a hmem

      have hm : m ∈ span R s := by rw [hs_span]; trivial
      refine Submodule.span_induction
        (p := fun (m : Nn) _ =>
          ⟨f (1 ⊗ₜ[R] m), ⟨1 ⊗ₜ m, rfl⟩⟩ ∈ span S gs)
        ?_ ?_ ?_ ?_ hm
      · exact fun g hg => Submodule.subset_span ⟨g, hg, rfl⟩
      · simp only [TensorProduct.tmul_zero, map_zero]
        exact (Quotient.mk_eq_zero (span S gs)).mp rfl
      · intro x y _ _ hx hy
        change ⟨f (1 ⊗ₜ[R] (x + y)), _⟩ ∈ span S gs
        have heq : f (1 ⊗ₜ[R] (x + y)) =
            f (1 ⊗ₜ[R] x) + f (1 ⊗ₜ[R] y) := by
            rw [TensorProduct.tmul_add, map_add]
        simp only [heq]
        exact add_mem hx hy
      · intro r x _ hx
        have heq : f (1 ⊗ₜ[R] (r • x)) =
            algebraMap R S r • f (1 ⊗ₜ[R] x) := by
          rw [TensorProduct.tmul_smul]
          simp [f, LinearMap.baseChange_tmul, Algebra.smul_def,
            TensorProduct.smul_tmul']
        simp only [heq]
        exact Submodule.smul_mem _ _ hx
    | add x y hx hy =>
      simp only [map_add]
      exact add_mem hx hy

have countable_biSup_cg :
      ∀ {ι' : Type w} (J : Set ι')
        (sub : ι' → Submodule S (TensorProduct R S M)),
        J.Countable →
        (∀ i ∈ J, (sub i).IsCountablyGenerated) →
        (⨆ i ∈ J, sub i).IsCountablyGenerated := by
    intro ι' J sub hJ hcg
    choose s hs_count hs_span using hcg
    let bigset : Set (TensorProduct R S M) :=
      ⋃ (i : ι') (_ : i ∈ J), (sub i).subtype '' s i ‹_›
    have hbig : bigset.Countable :=
      hJ.biUnion (fun i hi => (hs_count i hi).image _)
    refine ⟨Subtype.val ⁻¹' bigset,
      hbig.preimage Subtype.val_injective, ?_⟩
    have : span S bigset = ⨆ i ∈ J, sub i := by
      simp_rw [bigset, Submodule.span_iUnion₂,
        Submodule.span_image, hs_span,
        Submodule.map_top, Submodule.range_subtype]
    exact this ▸ Submodule.span_span_coe_preimage

have countable_iSup_cg_R :
      ∀ (sub : ℕ → Submodule R M),
        (∀ n, (sub n).IsCountablyGenerated) →
        (⨆ n, sub n).IsCountablyGenerated := by
    intro sub hcg
    choose s hs_count hs_span using hcg
    let bigset : Set M := ⋃ n, (sub n).subtype '' s n
    have hbig : bigset.Countable :=
      Set.countable_iUnion (fun n =>
        (hs_count n).image _)
    refine ⟨Subtype.val ⁻¹' bigset,
      hbig.preimage Subtype.val_injective, ?_⟩
    have : span R bigset = ⨆ n, sub n := by
      rw [show bigset = ⋃ n, (sub n).subtype '' s n
        from rfl]
      simp_rw [Submodule.span_iUnion,
        Submodule.span_image, hs_span,
        Submodule.map_top, Submodule.range_subtype]
    exact this ▸ Submodule.span_span_coe_preimage


-- Build Nseq : ℕ → Submodule R M by induction: at each step, use lemma_cg to extend
-- the current stage so that the sup of the direct summands indexed by the support of
-- the base-changed image is covered at the next stage.
have h_build : ∃ (Nseq : ℕ → Submodule R M),
    Nseq 0 = N
    ∧ (∀ n, (Nseq n).IsCountablyGenerated)
    ∧ (∀ n, N ≤ Nseq n)
    ∧ (∀ n, Nseq n ≤ Nseq (n + 1))
    ∧ (∀ n, (⨆ i ∈ support (LinearMap.range
        (LinearMap.baseChange S (Nseq n).subtype)),
          fam i)
      ≤ LinearMap.range
        (LinearMap.baseChange S
          (Nseq (n + 1)).subtype)) := by

  have step : ∀ (Nn : Submodule R M),
      Nn.IsCountablyGenerated →
      ∃ P : Submodule R M, P.IsCountablyGenerated ∧
        (⨆ i ∈ support (LinearMap.range
          (LinearMap.baseChange S Nn.subtype)), fam i)
        ≤ LinearMap.range
          (LinearMap.baseChange S (Nn ⊔ P).subtype) := by
    intro Nn hNncg
    set Q := ⨆ i ∈ support (LinearMap.range
      (LinearMap.baseChange S Nn.subtype)), fam i
    have hQcg : Q.IsCountablyGenerated := by
      have hrange_cg := range_baseChange_cg Nn hNncg
      have hJ_count := support_countable _ hrange_cg
      exact countable_biSup_cg _ fam hJ_count (fun i _ => h_count_fam i)

    obtain ⟨P, hPcg, hQP⟩ := lemma_cg Q hQcg
    exact ⟨P, hPcg, hQP.trans (by
      have hle : P ≤ Nn ⊔ P := le_sup_right
      calc LinearMap.range
            (LinearMap.baseChange S P.subtype)
          = LinearMap.range
              (LinearMap.baseChange S
                ((Nn ⊔ P).subtype.comp
                  (Submodule.inclusion hle))) := by
            congr 1
        _ = LinearMap.range
              ((LinearMap.baseChange S
                  (Nn ⊔ P).subtype).comp
                (LinearMap.baseChange S
                  (Submodule.inclusion hle))) := by
            rw [← LinearMap.baseChange_comp]
        _ ≤ LinearMap.range
              (LinearMap.baseChange S
                (Nn ⊔ P).subtype) :=
            LinearMap.range_comp_le_range _ _)⟩

  have sup_cg : ∀ (A B : Submodule R M),
      A.IsCountablyGenerated → B.IsCountablyGenerated →
      (A ⊔ B).IsCountablyGenerated := by
    intro A B ⟨s1, s1count, s1gen⟩ ⟨t, tcount, tgen⟩
    let s1' : Set M := A.subtype '' s1
    let t' : Set M := B.subtype '' t
    refine ⟨Subtype.val ⁻¹' (s1' ∪ t'), ?_, ?_⟩
    · exact Countable.preimage
        ((s1count.image _).union (tcount.image _))
        Subtype.val_injective
    · have h1 : span R s1' = A := by
        simp only [s1']
        rw [Submodule.span_image, s1gen, Submodule.map_top,
          Submodule.range_subtype]
      have h2 : span R t' = B := by
        simp only [t']
        rw [Submodule.span_image,  tgen, Submodule.map_top,
          Submodule.range_subtype]
      have : span R (s1' ∪ t') = A ⊔ B := by
        rw [Submodule.span_union, h1, h2]
      rw [← this]
      exact Submodule.span_span_coe_preimage

  let data : ℕ → {Nn : Submodule R M //
      Nn.IsCountablyGenerated ∧ N ≤ Nn} :=
    Nat.rec
      ⟨N, hN, le_rfl⟩
      (fun _ prev =>
        let Nn := prev.val
        let hNncg := prev.property.1
        let hNle := prev.property.2
        let P := (step Nn hNncg).choose
        let hP := (step Nn hNncg).choose_spec
        ⟨Nn ⊔ P,
         sup_cg Nn P hNncg hP.1,
         hNle.trans le_sup_left⟩)

  let Nseq : ℕ → Submodule R M :=
    fun n => (data n).val

  refine ⟨Nseq, rfl,
    fun n => (data n).property.1,
    fun n => (data n).property.2, ?_, ?_⟩
  · intro n
    change (data n).val ≤ (data (n + 1)).val
    change (data n).val ≤ (data n).val ⊔
      (step (data n).val (data n).property.1).choose
    exact le_sup_left


  · intro n
    change (⨆ i ∈ support (LinearMap.range
        (LinearMap.baseChange S (data n).val.subtype)),
          fam i) ≤
      LinearMap.range
        (LinearMap.baseChange S (data (n + 1)).val.subtype)
    simp only [data]
    exact (step (data n).val (data n).property.1).choose_spec.2


obtain ⟨Nseq, hN0, hNcg, hNle, hNmono, hNstep⟩ := h_build

-- The colimit N' = ⨆ n, Nseq n and the index set I' = ⋃ n, support(range(bc(Nseq n))).
let N' := ⨆ n, Nseq n
use N'

have N'Count : N'.IsCountablyGenerated := countable_iSup_cg_R Nseq hNcg

use N'Count

have N'Cont : N ≤ N' := by
  calc N = Nseq 0 := hN0.symm
    _ ≤ ⨆ n, Nseq n := le_iSup Nseq 0
use N'Cont

let Iseq : ℕ → Set ι := fun n =>
  support (LinearMap.range
    (LinearMap.baseChange S (Nseq n).subtype))

let I' : Set ι := ⋃ n, Iseq n
use I'

-- h1: range(S ⊗[R] N') ≤ ⨆ i ∈ I', fam i.
-- Each pure tensor s ⊗ m with m ∈ N' lies in Nseq k for some k (by directedness),
-- giving it index in Iseq k ⊆ I'.
have h1 :
    LinearMap.range
      (LinearMap.baseChange S N'.subtype) ≤
      ⨆ i ∈ I', fam i := by
  have hrange_union :
      LinearMap.range
        (LinearMap.baseChange S N'.subtype) ≤
        ⨆ n, LinearMap.range
          (LinearMap.baseChange S
            (Nseq n).subtype) := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    induction y using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero]
      exact zero_mem _
    | tmul s m =>
      have hNseq_mono : Monotone Nseq :=
        monotone_nat_of_le_succ hNmono
      have hm : (m : M) ∈ ⨆ n, Nseq n :=
        m.property
      have hdir : Directed (· ≤ ·) Nseq :=
        Monotone.directed_le hNseq_mono
      have ⟨k, hk⟩ : ∃ k, (m : M) ∈ Nseq k :=
        (Submodule.mem_iSup_of_directed Nseq hdir).mp hm
      apply Submodule.mem_iSup_of_mem k
      exact ⟨s ⊗ₜ ⟨(m : M), hk⟩,
        by simp [LinearMap.baseChange_tmul]⟩    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  refine hrange_union.trans ?_
  refine iSup_le ?_
  intro n
  refine (support_le _).trans ?_
  apply iSup₂_mono'
  intro i hi
  exact ⟨i, Set.mem_iUnion.mpr ⟨n, hi⟩, le_rfl⟩

-- h2: ⨆ i ∈ I', fam i ≤ range(S ⊗[R] N').
-- Each summand fam i with i ∈ Iseq n is covered at stage n+1 by hNstep.
have h2 :
    ⨆ i ∈ I', fam i ≤
      LinearMap.range
        (LinearMap.baseChange S N'.subtype) := by
  change (⨆ i ∈ ⋃ n, Iseq n, fam i) ≤ _
  have hunion :
      (⨆ i ∈ ⋃ n, Iseq n, fam i) =
        ⨆ n, ⨆ i ∈ Iseq n, fam i := by
    refine le_antisymm ?_ ?_
    · refine iSup₂_le ?_
      intro i hi
      rcases hi with ⟨n, hin⟩
      rcases hin with ⟨⟨k, rfl⟩, hik⟩
      exact le_iSup_of_le k
        (le_iSup_of_le i
          (le_iSup_of_le hik le_rfl))
    · refine iSup_le ?_
      intro n
      refine iSup₂_le ?_
      intro i hi
      have hi' : i ∈ ⋃ n, Iseq n :=
        Set.mem_iUnion.mpr ⟨n, hi⟩
      exact le_iSup_of_le i
        (le_iSup_of_le hi' le_rfl)
  rw [hunion]
  refine iSup_le ?_
  intro n
  calc ⨆ i ∈ Iseq n, fam i
      ≤ LinearMap.range
          (LinearMap.baseChange S
            (Nseq (n + 1)).subtype) :=
        hNstep n
    _ ≤ LinearMap.range
          (LinearMap.baseChange S N'.subtype) := by
        have hle : Nseq (n + 1) ≤ N' :=
          le_iSup Nseq (n + 1)
        calc LinearMap.range
              (LinearMap.baseChange S
                (Nseq (n + 1)).subtype)
            = LinearMap.range
                (LinearMap.baseChange S
                  (N'.subtype.comp
                    (Submodule.inclusion hle))) := by
              congr 1
          _ = LinearMap.range
                ((LinearMap.baseChange S
                    N'.subtype).comp
                  (LinearMap.baseChange S
                    (Submodule.inclusion hle))) := by
              rw [← LinearMap.baseChange_comp]
          _ ≤ LinearMap.range
                (LinearMap.baseChange S
                  N'.subtype) :=
              LinearMap.range_comp_le_range _ _

exact le_antisymm h1 h2


/-- The quotient of an internal direct sum ⨁ᵢ Qᵢ by a partial sub-direct-sum ⨆ i ∈ J, Qᵢ
is again an internal direct sum, indexed by the complement Jᶜ, and each summand is
isomorphic to the corresponding Qᵢ.

This is used in the transfinite devissage to identify the quotient of successive stages
of the filtration. -/
lemma quotient_dirsum_complement
    {S : Type*} [CommRing S]
    {M : Type*} [AddCommGroup M] [Module S M]
    {I : Type*} [DecidableEq I]
    {Q : I → Submodule S M}
    (hQ : DirectSum.IsInternal Q)
    (hcg : ∀ i, (Q i).IsCountablyGenerated)
    (J : Set I) :
    let := ⨆ i ∈ J, Q i
    ∃ (fam : ↥Jᶜ → Submodule S (M ⧸ (⨆ i ∈ J, Q i))),
      DirectSum.IsInternal fam ∧
      (∀ (j : ↥Jᶜ), (fam j).IsCountablyGenerated ∧
        Nonempty (Q (↑j) ≃ₗ[S] fam j)) ∧
      ∀ j, fam j = (Q (↑j)).map (⨆ i ∈ J, Q i).mkQ := by
  intro QJ
  let fam : ↥Jᶜ → Submodule S (M ⧸ QJ) :=
    fun j => (Q (↑j)).map QJ.mkQ
  have hind : iSupIndep Q := hQ.submodule_iSupIndep
  -- mkQ is injective on Q j for j ∉ J since Q j ∩ QJ = ⊥ by independence.
  have hinj : ∀ j : ↥Jᶜ, Function.Injective (QJ.mkQ.domRestrict (Q (↑j))) := by
    intro ⟨j, hj⟩
    rw [LinearMap.ker_eq_bot.symm, Submodule.eq_bot_iff]
    intro ⟨x, hxQ⟩ hker
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hker
    have hdisj := hind.disjoint_biSup (y := J) hj
    rw [Submodule.disjoint_def] at hdisj
    exact Subtype.ext (hdisj x hxQ hker)
  have hequiv : ∀ j : ↥Jᶜ, Nonempty (Q (↑j) ≃ₗ[S] fam j) := by
    intro j
    exact ⟨LinearEquiv.ofBijective
      ((QJ.mkQ.domRestrict (Q (↑j))).codRestrict (fam j) (by
        intro ⟨x, hx⟩; exact ⟨x, hx, rfl⟩))
      ⟨by
        intro a b hab
        exact hinj j (congr_arg Subtype.val hab),
       by
        intro ⟨y, x, hx, hxy⟩
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩⟩
  refine ⟨fam, ?_, fun j => ⟨?_, hequiv j⟩, fun j => rfl⟩
  · -- IsInternal fam: independence and spanning.
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · rw [iSupIndep_def]
      intro ⟨j, hj⟩
      rw [Submodule.disjoint_def]
      intro x hx_fam hx_rest
      have hmap : ⨆ (k : ↥Jᶜ) (_ : k ≠ ⟨j, hj⟩), fam k =
          (⨆ (k : ↥Jᶜ) (_ : k ≠ ⟨j, hj⟩), Q ↑k).map QJ.mkQ := by
        simp only [fam, ← Submodule.map_iSup]
      obtain ⟨m, hm, rfl⟩ := hx_fam
      rw [hmap] at hx_rest
      obtain ⟨m', hm', hmm'⟩ := hx_rest
      have hdiff : m - m' ∈ QJ := by
        have h : m - m' ∈ LinearMap.ker QJ.mkQ := by
          rw [LinearMap.mem_ker]
          rw [map_sub, sub_eq_zero]
          exact hmm'.symm
        rwa [Submodule.ker_mkQ] at h
      have hm_in : m ∈ ⨆ (i : I) (_ : i ≠ j), Q i := by
        have heq : m = (m - m') + m' := by abel
        rw [heq]
        apply Submodule.add_mem
        · have hle1 : QJ ≤ ⨆ (i : I) (_ : i ≠ j), Q i := by
            apply iSup₂_le
            intro i hi
            have hij : i ≠ j := fun h => hj (h ▸ hi)
            calc Q i = ⨆ (_ : i ≠ j), Q i := by rw [iSup_pos hij]
              _ ≤ ⨆ (i : I) (_ : i ≠ j), Q i := le_iSup (fun i => ⨆ (_ : i ≠ j), Q i) i
          exact hle1 hdiff
        · have hle2 : (⨆ (k : ↥Jᶜ) (_ : k ≠ ⟨j, hj⟩), Q ↑k) ≤ ⨆ (i : I) (_ : i ≠ j), Q i := by
            apply iSup₂_le
            intro ⟨k, hk⟩ hne
            have hkj : k ≠ j := fun h => hne (Subtype.ext h)
            calc Q k = ⨆ (_ : k ≠ j), Q k := by rw [iSup_pos hkj]
              _ ≤ ⨆ (i : I) (_ : i ≠ j), Q i := le_iSup (fun i => ⨆ (_ : i ≠ j), Q i) k
          exact hle2 hm'

      have hdisj := (iSupIndep_def.mp hind) j
      rw [Submodule.disjoint_def] at hdisj
      have := hdisj m hm hm_in
      simp only [this, mkQ_apply, Quotient.mk_zero]
    · rw [eq_top_iff]
      intro x _
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective QJ x
      have hm : m ∈ ⨆ i, Q i := hQ.submodule_iSup_eq_top ▸ Submodule.mem_top
      have : ⨆ i, Q i = (⨆ i ∈ J, Q i) ⊔ (⨆ i ∈ Jᶜ, Q i) := by
        rw [← iSup_union, Set.union_compl_self]
        simp only [Set.mem_univ, iSup_pos]
      rw [this] at hm
      rw [Submodule.mem_sup] at hm
      obtain ⟨a, ha, b, hb, hab⟩ := hm
      have ha_zero : Submodule.Quotient.mk (p := QJ) a = 0 := by
        rw [Submodule.Quotient.mk_eq_zero]
        exact ha
      rw [← hab]
      rw [show Submodule.Quotient.mk (a + b) = QJ.mkQ (a + b) from rfl,
          map_add, show QJ.mkQ a = Submodule.Quotient.mk a from rfl, ha_zero, zero_add]

      have hfam_eq : ⨆ j : ↥Jᶜ, fam j = (⨆ i ∈ Jᶜ, Q i).map QJ.mkQ := by
        simp only [fam, ← Submodule.map_iSup, iSup_subtype']

      rw [hfam_eq]
      exact Submodule.mem_map_of_mem hb
  · -- Countable generation of fam j: transferred from Q j via the linear equivalence.
    obtain ⟨s, hs_count, hs_span⟩ := hcg j
    rw[IsCountablyGenerated]
    obtain ⟨e⟩ := hequiv j
    let t : Set ↥(fam j) := e '' s
    refine ⟨t, hs_count.image _, ?_⟩
    rw [eq_top_iff]
    intro x _
    have hx : e.symm x ∈ span S s := by rw [hs_span]; exact mem_top
    rw [← e.apply_symm_apply x]
    exact Submodule.span_image e.toLinearMap ▸ Submodule.mem_map_of_mem hx


/-- For a flat R-algebra S and an R-submodule Pβ of P, there is a natural S-linear
isomorphism

  S ⊗[R] (P ⧸ Pβ)  ≃ₗ[S]  (S ⊗[R] P) ⧸ image(S ⊗[R] Pβ → S ⊗[R] P).

This is a standard consequence of flatness: the functor S ⊗[R] - preserves the short
exact sequence 0 → Pβ → P → P/Pβ → 0. It is used throughout to translate between
quotients of R-modules and quotients of their base changes. -/
noncomputable def baseChange_quotient_equiv
    {R : Type u} {S : Type u} {P : Type u}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    [AddCommGroup P] [Module R P]
    (Pβ : Submodule R P) :
    TensorProduct R S (P ⧸ Pβ) ≃ₗ[S]
    (TensorProduct R S P) ⧸ (LinearMap.range (LinearMap.baseChange S Pβ.subtype)) := by
  let f := LinearMap.baseChange S Pβ.subtype
  let g := LinearMap.baseChange S Pβ.mkQ

  have g_surj : Function.Surjective g := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero g⟩
    | tmul s q =>
      obtain ⟨p, rfl⟩ := mkQ_surjective Pβ q
      exact ⟨s ⊗ₜ p, by simp [g, LinearMap.baseChange_tmul]⟩
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add g a b⟩

  have ker_eq : LinearMap.ker g = LinearMap.range f := by
    have exact_orig : Function.Exact Pβ.subtype Pβ.mkQ := by
      rw[Function.Exact]
      simp only [mkQ_apply, Quotient.mk_eq_zero, coe_subtype, Subtype.range_coe_subtype,
        SetLike.setOf_mem_eq, SetLike.mem_coe, implies_true]
    have exact_tensor := Module.Flat.lTensor_exact S exact_orig
    rw [LinearMap.exact_iff] at exact_tensor
    have lTensor_eq_baseChange_mkQ : ∀ x, (Pβ.mkQ.lTensor S) x
      = (LinearMap.baseChange S Pβ.mkQ) x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul s p => simp [LinearMap.lTensor_tmul, LinearMap.baseChange_tmul]
      | add x y hx hy => simp [map_add, hx, hy]
    have lTensor_eq_baseChange_sub : ∀ x, (Pβ.subtype.lTensor S) x
      = (LinearMap.baseChange S Pβ.subtype) x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul s p => simp [LinearMap.lTensor_tmul, LinearMap.baseChange_tmul]
      | add x y hx hy => simp [map_add, hx, hy]
    ext x
    constructor
    · intro hx
      have : x ∈ LinearMap.ker (Pβ.mkQ.lTensor S) := by
        rw [LinearMap.mem_ker, lTensor_eq_baseChange_mkQ]
        exact LinearMap.mem_ker.mp hx
      rw [exact_tensor] at this
      obtain ⟨y, hy⟩ := this
      exact ⟨y, by rw [← lTensor_eq_baseChange_sub, hy]⟩
    · rintro ⟨y, rfl⟩
      rw [LinearMap.mem_ker, ← lTensor_eq_baseChange_mkQ, ← lTensor_eq_baseChange_sub]
      have : (Pβ.subtype.lTensor S) y ∈ LinearMap.range (Pβ.subtype.lTensor S) := ⟨y, rfl⟩
      rw [← exact_tensor] at this
      exact LinearMap.mem_ker.mp this

  exact (LinearMap.quotKerEquivOfSurjective g g_surj).symm.trans
    (Submodule.quotEquivOfEq _ _ ker_eq)


/-- If e : M ≃ₗ[R] N and fam is an internally direct family in N, then the preimages
under e form an internally direct family in M. This is used to transport internal direct
sum structures along linear equivalences. -/
lemma DirectSum.IsInternal.of_equiv
    {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    {ι : Type*} [DecidableEq ι]
    (e : M ≃ₗ[R] N)
    (fam : ι → Submodule R N)
    (hint : DirectSum.IsInternal fam) :
    DirectSum.IsInternal
      (fun i => (fam i).map e.symm.toLinearMap) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    have hind := hint.submodule_iSupIndep
    rw [iSupIndep_def] at hind
    intro i
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx1
    rw [show (⨆ j, ⨆ (_ : j ≠ i), Submodule.map e.symm.toLinearMap (fam j)) =
      Submodule.map e.symm.toLinearMap (⨆ j, ⨆ (_ : j ≠ i), fam j) by
      simp [Submodule.map_iSup]] at hx2
    obtain ⟨z, hz, hxz⟩ := Submodule.mem_map.mp hx2
    have hyz : y = z := e.symm.injective hxz.symm
    have : y = 0 := by
      have hind_i := hind i
      rw [Submodule.disjoint_def] at hind_i
      exact hind_i y hy (hyz ▸ hz)
    rw [this, map_zero]
  · simp only [← Submodule.map_iSup, hint.submodule_iSup_eq_top,
      Submodule.map_top, LinearMap.range_eq_top]
    exact e.symm.surjective


/-- The image of a countably generated submodule under a linear map is countably generated. -/
lemma Submodule.IsCountablyGenerated.map {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (p : Submodule R M)
    (hcg : p.IsCountablyGenerated) :
    (p.map f).IsCountablyGenerated := by
  obtain ⟨s, hs_count, hs_span⟩ := hcg
  have h1 : Submodule.span R (p.subtype '' s) = p := by
    rw [Submodule.span_image, hs_span, Submodule.map_top, Submodule.range_subtype]
  have h2 : p.map f = Submodule.span R (f '' (p.subtype '' s)) := by
    rw [← Submodule.map_span, h1]
  rw [h2]
  exact ⟨Subtype.val ⁻¹' (f '' (p.subtype '' s)),
    (hs_count.image p.subtype |>.image f).preimage Subtype.val_injective,
    Submodule.span_span_coe_preimage⟩


/-- A key lift lemma for the transfinite induction in the proof of Theorem I.

Given:
  * An internal direct sum S ⊗[R] P = ⨁ᵢ Qᵢ with each Qᵢ countably generated,
  * An R-submodule Pβ ≤ P with base-changed image ⨆ i ∈ Iβ, Qᵢ,
  * An element x ∈ P,

there exists an R-submodule P' ≥ Pβ containing x, a finite set J' ⊆ Iβᶜ of new
indices, and a countably generated quotient P'/Pβ, such that the base-changed image
of P' equals ⨆ i ∈ Iβ ∪ J', Qᵢ.

This lemma is the inductive step of the Kaplansky filtration constructed in the proof
of proj_faithfully_flat: it extends the current stage by one element while maintaining
the bijective correspondence between R-submodules of P and sub-direct-sums of S ⊗[R] P. -/
lemma countably_generated_lift
    {R : Type u} {S : Type u} {P : Type u}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    [AddCommGroup P] [Module R P]
    {I : Type*} [DecidableEq I]
    {Q : I → Submodule S (TensorProduct R S P)}
    (dirSumSRP : DirectSum.IsInternal Q)
    (countGen : ∀ i, (Q i).IsCountablyGenerated)
    (Pβ : Submodule R P) (Iβ : Set I)
    (hβds : LinearMap.range (LinearMap.baseChange S Pβ.subtype) = ⨆ i ∈ Iβ, Q i)
    (x : P) :
    ∃ (P' : Submodule R P) (J' : Set I),
      (P'.map Pβ.mkQ).IsCountablyGenerated ∧
      Pβ ≤ P' ∧
      x ∈ P' ∧
      J' ⊆ Iβᶜ ∧
      LinearMap.range (LinearMap.baseChange S P'.subtype) = ⨆ i ∈ (Iβ ∪ J'), Q i := by
  -- Step 1: Apply quotient_dirsum_complement to get a decomposition of S ⊗ (P/Pβ).
  set R_Pβ := LinearMap.range (LinearMap.baseChange S Pβ.subtype) with R_Pβ_def
  let eQ := baseChange_quotient_equiv (S := S) Pβ
  have eQ_def : eQ = baseChange_quotient_equiv (S := S) Pβ := rfl


  have hcomm : ∀ y : TensorProduct R S P,
        R_Pβ.mkQ y = eQ (LinearMap.baseChange S Pβ.mkQ y) := by
    intro y
    rw [eQ_def]
    unfold baseChange_quotient_equiv
    simp only [mkQ_apply, LinearEquiv.trans_apply, quotKerEquivOfSurjective_symm_apply,
      quotEquivOfEq_mk]

  have quotientDecomp : ∃ (Q' : (Iβᶜ : Set I) → Submodule S (TensorProduct R S (P ⧸ Pβ))),
        DirectSum.IsInternal Q' ∧
        (∀ j, (Q' j).IsCountablyGenerated) ∧
        (∀ j, (Q' j).map eQ.toLinearMap = (Q j.val).map R_Pβ.mkQ) := by
      let eS' : TensorProduct R S (P ⧸ Pβ) ≃ₗ[S]
          (TensorProduct R S P) ⧸ (⨆ i ∈ Iβ, Q i) :=
        eQ.trans (Submodule.quotEquivOfEq _ _ hβds)
      obtain ⟨fam', hint, hcg, hfam'_def⟩ := quotient_dirsum_complement dirSumSRP countGen Iβ
      refine ⟨fun j => (fam' j).map eS'.symm.toLinearMap,
        DirectSum.IsInternal.of_equiv eS' fam' hint,
        fun j => Submodule.IsCountablyGenerated.map eS'.symm.toLinearMap (fam' j) (hcg j).1,
        fun j => ?_⟩
      rw [← Submodule.map_comp]
      have hfam' : fam' j = (Q j.val).map (⨆ i ∈ Iβ, Q i).mkQ := hfam'_def j
      rw [hfam', ← Submodule.map_comp]
      congr 1
      ext y
      simp [eS', Submodule.quotEquivOfEq]
      rfl


  obtain ⟨Q', dirSumQ', countGenQ', hQ'_map⟩ := quotientDecomp

  -- Step 2: Form the cyclic submodule spanned by the image x̄ of x in P/Pβ.
  let xbar := Submodule.Quotient.mk (p := Pβ) x
  let N₀ : Submodule R (P ⧸ Pβ) := Submodule.span R {xbar}

  have hN₀cg : N₀.IsCountablyGenerated := by
    exact ⟨Subtype.val ⁻¹' {xbar},
      (Set.countable_singleton xbar).preimage Subtype.val_injective,
      Submodule.span_span_coe_preimage⟩

  -- Step 3: Apply count_gen_sum_im to P/Pβ with decomposition Q' and submodule N₀,
  -- to get a countably generated N' ⊇ N₀ with range(S ⊗ N') = ⨆ j ∈ J', Q' j.
  obtain ⟨N', hN'cg, hN₀_le, J'sub, hN'ds⟩ :=
    count_gen_sum_im (ι := (Iβᶜ : Set I)) Q' dirSumQ' countGenQ' N₀ hN₀cg

  -- Step 4: Lift N' ⊆ P/Pβ back to P' = comap(mkQ, N').
  let P' := N'.comap Pβ.mkQ

  have hPβ_le : Pβ ≤ P' := by
    intro p hp
    change Pβ.mkQ p ∈ N'
    simp only [mkQ_apply]
    have : Submodule.Quotient.mk (p := Pβ) p = 0 :=
      (Submodule.Quotient.mk_eq_zero Pβ).mpr hp
    rw [this]
    exact N'.zero_mem

  have hx_mem : x ∈ P' := by
    change Pβ.mkQ x ∈ N'
    exact hN₀_le (Submodule.subset_span (Set.mem_singleton xbar))

  -- Step 5: P'.map Pβ.mkQ = N', so countable generation of P'/Pβ follows.
  have hP'cg : (P'.map Pβ.mkQ).IsCountablyGenerated := by
    rw [Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective Pβ) N']
    exact hN'cg
  let J'I : Set I := Subtype.val '' J'sub

  have hJ'I_disj : J'I ⊆ Iβᶜ := by
    rintro i ⟨⟨j, hj⟩, _, rfl⟩
    exact hj


  -- Step 6: Prove the range equation for the base-changed inclusion of P'.
  have hrange : LinearMap.range (LinearMap.baseChange S P'.subtype) =
        ⨆ i ∈ (Iβ ∪ J'I), Q i := by

      have hunion : (⨆ i ∈ (Iβ ∪ J'I), Q i) = (⨆ i ∈ Iβ, Q i) ⊔ (⨆ i ∈ J'I, Q i) := by
        rw [iSup_union]

      rw [hunion, ← hβds]


      set R_P' := LinearMap.range (LinearMap.baseChange S P'.subtype) with R_P'_def
      set C := ⨆ i ∈ J'I, Q i with C_def

      have hP'_map_eq_N' : Submodule.map Pβ.mkQ P' = N' :=
        Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective Pβ) N'

      -- R_Pβ ≤ R_P' because Pβ ≤ P'.
      have h1 : R_Pβ ≤ R_P' := by
        calc R_Pβ = LinearMap.range (LinearMap.baseChange S Pβ.subtype) := rfl
          _ = LinearMap.range (LinearMap.baseChange S
            (P'.subtype.comp (Submodule.inclusion hPβ_le))) := by
              congr 1
          _ = LinearMap.range ((LinearMap.baseChange S P'.subtype).comp
          (LinearMap.baseChange S (Submodule.inclusion hPβ_le))) := by
              rw [← LinearMap.baseChange_comp]
          _ ≤ LinearMap.range (LinearMap.baseChange S P'.subtype) :=
            LinearMap.range_comp_le_range _ _


      -- Disjointness of ⨆ Iβ Qi and C = ⨆ J'I Qi, since J'I ⊆ Iβᶜ and
      -- the Qi form a direct sum.
      have component_zero_outside {S' : Set I} (y : TensorProduct R S P)
          (hy : y ∈ ⨆ i ∈ S', Q i) (i : I) (hi : i ∉ S') :
          (LinearEquiv.ofBijective (DirectSum.coeLinearMap Q) dirSumSRP).symm y i = 0 := by
        let decomp := LinearEquiv.ofBijective (DirectSum.coeLinearMap Q) dirSumSRP
        rw [show (⨆ i ∈ S', Q i) = ⨆ (j : S'), Q j.val from iSup_subtype'] at hy
        refine Submodule.iSup_induction (fun j : S' => Q j.val)
          (motive := fun y => decomp.symm y i = 0) hy ?_ ?_ ?_
        · intro ⟨j, hj⟩ x hx
          simp only at hx
          have hne : j ≠ i := fun h => hi (h ▸ hj)
          exact dirSumSRP.ofBijective_coeLinearMap_of_mem_ne hne hx
        · simp [map_zero, DirectSum.zero_apply]
        · intro a b ha hb
          simp [map_add, DirectSum.add_apply, ha, hb]

      have h2 : Disjoint (⨆ i ∈ Iβ, Q i) (⨆ i ∈ J'I, Q i) := by
          rw [_root_.disjoint_iff, eq_bot_iff]
          intro x hx
          rw [Submodule.mem_inf] at hx
          obtain ⟨hx1, hx2⟩ := hx
          have hzero : ∀ i,
          ((LinearEquiv.ofBijective (DirectSum.coeLinearMap Q) dirSumSRP).symm x) i = 0 := by
            intro i
            by_cases hi : i ∈ Iβ
            · exact component_zero_outside x hx2 i (fun h => (hJ'I_disj h) hi)
            · exact component_zero_outside x hx1 i hi
          have : (LinearEquiv.ofBijective (DirectSum.coeLinearMap Q) dirSumSRP).symm x = 0 := by
            ext i
            simp [hzero i]
          have : x = 0 := by
            rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap Q) dirSumSRP).apply_symm_apply x,
                this, map_zero]
          rw [this]; exact Submodule.zero_mem _

      -- The quotient images match: R_P' modulo R_Pβ equals C modulo R_Pβ.
      -- This is the core calculation connecting the R-module filtration to the S-decomposition.
      have h3 : R_P'.map R_Pβ.mkQ = C.map R_Pβ.mkQ := by

        let φ : P' →ₗ[R] N' := Pβ.mkQ.restrict (fun p hp => hp)

        have hfactor : Pβ.mkQ.comp P'.subtype = N'.subtype.comp φ := by
          ext; simp [φ, LinearMap.restrict]

        have hφ_surj : Function.Surjective φ := by
          intro ⟨n, hn⟩
          have : n ∈ Submodule.map Pβ.mkQ P' := hP'_map_eq_N' ▸ hn
          obtain ⟨p, hp, rfl⟩ := this
          exact ⟨⟨p, hp⟩, rfl⟩

        have hbc_φ_surj : Function.Surjective (LinearMap.baseChange S φ) := by
          exact LinearMap.lTensor_surjective S hφ_surj

        have hchain_val : ∀ w : S ⊗[R] P',
            R_Pβ.mkQ ((LinearMap.baseChange S P'.subtype) w) =
            eQ ((LinearMap.baseChange S N'.subtype) ((LinearMap.baseChange S φ) w)) := by
          intro w
          induction w using TensorProduct.induction_on with
          | zero => simp
          | tmul s p =>
            rw [LinearMap.baseChange_tmul, hcomm, LinearMap.baseChange_tmul,
                LinearMap.baseChange_tmul]
            congr 1
          | add x y hx hy => simp [map_add, hx, hy]

        have step1 : R_P'.map R_Pβ.mkQ =
            (LinearMap.range (LinearMap.baseChange S N'.subtype)).map eQ.toLinearMap := by
          ext z
          simp only [Submodule.mem_map, LinearMap.mem_range]
          constructor
          · rintro ⟨y, ⟨w, rfl⟩, rfl⟩
            exact ⟨(LinearMap.baseChange S N'.subtype) ((LinearMap.baseChange S φ) w),
                  ⟨(LinearMap.baseChange S φ) w, rfl⟩, (hchain_val w).symm⟩
          · rintro ⟨y, ⟨w, rfl⟩, rfl⟩
            obtain ⟨v, rfl⟩ := hbc_φ_surj w
            exact ⟨(LinearMap.baseChange S P'.subtype) v, ⟨v, rfl⟩, hchain_val v⟩

        have step2 : C.map R_Pβ.mkQ =
            (⨆ j ∈ J'sub, Q' j).map eQ.toLinearMap := by
            have hQ'_map_local : ∀ j ∈ J'sub, Submodule.map
              eQ.toLinearMap (Q' j) = Submodule.map R_Pβ.mkQ (Q j.val) := by
              intro j _
              have := hQ'_map j
              convert this using 2

            rw [Submodule.map_iSup, Submodule.map_iSup]
            simp only [Submodule.map_iSup]
            conv_lhs => simp only [J'I, iSup_image]
            congr 1; ext1 ⟨j, hj⟩; congr 1; ext1 hjsub
            exact (hQ'_map_local ⟨j, hj⟩ hjsub).symm


        rw [step1, hN'ds, step2]

      -- Abstract pushout argument: B = A ⊔ D when A ≤ B, A ∩ D = ⊥, and B/A = D/A.
      have key : ∀ (A B D : Submodule S (TensorProduct R S P)),
          A ≤ B → Disjoint A D → B.map A.mkQ = D.map A.mkQ → B = A ⊔ D := by
        intro A B D hAB hDisj hMap
        apply le_antisymm
        · intro b hb
          have hbq : A.mkQ b ∈ B.map A.mkQ := Submodule.mem_map_of_mem hb
          rw [hMap] at hbq
          obtain ⟨d, hd, hdq⟩ := hbq
          have hab : b - d ∈ A := by
            rw [← Submodule.ker_mkQ A]
            rw [LinearMap.mem_ker]
            rw [map_sub, hdq]
            simp only [mkQ_apply, _root_.sub_self]
          exact Submodule.mem_sup.mpr ⟨b - d, hab, d, hd, by simp only [sub_add_cancel]⟩
        · apply sup_le hAB
          intro d hd
          have hdq : A.mkQ d ∈ D.map A.mkQ := Submodule.mem_map_of_mem hd
          rw [← hMap] at hdq
          obtain ⟨b, hb, hbq⟩ := hdq
          have hdb : d - b ∈ A := by
            rw [← Submodule.ker_mkQ A]
            rw [LinearMap.mem_ker]
            rw [map_sub, hbq]
            simp only [mkQ_apply, _root_.sub_self]
          have hd_in_B : d = (d - b) + b := by simp only [sub_add_cancel]
          rw [hd_in_B]
          exact B.add_mem (hAB hdb) hb


      exact key R_Pβ R_P' C h1 (hβds ▸ h2) h3


  exact ⟨P', J'I, hP'cg, hPβ_le, hx_mem, hJ'I_disj, hrange⟩


/-- The base-changed range of an indexed supremum of submodules equals the supremum of the
individual base-changed ranges:
  range(S ⊗[R] (⨆ᵢ Nᵢ) → S ⊗[R] M) = ⨆ᵢ range(S ⊗[R] Nᵢ → S ⊗[R] M). -/
lemma baseChange_range_iSup {R S P : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup P] [Module R P]
    {ι : Type*} (N : ι → Submodule R P) :
    LinearMap.range (LinearMap.baseChange S (⨆ i, N i).subtype) =
    ⨆ i, LinearMap.range (LinearMap.baseChange S (N i).subtype) := by
  apply le_antisymm
  · rintro z ⟨w, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul s p =>
      simp only [LinearMap.baseChange_tmul, Submodule.subtype_apply]
      refine Submodule.iSup_induction N
              (motive := fun p' =>
                s ⊗ₜ[R] p' ∈ ⨆ i, LinearMap.range (LinearMap.baseChange S (N i).subtype))
              p.property ?_ ?_ ?_
      · intro i x hx
        apply Submodule.mem_iSup_of_mem i
        exact ⟨s ⊗ₜ ⟨x, hx⟩, by simp [LinearMap.baseChange_tmul]⟩
      · simp [TensorProduct.tmul_zero]
      · intro a b ha hb
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ ha hb
    | add x y hx hy => simp only [map_add]; exact Submodule.add_mem _ hx hy
  · apply iSup_le
    intro i
    rintro z ⟨w, rfl⟩
    have hle : N i ≤ ⨆ i, N i := le_iSup N i
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul s p =>
      exact ⟨s ⊗ₜ ⟨(p : P), hle p.property⟩, by simp [LinearMap.baseChange_tmul]⟩
    | add x y hx hy => simp only [map_add]; exact Submodule.add_mem _ hx hy


/-- A variant of baseChange_range_iSup for doubly indexed suprema with a predicate:
range(S ⊗[R] (⨆ᵢ (hᵢ : pᵢ), N i hᵢ) → S ⊗[R] M) = ⨆ᵢ (hᵢ : pᵢ), range(S ⊗[R] N i hᵢ → S ⊗[R] M). -/
lemma baseChange_range_biSup' {R S P : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup P] [Module R P]
    {ι : Type*} {p : ι → Prop} (N : (i : ι) → p i → Submodule R P) :
    LinearMap.range (LinearMap.baseChange S (⨆ (i : ι) (hi : p i), N i hi).subtype) =
    ⨆ (i : ι) (hi : p i), LinearMap.range (LinearMap.baseChange S (N i hi).subtype) := by
  apply le_antisymm
  · rintro z ⟨w, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul s q =>
      simp only [LinearMap.baseChange_tmul, Submodule.subtype_apply]
      have hq := q.property
      refine Submodule.iSup_induction (p := fun i => ⨆ (hi : p i), N i hi)
        (motive := fun q' =>
          s ⊗ₜ[R] q' ∈ ⨆ (i : ι) (hi : p i),
            LinearMap.range (LinearMap.baseChange S (N i hi).subtype))
        hq ?_ ?_ ?_
      · intro i x hx
        refine Submodule.iSup_induction (p := fun (hi : p i) => N i hi)
          (motive := fun x' =>
            s ⊗ₜ[R] x' ∈ ⨆ (i : ι) (hi : p i),
              LinearMap.range (LinearMap.baseChange S (N i hi).subtype))
          hx ?_ ?_ ?_
        · intro hi y hy
          apply mem_iSup_of_mem i
          apply mem_iSup_of_mem hi
          exact ⟨s ⊗ₜ ⟨y, hy⟩, by simp [LinearMap.baseChange_tmul]⟩
        · simp [TensorProduct.tmul_zero]
        · intro a b ha hb
          rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ha hb
      · simp [TensorProduct.tmul_zero]
      · intro a b ha hb
        rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ha hb
    | add x y hx hy => simp only [map_add]; exact Submodule.add_mem _ hx hy
  · apply iSup₂_le
    intro i hi
    rintro z ⟨w, rfl⟩
    have hle : N i hi ≤ ⨆ (i : ι) (hi : p i), N i hi := le_iSup₂ i hi
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul s q =>
      exact ⟨s ⊗ₜ ⟨(q : P), hle q.property⟩, by simp [LinearMap.baseChange_tmul]⟩
    | add x y hx hy => simp only [map_add]; exact Submodule.add_mem _ hx hy



/-- If M has a countable generating set over R, then S ⊗[R] M has a countable
generating set over S. The generating set is taken to be the image of the R-generators
under the map m ↦ 1 ⊗ m. -/
lemma countably_generated_baseChange {R S M : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M]
    (h : ∃ s : Set M, s.Countable ∧ span R s = ⊤) :
    ∃ t : Set (TensorProduct R S M), t.Countable ∧ span S t = ⊤ := by
  obtain ⟨s, hs_count, hs_span⟩ := h
  refine ⟨(fun x => (1 : S) ⊗ₜ[R] x) '' s, hs_count.image _, ?_⟩
  rw [eq_top_iff]
  intro x _
  induction x using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul a m =>
    suffices h : (1 : S) ⊗ₜ[R] m ∈ span S ((fun x => (1 : S) ⊗ₜ[R] x) '' s) by
      have h1 : a ⊗ₜ[R] m = a • (1 : S) ⊗ₜ[R] m := by
        rw [TensorProduct.smul_tmul']
        simp only [_root_.smul_eq_mul, mul_one]
      rw [h1]
      exact Submodule.smul_mem _ a h
    have hm : m ∈ span R s := by rw [hs_span]; exact Submodule.mem_top
    have h2 : span R ((fun x => (1 : S) ⊗ₜ[R] x) '' s) ≤
        (span S ((fun x => (1 : S) ⊗ₜ[R] x) '' s)).restrictScalars R := by
      apply Submodule.span_le.mpr
      intro x hx
      exact Submodule.subset_span hx
    have h3 : (1 : S) ⊗ₜ[R] m ∈ span R ((fun x => (1 : S) ⊗ₜ[R] x) '' s) := by
      have : Submodule.map (TensorProduct.mk R S M 1) (span R s) ≤
          span R ((fun x => (1 : S) ⊗ₜ[R] x) '' s) := by
        rw [Submodule.map_span]
        simp only [TensorProduct.mk_apply, le_refl]
      exact this ⟨m, hm, rfl⟩
    exact h2 h3
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)



/-- If M = ⨁ᵢ Qᵢ is an internal direct sum decomposition and P is a projective module
which surjects onto M with complement K, then for any subset J of the index set, the
partial sub-direct-sum ⨆ i ∈ J, Qᵢ is projective. The proof uses the complement
decomposition: M = (⨆ i ∈ J, Qᵢ) ⊕ (⨆ i ∈ Jᶜ, Qᵢ), so ⨆ i ∈ J, Qᵢ is a retract
of M, and projectivity descends to retracts. -/
lemma projective_of_biSup_sub
    {S : Type u} [CommRing S]
    {M : Type u} [AddCommGroup M] [Module S M]
    {I : Type*} [DecidableEq I]
    {Q : I → Submodule S M}
    (hint : DirectSum.IsInternal Q)
    (hproj : Module.Projective S M)
    (J : Set I) :
    Module.Projective S (↥(⨆ i ∈ J, Q i)) := by
  have hsup : (⨆ i ∈ J, Q i) ⊔ (⨆ i ∈ Jᶜ, Q i) = ⊤ := by
    rw [← iSup_union, Set.union_compl_self]
    simp only [Set.mem_univ, iSup_pos]
    exact hint.submodule_iSup_eq_top

  have hdisj : Disjoint (⨆ i ∈ J, Q i) (⨆ i ∈ Jᶜ, Q i) := by
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    let decomp := LinearEquiv.ofBijective (DirectSum.coeLinearMap Q) hint
    have hzero : ∀ i, (decomp.symm x) i = 0 := by
      intro i
      by_cases hi : i ∈ J
      · have h_eq : (⨆ i ∈ Jᶜ, Q i) = ⨆ (j : ↥(Jᶜ)), Q j.val := iSup_subtype'
        rw [h_eq] at hx2
        refine Submodule.iSup_induction (motive := fun y => (decomp.symm y) i = 0)
          (fun (j : ↥(Jᶜ)) => Q j.val) hx2 ?_ ?_ ?_
        · intro ⟨j, hj⟩ y hy
          have hne : j ≠ i := fun h => hj (h ▸ hi)
          exact hint.ofBijective_coeLinearMap_of_mem_ne hne hy
        · simp [map_zero, DirectSum.zero_apply]
        · intro a b ha hb
          simp [map_add, DirectSum.add_apply, ha, hb]
      · have h_eq : (⨆ i ∈ J, Q i) = ⨆ (j : ↥J), Q j.val := iSup_subtype'
        rw [h_eq] at hx1
        refine Submodule.iSup_induction (motive := fun y => (decomp.symm y) i = 0)
          (fun (j : ↥J) => Q j.val) hx1 ?_ ?_ ?_
        · intro ⟨j, hj⟩ y hy
          have hne : j ≠ i := fun h => hi (h ▸ hj)
          exact hint.ofBijective_coeLinearMap_of_mem_ne hne hy
        · simp [map_zero, DirectSum.zero_apply]
        · intro a b ha hb
          simp [map_add, DirectSum.add_apply, ha, hb]
    have hx_zero : decomp.symm x = 0 := by ext i; exact congrArg Subtype.val (hzero i)
    rw [← decomp.apply_symm_apply x, hx_zero, map_zero]

  have hcompl : IsCompl (⨆ i ∈ J, Q i) (⨆ i ∈ Jᶜ, Q i) := ⟨hdisj, codisjoint_iff.mpr hsup⟩
  let proj : M →ₗ[S] ↥(⨆ i ∈ J, Q i) :=
    Submodule.linearProjOfIsCompl _ _ hcompl
  have hsplit : proj.comp (⨆ i ∈ J, Q i).subtype = LinearMap.id := by
    ext ⟨x, hx⟩
    simp only [proj]
    simp only [mem_compl_iff, coe_comp, coe_subtype, Function.comp_apply,
      coe_linearProjOfIsCompl_apply, id_coe, id_eq, IsCompl.projection_eq_self_iff]
    exact hx
  exact Module.Projective.of_split (⨆ i ∈ J, Q i).subtype proj hsplit

/-- If B is a projective S-module, A ≤ B, and A has a complement in the ambient module,
then B/A (identified with the comap of A inside B) is projective. The complement of A
inside B gives a direct summand B = (A ∩ B) ⊕ C', and the quotient B/A ≅ C' inherits
projectivity. -/
lemma projective_quotient_of_direct_summand
    {S : Type u} [CommRing S]
    {M : Type u} [AddCommGroup M] [Module S M]
    (A B : Submodule S M)
    (hAB : A ≤ B)
    (hBproj : Module.Projective S B)
    (hAcompl : ∃ C : Submodule S M, IsCompl A C) :
    Module.Projective S (B ⧸ Submodule.comap B.subtype A) := by
  obtain ⟨C, hAC⟩ := hAcompl
  let AB := Submodule.comap B.subtype A
  let CB := Submodule.comap B.subtype C
  have hcompl_B : IsCompl AB CB := by
    constructor
    · rw [Submodule.disjoint_def]
      intro ⟨x, hxB⟩ hxAB hxCB
      simp only [AB, CB, Submodule.mem_comap, Submodule.subtype_apply] at hxAB hxCB
      have := hAC.1
      rw [Submodule.disjoint_def] at this
      exact Subtype.ext (this x hxAB hxCB)
    · rw [codisjoint_iff, eq_top_iff]
      intro ⟨x, hxB⟩ _
      have hx_top : x ∈ A ⊔ C := by
        rw [hAC.2.eq_top]; exact Submodule.mem_top
      rw [Submodule.mem_sup] at hx_top
      obtain ⟨a, ha, c, hc, hac⟩ := hx_top
      rw [Submodule.mem_sup]
      have haB : a ∈ B := hAB ha
      have hcB : c ∈ B := by
        have : x = a + c := by exact id (Eq.symm hac)
        have : c = x - a := by exact eq_sub_of_add_eq' hac
        rw [this]
        exact B.sub_mem hxB haB
      refine ⟨⟨a, haB⟩, ?_, ⟨c, hcB⟩, ?_, ?_⟩
      · simp only [AB, Submodule.mem_comap, Submodule.subtype_apply]
        exact ha
      · simp only [CB, Submodule.mem_comap, Submodule.subtype_apply]
        exact hc
      · ext
        simp only [Submodule.coe_add]
        exact hac

  let e := Submodule.quotientEquivOfIsCompl AB CB hcompl_B
  have hCBproj : Module.Projective S CB := by
    apply Module.Projective.of_split CB.subtype
      (Submodule.linearProjOfIsCompl CB AB hcompl_B.symm)
    ext ⟨x, hx⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply]
    have h1 := Submodule.linearProjOfIsCompl_apply_left hcompl_B.symm ⟨x, hx⟩
    have h2 : (CB.linearProjOfIsCompl AB hcompl_B.symm) x = ⟨x, hx⟩ := h1
    simp only [h2, Submodule.coe_mk]
  exact Module.Projective.of_equiv e.symm



set_option maxHeartbeats 800000 in -- ordinal induction
/-- The main theorem: faithfully flat descent of projectivity (Theorem I of the paper).

Let R → S be a faithfully flat map of commutative rings and P an R-module.
Then P is projective over R if and only if S ⊗[R] P is projective over S.

Forward direction: proj_base_change (base change preserves projectivity, no faithful
flatness needed).

Backward direction (the hard part): We assume S ⊗[R] P is projective over S and
construct a Kaplansky filtration 0 = P₀ ⊆ P₁ ⊆ ⋯ ⊆ Pᵧ = P indexed by ordinals up
to γ = succ(type(P)), such that each successive quotient Pₐ₊₁/Pₐ is countably
generated and projective over R. The strategy is:

  1. Write S ⊗[R] P = ⨁ᵢ∈I Qᵢ (direct sum of countably generated S-modules), using
     the fact that S ⊗[R] P is projective (proj_is_dirSumCountable).
  2. Build the filtration by transfinite recursion: at each successor step, use a
     well-ordering of P to pick the least element not yet in Pₐ, and apply
     countably_generated_lift to extend Pₐ to Pₐ₊₁ by a countably generated piece
     while tracking the bijection {R-submodules of P} ↔ {sub-direct-sums of S ⊗[R] P}.
  3. At limit steps, take the union.
  4. Each quotient Pₐ₊₁/Pₐ is shown projective using proj_countable_faithfully_flat,
     using the isomorphism S ⊗[R] (Pₐ₊₁/Pₐ) ≅ (⨁ᵢ∈Iₐ' Qᵢ) / (⨁ᵢ∈Iₐ Qᵢ) for
     appropriate index sets Iₐ ⊆ Iₐ', which is a direct summand of S ⊗[R] P and hence
     projective over S.
  5. The filtration constitutes a Kaplansky devissage for P (isInternal_of_filtration),
     expressing P as a direct sum of countably generated projective modules
     (projective_if_interalsum_is). -/
theorem proj_faithfully_flat {R : Type u} {S : Type u} {P : Type u}
[CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S] [AddCommGroup P] [Module R P] :
Module.Projective R P ↔ Module.Projective S (TensorProduct R S P) := by
constructor
· apply proj_base_change
· intro projSRP
  have SRPDirSum : IsDirectSumOfCountablyGenerated S (TensorProduct R S P) := by
    exact proj_is_dirSumCountable (R:=S)
      (P:= (TensorProduct R S P)) (pproj :=projSRP)
  -- S⊗_R P = ⊕ i∈I, Q i, with each Q i countably generated.
  rcases SRPDirSum.out with ⟨I, dec, Q, dirSumSRP, countGen⟩

  -- Set up the ordinal bounds for the transfinite induction.
  -- γ = succ(type(P)) ensures the filtration covers all of P.
  let T := Ordinal.type (WellOrderingRel (α := P))
  let γ := Order.succ T

  have ⟨Psub, hPsub_zero, hPsub_top, hPsub_mono,
      hPsub_limit, hPsub_dirsum, hPsub_quot⟩ :
      ∃ (Psub : Ordinal → Submodule R P),
        Psub 0 = ⊥ ∧
        Psub γ = ⊤ ∧
        (∀ α β, α ≤ β → Psub α ≤ Psub β) ∧
        (∀ o, Order.IsSuccLimit o → Psub o = ⨆ (β : Ordinal) (_ : β < o), Psub β) ∧
        (∀ α, α ≤ γ → ∃ (I' : Set I),
          LinearMap.range (LinearMap.baseChange S (Psub α).subtype) = ⨆ i ∈ I', Q i) ∧
        (∀ α, α < γ →
          let Qq := (Psub (Order.succ α)).map (Psub α).mkQ
          Module.Projective R Qq ∧ Module.IsCountablyGenerated R Qq)
      := by
      classical

      have quotient_dirsum : ∀ (J : Set I),
        ∃ (fam' : (Jᶜ : Set I) → Submodule S ((S ⊗[R] P) ⧸ (⨆ i ∈ J, Q i))),
          DirectSum.IsInternal fam' ∧
          ∀ j, (fam' j).IsCountablyGenerated := by
          intro J
          obtain ⟨fam', hint, hcg, _⟩ := quotient_dirsum_complement dirSumSRP countGen J
          exact ⟨fam', hint, fun j => (hcg j).1⟩

      -- Each state in the transfinite recursion stores the current submodule and the
      -- corresponding index set, together with the range equation as a proof.
      let State := { p : (Submodule R P) × (Set I) //
        LinearMap.range (LinearMap.baseChange S p.1.subtype) = ⨆ i ∈ p.2, Q i }

      -- The successor step of the transfinite recursion: pick the least element of P
      -- not yet in Pβ (via the well-ordering of P) and apply countably_generated_lift.
      let step : Ordinal → State := fun α =>
        Ordinal.limitRecOn α
          -- base case: Psub 0 = ⊥, indexed by the empty set
          ⟨(⊥, ∅), by
          simp only [mem_empty_iff_false, not_false_eq_true, iSup_neg, iSup_bot]
          rw [@range_eq_bot]
          rw [← @baseChange_zero]
          simp only [baseChange_zero]
          ext x
          simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
              LinearMap.coe_restrictScalars, baseChange_tmul, subtype_apply, restrictScalars_zero,
              LinearMap.zero_apply, Module.FaithfullyFlat.one_tmul_eq_zero_iff,
              ZeroMemClass.coe_eq_zero]
          exact eq_zero_of_bot_submodule x⟩
          -- successor step
        (fun β ⟨⟨Pβ, Iβ⟩, hβds⟩ => by
          simp only at hβds
          by_cases htop : Pβ = ⊤
          · exact ⟨(Pβ, Iβ), hβds⟩
          · let bad := {x : P | x ∉ Pβ}
            have hbad : bad.Nonempty := by
              by_contra h
              push_neg at h
              apply htop
              rw [eq_top_iff]
              intro x _
              by_contra hx
              exact Set.eq_empty_iff_forall_notMem.mp h x hx
            let x := WellFounded.min (IsWellFounded.wf (r := WellOrderingRel)) bad hbad
            have hx : x ∉ Pβ :=
              WellFounded.min_mem (IsWellFounded.wf (r := WellOrderingRel)) bad hbad
            have h := countably_generated_lift dirSumSRP countGen Pβ Iβ hβds x
            let P' := h.choose
            let J' := h.choose_spec.choose
            have hrange := h.choose_spec.choose_spec.2.2.2.2
            exact ⟨(P', Iβ ∪ J'), hrange⟩)
          -- limit step: take the union over all previous stages
          (fun o ho ih =>
            ⟨(⨆ (β : Ordinal) (hβ : β < o), (ih β hβ).1.1,
              ⋃ (β : Ordinal) (hβ : β < o), (ih β hβ).1.2), by
              have rhs_eq : (⨆ i ∈ (⋃ (β : Ordinal) (hβ : β < o), (ih β hβ).1.2), Q i) =
                  ⨆ (β : Ordinal) (hβ : β < o), ⨆ i ∈ (ih β hβ).1.2, Q i := by
                simp only [Set.mem_iUnion]
                apply le_antisymm
                · apply iSup₂_le
                  intro i ⟨b, hb, hi⟩
                  calc Q i = ⨆ (_ : i ∈ (ih b hb).1.2), Q i := by rw [iSup_pos hi]
                    _ ≤ ⨆ i ∈ (ih b hb).1.2, Q i :=
                        le_iSup (fun i => ⨆ (_ : i ∈ (ih b hb).1.2), Q i) i
                    _ = ⨆ (_ : b < o), ⨆ i ∈ (ih b _).1.2, Q i := by rw [iSup_pos hb]
                    _ ≤ ⨆ β, ⨆ (_ : β < o), ⨆ i ∈ (ih β _).1.2, Q i :=
                        le_iSup (fun β => ⨆ (_ : β < o), ⨆ i ∈ (ih β _).1.2, Q i) b
                · apply iSup₂_le
                  intro b hb
                  apply iSup₂_le
                  intro i hi
                  calc Q i = ⨆ (_ : ∃ β, ∃ (hβ : β < o), i ∈ (ih β hβ).1.2), Q i :=
                        by rw [iSup_pos ⟨b, hb, hi⟩]
                    _ ≤ ⨆ i, ⨆ (_ : ∃ β, ∃ (hβ : β < o), i ∈ (ih β hβ).1.2), Q i :=
                        le_iSup (fun i => ⨆ (_ : ∃ β, ∃ (hβ : β < o), i ∈ (ih β hβ).1.2), Q i) i

              have ih_eq : ∀ β (hβ : β < o),
                  ⨆ i ∈ (ih β hβ).1.2, Q i =
                  LinearMap.range (LinearMap.baseChange S (ih β hβ).1.1.subtype) := by
                intro β hβ
                exact (ih β hβ).2.symm

              have lhs_eq : LinearMap.range (LinearMap.baseChange S
                  (⨆ (β : Ordinal) (hβ : β < o), (ih β hβ).1.1).subtype) =
                  ⨆ (β : Ordinal) (hβ : β < o),
                    LinearMap.range (LinearMap.baseChange S (ih β hβ).1.1.subtype) :=
                baseChange_range_biSup' (fun β hβ => (ih β hβ).1.1)

              rw [rhs_eq]
              simp_rw [ih_eq]
              exact lhs_eq
              ⟩)

      let Psub : Ordinal → Submodule R P := fun α => (step α).1.1

      -- Monotonicity: Psub α ≤ Psub (succ α) follows from the successor step.
      have hPsub_succ_le : ∀ α, Psub α ≤ Psub (Order.succ α) := by
        intro α
        change (step α).1.1 ≤ (step (Order.succ α)).1.1
        simp only [step, Ordinal.limitRecOn_succ]
        split
        case h_1 Pα Iα hαds heq =>
          have hPα : (step α).1.1 = Pα := by
            have := congr_arg (fun s => s.1.1) heq
            simpa [step] using this
          rw [hPα]
          split
          · exact le_refl _
          · rename_i htop
            simp only
            exact (countably_generated_lift dirSumSRP countGen Pα Iα
              (by simpa using hαds) _).choose_spec.choose_spec.2.1

      -- Strict monotonicity: Psub α < Psub (succ α) when Psub α ≠ ⊤.
      have hPsub_succ_lt : ∀ α, Psub α ≠ ⊤ → Psub α < Psub (Order.succ α) := by
        intro α hne
        apply lt_of_le_of_ne (hPsub_succ_le α)
        change (step α).1.1 ≠ (step (Order.succ α)).1.1
        simp only [step, Ordinal.limitRecOn_succ]
        split
        case h_1 Pα Iα hαds heq =>
          have hPα : (step α).1.1 = Pα := by
            have := congr_arg (fun s => s.1.1) heq
            simpa [step] using this
          simp only [heq]
          have hne' : Pα ≠ ⊤ := hPα ▸ hne
          simp only [dif_neg hne']
          intro heq'
          have hαds' : LinearMap.range (LinearMap.baseChange S Pα.subtype) = ⨆ i ∈ Iα, Q i :=
            by simpa using hαds
          have hbad : {x : P | x ∉ Pα}.Nonempty := by
            by_contra h
            push_neg at h
            exact hne' (eq_top_iff.mpr (fun x _ => by
              by_contra hx; exact Set.eq_empty_iff_forall_notMem.mp h x hx))
          have hx_notin := WellFounded.min_mem
            (IsWellFounded.wf (r := WellOrderingRel)) {x | x ∉ Pα} hbad
          have hx_in := (countably_generated_lift dirSumSRP countGen Pα Iα hαds'
            (WellFounded.min (IsWellFounded.wf (r := WellOrderingRel))
              {x | x ∉ Pα} hbad)).choose_spec.choose_spec.2.2.1
          have hx_in' : WellFounded.min (IsWellFounded.wf (r := WellOrderingRel))
              {x | x ∉ Pα} hbad ∈ Pα := by
            have : (countably_generated_lift dirSumSRP countGen Pα Iα hαds'
              (WellFounded.min (IsWellFounded.wf (r := WellOrderingRel))
              {x | x ∉ Pα} hbad)).choose = Pα :=
              heq'.symm
            rw [this] at hx_in
            exact hx_in
          exact absurd hx_in' hx_notin


      have bad_nonempty : ∀ α, Psub α ≠ ⊤ → {x | x ∉ Psub α}.Nonempty := by
        intro α hne_top
        by_contra h
        rw [Set.not_nonempty_iff_eq_empty] at h
        exact hne_top (eq_top_iff.mpr (fun x _ => by_contra (fun hx =>
          (Set.eq_empty_iff_forall_notMem.mp h x) hx)))

      have hmin_in_succ : ∀ α, (h : Psub α ≠ ⊤) →
          (IsWellFounded.wf (r := WellOrderingRel)).min {x | x ∉ Psub α} (bad_nonempty α h) ∈
          Psub (Order.succ α) := by
        intro α hne_top'
        change _ ∈ (step (Order.succ α)).1.1
        simp only [step, Ordinal.limitRecOn_succ]
        split
        case h_1 Pα Iα hαds heq =>
          have hPα : (step α).1.1 = Pα := by
            have := congr_arg (fun s => s.1.1) heq
            simpa [step] using this
          have hPα' : Psub α = Pα := hPα
          have hne' : Pα ≠ ⊤ := hPα' ▸ hne_top'
          simp only [dif_neg hne']
          have hαds' : LinearMap.range (LinearMap.baseChange S Pα.subtype) = ⨆ i ∈ Iα, Q i :=
            by simpa using hαds
          rw [hPα'] at hne_top'
          have hbad' : {x | x ∉ Pα}.Nonempty := by
            have := bad_nonempty α (hPα' ▸ hne')
            rwa [hPα'] at this
          simp only [hPα']
          exact (countably_generated_lift dirSumSRP countGen Pα Iα hαds'
            ((IsWellFounded.wf (r := WellOrderingRel)).min
            {x | x ∉ Pα} hbad')).choose_spec.choose_spec.2.2.1


      -- Global monotonicity: derived from strict monotonicity and limit continuity.
      have hPsub_mono : ∀ α β, α ≤ β → Psub α ≤ Psub β := by
        intro α β
        induction β using Ordinal.induction with
        | h β ih =>
          intro hαβ
          by_cases h1 : α = β
          · rw [h1]
          · have hlt : α < β := lt_of_le_of_ne hαβ h1
            by_cases h2 : Order.IsSuccLimit β
            · change (step α).1.1 ≤ (step β).1.1
              simp only [step, Ordinal.limitRecOn_limit _ _ _ _ h2]
              exact le_iSup₂ (f := fun b (hb : b < β) => (step b).1.1) α hlt
            · have hne : β ≠ 0 := by
                intro h; rw [h] at hlt; exact not_lt.mpr (zero_le α) hlt
              rw [Ordinal.isSuccLimit_iff] at h2
              push_neg at h2
              have h2 := h2 hne
              rw [Order.not_isSuccPrelimit_iff] at h2
              obtain ⟨β', _, rfl⟩ := h2
              by_cases h3 : α ≤ β'
              · exact (ih β' (Order.lt_succ β') h3).trans (hPsub_succ_le β')
              · push_neg at h3
                exact absurd (le_antisymm hαβ (Order.succ_le_of_lt h3)) h1

      -- Each successive quotient is countably generated.
      have succ_cg : ∀ α, Psub α ≠ ⊤ →
          (Submodule.map (Psub α).mkQ (Psub (Order.succ α))).IsCountablyGenerated := by
        intro α htop
        have : (Submodule.map ((step α).1.1).mkQ
        ((step (Order.succ α)).1.1)).IsCountablyGenerated := by
          simp only [step, Ordinal.limitRecOn_succ]
          split
          case h_1 Pα Iα hαds heq =>
            have hPα : (step α).1.1 = Pα := by
              have := congr_arg (fun s => s.1.1) heq; simpa [step] using this
            have hne : Pα ≠ ⊤ := hPα ▸ htop
            simp only [dif_neg hne]
            rw [hPα]
            exact (countably_generated_lift dirSumSRP countGen Pα Iα
              (by simpa using hαds)
              (WellFounded.min (IsWellFounded.wf
              (r := WellOrderingRel)) _ _)).choose_spec.choose_spec.1
        exact this


      refine ⟨Psub, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- Psub 0 = ⊥
        simp only [Psub, step, limitRecOn_zero]
      · -- Psub γ = ⊤: if not, there is an element of P with ordinal rank < T still outside,
        -- but the well-ordering argument places each element of P inside Psub (succ αₚ)
        -- where αₚ = typein(p), and succ αₚ ≤ γ.
        by_contra hne
        have hne_T : Psub T ≠ ⊤ := fun h =>
          hne (eq_top_iff.mpr (h ▸ hPsub_succ_le T))
        have hall : ∀ α, α ≤ T → Psub α ≠ ⊤ := by
          intro α hα h
          exact hne_T (eq_top_iff.mpr (h ▸ hPsub_mono α T hα))

        suffices key : ∀ p : P, p ∈ Psub γ from
          hne (eq_top_iff.mpr (fun p _ => key p))

        intro p
        let αp := Ordinal.typein WellOrderingRel p
        have hαp_lt_T : αp < T := Ordinal.typein_lt_type WellOrderingRel p
        have hαp_lt_γ : αp < γ := hαp_lt_T.trans (Order.lt_succ T)
        have hsucc_le_γ : Order.succ αp ≤ γ :=
          Order.succ_le_of_lt (hαp_lt_T.trans (Order.lt_succ T))
        suffices p ∈ Psub (Order.succ αp) from hPsub_mono _ _ hsucc_le_γ this

        -- Inner induction: every p with typein(p) = α lies in Psub (succ α).
        -- The key point is that p is the WellOrderingRel-minimum element not yet
        -- in Psub α, so it gets picked up at stage succ α by hmin_in_succ.
        have claim : ∀ α, α < T → ∀ q : P, Ordinal.typein WellOrderingRel q = α →
            q ∈ Psub (Order.succ α) := by
          intro α hα
          induction α using Ordinal.induction with
          | h α ih =>
            intro q hq
            by_cases hmem : q ∈ Psub α
            · exact hPsub_succ_le α hmem
            · have prior : ∀ r : P, Ordinal.typein WellOrderingRel r < α → r ∈ Psub α := by
                intro r hr
                have hr_lt_T : Ordinal.typein WellOrderingRel r < T := hr.trans hα
                have := ih (Ordinal.typein WellOrderingRel r) hr hr_lt_T r rfl
                exact hPsub_mono _ _ (Order.succ_le_of_lt hr) this
              have hbad : {x : P | x ∉ Psub α}.Nonempty := ⟨q, hmem⟩
              have q_is_min : q = WellFounded.min (IsWellFounded.wf
                (r := WellOrderingRel)) {x | x ∉ Psub α} hbad := by
                set m := WellFounded.min (IsWellFounded.wf
                (r := WellOrderingRel)) {x | x ∉ Psub α} hbad
                have hm_mem : m ∉ Psub α :=
                  WellFounded.min_mem (IsWellFounded.wf
                  (r := WellOrderingRel)) {x | x ∉ Psub α} hbad
                have hm_min : ∀ r, WellOrderingRel r m → r ∈ Psub α :=
                  fun r hr => by_contra (fun hr' => WellFounded.not_lt_min (IsWellFounded.wf
                  (r := WellOrderingRel)) _ hbad hr' hr)
                have hq_min : ∀ r, WellOrderingRel r q → r ∈ Psub α := by
                  intro r hr
                  apply prior
                  rw [← hq]
                  exact Ordinal.typein_lt_typein WellOrderingRel |>.mpr hr
                rcases trichotomous_of WellOrderingRel q m with h | h | h
                · exact absurd (hm_min q h) hmem
                · exact h
                · exact absurd (hq_min m h) hm_mem
              rw [q_is_min]
              have : WellFounded.min (IsWellFounded.wf
              (r := WellOrderingRel)) {x | x ∉ Psub α} hbad =
                  WellFounded.min (IsWellFounded.wf (r := WellOrderingRel)) {x | x ∉ Psub α}
                    (bad_nonempty α (hall α hα.le)) := by
                congr 1
              rw [this]
              exact hmin_in_succ α (hall α hα.le)

        exact claim αp hαp_lt_T p rfl



      · exact fun α β a ↦ hPsub_mono α β a
      · intro α hlimit
        change (step α).1.1 = ⨆ β, ⨆ (_ : β < α), (step β).1.1
        simp only [step, Ordinal.limitRecOn_limit _ _ _ _ hlimit]

      · -- Direct sum property: follows directly from the definition of step.
        intro α _
        exact ⟨(step α).1.2, (step α).2⟩
      · -- Quotients are countably generated and projective.
        -- This uses proj_countable_faithfully_flat with the identification
        -- S ⊗[R] (Pα+1/Pα) ≅ (⨆ i ∈ Iα', Qi) / (⨆ i ∈ Iα, Qi) which is a
        -- direct summand of S ⊗[R] P, hence projective over S.
        intro α hα
        have hIα : ∃ Iα, LinearMap.range (LinearMap.baseChange S (Psub α).subtype)
        = ⨆ i ∈ Iα, Q i :=
          ⟨(step α).1.2, (step α).2⟩
        by_cases htop : Psub α = ⊤
        · -- Trivial case: Psub α = ⊤ implies Pα+1 = ⊤ and Qq = ⊥.
          have h1 : Psub (Order.succ α) = ⊤ :=
            eq_top_iff.mpr (htop ▸ hPsub_succ_le α)
          have hQq : Submodule.map (Psub α).mkQ (Psub (Order.succ α)) = ⊥ := by
            rw [h1, htop, Submodule.map_top, Submodule.range_mkQ,
                eq_bot_iff]
            intro x hx
            obtain ⟨p, _, rfl⟩ := hx
            exact Subsingleton.eq_zero x
          rw [hQq]
          refine ⟨inferInstance, ?_⟩
          use ∅
          refine ⟨Set.countable_empty,?_⟩
          simp only [span_empty]
          exact Eq.symm eq_bot_of_subsingleton

        · -- Nontrivial case: apply proj_countable_faithfully_flat.
          have key := succ_cg α htop

          have key2 : Module.Projective R
              (Submodule.map (Psub α).mkQ (Psub (Order.succ α))) := by
            apply proj_countable_faithfully_flat (S := S)
            · -- S ⊗[R] Qq is countably generated.
              exact countably_generated_baseChange key
            · -- S ⊗[R] Qq is projective: it is isomorphic to
              -- (⨆ i ∈ Iα', Qi) / (⨆ i ∈ Iα, Qi), a direct summand of S ⊗[R] P.
              obtain ⟨Iα, hIα_eq⟩ := hIα
              have hIα' : ∃ Iα', LinearMap.range (LinearMap.baseChange S
              (Psub (Order.succ α)).subtype) = ⨆ i ∈ Iα', Q i :=
                ⟨(step (Order.succ α)).1.2, (step (Order.succ α)).2⟩
              obtain ⟨Iα', hIα'_eq⟩ := hIα'
              have hAB : (⨆ i ∈ Iα, Q i) ≤ (⨆ i ∈ Iα', Q i) := by
                rw [← hIα_eq, ← hIα'_eq]
                intro x hx
                obtain ⟨w, rfl⟩ := hx
                have hle : Psub α ≤ Psub (Order.succ α) := hPsub_succ_le α
                induction w using TensorProduct.induction_on with
                | zero => simp only [map_zero, zero_mem]
                | tmul s p =>
                  exact ⟨s ⊗ₜ ⟨(p : P), hle p.property⟩, by simp only [baseChange_tmul,
                    subtype_apply]⟩
                | add x y hx hy =>
                  simp only [map_add]
                  exact Submodule.add_mem _ hx hy
              have hBproj : Module.Projective S ↥(⨆ i ∈ Iα', Q i) :=
                projective_of_biSup_sub dirSumSRP projSRP Iα'
              have hAcompl : ∃ C : Submodule S (TensorProduct R S P),
                  IsCompl (⨆ i ∈ Iα, Q i) C := by
                use ⨆ i ∈ Iαᶜ, Q i
                constructor
                · rw [Submodule.disjoint_def]
                  intro x hx1 hx2
                  let decomp := LinearEquiv.ofBijective (DirectSum.coeLinearMap Q) dirSumSRP
                  have hzero : ∀ i, (decomp.symm x) i = 0 := by
                    intro i
                    by_cases hi : i ∈ Iα
                    · have h_eq : (⨆ i ∈ Iαᶜ, Q i) = ⨆ (j : ↥(Iαᶜ)), Q j.val := iSup_subtype'
                      rw [h_eq] at hx2
                      refine Submodule.iSup_induction (motive := fun y => (decomp.symm y) i = 0)
                        (fun (j : ↥(Iαᶜ)) => Q j.val) hx2 ?_ ?_ ?_
                      · intro ⟨j, hj⟩ y hy
                        have hne : j ≠ i := fun h => hj (h ▸ hi)
                        exact dirSumSRP.ofBijective_coeLinearMap_of_mem_ne hne hy
                      · simp [map_zero, DirectSum.zero_apply]
                      · intro a b ha hb
                        simp [map_add, DirectSum.add_apply, ha, hb]
                    · have h_eq : (⨆ i ∈ Iα, Q i) = ⨆ (j : ↥Iα), Q j.val := iSup_subtype'
                      rw [h_eq] at hx1
                      refine Submodule.iSup_induction (motive := fun y => (decomp.symm y) i = 0)
                        (fun (j : ↥Iα) => Q j.val) hx1 ?_ ?_ ?_
                      · intro ⟨j, hj⟩ y hy
                        have hne : j ≠ i := fun h => hi (h ▸ hj)
                        exact dirSumSRP.ofBijective_coeLinearMap_of_mem_ne hne hy
                      · simp [map_zero, DirectSum.zero_apply]
                      · intro a b ha hb
                        simp [map_add, DirectSum.add_apply, ha, hb]
                  have hx_zero : decomp.symm x = 0 := by ext i; exact congrArg Subtype.val (hzero i)
                  rw [← decomp.apply_symm_apply x, hx_zero, map_zero]
                · rw [codisjoint_iff, eq_top_iff]
                  intro x _
                  rw [← iSup_union, Set.union_compl_self]
                  simp only [Set.mem_univ, iSup_pos]
                  exact dirSumSRP.submodule_iSup_eq_top ▸ Submodule.mem_top

              have hQuotProj : Module.Projective S
                  (↥(⨆ i ∈ Iα', Q i) ⧸
                    Submodule.comap (⨆ i ∈ Iα', Q i).subtype (⨆ i ∈ Iα, Q i)) := by
                exact projective_quotient_of_direct_summand
                  (⨆ i ∈ Iα, Q i) (⨆ i ∈ Iα', Q i) hAB hBproj hAcompl

              -- Build the S-linear isomorphism S ⊗[R] Qq ≃ₗ[S] (⨆ i ∈ Iα', Qi)/(⨆ i ∈ Iα, Qi)
              -- by composing:
              --   S ⊗ Qq  ≅  S ⊗ (Pα' / Kα)  [via Qq ≅ Pα'/Kα]
              --            ≅  (S ⊗ Pα') / range(bc(Kα))  [via flatness]
              --            ≅  (⨆ Iα' Qi) / (comap of ⨆ Iα Qi)  [via step3]
              have hiso : TensorProduct R S
                  ↥((Psub (Order.succ α)).map (Psub α).mkQ) ≃ₗ[S]
                  (↥(⨆ i ∈ Iα', Q i) ⧸
                    Submodule.comap (⨆ i ∈ Iα', Q i).subtype (⨆ i ∈ Iα, Q i)) := by
                let Pα := Psub α
                let Pα' := Psub (Order.succ α)
                let Qq := Pα'.map Pα.mkQ
                let Kα := Submodule.comap Pα'.subtype Pα
                -- Step 1: Qq ≃ₗ[R] Pα' ⧸ Kα (comap quotient isomorphism).
                have hQq_iso : Qq ≃ₗ[R] Pα' ⧸ Kα := by
                  let φ : Pα' →ₗ[R] Qq :=
                    (Pα.mkQ.comp Pα'.subtype).codRestrict Qq (by
                      intro x
                      exact ⟨x.val, x.property, rfl⟩)
                  have hφ_surj : Function.Surjective φ := by
                    intro ⟨y, hy⟩
                    obtain ⟨p, hp, rfl⟩ := hy
                    exact ⟨⟨p, hp⟩, by ext; simp [φ]⟩
                  have hφ_ker : LinearMap.ker φ = Kα := by
                    ext ⟨x, hx⟩
                    simp only [LinearMap.mem_ker, Kα, Submodule.mem_comap, Submodule.subtype_apply]
                    constructor
                    · intro h
                      have : Pα.mkQ x = 0 := by
                        have := congr_arg Subtype.val h
                        simpa [φ] using this
                      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
                    · intro h
                      ext
                      simp only [φ, LinearMap.codRestrict_apply, LinearMap.comp_apply,
                        Submodule.subtype_apply, Submodule.mkQ_apply]
                      exact (Submodule.Quotient.mk_eq_zero Pα).mpr h
                  exact (LinearMap.quotKerEquivOfSurjective φ hφ_surj).symm.trans
                    (Submodule.quotEquivOfEq _ _ hφ_ker)
                let step1 : TensorProduct R S Qq ≃ₗ[S] TensorProduct R S (Pα' ⧸ Kα) :=
                  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) hQq_iso
                -- Step 2: S ⊗ (Pα' ⧸ Kα) ≃ₗ[S] (S ⊗ Pα') ⧸ range(bc(Kα)) by flatness.
                let step2 : TensorProduct R S (Pα' ⧸ Kα) ≃ₗ[S]
                    (TensorProduct R S Pα') ⧸ LinearMap.range (LinearMap.baseChange S Kα.subtype) :=
                  baseChange_quotient_equiv Kα
                -- Step 3: (S ⊗ Pα') ≃ₗ[S] ⨆ i ∈ Iα', Qi via injectivity and hIα'_eq.
                have hPα'_inj : Function.Injective (LinearMap.baseChange S Pα'.subtype) := by
                  have hlTensor : Function.Injective (Pα'.subtype.lTensor S) :=
                    Module.Flat.lTensor_preserves_injective_linearMap Pα'.subtype
                    Subtype.val_injective
                  have heq : ∀ x, (Pα'.subtype.lTensor S) x =
                  (LinearMap.baseChange S Pα'.subtype) x := by
                    intro x
                    induction x using TensorProduct.induction_on with
                    | zero => simp
                    | tmul s p => simp [LinearMap.lTensor_tmul, LinearMap.baseChange_tmul]
                    | add x y hx hy => simp [map_add, hx, hy]
                  intro x y hxy
                  apply hlTensor
                  rw [heq x, heq y, hxy]
                let step3a : TensorProduct R S Pα' ≃ₗ[S]
                    LinearMap.range (LinearMap.baseChange S Pα'.subtype) :=
                  LinearEquiv.ofInjective (LinearMap.baseChange S Pα'.subtype) hPα'_inj
                let step3b : LinearMap.range (LinearMap.baseChange S Pα'.subtype) ≃ₗ[S]
                    ↥(⨆ i ∈ Iα', Q i) :=
                  LinearEquiv.ofEq _ _ hIα'_eq
                let step3 : TensorProduct R S Pα' ≃ₗ[S] ↥(⨆ i ∈ Iα', Q i) :=
                  step3a.trans step3b
                -- Step 4: Identify the image of Kα under base change as the comap of
                -- ⨆ i ∈ Iα, Qi inside ⨆ i ∈ Iα', Qi (via the range equation hIα_eq).
                have hKα_image : Submodule.map step3.toLinearMap
                    (LinearMap.range (LinearMap.baseChange S Kα.subtype)) =
                    Submodule.comap (⨆ i ∈ Iα', Q i).subtype (⨆ i ∈ Iα, Q i) := by
                  ext ⟨x, hx_Iα'⟩
                  simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_comap,
                    Submodule.subtype_apply]
                  have step3_val : ∀ (z : TensorProduct R S Pα'),
                      ((step3 z : ↥(⨆ i ∈ Iα', Q i)) : TensorProduct R S P) =
                      LinearMap.baseChange S Pα'.subtype z := by
                    intro z
                    simp only [LinearEquiv.trans_apply, step3, step3a, step3b]
                    rfl

                  have factor_val : ∀ (w : TensorProduct R S Kα),
                      LinearMap.baseChange S Pα'.subtype (LinearMap.baseChange S Kα.subtype w) =
                      LinearMap.baseChange S Pα.subtype
                        (LinearMap.baseChange S
                          (Submodule.comapSubtypeEquivOfLe (hPsub_succ_le α)).toLinearMap w) := by
                    intro w
                    induction w using TensorProduct.induction_on with
                    | zero => simp
                    | tmul s k =>
                      simp only [LinearMap.baseChange_tmul, Submodule.subtype_apply]
                      congr 1
                    | add x y hx hy => simp [map_add, hx, hy]

                  constructor
                  · rintro ⟨y, ⟨w, rfl⟩, hy⟩
                    have hval := step3_val (LinearMap.baseChange S Kα.subtype w)
                    have hx_eq : x = LinearMap.baseChange
                      S Pα'.subtype (LinearMap.baseChange S Kα.subtype w) := by
                        have := congr_arg Subtype.val hy
                        exact this.symm
                    rw [hx_eq, factor_val]
                    rw [← hIα_eq]
                    exact ⟨_, rfl⟩
                  · intro hx_Iα
                    rw [← hIα_eq] at hx_Iα
                    obtain ⟨w_pα, hw_pα⟩ := hx_Iα
                    let e : Pα ≃ₗ[R] Kα := (Submodule.comapSubtypeEquivOfLe (hPsub_succ_le α)).symm
                    let w_kα := LinearMap.baseChange S e.toLinearMap w_pα
                    refine ⟨LinearMap.baseChange S Kα.subtype w_kα, ⟨w_kα, rfl⟩, ?_⟩
                    apply Subtype.ext
                    change (step3 (LinearMap.baseChange S Kα.subtype w_kα)).val = x
                    rw [step3_val]
                    rw [factor_val]
                    have comp_eq : (Submodule.comapSubtypeEquivOfLe
                      (hPsub_succ_le α)).toLinearMap.comp
                        e.toLinearMap = LinearMap.id := by
                      simp only [LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
                        LinearEquiv.refl_toLinearMap, e]

                    have hcomp : LinearMap.baseChange S
                        (Submodule.comapSubtypeEquivOfLe (hPsub_succ_le α)).toLinearMap
                        (LinearMap.baseChange S e.toLinearMap w_pα) =
                        LinearMap.baseChange S
                        ((Submodule.comapSubtypeEquivOfLe (hPsub_succ_le α)).toLinearMap.comp
                          e.toLinearMap) w_pα := by
                      induction w_pα using TensorProduct.induction_on with
                      | zero => simp only [map_zero, LinearEquiv.comp_coe]
                      | tmul s p =>
                        simp only [baseChange_tmul, LinearEquiv.coe_coe, LinearEquiv.comp_coe,
                          LinearEquiv.trans_apply]
                        rfl
                      | add x y hx hy =>
                        simp only [map_add, LinearMap.baseChange_comp]
                        rfl
                    rw [hcomp, comp_eq, LinearMap.baseChange_id, LinearMap.id_apply]
                    exact hw_pα
                -- Step 5: Combine into the quotient isomorphism.
                let rangeKα : Submodule S (TensorProduct R S Pα') :=
                  LinearMap.range (LinearMap.baseChange S Kα.subtype)
                have hKα_image' : Submodule.map step3.toLinearMap rangeKα =
                    Submodule.comap (⨆ i ∈ Iα', Q i).subtype (⨆ i ∈ Iα, Q i) := hKα_image
                let step5 := Submodule.Quotient.equiv rangeKα
                  (Submodule.comap (⨆ i ∈ Iα', Q i).subtype (⨆ i ∈ Iα, Q i))
                  step3 hKα_image'

                exact step1.trans (step2.trans step5)
              exact Module.Projective.of_equiv hiso.symm

          exact ⟨key2, key⟩

  -- Extract the filtration properties and assemble the Kaplansky devissage.
  have hPsub_succ_le : ∀ α, Psub α ≤ Psub (Order.succ α) := by
    intro α
    apply hPsub_mono
    exact Order.le_succ α

  -- For each α < γ, extract the complement Cα making IsRelativeComplement hold.
  -- The complement comes from splitting the quotient map via projectivity of Qq.
  have hChoose : ∀ (α : Ordinal) (hα : α < γ), ∃ C' : Submodule R P,
        IsRelativeComplement (Psub α) (Psub (Order.succ α)) C' ∧
        C'.IsCountablyGenerated ∧
        Module.Projective R ↥C' := by
      intro α hα
      obtain ⟨hproj, hcg⟩ := hPsub_quot α hα
      let Qq := (Psub (Order.succ α)).map (Psub α).mkQ
      let φ : ↥(Psub (Order.succ α)) →ₗ[R] ↥Qq :=
        ((Psub α).mkQ.comp (Psub (Order.succ α)).subtype).codRestrict Qq
          (fun x => ⟨x.val, x.property, rfl⟩)
      have hφ_surj : Function.Surjective φ := by
        intro ⟨y, hy⟩
        obtain ⟨p, hp, rfl⟩ := hy
        exact ⟨⟨p, hp⟩, by ext; simp [φ]⟩
      -- Since Qq is projective, split φ to get a section s.
      obtain ⟨s, hs⟩ := Module.projective_lifting_property φ LinearMap.id hφ_surj
      let C' : Submodule R P := (LinearMap.range s).map (Psub (Order.succ α)).subtype
      refine ⟨C', ?_, ?_⟩
      · -- IsRelativeComplement
        refine ⟨hPsub_succ_le α, ?_, ?_, ?_⟩
        · exact Submodule.map_le_iff_le_comap.mpr (fun x _ => x.property)
        · rw [_root_.disjoint_iff, eq_bot_iff]
          intro x ⟨hxα, hxC⟩
          obtain ⟨⟨y, hysucc⟩, ⟨q, hq⟩, hxy⟩ := hxC
          simp only [Submodule.subtype_apply] at hxy
          have hφsq : φ (s q) = q := by
            have := congrFun (congrArg DFunLike.coe hs) q
            simpa using this
          have hφ0 : φ ⟨x, hxy ▸ hysucc⟩ = 0 := by
            ext; simp only [φ, LinearMap.codRestrict_apply, LinearMap.comp_apply,
              Submodule.subtype_apply, Submodule.mkQ_apply, ZeroMemClass.coe_zero]
            exact (Submodule.Quotient.mk_eq_zero _).mpr hxα
          have hsq_eq : s q = ⟨x, hxy ▸ hysucc⟩ := by rw [hq]; ext; exact hxy
          rw [hsq_eq] at hφsq; rw [hφ0] at hφsq
          have hq_zero : q = 0 := by rw [← hφsq]
          have : s q = 0 := by rw [hq_zero, map_zero]
          rw [Submodule.mem_bot]
          have := hsq_eq.symm.trans this
          exact congr_arg Subtype.val this
        · apply le_antisymm
          · apply sup_le (hPsub_succ_le α)
            exact Submodule.map_le_iff_le_comap.mpr (fun x _ => x.property)
          · intro x hx
            rw [Submodule.mem_sup]
            let q := φ ⟨x, hx⟩
            let y := (Psub (Order.succ α)).subtype (s q)
            have hy_C : y ∈ C' := ⟨s q, ⟨q, rfl⟩, rfl⟩
            have hφ_eq : φ (s q) = q := by
              have := congrFun (congrArg DFunLike.coe hs) q; simpa using this
            have hx_minus_y : x - y ∈ Psub α := by
              have : (Psub α).mkQ (x - y) = 0 := by
                simp only [map_sub, y, Submodule.subtype_apply]
                have h1 : (Psub α).mkQ x = (φ ⟨x, hx⟩).val := rfl
                have h2 : (Psub α).mkQ ((Psub (Order.succ α)).subtype (s q)) =
                    (φ (s q)).val := rfl
                rw [h1]
                simp only [Submodule.subtype_apply] at h2
                rw [h2, hφ_eq]
                rw [@sub_eq_zero]
              exact (Submodule.Quotient.mk_eq_zero _).mp this
            exact ⟨x - y, hx_minus_y, y, hy_C, by abel⟩
      · -- Countable generation and projectivity of C'.
        obtain ⟨genQq, hgenQq_count, hgenQq_span⟩ := hcg
        let f : ↥Qq → ↥C' := fun q => ⟨(Psub (Order.succ α)).subtype (s q),
          ⟨s q, ⟨q, rfl⟩, rfl⟩⟩
        constructor
        · refine ⟨f '' genQq, hgenQq_count.image f, ?_⟩
          rw [eq_top_iff]
          intro ⟨z, hz⟩ _
          obtain ⟨w, ⟨q, rfl⟩, hwz⟩ := hz
          change ⟨z, _⟩ ∈ span R (f '' genQq)
          convert_to f q ∈ span R (f '' genQq)
          · exact Subtype.ext hwz.symm
          have hq_mem : q ∈ Submodule.span R genQq := hgenQq_span ▸ Submodule.mem_top
          exact Submodule.span_induction
            (fun x hx => Submodule.subset_span ⟨x, hx, rfl⟩)
            (by simp only [f, map_zero]; exact Submodule.zero_mem _)
            (fun a b _ _ ha hb => by simp only [f, map_add]; exact Submodule.add_mem _ ha hb)
            (fun r a _ ha => by simp only [f, map_smul]; exact Submodule.smul_mem _ r ha)
            hq_mem
        · have hs_inj : Function.Injective s :=
            Function.HasLeftInverse.injective ⟨φ, fun q => by
              have := congrFun (congrArg DFunLike.coe hs) q; simpa using this⟩
          let f' : ↥Qq →ₗ[R] ↥C' :=
            ((Psub (Order.succ α)).subtype.comp s).codRestrict C'
              (fun q => ⟨s q, ⟨q, rfl⟩, rfl⟩)
          have hf'_inj : Function.Injective f' := by
            intro a b hab
            have := congr_arg Subtype.val hab
            exact hs_inj (Subtype.ext this)
          have hf'_surj : Function.Surjective f' := by
            intro ⟨z, hz⟩
            obtain ⟨w, ⟨q, rfl⟩, hwz⟩ := hz
            exact ⟨q, by ext; simp only [codRestrict_apply, coe_comp, coe_subtype,
              Function.comp_apply, f'];exact hwz⟩
          let e : ↥Qq ≃ₗ[R] ↥C' :=
            LinearEquiv.ofBijective f' ⟨hf'_inj, hf'_surj⟩
          exact Module.Projective.of_equiv e


  choose C hC hC_cg hC_proj using hChoose
  -- The collection {Cα}α<γ forms an internal direct sum equal to P (Kaplansky devissage).
  have hint := isInternal_of_filtration Psub hPsub_zero hPsub_top hPsub_mono hPsub_limit C hC

  have e : (⨁ (p : {α // α < γ}), ↥(C p.val p.prop)) ≃ₗ[R] P :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap (fun (p : {α // α < γ}) => C p.val p.prop)) hint

  -- P is projective: each Cα is projective and P ≅ ⨁ Cα.
  have : Module.Projective R (⨁ (p : {α // α < γ}), ↥(C p.val p.prop)) := by
    apply Module.instProjectiveDFinsupp

  exact Module.Projective.of_equiv e
