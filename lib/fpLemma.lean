/-
Copyright (c) 2026 Liran Shaul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Liran Shaul

This file is part of the formalization project accompanying the paper:
  "Formalization in Lean of faithfully flat descent of projectivity"
  by Liran Shaul, Charles University in Prague.

We prove that finitely presented R-modules (in the sense of `Module.FinitePresentation`)
are finitely presentable in the categorical sense (i.e., `IsFinitelyPresentable` in the
category `ModuleCat R`). This bridge between the algebraic and categorical notions of
finite presentation is needed in the formalization of the Mittag-Leffler theory, where
the categorical finite presentability of Hom-sets plays a key role.

## Main Results

* `ModuleCat.isFinitelyPresentable_self`: R as a module over itself is finitely presentable.
* `ModuleCat.isFinitelyPresentable_biproduct`: A finite biproduct of finitely presentable
  modules is finitely presentable.
* `ModuleCat.isFinitelyPresentable_free_module`: The finite free module R^n is
  finitely presentable.
* `ModuleCat.isFinitelyPresentable_cokernel`: The cokernel of a map between finitely
  presentable modules is finitely presentable.
* `ModuleCat.instIsFinitelyPresentable`: If `Module.FinitePresentation R P`, then
  `IsFinitelyPresentable (ModuleCat.of R P)`.

## Proof Strategy

1. Show that R as a module over itself is finitely presentable, since Hom(R, -) is
   naturally isomorphic to the forgetful functor, which preserves filtered colimits.
2. Use closure of finitely presentable objects under finite colimits
   (via `CategoryTheory.isCardinalPresentable_of_isColimit`).
3. Any finitely presented module is a cokernel of a map between finite free modules,
   which are finite coproducts of R, and hence finitely presentable by steps 1 and 2.

## References

* `Mathlib.CategoryTheory.Presentable.Limits` for `isCardinalPresentable_of_isColimit`
* `Mathlib.Algebra.Module.FinitePresentation` for `Module.FinitePresentation`
-/

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Presentation.Finite
import Mathlib.CategoryTheory.Presentable.Basic
import Mathlib.CategoryTheory.Presentable.Limits
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Regular

universe u v

open CategoryTheory CategoryTheory.Limits Cardinal

variable {R : Type u} [CommRing R]

namespace ModuleCat

/-- R as a module over itself is finitely presentable in the categorical sense. The key
insight is that Hom(R, M) ≅ M naturally for any R-module M, so the coyoneda functor at R
is naturally isomorphic to the forgetful functor. Since the forgetful functor preserves
filtered colimits, so does Hom(R, -), which is exactly the definition of R being finitely
presentable. -/
instance isFinitelyPresentable_self : IsFinitelyPresentable.{u} (of R R) := by
  haveI : Fact (Cardinal.IsRegular ℵ₀) := ⟨Cardinal.isRegular_aleph0⟩
  constructor
  intro J _ _
  -- Construct the natural isomorphism Hom(R, -) ≅ forgetful functor via the
  -- standard identification of R-linear maps R → M with elements of M.
  have iso : coyoneda.obj (Opposite.op (of R R)) ≅ forget (ModuleCat.{u} R) :=
    NatIso.ofComponents (fun M => Equiv.toIso {
      toFun := fun f => f.hom (1 : R)
      invFun := fun m => ModuleCat.homEquiv.symm ((LinearMap.ringLmapEquivSelf R R M).symm m)
      left_inv := fun f => by
        apply ModuleCat.homEquiv.injective
        simp only [Equiv.apply_symm_apply]
        ext
        simp [LinearMap.ringLmapEquivSelf, homEquiv]
      right_inv := fun m => by simp [LinearMap.ringLmapEquivSelf, ModuleCat.homEquiv]
    })
  haveI : IsFiltered J := isFiltered_of_isCardinalFiltered J ℵ₀
  haveI : PreservesColimitsOfShape J (forget (ModuleCat.{u} R)) :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
  exact preservesColimitsOfShape_of_natIso iso.symm

/-- A finite biproduct of finitely presentable R-modules is finitely presentable.
This follows from the general fact that finitely presentable objects are closed under
finite colimits, applied here to the biproduct as a finite coproduct. -/
instance isFinitelyPresentable_biproduct {n : ℕ} (f : Fin n → ModuleCat.{u} R)
    [inst : ∀ i, IsFinitelyPresentable.{w} (f i)] :
    IsFinitelyPresentable.{w} (⨁ f) := by
  haveI : Fact (Cardinal.IsRegular ℵ₀) := ⟨Cardinal.isRegular_aleph0⟩
  letI : ∀ k : Discrete (Fin n), IsCardinalPresentable.{w} ((Discrete.functor f).obj k) ℵ₀ :=
    fun ⟨i⟩ => inst i
  exact isCardinalPresentable_of_isColimit'.{w} (c := (biproduct.bicone f).toCocone)
    (biproduct.isColimit f) (κ := ℵ₀)
    (hasCardinalLT_of_finite (Arrow (Discrete (Fin n))) ℵ₀ (le_refl ℵ₀))

/-- The finite free module R^n = (Fin n → R) is finitely presentable. This follows
from `isFinitelyPresentable_biproduct` applied to n copies of R, together with the
canonical isomorphism ⨁ (Fin n → R) ≅ (Fin n → R). -/
instance isFinitelyPresentable_free_module (n : ℕ) :
    IsFinitelyPresentable.{u} (of R (Fin n → R)) := by
  haveI : Fact (Cardinal.IsRegular ℵ₀) := ⟨Cardinal.isRegular_aleph0⟩
  haveI : IsFinitelyPresentable.{u} (⨁ (fun (_ : Fin n) => of R R)) :=
    isFinitelyPresentable_biproduct _
  exact isCardinalPresentable_of_iso (biproductIsoPi (fun _ : Fin n => of R R)) ℵ₀

/-- The cokernel of a map between finitely presentable R-modules is finitely presentable.
This uses the general closure of finitely presentable objects under finite colimits,
applied to the coequalizer diagram M ⇉ N realizing the cokernel. -/
instance isFinitelyPresentable_cokernel {M N : ModuleCat.{u} R}
    [IsFinitelyPresentable.{u} M] [IsFinitelyPresentable.{u} N] (f : M ⟶ N) :
    IsFinitelyPresentable.{u} (cokernel f) := by
  haveI : Fact (Cardinal.IsRegular ℵ₀) := ⟨Cardinal.isRegular_aleph0⟩
  -- Realize the cokernel as the colimit of the parallel pair diagram f, 0 : M ⇉ N.
  have hcond : f ≫ cokernel.π f = 0 ≫ cokernel.π f := by simp [cokernel.condition]
  let c : Cocone (parallelPair f 0) := Cofork.ofπ (cokernel.π f) hcond
  have hcoeq : IsColimit c := cokernelIsCokernel f
  -- Both objects in the parallel pair diagram are finitely presentable by hypothesis.
  haveI : ∀ j, IsCardinalPresentable.{u} ((parallelPair f 0).obj j) ℵ₀ := by
    intro j
    match j with
    | .zero => simp only [parallelPair_obj_zero]; infer_instance
    | .one => simp only [parallelPair_obj_one]; infer_instance
  exact isCardinalPresentable_of_isColimit'.{u} c hcoeq (κ := ℵ₀)
    (hasCardinalLT_of_finite (Arrow WalkingParallelPair) ℵ₀ (le_refl ℵ₀))

/-- Any finitely presented R-module P can be expressed as the cokernel of a map between
finite free modules R^m → R^n. This is the standard algebraic fact that a finitely
presented module admits a finite presentation, made explicit at the level of `ModuleCat`.
It is used in `instIsFinitelyPresentable` to reduce to the case of cokernels of maps
between finitely presentable objects. -/
theorem exists_iso_cokernel_of_finitePresentation (P : Type u) [AddCommGroup P] [Module R P]
    [Module.FinitePresentation R P] :
    ∃ (m n : ℕ) (f : of R (Fin m → R) ⟶ of R (Fin n → R)),
      Nonempty ((of R P) ≅ cokernel f) := by
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin (R := R) (M := P)
  rw [Submodule.fg_iff_exists_fin_generating_family] at hK
  obtain ⟨m, s, hs⟩ := hK
  -- Construct the map g : R^m → R^n whose image is K, using the generating family s.
  let g : (Fin m → R) →ₗ[R] (Fin n → R) :=
    Finsupp.linearCombination R s ∘ₗ
      (Finsupp.linearEquivFunOnFinite R R (Fin m)).symm.toLinearMap
  use m, n, ModuleCat.ofHom g
  have hrange : LinearMap.range g = K := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
      Finsupp.range_linearCombination, hs]
  constructor
  -- Chain the isomorphism P ≅ R^n/K ≅ R^n/im(g) ≅ cokernel(g).
  refine e.toModuleIso ≪≫ ?_ ≪≫
    (ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom g)).symm
  exact (Submodule.quotEquivOfEq K (LinearMap.range g) hrange.symm).toModuleIso

/-- If P is finitely presented as an R-module (in the sense of `Module.FinitePresentation`),
then `ModuleCat.of R P` is finitely presentable in the categorical sense. This is the main
result of the file, bridging the algebraic and categorical notions of finite presentation.
The proof writes P as the cokernel of a map R^m → R^n via
`exists_iso_cokernel_of_finitePresentation`, and then applies `isFinitelyPresentable_cokernel`
since finite free modules are finitely presentable. -/
instance instIsFinitelyPresentable (P : Type u) [AddCommGroup P] [Module R P]
    [Module.FinitePresentation R P] : IsFinitelyPresentable.{u} (of R P) := by
  obtain ⟨m, n, f, ⟨iso⟩⟩ := exists_iso_cokernel_of_finitePresentation (R := R) P
  haveI : IsFinitelyPresentable (cokernel f) := isFinitelyPresentable_cokernel f
  haveI : Fact (Cardinal.IsRegular ℵ₀) := ⟨Cardinal.isRegular_aleph0⟩
  exact isCardinalPresentable_of_iso iso.symm ℵ₀

end ModuleCat
