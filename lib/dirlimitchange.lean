/-
Copyright (c) 2026 Liran Shaul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Liran Shaul

This file is part of the formalization project accompanying the paper:
  "Formalization in Lean of faithfully flat descent of projectivity"
  by Liran Shaul, Charles University in Prague.

We establish an S-linear isomorphism between S ⊗[R] (DirectLimit G f) and
DirectLimit (S ⊗[R] G ·), i.e., that scalar extension commutes with direct limits
of modules. This result is used in the base-change arguments throughout the project,
in particular in the proof that faithfully flat base change reflects the
Mittag-Leffler property (Section 8 of the paper).
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


/-- Scalar extension commutes with direct limits: given a commutative ring R, an R-algebra S,
and a directed system (G, f) of R-modules indexed by a directed preorder ι, there is a
natural S-linear isomorphism

  S ⊗[R] (DirectLimit G f)  ≃ₗ[S]  DirectLimit (S ⊗[R] G ·)

where the transition maps in the right-hand side are obtained by applying S ⊗[R] - to those
of (G, f). This is the standard fact that tensor product (being a left adjoint) commutes with
colimits, here made explicit at the level of directed limits of modules. -/
noncomputable def TensorProduct.directLimitRightSLinear
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [DecidableEq ι] [Nonempty ι]
    (G : ι → Type*) [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) [DirectedSystem G (fun i j h => f i j h)] :
    TensorProduct R S (Module.DirectLimit G f) ≃ₗ[S]
    Module.DirectLimit (fun i => TensorProduct R S (G i))
      (fun i j h => TensorProduct.AlgebraTensorModule.map
        (LinearMap.id (R := S) (M := S)) (f i j h)) := by
  -- Abbreviate the base-changed transition maps and the target direct limit.
  let f' := fun i j h => TensorProduct.AlgebraTensorModule.map
    (LinearMap.id (R := S) (M := S)) (f i j h)
  let L_S := Module.DirectLimit (fun i => TensorProduct R S (G i)) f'
  -- View L_S as an R-module via restriction of scalars along R → S, and record the
  -- resulting scalar tower R → S → L_S, which is needed to state the R-linear maps below.
  letI : Module R L_S := Module.compHom L_S (algebraMap R S)
  haveI : IsScalarTower R S L_S := IsScalarTower.of_algebraMap_smul (fun r x => rfl)
  -- For each s : S and index i, define an R-linear map G i → L_S sending x to of i (s ⊗ x).
  -- These will be assembled via the universal property of the direct limit to give the
  -- forward map S ⊗[R] DirectLimit G f → L_S.
  let ψ : (s : S) → (i : ι) → G i →ₗ[R] L_S := fun s i =>
    { toFun := fun x => Module.DirectLimit.of S ι _ f' i (s ⊗ₜ[R] x)
      map_add' := by intros; simp [TensorProduct.tmul_add]
      map_smul' := by
        intros r x
        simp only [RingHom.id_apply, TensorProduct.tmul_smul, LinearMap.map_smul_of_tower] }
  -- The maps ψ s are compatible with the transition maps, so they descend to the direct limit.
  have hψ_compat : ∀ s i j (hij : i ≤ j) x, ψ s j (f i j hij x) = ψ s i x := by
    intros s i j hij x
    change Module.DirectLimit.of S ι _ f' j (s ⊗ₜ[R] (f i j hij x)) =
           Module.DirectLimit.of S ι _ f' i (s ⊗ₜ[R] x)
    have h : s ⊗ₜ[R] (f i j hij x) = f' i j hij (s ⊗ₜ[R] x) := by
      simp only [f', TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply]
    rw [h, Module.DirectLimit.of_f]
  -- Assemble ψ into an S-linear map φ : S →ₗ[S] (DirectLimit G f →ₗ[R] L_S) using the
  -- universal property of the direct limit on each fiber. This is the curried form of the
  -- forward map, allowing us to apply AlgebraTensorModule.lift.
  let φ : S →ₗ[S] (Module.DirectLimit G f) →ₗ[R] L_S :=
    { toFun := fun s => Module.DirectLimit.lift R ι G f (ψ s) (hψ_compat s)
      map_add' := by
        intros s t
        apply Module.DirectLimit.hom_ext
        intro i
        ext x
        simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
          Module.DirectLimit.lift_of, ψ, TensorProduct.add_tmul, map_add]
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
      map_smul' := by
        intros r s
        apply Module.DirectLimit.hom_ext
        intro i
        ext x
        simp only [LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
          Module.DirectLimit.lift_of, ψ, RingHom.id_apply]
        simp only [smul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk]
        rw [← map_smul]
        congr 1 }
  -- The forward map S ⊗[R] DirectLimit G f → L_S is obtained from φ via the universal
  -- property of the tensor product.
  let toFun : TensorProduct R S (Module.DirectLimit G f) →ₗ[S] L_S :=
    TensorProduct.AlgebraTensorModule.lift φ
  -- The components of the inverse map: each S ⊗[R] G i maps into S ⊗[R] DirectLimit G f
  -- via id ⊗ (of i).
  let invFun_components : (i : ι) → TensorProduct R S (G i) →ₗ[S]
      TensorProduct R S (Module.DirectLimit G f) := fun i =>
    TensorProduct.AlgebraTensorModule.map LinearMap.id (Module.DirectLimit.of R ι G f i)
  -- The components are compatible with the transition maps f', so they assemble into a
  -- map L_S → S ⊗[R] DirectLimit G f via the universal property of the direct limit.
  have hinv_compat : ∀ i j (hij : i ≤ j) x,
      invFun_components j (f' i j hij x) = invFun_components i x := by
    intros i j hij x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s g =>
      simp only [invFun_components, f', TensorProduct.AlgebraTensorModule.map_tmul,
        LinearMap.id_apply, Module.DirectLimit.of_f]
    | add x y hx hy => simp only [map_add, hx, hy]
  let invFun : L_S →ₗ[S] TensorProduct R S (Module.DirectLimit G f) :=
    Module.DirectLimit.lift S ι _ f' invFun_components hinv_compat
  -- Verify that toFun and invFun are mutually inverse by checking on generators
  -- (pure tensors s ⊗ of i g) using the universal properties of tensor product and direct limit.
  have left_inv : ∀ x, invFun (toFun x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      induction m using Module.DirectLimit.induction_on with
      | ih i g =>
        simp only [toFun, invFun, TensorProduct.AlgebraTensorModule.lift_tmul,
          φ, Module.DirectLimit.lift_of, ψ, LinearMap.coe_mk, AddHom.coe_mk,
          Module.DirectLimit.lift_of, invFun_components]
        rw [Module.DirectLimit.lift_of]
        simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have right_inv : ∀ x, toFun (invFun x) = x := by
    intro x
    induction x using Module.DirectLimit.induction_on with
    | ih i y =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul s g =>
        simp only [invFun, invFun_components]
        rw [Module.DirectLimit.lift_of]
        simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply]
        simp only [toFun, TensorProduct.AlgebraTensorModule.lift_tmul]
        simp only [φ, LinearMap.coe_mk, AddHom.coe_mk]
        rw [Module.DirectLimit.lift_of]
        simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk]
      | add x y hx hy => simp only [map_add, hx, hy]
  exact {
    toFun := toFun
    invFun := invFun
    left_inv := left_inv
    right_inv := right_inv
    map_add' := toFun.map_add
    map_smul' := toFun.map_smul
  }

/-- The isomorphism `TensorProduct.directLimitRightSLinear` sends a pure tensor s ⊗ (of i g)
to of i (s ⊗ g), i.e., it intertwines the inclusions of the i-th component into the two
direct limits in the natural way. This simp lemma allows rewriting along the isomorphism
on generators. -/
@[simp]
lemma TensorProduct.directLimitRightSLinear_tmul_of
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [DecidableEq ι] [Nonempty ι]
    (G : ι → Type*) [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) [DirectedSystem G (fun i j h => f i j h)]
    (s : S) (i : ι) (g : G i) :
    TensorProduct.directLimitRightSLinear G f (s ⊗ₜ Module.DirectLimit.of R ι G f i g) =
    Module.DirectLimit.of S ι (fun i => TensorProduct R S (G i))
      (fun i j h => TensorProduct.AlgebraTensorModule.map LinearMap.id (f i j h)) i (s ⊗ₜ g) := by
  -- Set up the same local abbreviations as in the definition, needed to state the
  -- intermediate rewriting steps.
  let f' := fun i j h => TensorProduct.AlgebraTensorModule.map
    (LinearMap.id (R := S) (M := S)) (f i j h)
  let L_S := Module.DirectLimit (fun i => TensorProduct R S (G i)) f'
  letI : Module R L_S := Module.compHom L_S (algebraMap R S)
  haveI : IsScalarTower R S L_S := IsScalarTower.of_algebraMap_smul (fun r x => rfl)
  -- Unfold the definition of directLimitRightSLinear to expose the AlgebraTensorModule.lift,
  -- then evaluate on the pure tensor using the universal properties of lift and DirectLimit.of.
  change (TensorProduct.AlgebraTensorModule.lift _) (s ⊗ₜ Module.DirectLimit.of R ι G f i g) = _
  rw [TensorProduct.AlgebraTensorModule.lift_tmul]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Module.DirectLimit.lift_of]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
