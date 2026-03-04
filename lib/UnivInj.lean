/-
Copyright (c) 2026 Liran Shaul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Liran Shaul

This file is part of the formalization project accompanying the paper:
  "Formalization in Lean of faithfully flat descent of projectivity"
  by Liran Shaul, Charles University in Prague.

We develop the theory of universally injective linear maps, following Section 4 of the paper
and the Stacks Project (Tag 058K). An R-linear map f : M →ₗ[R] N is universally injective
if for every R-module Q, the map f ⊗ id_Q : M ⊗[R] Q → N ⊗[R] Q is injective.

The main results proved here are:

  UniversallyInjective.injective (Stacks 058K, (1) ⟹ injectivity):
    Every universally injective map is injective, proved by specializing to Q = R.

  universally_injective_lift_free (Stacks 058K, (1) ⟹ (4)):
    If f : M →ₗ[R] N is universally injective and we have a commutative square
      F --k--> G
      |        |
      g        h
      ↓        ↓
      M --f--> N
    with F, G finite free, then there exists φ : G →ₗ[R] M with φ ∘ k = g. This is
    the key lifting property that allows maps out of finitely presented modules to be
    lifted across universally injective maps.

    The proof works by choosing bases for F and G and reducing to linear algebra over R:
    we find z : ι_G → M by showing that the pointwise application of f on (ι_F → M)
    is injective on cokernels of the matrix action, using the isomorphism
    (ι_F → M) / im(A·) ≅ M ⊗[R] Q' (where Q' is the cokernel of the transpose matrix map)
    and the universal injectivity of f ⊗ id_{Q'}.

  univ_exact_lift_fp (Stacks 058K, (1) ⟹ (5)):
    If 0 → X₁ →f X₂ →g X₃ → 0 is a universally exact short exact sequence of R-modules
    and P is a finitely presented R-module, then every R-linear map P →ₗ[R] X₃ lifts to
    P →ₗ[R] X₂. This is Theorem 4.1 of the paper and a key step in the proof of
    faithfully flat descent of projectivity (Theorem I).

    The proof uses the finite presentation of P to reduce to `universally_injective_lift_free`
    for the relations module, then corrects the resulting map by subtracting the image of a
    lift of the relations.

  UniversallyInjective.of_baseChange_faithfullyFlat (Theorem 4.2 of the paper):
    If S is a faithfully flat R-algebra and the base change f_S : S ⊗[R] M →ₗ[S] S ⊗[R] N
    is universally injective (as an S-linear map), then f itself is universally injective.
    The proof reduces S-linear universal injectivity of f_S to R-linear injectivity of
    f ⊗ id_Q using the natural isomorphism
      (S ⊗[R] M) ⊗[S] (S ⊗[R] Q) ≃ₗ[R] S ⊗[R] (M ⊗[R] Q)
    formalized as `baseChangeTensorBaseChange`, and then applies faithful flatness.
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
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import lib.mlSystem
import lib.Pushout


namespace LinearMap

universe u

variable {R : Type u} [CommRing R]
variable {M : Type u} {N : Type u} {M' : Type u}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup M']
variable [Module R M] [Module R N] [Module R M']

/-- An R-linear map f : M →ₗ[R] N is universally injective if for every R-module Q,
the map f ⊗ id_Q : M ⊗[R] Q →ₗ[R] N ⊗[R] Q is injective.

This is the defining condition of Stacks Project Tag 058K (1) and Definition 4.1 of the paper.
It is stronger than ordinary injectivity; see `UniversallyInjective.injective` for the
implication. Universally injective maps are also called pure monomorphisms in the literature. -/
def UniversallyInjective (f : M →ₗ[R] N) : Prop :=
  ∀ (Q : Type u) [AddCommGroup Q] [Module R Q], Function.Injective (f.rTensor Q)

/-- Every universally injective map is injective. The proof specializes the universal
injectivity condition to Q = R, using the identification M ⊗[R] R ≅ M via `TensorProduct.rid`.
This is Stacks 058K (1) ⟹ injectivity. -/
theorem UniversallyInjective.injective {f : M →ₗ[R] N}
(hf : f.UniversallyInjective) : Function.Injective f := by
  intro x y hxy
  have hinj := hf R
  have : f.rTensor R (x ⊗ₜ 1) = f.rTensor R (y ⊗ₜ 1) := by simp [hxy]
  have heq := hinj this
  have := congrArg (TensorProduct.rid R M) heq
  simpa using this

/-- If f : M →ₗ[R] N is universally injective and we have a commutative square
      F --k--> G
      |        |
      g        h
      ↓        ↓
      M --f--> N
with F and G finite free R-modules, then there exists φ : G →ₗ[R] M with φ ∘ k = g.

This is Stacks 058K (1) ⟹ (4) and is used as a subroutine in `univ_exact_lift_fp`.

Proof strategy: Choose bases (bF, bG) for F and G. Write k(bF i) = Σⱼ aᵢⱼ bG j.
We need z : ι_G → M with g(bF i) = Σⱼ aᵢⱼ z j for all i. We know f(g(bF i)) = Σⱼ aᵢⱼ h(bG j),
so (g(bF i)) lies in the image of the matrix action A· : (ι_G → M) → (ι_F → M), z ↦ (Σⱼ aᵢⱼ zⱼ)ᵢ
if and only if its image under f lies in the image of the corresponding action on N.
To show this, we use the isomorphism (ι_F → M) / im(A·) ≅ M ⊗[R] Q' (where Q' is the
cokernel of the transpose matrix map k_transpose : (ι_G → R) → (ι_F → R)) obtained from
the identification (ι_F → M) ≅ M ⊗ (ι_F → R) and the right exactness of tensor product.
Injectivity of the induced map on cokernels follows from universal injectivity of f applied
to Q', giving the desired z. -/
theorem universially_injective_lift_free
{F : Type u} [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F]
{G : Type u} [AddCommGroup G] [Module R G] [Module.Free R G] [Module.Finite R G]
(f : M →ₗ[R] N) (univf : UniversallyInjective f)
(g : F →ₗ[R] M) (h : G →ₗ[R] N) (k : F →ₗ[R] G) (commSquare : h ∘ₗ k = f ∘ₗ g)
: ∃ φ : G →ₗ[R] M, φ ∘ₗ k = g := by

  let Q := G ⧸ (range k)
  let fQ := f.rTensor Q
  have injfQ : Function.Injective fQ := by apply univf
  let bF := Module.Free.chooseBasis R F
  let bG := Module.Free.chooseBasis R G
  haveI : Fintype (Module.Free.ChooseBasisIndex R F) := Module.Free.ChooseBasisIndex.fintype R F
  haveI : Fintype (Module.Free.ChooseBasisIndex R G) := Module.Free.ChooseBasisIndex.fintype R G
  -- Let x i = g(bF i) and y j = h(bG j) be the images of basis elements
  let x : Module.Free.ChooseBasisIndex R F → M := fun i => g (bF i)
  let y : Module.Free.ChooseBasisIndex R G → N := fun j => h (bG j)

  -- The matrix coefficients: k(bF i) = Σ_j a_ij · (bG j)
  let a : Module.Free.ChooseBasisIndex R F → Module.Free.ChooseBasisIndex R G → R :=
    fun i j => bG.repr (k (bF i)) j

  -- From the commutative square, f(x i) = Σ_j a_ij · y j for all i
  have hfx : ∀ i, f (x i) = ∑ j, a i j • y j := by
    intro i
    have : f (g (bF i)) = h (k (bF i)) := by
      have := congrFun (congrArg DFunLike.coe commSquare) (bF i)
      simp at this
      exact this.symm
    simp only [x, y]
    rw [this]
    conv_lhs => rw [← bG.sum_repr (k (bF i))]
    simp only [map_sum, map_smul]
    rfl

  -- Key step: use universal injectivity to find z : ι_G → M with x i = Σ_j a_ij · z j
  have key : ∃ z : Module.Free.ChooseBasisIndex R G → M, ∀ i, x i = ∑ j, a i j • z j := by
    let ι_F := Module.Free.ChooseBasisIndex R F
    let ι_G := Module.Free.ChooseBasisIndex R G

    -- The transpose matrix map k_transpose : (ι_G → R) → (ι_F → R), v ↦ (Σ_j a_ij v_j)_i
    let k_transpose : (ι_G → R) →ₗ[R] (ι_F → R) := {
      toFun := fun v => fun i => ∑ j, a i j * v j
      map_add' := by intros; ext; simp [Finset.sum_add_distrib, mul_add]
      map_smul' := by
        intros m v
        ext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        congr 1
        ext j
        ring
    }

    -- Q' = cokernel of k_transpose, with projection π'
    let Q' := (ι_F → R) ⧸ LinearMap.range k_transpose
    let π' : (ι_F → R) →ₗ[R] Q' := Submodule.mkQ (LinearMap.range k_transpose)

    -- The matrix action A· on M-valued functions: z ↦ (Σ_j a_ij · z_j)_i
    let matrix_action_M : (ι_G → M) →ₗ[R] (ι_F → M) := {
      toFun := fun z => fun i => ∑ j, a i j • z j
      map_add' := by intros; ext; simp [Finset.sum_add_distrib, smul_add]
      map_smul' := by
        intros m v
        ext i
        simp only [Pi.smul_apply, RingHom.id_apply]
        rw [Finset.smul_sum]
        congr 1
        ext j
        rw [smul_comm]
    }

    -- The same matrix action on N-valued functions
    let matrix_action_N : (ι_G → N) →ₗ[R] (ι_F → N) := {
      toFun := fun z => fun i => ∑ j, a i j • z j
      map_add' := by intros; ext; simp [Finset.sum_add_distrib, smul_add]
      map_smul' := by
        intros m v
        ext i
        simp only [Pi.smul_apply, RingHom.id_apply]
        rw [Finset.smul_sum]
        congr 1
        ext j
        rw [smul_comm]
    }

    -- The image of x under pointwise f equals the matrix action of y
    have h_fx_in_image : (fun i => f (x i)) = matrix_action_N y := by
      ext i
      simp only [matrix_action_N]
      exact hfx i

    have fx_in_image_N : (fun i => f (x i)) ∈ LinearMap.range matrix_action_N := by
      rw [h_fx_in_image]
      exact LinearMap.mem_range_self matrix_action_N y

    -- Main sub-claim: x ∈ range(matrix_action_M), proved using universal injectivity
    have x_in_image_M : x ∈ LinearMap.range matrix_action_M := by
      -- Pointwise application of f: (ι_F → M) → (ι_F → N)
      let f_pointwise : (ι_F → M) →ₗ[R] (ι_F → N) := {
        toFun := fun v => fun i => f (v i)
        map_add' := by intros; ext; simp
        map_smul' := by intros; ext; simp
      }

      -- f_pointwise maps range(matrix_action_M) into range(matrix_action_N)
      have f_maps_range : LinearMap.range matrix_action_M ≤
          (LinearMap.range matrix_action_N).comap f_pointwise := by
            intro v hv
            simp only [Submodule.mem_comap]
            obtain ⟨w, hw⟩ := hv
            rw [← hw]
            use fun j => f (w j)
            ext i
            simp only [f_pointwise, matrix_action_M, matrix_action_N]
            simp

      -- The cokernel (ι_F → M) / range(matrix_action_M) ≅ M ⊗ Q', with explicit formula:
      -- the isomorphism sends [w] to (id ⊗ π')((piScalarRight)⁻¹(w)).
      -- Key steps: (ι_F → M) ≅ M ⊗ (ι_F → R) via piScalarRight, under which matrix_action_M
      -- corresponds to id ⊗ k_transpose, and right exactness gives the cokernel identification.
      have coker_equiv_M_with_apply :
        ∃ (e : ((ι_F → M) ⧸ LinearMap.range matrix_action_M) ≃ₗ[R] TensorProduct R M Q'),
        ∀ w, e (Submodule.Quotient.mk w) =
          (TensorProduct.map LinearMap.id π') ((TensorProduct.piScalarRight R R M ι_F).symm w) := by
        -- Step 1: The isomorphism (ι_F → M) ≃ M ⊗ (ι_F → R)
        let piEquivTensor_M : (ι_F → M) ≃ₗ[R] TensorProduct R M (ι_F → R) :=
          (TensorProduct.piScalarRight R R M ι_F).symm

        -- Step 2: The isomorphism (ι_G → M) ≃ M ⊗ (ι_G → R)
        let piEquivTensor_G : (ι_G → M) ≃ₗ[R] TensorProduct R M (ι_G → R) :=
          (TensorProduct.piScalarRight R R M ι_G).symm

        -- Step 3: Under piScalarRight, matrix_action_M corresponds to id ⊗ k_transpose.
        -- Verified on basis elements Pi.single z m: both sides equal m ⊗ (fun i => a i z).
        have matrix_action_eq : piEquivTensor_M.toLinearMap ∘ₗ matrix_action_M =
          (TensorProduct.map LinearMap.id k_transpose) ∘ₗ piEquivTensor_G.toLinearMap := by
            ext z m
            simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
            piEquivTensor_M, piEquivTensor_G]

            have h1 : matrix_action_M (Pi.single z m) = fun i => a i z • m := by
              ext i
              simp only [matrix_action_M, LinearMap.coe_mk, AddHom.coe_mk]
              rw [Finset.sum_eq_single z]
              · simp only [Pi.single_eq_same]
              · intro j _ hj
                simp only [Pi.single_eq_of_ne hj, smul_zero]
              · intro hz
                exact (hz (Finset.mem_univ z)).elim

            have h2 : (TensorProduct.piScalarRight R R M ι_F).symm (fun i => a i z • m) =
            TensorProduct.tmul R m (fun i => a i z) := by
                apply (TensorProduct.piScalarRight R R M ι_F).injective
                rw [LinearEquiv.apply_symm_apply]
                ext i
                simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]

            have h3 : (TensorProduct.piScalarRight R R M ι_G).symm (Pi.single z m) =
                TensorProduct.tmul R m (Pi.single z 1) := by
                  apply (TensorProduct.piScalarRight R R M ι_G).injective
                  rw [LinearEquiv.apply_symm_apply]
                  ext i
                  simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
                  simp only [Pi.single_apply]
                  split_ifs with h
                  · simp
                  · simp

            have h4 : (TensorProduct.map LinearMap.id k_transpose)
              (TensorProduct.tmul R m (Pi.single z 1)) =
                TensorProduct.tmul R m (k_transpose (Pi.single z 1)) := by
              rw [TensorProduct.map_tmul]
              simp

            have h5 : k_transpose (Pi.single z 1) = fun i => a i z := by
              ext i
              simp only [k_transpose, LinearMap.coe_mk, AddHom.coe_mk]
              rw [Finset.sum_eq_single z]
              · simp only [Pi.single_eq_same, mul_one]
              · intro j _ hj
                simp only [Pi.single_eq_of_ne hj, mul_zero]
              · intro hz
                exact (hz (Finset.mem_univ z)).elim

            have hsingle : (single R (fun i ↦ M) z) m = Pi.single z m := by rfl
            rw [hsingle]
            rw [h1, h2]
            rw [h3, h4, h5]

        -- Step 4: piEquivTensor_M maps range(matrix_action_M) to range(id ⊗ k_transpose)
        have range_eq : Submodule.map piEquivTensor_M.toLinearMap
            (LinearMap.range matrix_action_M) =
            LinearMap.range (TensorProduct.map LinearMap.id k_transpose) := by
              ext t
              constructor
              · intro ht
                rw [Submodule.mem_map] at ht
                obtain ⟨v, hv, hvt⟩ := ht
                rw [LinearMap.mem_range] at hv
                obtain ⟨w, hw⟩ := hv
                rw [LinearMap.mem_range]
                use piEquivTensor_G w
                rw [← hvt, ← hw]
                have := congrFun (congrArg DFunLike.coe matrix_action_eq) w
                simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at this
                exact this.symm
              · intro ht
                rw [LinearMap.mem_range] at ht
                obtain ⟨s, hs⟩ := ht
                rw [Submodule.mem_map]
                use matrix_action_M (piEquivTensor_G.symm s)
                constructor
                · rw [LinearMap.mem_range]
                  use piEquivTensor_G.symm s
                · rw [← hs]
                  have := congrFun (congrArg DFunLike.coe matrix_action_eq) (piEquivTensor_G.symm s)
                  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
                            LinearEquiv.apply_symm_apply] at this
                  exact this

        -- Step 5: By right exactness, (M ⊗ (ι_F → R)) / range(id ⊗ k_transpose) ≃ M ⊗ Q',
        -- using `lTensor.equiv` with the exact sequence k_transpose → π' → 0
        let rangeInTensor : Submodule R (TensorProduct R M (ι_F → R)) :=
            LinearMap.range (TensorProduct.map LinearMap.id k_transpose)

        let tensorCokerEquiv : (TensorProduct R M (ι_F → R) ⧸ rangeInTensor) ≃ₗ[R]
            TensorProduct R M Q' := by
          have exact_seq : Function.Exact k_transpose π' := by
              rw [LinearMap.exact_iff]
              ext v
              simp only [LinearMap.mem_ker, LinearMap.mem_range, π']
              rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
              simp only [LinearMap.mem_range]

          have surj_π' : Function.Surjective π' := Submodule.mkQ_surjective _

          have h_range : rangeInTensor = LinearMap.range (LinearMap.lTensor M k_transpose) := by
            simp only [rangeInTensor, LinearMap.lTensor]

          rw [h_range]
          exact lTensor.equiv M exact_seq surj_π'

        -- Step 6: Combine the two equivalences to get coker(matrix_action_M) ≃ M ⊗ Q'
        let step6a : ((ι_F → M) ⧸ LinearMap.range matrix_action_M) ≃ₗ[R]
            (TensorProduct R M (ι_F → R) ⧸ rangeInTensor) := by
          apply Submodule.Quotient.equiv (LinearMap.range matrix_action_M)
            rangeInTensor piEquivTensor_M
          simp only [rangeInTensor]
          exact range_eq

        let e := step6a.trans tensorCokerEquiv
        use e
        intro w
        simp only [e, LinearEquiv.trans_apply]
        have h_step6a : step6a (Submodule.Quotient.mk w) =
          Submodule.Quotient.mk (piEquivTensor_M w) := by
          simp only [step6a, Submodule.Quotient.equiv_apply]
          rfl

        rw [h_step6a]
        have h_tensorCokerEquiv : ∀ t, tensorCokerEquiv (Submodule.Quotient.mk t) =
          (TensorProduct.map LinearMap.id π') t := by
          intro t
          simp only [tensorCokerEquiv]
          unfold lTensor.equiv
          simp
          rfl

        rw [h_tensorCokerEquiv]

      obtain ⟨coker_equiv_M, coker_equiv_M_apply⟩ := coker_equiv_M_with_apply

      -- Analogous cokernel isomorphism for N: coker(matrix_action_N) ≃ N ⊗ Q'
      have coker_equiv_N_with_apply :
        ∃ (e : ((ι_F → N) ⧸ LinearMap.range matrix_action_N) ≃ₗ[R] TensorProduct R N Q'),
        ∀ w, e (Submodule.Quotient.mk w) =
          (TensorProduct.map LinearMap.id π') ((TensorProduct.piScalarRight R R N ι_F).symm w) := by
          let piEquivTensor_N_F : (ι_F → N) ≃ₗ[R] TensorProduct R N (ι_F → R) :=
            (TensorProduct.piScalarRight R R N ι_F).symm

          let piEquivTensor_N_G : (ι_G → N) ≃ₗ[R] TensorProduct R N (ι_G → R) :=
            (TensorProduct.piScalarRight R R N ι_G).symm

          -- Under piScalarRight, matrix_action_N corresponds to id ⊗ k_transpose
          have matrix_action_eq_N : piEquivTensor_N_F.toLinearMap ∘ₗ matrix_action_N =
            (TensorProduct.map LinearMap.id k_transpose) ∘ₗ piEquivTensor_N_G.toLinearMap := by
              ext z n
              simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
              piEquivTensor_N_F, piEquivTensor_N_G]

              have h1 : matrix_action_N (Pi.single z n) = fun i => a i z • n := by
                ext i
                simp only [matrix_action_N, LinearMap.coe_mk, AddHom.coe_mk]
                rw [Finset.sum_eq_single z]
                · simp only [Pi.single_eq_same]
                · intro j _ hj
                  simp only [Pi.single_eq_of_ne hj, smul_zero]
                · intro hz
                  exact (hz (Finset.mem_univ z)).elim

              have h2 : (TensorProduct.piScalarRight R R N ι_F).symm (fun i => a i z • n) =
              TensorProduct.tmul R n (fun i => a i z) := by
                  apply (TensorProduct.piScalarRight R R N ι_F).injective
                  rw [LinearEquiv.apply_symm_apply]
                  ext i
                  simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]

              have h3 : (TensorProduct.piScalarRight R R N ι_G).symm (Pi.single z n) =
                  TensorProduct.tmul R n (Pi.single z 1) := by
                    apply (TensorProduct.piScalarRight R R N ι_G).injective
                    rw [LinearEquiv.apply_symm_apply]
                    ext i
                    simp only [TensorProduct.piScalarRight_apply,
                      TensorProduct.piScalarRightHom_tmul]
                    simp only [Pi.single_apply]
                    split_ifs with h
                    · simp
                    · simp

              have h4 : (TensorProduct.map LinearMap.id k_transpose)
                (TensorProduct.tmul R n (Pi.single z 1)) =
                  TensorProduct.tmul R n (k_transpose (Pi.single z 1)) := by
                rw [TensorProduct.map_tmul]
                simp

              have h5 : k_transpose (Pi.single z 1) = fun i => a i z := by
                ext i
                simp only [k_transpose, LinearMap.coe_mk, AddHom.coe_mk]
                rw [Finset.sum_eq_single z]
                · simp only [Pi.single_eq_same, mul_one]
                · intro j _ hj
                  simp only [Pi.single_eq_of_ne hj, mul_zero]
                · intro hz
                  exact (hz (Finset.mem_univ z)).elim

              have hsingle : (single R (fun i ↦ N) z) n = Pi.single z n := by rfl
              rw [hsingle]
              rw [h1, h2]
              rw [h3, h4, h5]

          have range_eq_N : Submodule.map piEquivTensor_N_F.toLinearMap
              (LinearMap.range matrix_action_N) =
              LinearMap.range (TensorProduct.map LinearMap.id k_transpose) := by
                ext t
                constructor
                · intro ht
                  rw [Submodule.mem_map] at ht
                  obtain ⟨v, hv, hvt⟩ := ht
                  rw [LinearMap.mem_range] at hv
                  obtain ⟨w, hw⟩ := hv
                  rw [LinearMap.mem_range]
                  use piEquivTensor_N_G w
                  rw [← hvt, ← hw]
                  have := congrFun (congrArg DFunLike.coe matrix_action_eq_N) w
                  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at this
                  exact this.symm
                · intro ht
                  rw [LinearMap.mem_range] at ht
                  obtain ⟨s, hs⟩ := ht
                  rw [Submodule.mem_map]
                  use matrix_action_N (piEquivTensor_N_G.symm s)
                  constructor
                  · rw [LinearMap.mem_range]
                    use piEquivTensor_N_G.symm s
                  · rw [← hs]
                    have := congrFun (congrArg DFunLike.coe matrix_action_eq_N)
                      (piEquivTensor_N_G.symm s)
                    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
                              LinearEquiv.apply_symm_apply] at this
                    exact this

          let rangeInTensor_N : Submodule R (TensorProduct R N (ι_F → R)) :=
              LinearMap.range (TensorProduct.map LinearMap.id k_transpose)

          let tensorCokerEquiv_N : (TensorProduct R N (ι_F → R) ⧸ rangeInTensor_N) ≃ₗ[R]
              TensorProduct R N Q' := by
            have exact_seq : Function.Exact k_transpose π' := by
                rw [LinearMap.exact_iff]
                ext v
                simp only [LinearMap.mem_ker, LinearMap.mem_range, π']
                rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
                simp only [LinearMap.mem_range]

            have surj_π' : Function.Surjective π' := Submodule.mkQ_surjective _

            have h_range : rangeInTensor_N = LinearMap.range (LinearMap.lTensor N k_transpose) := by
              simp only [rangeInTensor_N, LinearMap.lTensor]

            rw [h_range]
            exact lTensor.equiv N exact_seq surj_π'

          let step6a_N : ((ι_F → N) ⧸ LinearMap.range matrix_action_N) ≃ₗ[R]
              (TensorProduct R N (ι_F → R) ⧸ rangeInTensor_N) := by
            apply Submodule.Quotient.equiv (LinearMap.range matrix_action_N)
              rangeInTensor_N piEquivTensor_N_F
            simp only [rangeInTensor_N]
            exact range_eq_N

          let e := step6a_N.trans tensorCokerEquiv_N
          use e
          intro w
          simp only [e, LinearEquiv.trans_apply]
          have h_step6a_N : step6a_N (Submodule.Quotient.mk w) =
            Submodule.Quotient.mk (piEquivTensor_N_F w) := by
            simp only [step6a_N, Submodule.Quotient.equiv_apply]
            rfl

          rw [h_step6a_N]
          have h_tensorCokerEquiv_N : ∀ t, tensorCokerEquiv_N (Submodule.Quotient.mk t) =
            (TensorProduct.map LinearMap.id π') t := by
            intro t
            simp only [tensorCokerEquiv_N]
            unfold lTensor.equiv
            simp
            rfl

          rw [h_tensorCokerEquiv_N]

      obtain ⟨coker_equiv_N, coker_equiv_N_apply⟩ := coker_equiv_N_with_apply

      -- Under the cokernel isomorphisms, f_pointwise induces f ⊗ id_{Q'} on M ⊗ Q' → N ⊗ Q',
      -- which is injective by universal injectivity of f
      have f_tensor_inj : Function.Injective
        (TensorProduct.map f (LinearMap.id : Q' →ₗ[R] Q')) := by
        exact univf Q'

      -- The induced map on cokernels is injective, proved using the commutative diagram
      -- (f ⊗ id) ∘ coker_equiv_M = coker_equiv_N ∘ mapQ(f_pointwise)
      have coker_map_inj : Function.Injective
          (Submodule.mapQ (LinearMap.range matrix_action_M) (LinearMap.range matrix_action_N)
            f_pointwise f_maps_range) := by

              have f_tensor_inj : Function.Injective
                (TensorProduct.map f (LinearMap.id : Q' →ₗ[R] Q')) :=
                univf Q'

              -- The key commutative diagram: naturality of piScalarRight with respect to f
              have comm_diagram :
                (TensorProduct.map f LinearMap.id).comp coker_equiv_M.toLinearMap =
                  coker_equiv_N.toLinearMap.comp (Submodule.mapQ (LinearMap.range matrix_action_M)
                    (LinearMap.range matrix_action_N) f_pointwise f_maps_range) := by

                  -- piScalarRight is natural in the module variable: it intertwines f_pointwise
                  -- with f ⊗ id on the tensor product side
                  have piScalarRight_nat : ∀ w : ι_F → M,
    (TensorProduct.piScalarRight R R N ι_F).symm (f_pointwise w) =
    (TensorProduct.map f LinearMap.id) ((TensorProduct.piScalarRight R R M ι_F).symm w) := by
                    -- Check on basis elements Pi.single i m and extend by linearity
                    have h_single : ∀ i m,
                        (TensorProduct.piScalarRight R R N ι_F).symm
                          (f_pointwise (Pi.single i m)) =
                          (TensorProduct.map f LinearMap.id)
                          ((TensorProduct.piScalarRight R R M ι_F).symm (Pi.single i m)) := by
                      intro i m
                      have h1 : f_pointwise (Pi.single i m) = Pi.single i (f m) := by
                        ext j
                        simp only [f_pointwise, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
                        split_ifs <;> simp
                      have h2 : (TensorProduct.piScalarRight R R M ι_F).symm (Pi.single i m) =
                          TensorProduct.tmul R m (Pi.single i 1) := by
                        apply (TensorProduct.piScalarRight R R M ι_F).injective
                        rw [LinearEquiv.apply_symm_apply]
                        ext j
                        simp [TensorProduct.piScalarRight_apply,
                          TensorProduct.piScalarRightHom_tmul, Pi.single_apply]

                      have h3 : (TensorProduct.piScalarRight R R N ι_F).symm (Pi.single i (f m)) =
                          TensorProduct.tmul R (f m) (Pi.single i 1) := by
                        apply (TensorProduct.piScalarRight R R N ι_F).injective
                        rw [LinearEquiv.apply_symm_apply]
                        ext j
                        simp [TensorProduct.piScalarRight_apply,
                          TensorProduct.piScalarRightHom_tmul, Pi.single_apply]
                      rw [h1, h3, h2]
                      rw [TensorProduct.map_tmul]
                      simp

                    intro w
                    have hw : w = ∑ i, Pi.single i (w i) := by
                      ext j
                      simp [Pi.single_apply, Finset.sum_apply]
                    rw [hw]
                    simp only [map_sum]
                    congr 1
                    ext i
                    exact h_single i (w i)

                  apply LinearMap.ext
                  intro v
                  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
                  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective
                    (LinearMap.range matrix_action_M) v
                  rw [Submodule.mapQ_apply]
                  rw [coker_equiv_M_apply, coker_equiv_N_apply]
                  rw [piScalarRight_nat]
                  set t := (TensorProduct.piScalarRight R R M ι_F).symm w with ht_def
                  -- Both sides simplify to (f ⊗ π')(t) using map_comp
                  have h1 : (TensorProduct.map f LinearMap.id)
                    ((TensorProduct.map LinearMap.id π') t) =
                      (TensorProduct.map f π') t := by
                    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
                    simp only [LinearMap.id_comp, LinearMap.comp_id]
                  have h2 : (TensorProduct.map LinearMap.id π')
                    ((TensorProduct.map f LinearMap.id) t) =
                    (TensorProduct.map f π') t := by
                    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
                    simp only [LinearMap.id_comp, LinearMap.comp_id]
                  rw[h1, h2]

              -- Injectivity of the cokernel map follows from injectivity of f ⊗ id_{Q'}
              -- via the commutative diagram
              rw [← LinearMap.ker_eq_bot, eq_bot_iff]
              intro v hv
              simp only [LinearMap.mem_ker, Submodule.mem_bot] at hv ⊢
              have := congrFun (congrArg DFunLike.coe comm_diagram.symm) v
              simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at this
              rw [hv, map_zero] at this
              have h2 : coker_equiv_M v = 0 := f_tensor_inj (this.symm.trans (map_zero _).symm)
              exact coker_equiv_M.injective (h2.trans (map_zero _).symm)

      -- Since f_pointwise x lies in range(matrix_action_N), x maps to 0 in the cokernel of
      -- matrix_action_N, and injectivity of the cokernel map gives x ∈ range(matrix_action_M)
      have fx_eq : f_pointwise x = fun i => f (x i) := rfl

      have fx_in_range : f_pointwise x ∈ LinearMap.range matrix_action_N := by
        rw [fx_eq]
        exact fx_in_image_N

      have x_to_zero_in_coker_N : Submodule.mkQ
        (LinearMap.range matrix_action_N) (f_pointwise x) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact fx_in_range

      have x_to_zero_in_coker_M : Submodule.mkQ (LinearMap.range matrix_action_M) x = 0 := by
          have fx_to_zero : Submodule.mkQ (LinearMap.range matrix_action_N)
            (f_pointwise x) = 0 := by
            rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
            exact fx_in_range
          have mapQ_x_zero : (LinearMap.range matrix_action_M).mapQ
            (LinearMap.range matrix_action_N)
            f_pointwise f_maps_range ((LinearMap.range matrix_action_M).mkQ x) = 0 := by
            simp only [Submodule.mapQ_apply, Submodule.mkQ_apply]
            rw [Submodule.Quotient.mk_eq_zero]
            exact fx_in_range

          exact coker_map_inj (mapQ_x_zero.trans (map_zero _).symm)

      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at x_to_zero_in_coker_M
      exact x_to_zero_in_coker_M

    -- Extract z : ι_G → M with x i = Σ_j a_ij · z j, and define φ via the basis
    obtain ⟨z, hz⟩ := x_in_image_M
    use z
    intro i
    have : x i = (matrix_action_M z) i := by rw [← hz]
    simp only [matrix_action_M] at this
    exact this

  obtain ⟨z, hz⟩ := key

  -- Construct φ : G →ₗ[R] M as the unique map sending bG j to z j
  let φ : G →ₗ[R] M := bG.constr R z

  use φ

  -- Verify φ ∘ k = g by checking on basis elements of F
  ext v
  rw [LinearMap.comp_apply]
  conv_lhs => rw [← bF.sum_repr v]
  simp only [map_sum, map_smul]
  conv_rhs => rw [← bF.sum_repr v]
  simp only [map_sum, map_smul]

  congr 1
  ext i
  congr 1

  change φ (k (bF i)) = x i

  -- k(bF i) = Σ_j a_ij (bG j), so φ(k(bF i)) = Σ_j a_ij · z j = x i by hz
  conv_lhs => rw [← bG.sum_repr (k (bF i))]
  simp only [map_sum, map_smul]

  have hφ : ∀ j, φ (bG j) = z j := fun j => bG.constr_basis R z j
  simp only [hφ]

  rw [hz i]


open CategoryTheory

/-- A short complex S = (X₁ →f X₂ →g X₃) in ModuleCat R is universally exact if the
inclusion f : X₁ → X₂ is universally injective.

This is the hypothesis appearing in `univ_exact_lift_fp` (Stacks 058K (1) ⟹ (5)) and
in the proof of faithfully flat descent of projectivity (Theorem I of the paper). -/
def ShortComplex.UniversallyExact (S : ShortComplex (ModuleCat R)) : Prop :=
  UniversallyInjective S.f.hom

/-- If 0 → X₁ →f X₂ →g X₃ → 0 is universally exact and P is a finitely presented R-module,
then every R-linear map φ : P →ₗ[R] X₃ lifts to a map ψ : P →ₗ[R] X₂ with g ∘ ψ = φ.

This is Stacks 058K (1) ⟹ (5) and Theorem 4.1 of the paper. It is applied in the proof of
Theorem I (faithfully flat descent of projectivity) in the following way: given a projective
presentation of S ⊗[R] P, the lifting property provides the required compatible maps for
the colimit argument.

Proof: Let s be a finite generating set for P and t a finite generating set for the kernel
of the surjection G = s →₀ R → P. Set F = t →₀ R with the map k : F → G given by the
relation generators. Use surjectivity of g to lift φ ∘ π : G → X₃ to h₂ : G → X₂.
The obstruction h₂ ∘ k maps to 0 in X₃, hence lies in X₁ = ker g; lift it further to
h₁ : F → X₁ using exactness. Apply `universally_injective_lift_free` to f with the
square F → G → X₂ (h₂) and F → X₁ (h₁) to get k₁ : G → X₁ with k₁ ∘ k = h₁.
The correction ρ = h₂ - f ∘ k₁ vanishes on range(k) = ker(π), hence descends to a map
ρ̄ : P → X₂ with g ∘ ρ̄ = φ. -/
theorem univ_exact_lift_fp
    {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact)
    (hSUniv : ShortComplex.UniversallyExact S)
    {P : Type u} [AddCommGroup P] [Module R P]
    (PfP : Module.FinitePresentation R P)
    (φ : P →ₗ[R] S.X₃) :
    ∃ ψ : P →ₗ[R] S.X₂, ((S.g).hom).comp ψ = φ
     := by

    obtain ⟨s, hs_span, hs_ker_fg⟩ := Module.FinitePresentation.out (R := R) (M := P)
    obtain ⟨t, ht_span⟩ := hs_ker_fg
    haveI hs_finite : Finite s := s.finite_toSet.to_subtype
    haveI ht_finite : Finite t := t.finite_toSet.to_subtype

    let G := s →₀ R
    let F := t →₀ R

    haveI : Module.Free R G := by infer_instance
    haveI : Module.Finite R G := Module.Finite.finsupp (ι := s)
    haveI : Module.Free R F := by infer_instance
    haveI : Module.Finite R F := Module.Finite.finsupp (ι := t)

    -- π : G → P is the surjection from generators; k : F → G encodes the relations
    let π : G →ₗ[R] P := Finsupp.linearCombination R (Subtype.val : s → P)
    have hπ_surj : Function.Surjective π := by
      rw [← LinearMap.range_eq_top]
      rw [Finsupp.range_linearCombination]
      simp only [Subtype.range_coe_subtype, Finset.setOf_mem]
      exact hs_span
    let k : F →ₗ[R] G := Finsupp.linearCombination R (Subtype.val : t → G)
    have hk_range : LinearMap.range k = LinearMap.ker π := by
      rw [Finsupp.range_linearCombination]
      simp only [Subtype.range_coe_subtype, Finset.setOf_mem]
      exact ht_span

    have hg_surj : Function.Surjective S.g.hom := by
      have := hS.epi_g
      rwa [ModuleCat.epi_iff_surjective] at this

    -- Lift φ ∘ π on generators: for each s ∈ s, pick h₂'(s) ∈ X₂ mapping to φ(π(s))
    have keyl : ∀ x: s, ∃ m: S.X₂, (S.g.hom) m = φ (π (Finsupp.single x (1 : R))) :=
    by
      intro x
      let xval := Finsupp.single x (1 : R)
      let r := φ (π xval)
      have : ∃ y : S.X₂, (S.g).hom y = r := by apply hg_surj
      apply this
    choose h2' h2'prop using keyl
    let h2 : G →ₗ[R] S.X₂ := Finsupp.linearCombination R h2'
    have h2prop : ((S.g).hom).comp h2 = φ.comp π := by
      let basisG : Module.Basis ↥s R G := Finsupp.basisSingleOne
      apply Module.Basis.ext basisG
      intro x
      simp only [coe_comp, Function.comp_apply]
      have : Finsupp.basisSingleOne x = Finsupp.single x (1 : R) := by rfl
      let temp := h2'prop x
      rw[←this] at temp
      have : h2' x = h2 (Finsupp.single x (1 : R)) := by
        simp only [h2]
        simp only [Finsupp.linearCombination]
        rw [@Finsupp.lsum_apply]
        simp
      rw[this] at temp
      exact temp

    -- For each relation t ∈ t, h₂(k(t)) ∈ ker(g) = im(f), so lift to X₁
    have keyt : ∀ x: t, ∃ m: S.X₁, (S.f.hom) m = h2 (k (Finsupp.single x (1 : R))) := by
      intro x
      let xval := Finsupp.single x (1 : R)
      let r := h2 (k xval)
      have : (S.g).hom r = 0 := by
        simp only [r]
        change (ModuleCat.Hom.hom S.g ∘ₗ h2) (k xval) = 0
        rw[h2prop]
        have : k xval ∈ ker π := by rw [← hk_range]; exact LinearMap.mem_range_self k xval
        simp only [coe_comp, Function.comp_apply, LinearMap.mem_ker.mp this, map_zero]
      have : ∃ y : S.X₁, (S.f).hom y = r := by
        have : r ∈ LinearMap.ker (S.g).hom := by exact this
        have : r ∈ LinearMap.range (S.f).hom := by
          exact (ShortComplex.moduleCat_exact_iff S).1 hS.exact r (LinearMap.mem_ker.mp this)
        apply this
      apply this

    choose h1' h1'prop using keyt
    let h1 : F →ₗ[R] S.X₁ := Finsupp.linearCombination R h1'
    have h1prop : ((S.f).hom).comp h1 = h2.comp k := by
      let basisF : Module.Basis ↥t R F := Finsupp.basisSingleOne
      apply Module.Basis.ext basisF
      intro x
      simp only [coe_comp, Function.comp_apply, basisF]
      have : Finsupp.basisSingleOne x = Finsupp.single x (1 : R) := by rfl
      let temp := h1'prop x
      rw[←this] at temp
      have : h1' x = h1 (Finsupp.single x (1 : R)) := by
        simp only [h1]
        simp only [Finsupp.linearCombination]
        rw [@Finsupp.lsum_apply]
        simp only [coe_smulRight, id_coe, id_eq, zero_smul, Finsupp.sum_single_index, one_smul]
      rw[this] at temp
      exact temp

    -- Apply universally_injective_lift_free to f with the commutative square
    -- F --k--> G --h₂--> X₂, F --h₁--> X₁ --f--> X₂
    have thelift : ∃ k1: G →ₗ[R] S.X₁, k1.comp k = h1 := by
       have uninjf : UniversallyInjective (S.f).hom := by exact hSUniv
       apply universially_injective_lift_free (F:=F) (G:=G) (f:=S.f.hom)
         (g:=h1) (k:=k) (h:=h2) (univf:= uninjf) (commSquare := h1prop.symm)
    obtain ⟨k1,k1prop⟩ := thelift

    -- The correction ρ = h₂ - f ∘ k₁ vanishes on im(k) = ker(π)
    let ρ := h2 - (S.f.hom).comp k1
    have rhocomp: ρ.comp k = 0 := by
      simp only [ρ]
      rw[LinearMap.sub_comp]
      rw[LinearMap.comp_assoc]
      rw[k1prop]
      rw[h1prop]
      simp only [sub_self]
    let G' := LinearMap.range k
    have : ∀ x : G', ρ x = 0 := by
      intro x
      have : ∃ y : F, k y = x := by exact x.property
      obtain ⟨y,yprop⟩ := this
      rw[←yprop]
      rw [← LinearMap.comp_apply]
      simp only [rhocomp, zero_apply]

    -- ρ descends to ρ̄ : P → X₂ via the isomorphism G / ker(π) ≅ P
    let ρbar := Submodule.liftQ G' ρ (fun x hx => this ⟨x, hx⟩)
    let theiso := LinearMap.quotKerEquivRange π
    have hG'_eq : G' = ker π := hk_range
    let theiso2 : (G ⧸ G') ≃ₗ[R] P :=
      (Submodule.quotEquivOfEq G' (ker π) hG'_eq).trans
      (π.quotKerEquivRange.trans
      (LinearEquiv.ofTop (range π) (LinearMap.range_eq_top.mpr hπ_surj)))
    let iso2rev := theiso2.symm
    let theMap := ρbar.comp iso2rev.toLinearMap
    use theMap
    have keyDiag : theMap.comp π = ρ := by
      simp only [theMap]
      simp only [iso2rev]
      ext x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      let g : G := Finsupp.single x 1
      have key : theiso2.symm (π g) = G'.mkQ g := by
        apply theiso2.injective
        rw [theiso2.apply_symm_apply]
        have step1 : (Submodule.quotEquivOfEq G' (ker π) hG'_eq) (G'.mkQ g) = (ker π).mkQ g := by
          simp only [Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk]
        have step2 : (π.quotKerEquivRange ((ker π).mkQ g) : P) = π g := by
          rw [Submodule.mkQ_apply]
          exact LinearMap.quotKerEquivRange_apply_mk π g
        have step3 : π.quotKerEquivRange ((ker π).mkQ g) =
          ⟨π g, LinearMap.mem_range_self π g⟩ := by
          ext; exact step2
        have step4 : (LinearEquiv.ofTop (range π) (LinearMap.range_eq_top.mpr hπ_surj))
             ⟨π g, LinearMap.mem_range_self π g⟩ = π g := LinearEquiv.ofTop_apply _ _
        symm
        simp only [theiso2, LinearEquiv.trans_apply]
        rw [step1]
        rw [step3, step4]
      change ρbar (theiso2.symm (π g)) = ρ g
      rw[key]
      rfl

    -- Verify g ∘ theMap = φ using the commutative diagram and the correction by f ∘ k₁
    have : (S.g.hom).comp (theMap.comp π) = φ.comp π := by
      rw[keyDiag]
      simp only [ρ]
      rw[LinearMap.comp_sub]
      have : (S.g).hom.comp (S.f).hom = 0 := by
        have := S.zero
        rw [← ModuleCat.hom_comp]
        rw[this]
        simp only [ModuleCat.hom_zero]
      rw[←LinearMap.comp_assoc]
      simp only [this, zero_comp, sub_zero]
      exact h2prop
    ext x
    have : ∃ y : G, π y = x := by apply hπ_surj
    obtain ⟨y,yprop⟩ := this
    rw[←yprop]
    exact LinearMap.congr_fun this y

/-- The R-linear isomorphism (S ⊗[R] M) ⊗[S] (S ⊗[R] Q) ≃ₗ[R] S ⊗[R] (M ⊗[R] Q),
constructed as the composite
  (S ⊗[R] M) ⊗[S] (S ⊗[R] Q)
    ≃ₗ[S] (S ⊗[R] M) ⊗[R] Q    (cancelBaseChange)
    ≃ₗ[R] S ⊗[R] (M ⊗[R] Q).   (TensorProduct.assoc)

This isomorphism is used in `UniversallyInjective.of_baseChange_faithfullyFlat` to
translate universal injectivity of f_S back to universal injectivity of f. -/
def baseChangeTensorBaseChange (R : Type u) [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S]
    (P : Type u) [AddCommGroup P] [Module R P]
    (Q : Type u) [AddCommGroup Q] [Module R Q] :
    TensorProduct S (TensorProduct R S P) (TensorProduct R S Q) ≃ₗ[R]
    TensorProduct R S (TensorProduct R P Q) := by
  -- Step 1: (S ⊗[R] P) ⊗[S] (S ⊗[R] Q) ≃ₗ[S] (S ⊗[R] P) ⊗[R] Q
  let e1 : TensorProduct S (TensorProduct R S P) (TensorProduct R S Q) ≃ₗ[S]
           TensorProduct R (TensorProduct R S P) Q :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S S (TensorProduct R S P) Q
  -- Step 2: (S ⊗[R] P) ⊗[R] Q ≃ₗ[R] S ⊗[R] (P ⊗[R] Q)
  let e2 : TensorProduct R (TensorProduct R S P) Q ≃ₗ[R]
           TensorProduct R S (TensorProduct R P Q) :=
    TensorProduct.assoc R S P Q
  exact e1.restrictScalars R ≪≫ₗ e2

/-- The naturality of `baseChangeTensorBaseChange` with respect to f : M →ₗ[R] N:
the diagram
  (S ⊗ M) ⊗[S] (S ⊗ Q)  --f_S ⊗ id-->  (S ⊗ N) ⊗[S] (S ⊗ Q)
         |                                        |
    baseChange M                             baseChange N
         |                                        |
         ↓                                        ↓
  S ⊗[R] (M ⊗ Q)  ---id ⊗ (f ⊗ id)-->  S ⊗[R] (N ⊗ Q)
commutes. This is used in `UniversallyInjective.of_baseChange_faithfullyFlat` to relate
the universal injectivity of f_S to injectivity of id_S ⊗ (f ⊗ id_Q). -/
lemma baseChangeTensorBaseChange_naturality
    {R : Type u} [CommRing R]
    {S : Type u} [CommRing S] [Algebra R S]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    {Q : Type u} [AddCommGroup Q] [Module R Q]
    (f : M →ₗ[R] N) :
    (baseChangeTensorBaseChange R S N Q).toLinearMap ∘ₗ
      (LinearMap.restrictScalars R ((f.baseChange S).rTensor (TensorProduct R S Q))) =
    (f.rTensor Q).lTensor S ∘ₗ (baseChangeTensorBaseChange R S M Q).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul sm sq =>
    induction sm using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, TensorProduct.add_tmul]
    | tmul s m =>
      induction sq using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy, TensorProduct.tmul_add]
      | tmul s' q =>
        simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
                   LinearEquiv.coe_toLinearMap, baseChangeTensorBaseChange,
                   LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply]
        simp only [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
                   LinearMap.rTensor_tmul,
                   LinearMap.baseChange_tmul]
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
        rw [TensorProduct.assoc_tmul, TensorProduct.assoc_tmul]
        simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul]

/-- If S is a faithfully flat R-algebra and the base-changed map f_S : S ⊗[R] M →ₗ[S] S ⊗[R] N
is universally injective (as an S-linear map), then f : M →ₗ[R] N is universally injective.

This is Theorem 4.2 of the paper. It is the key step in the proof of Theorem I (faithfully
flat descent of projectivity): given that S ⊗[R] P is a projective S-module, one deduces
that Hom_R(P, –) preserves surjections by showing that the natural transformation
M → Hom_R(P, M) is universally injective, then applying this theorem.

The proof: to show f ⊗ id_Q is injective, it suffices (by faithful flatness) to show
id_S ⊗ (f ⊗ id_Q) is injective. By `baseChangeTensorBaseChange_naturality`, this is
equivalent to the injectivity of f_S ⊗ id_{S ⊗ Q} (after restricting scalars), which
holds by the universal injectivity of f_S. -/
theorem UniversallyInjective.of_baseChange_faithfullyFlat
    {R : Type u} [CommRing R]
    {S : Type u} [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S]
    {M : Type u} {N : Type u}
    [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (f : M →ₗ[R] N)
    (hf : UniversallyInjective (f.baseChange S)) :
    UniversallyInjective f := by
  intro Q _ _
  -- By faithful flatness, it suffices to show id_S ⊗ (f ⊗ id_Q) is injective
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective (R := R) (M := S)]

  have t : Function.Injective ((f.baseChange S).rTensor (TensorProduct R S Q)) := hf _

  have t' : Function.Injective (LinearMap.restrictScalars R
    ((f.baseChange S).rTensor (TensorProduct R S Q))) :=
    fun _ _ hxy => t hxy

  -- By naturality of baseChangeTensorBaseChange, id_S ⊗ (f ⊗ id_Q) ∘ baseChange_M
  -- = baseChange_N ∘ (f_S ⊗ id_{S ⊗ Q})|_R, and the right-hand side is injective
  have h1 : Function.Injective ((f.rTensor Q).lTensor S ∘ₗ
      (baseChangeTensorBaseChange R S M Q).toLinearMap) := by
    rw [← baseChangeTensorBaseChange_naturality f]
    exact (baseChangeTensorBaseChange R S N Q).injective.comp t'

  -- Since baseChangeTensorBaseChange is an isomorphism, injectivity of the composite gives
  -- injectivity of id_S ⊗ (f ⊗ id_Q)
  intro x y hxy
  apply (baseChangeTensorBaseChange R S M Q).symm.injective
  apply h1
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [(baseChangeTensorBaseChange R S M Q).apply_symm_apply,
      (baseChangeTensorBaseChange R S M Q).apply_symm_apply]
  exact hxy


end LinearMap
