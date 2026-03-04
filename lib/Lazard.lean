/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liran Shaul

This file is part of the formalization "Formalization in Lean of faithfully flat descent of
projectivity."

## Overview

This file proves Lazard's theorem: a module is flat if and only if it is a filtered direct limit
of finitely generated free modules. The proof proceeds in three main steps:

1. `Module.isDirectLimit_of_finitelyPresented`: Every module is a filtered direct limit of finitely
   presented modules. The index category is the poset of pairs (J, N) where J is a finite subset
   of M and N is a finitely generated submodule of the free module R^J that maps into the kernel
   of the canonical surjection R^M → M. The filtered colimit of the quotients R^J / N recovers M.

2. `Module.Flat.directLimit`: A filtered direct limit of flat modules is flat. The proof uses the
   equational criterion for flatness (via `Module.flat_iff`) and the fact that tensor products
   commute with filtered direct limits (`TensorProduct.directLimitLeft`). Given an equation
   x = y in N ⊗ M (after embedding N ↪ P), we lift to the colimit level, use flatness of each
   G i to obtain equality at a finite stage, and conclude by injectivity of the structure maps.

3. `Module.Flat.Lazard`: The main equivalence. The forward direction (⇒) combines
   `isDirectLimit_of_finitelyPresented` with repeated application of `enlarge_to_free` to upgrade
   the index category so that every quotient R^J / N is free. The reverse direction (⇐) follows
   from `directLimit` since free modules are flat.

### Key auxiliary lemma

`Module.Flat.enlarge_to_free`: Given a flat module M and a finitely generated submodule N ≤ R^J
whose image in R^M lies in ker(R^M → M), we can enlarge J to J' and N to N' such that R^{J'}/N'
is free and N maps into N'. The construction uses `exists_factorization_of_isFinitelyPresented`
to factor the map R^J/N → M through R^k, then defines J' = J ∪ {fresh indices for basis of R^k}
and N' = ker(φ) where φ : R^{J'} → R^k is the tautological map. The section s : R^k → R^{J'}
sending basis vectors to the fresh indices shows φ is split surjective, so N' is a direct summand
of the finite free module R^{J'} and is in particular finitely generated.

### References

- Lazard, D. (1969). Epimorphismes plats, Séminaire Samuel.
- Stacks Project, Tag 058G.
- Mathlib: `Module.flat_iff`, `TensorProduct.directLimitLeft`,
  `Module.Flat.exists_factorization_of_isFinitelyPresented`.
-/

import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion


universe u

variable (R : Type u) [CommRing R]
variable (M : Type u) [AddCommGroup M] [Module R M]


set_option linter.style.longLine false


set_option maxHeartbeats 400000 in -- reaches max heartbeats below
/-- Every module is a filtered direct limit of finitely presented modules.

The index poset `E` consists of pairs `(J, N)` where `J : Finset M` is a finite subset of `M`
and `N` is a finitely generated submodule of `J →₀ R` that maps into the kernel of the canonical
map `f : M →₀ R → M`. The ordering is by simultaneous inclusion of `J` and of the image of `N`
in `M →₀ R`. Each quotient `G(J,N) = (J →₀ R) / N` is finitely presented (since `N` is FG), and
the transition maps are the natural quotient maps induced by the inclusions of `J`.

The canonical map `φ : colim G → M` sends a class `[e_m]` in `G({m}, 0)` to `m`. Injectivity:
if `φ([y]) = 0` in `G(J, N)`, then `y` lies in the kernel of `J →₀ R → M`; enlarging `N` to
`N ⊔ span{y}` gives a larger index `j ≥ i` where `[y] = 0`. Surjectivity: every `m ∈ M` is
the image of `[e_m]` from the single-element index `({m}, 0)`. -/
theorem Module.isDirectLimit_of_finitelyPresented :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (_ : DecidableEq ι)
      (G : ι → Type u) (_ : ∀ i, AddCommGroup (G i)) (_ : ∀ i, Module R (G i))
      (_ : ∀ i, Module.FinitePresentation R (G i))
      (f : ⦃i j : ι⦄ → i ≤ j → G i →ₗ[R] G j) (_ : DirectedSystem G (fun _ _ h => f h)),
      Nonempty (DirectLimit G (fun _ _ h => f h) ≃ₗ[R] M) := by

  -- The index set: M itself, with the free module R^M and its kernel K.
  let I := M
  let f : (I →₀ R) →ₗ[R] M := Finsupp.linearCombination R id
  let K := LinearMap.ker f
  -- E: pairs (J, N) with J a finite subset of M, N ≤ R^J finitely generated, image in K.
  let E := { p : (J : Finset I) × Submodule R (J →₀ R) //
    p.2.FG ∧ ∀ x ∈ p.2, Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ x ∈ K }
  -- emb: the canonical embedding R^J ↪ R^M extending indices along J ↪ M.
  let emb : (e : E) → (e.1.1 →₀ R) →ₗ[R] (I →₀ R) := fun e => Finsupp.lmapDomain R R Subtype.val
  -- The ordering: e₁ ≤ e₂ iff J₁ ⊆ J₂ and the image of N₁ in R^M lies in the image of N₂.
  let E_le : E → E → Prop := fun e₁ e₂ =>
    e₁.1.1 ⊆ e₂.1.1 ∧ Submodule.map (emb e₁) e₁.1.2 ≤ Submodule.map (emb e₂) e₂.1.2

  letI E_le_inst : LE E := ⟨E_le⟩
  letI E_lt_inst : LT E := ⟨fun a b => a ≤ b ∧ ¬b ≤ a⟩
  have E_le_refl : ∀ e : E, E_le e e := by
    intro e
    exact ⟨Finset.Subset.refl _, le_refl _⟩

  have E_le_trans : ∀ a b c : E, E_le a b → E_le b c → E_le a c := by
    intro a b c hab hbc
    exact ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩

  letI E_preorder : Preorder E := {
    le_refl := E_le_refl
    le_trans := E_le_trans
    lt_iff_le_not_ge := fun _ _ => Iff.rfl
  }

  -- The empty pair (∅, 0) is a valid index, witnessing nonemptiness.
  have E_nonempty : Nonempty E := ⟨⟨⟨∅, ⊥⟩, Submodule.fg_bot, by simp only [Submodule.mem_bot,
    forall_eq, Finsupp.embDomain_zero, zero_mem]⟩⟩
  -- Directedness: given e₁, e₂, take J = J₁ ∪ J₂ and N = im(N₁) ⊔ im(N₂) in R^J.
  have E_directed : IsDirected E (· ≤ ·) := by
    constructor
    intro e₁ e₂
    haveI : DecidableEq I := Classical.decEq I
    let J : Finset I := e₁.1.1 ∪ e₂.1.1
    let ι₁ : (↥e₁.1.1 →₀ R) →ₗ[R] (↥J →₀ R) :=
      Finsupp.lmapDomain R R (fun x => ⟨x.1, Finset.mem_union_left _ x.2⟩)
    let ι₂ : (↥e₂.1.1 →₀ R) →ₗ[R] (↥J →₀ R) :=
      Finsupp.lmapDomain R R (fun x => ⟨x.1, Finset.mem_union_right _ x.2⟩)
    let N := Submodule.map ι₁ e₁.1.2 ⊔ Submodule.map ι₂ e₂.1.2
    have hN_fg : N.FG := Submodule.FG.sup (e₁.2.1.map ι₁) (e₂.2.1.map ι₂)
    -- The combined submodule N maps into K because each summand does.
    have hN_ker : ∀ x ∈ N, Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ x ∈ K := by
      intro x hx
      rw [Submodule.mem_sup] at hx
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hx
      rw [Finsupp.embDomain_add]
      apply K.add_mem
      case h₁ =>
        rw [Submodule.mem_map] at hy₁
        obtain ⟨z₁, hz₁, rfl⟩ := hy₁
        have := e₁.2.2 z₁ hz₁
        convert this using 1
        simp only [Finsupp.embDomain_eq_mapDomain]
        rw [Finsupp.lmapDomain_apply]
        rw [←Finsupp.mapDomain_comp]
        rfl
      case h₂ =>
        rw [Submodule.mem_map] at hy₂
        obtain ⟨z₂, hz₂, rfl⟩ := hy₂
        have := e₂.2.2 z₂ hz₂
        convert this using 1
        simp only [Finsupp.embDomain_eq_mapDomain]
        rw [Finsupp.lmapDomain_apply]
        rw [← Finsupp.mapDomain_comp]
        rfl
    use ⟨⟨J, N⟩, hN_fg, hN_ker⟩
    constructor
    · constructor
      · exact Finset.subset_union_left
      · intro x hx
        rw [Submodule.mem_map] at hx ⊢
        obtain ⟨y, hy, rfl⟩ := hx
        use ι₁ y
        constructor
        · exact Submodule.mem_sup_left (Submodule.mem_map_of_mem hy)
        · simp only [emb, Finsupp.lmapDomain_apply]
          rw [Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
          rfl
    · constructor
      · exact Finset.subset_union_right
      · intro x hx
        rw [Submodule.mem_map] at hx ⊢
        obtain ⟨y, hy, rfl⟩ := hx
        use ι₂ y
        constructor
        · exact Submodule.mem_sup_right (Submodule.mem_map_of_mem hy)
        · simp only [emb, Finsupp.lmapDomain_apply]
          rw [Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
          rfl

  letI E_deceq : DecidableEq E := Classical.decEq E
  -- G(J, N) = (J →₀ R) / N, a finitely presented R-module.
  let G : E → Type u := fun e => (e.1.1 →₀ R) ⧸ e.1.2
  have G_fp : ∀ i, Module.FinitePresentation R (G i) := by
    intro i
    apply Module.finitePresentation_of_surjective (Submodule.mkQ i.1.2)
    · exact Submodule.mkQ_surjective i.1.2
    · rw [Submodule.ker_mkQ]
      exact i.2.1

  -- Transition maps: induced by the inclusion of index sets.
  let trans : ⦃i j : E⦄ → i ≤ j → G i →ₗ[R] G j := by
    intro i j hij
    let ι : (i.1.1 →₀ R) →ₗ[R] (j.1.1 →₀ R) := Finsupp.lmapDomain R R (fun x => ⟨x.1, hij.1 x.2⟩)
    apply Submodule.mapQ i.1.2 j.1.2 ι
    -- Need: ι(N_i) ≤ N_j, i.e., ι(N_i) ⊆ N_j. Use injectivity of emb j.
    intro x hx
    rw [Submodule.mem_comap]
    have h1 : emb i x ∈ Submodule.map (emb i) i.1.2 := Submodule.mem_map_of_mem hx
    have h2 : emb i x ∈ Submodule.map (emb j) j.1.2 := hij.2 h1
    rw [Submodule.mem_map] at h2
    obtain ⟨y, hy, heq⟩ := h2
    have heq2 : emb j (ι x) = emb i x := by
      simp only [emb, ι, Finsupp.lmapDomain_apply]
      rw [← Finsupp.mapDomain_comp]
      rfl
    have hinj : Function.Injective (emb j) := Finsupp.mapDomain_injective Subtype.val_injective
    have : y = ι x := hinj (heq.trans heq2.symm)
    rw [← this]
    exact hy

  have G_directed : DirectedSystem G (fun _ _ h => trans h) := by
    constructor
    · intro i x
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective i.1.2 x
      simp only [trans]
      rw [Submodule.mapQ_apply]
      congr 1
      rw [Finsupp.lmapDomain_apply]
      have : (fun x : ↥i.1.1 => ⟨x.1, (le_refl i).1 x.2⟩) = id := by
        ext ⟨val, prop⟩
        rfl
      rw[this,Finsupp.mapDomain_id]
    · intro a b c hab hbc x
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective c.1.2 x
      simp only [trans]
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.mapQ_apply]
      congr 1
      rw [Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply]
      rw [← Finsupp.mapDomain_comp]
      rfl
  refine ⟨E, E_preorder, E_directed, E_nonempty,
  E_deceq, G, inferInstance, inferInstance, G_fp, trans, G_directed, ?_⟩
  constructor
  -- The colimit map φ : colim G → M sends [e_m] ↦ m.
  let toM : ∀ e : E, G e →ₗ[R] M := by
    intro e
    apply Submodule.liftQ e.1.2 (f.comp (emb e))
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply]
    have := e.2.2 x hx
    simp only [Finsupp.embDomain_eq_mapDomain] at this
    convert this
  have toM_compat : ∀ (i j : E) (hij : i ≤ j) (x : G i), toM j (trans hij x) = toM i x := by
    intro i j hij x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective i.1.2 x
    simp only [trans, toM]
    change f.comp (emb j) ((Finsupp.lmapDomain R R fun x => ⟨x.1, hij.1 x.2⟩) x) = f.comp (emb i) x
    simp only [LinearMap.coe_comp, Function.comp_apply, emb, Finsupp.lmapDomain_apply]
    rw [← Finsupp.mapDomain_comp]
    rfl
  let φ : DirectLimit G (fun _ _ h => trans h) →ₗ[R] M :=
    DirectLimit.lift R E G (fun _ _ h => trans h) toM toM_compat
  have φ_bij : Function.Bijective φ := by
    constructor
    · -- Injectivity: if φ([y]) = 0 at stage i, enlarge N to N ⊔ span{y'} to kill [y'].
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨i, y, rfl⟩ := DirectLimit.exists_of x
      simp only [φ, DirectLimit.lift_of] at hx
      obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective i.1.2 y
      simp only [toM] at hx
      rw [Submodule.liftQ_apply, LinearMap.coe_comp, Function.comp_apply] at hx
      -- y' maps to 0 in M, so emb i y' ∈ K.
      have hy'_in_K : emb i y' ∈ K := by
        rw [LinearMap.mem_ker]
        exact hx

      -- Enlarge N to newSub = N ⊔ span{y'}; this is still FG and maps into K.
      let newSub := i.1.2 ⊔ Submodule.span R {y'}
      have newSub_fg : newSub.FG := Submodule.FG.sup i.2.1 (Submodule.fg_span_singleton y')
      have newSub_in_K : ∀ x ∈ newSub,
        Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ x ∈ K := by
        intro x hx'
        rw [Submodule.mem_sup] at hx'
        obtain ⟨a, ha, b, hb, rfl⟩ := hx'
        rw [Finsupp.embDomain_add]
        apply K.add_mem
        · exact i.2.2 a ha
        · rw [Submodule.mem_span_singleton] at hb
          obtain ⟨r, rfl⟩ := hb
          rw [Finsupp.embDomain_eq_mapDomain, Finsupp.mapDomain_smul]
          apply Submodule.smul_mem
          rw [← Finsupp.embDomain_eq_mapDomain]
          convert hy'_in_K using 1
          simp only [emb, Finsupp.lmapDomain_apply, Finsupp.embDomain_eq_mapDomain]
          rfl

      -- j = (i.J, newSub) is a valid larger index, and [y'] = 0 in G(j).
      let j : E := ⟨⟨i.1.1, newSub⟩, newSub_fg, newSub_in_K⟩
      have hij : i ≤ j := ⟨Finset.Subset.refl _, Submodule.map_mono le_sup_left⟩

      -- trans(hij)([y']) = 0 because y' ∈ newSub (as a generator of the enlarged part).
      have htrans_zero : trans hij (Submodule.Quotient.mk y') = 0 := by
        simp only [trans]
        rw [Submodule.mapQ_apply]
        rw [Submodule.Quotient.mk_eq_zero]
        change (Finsupp.lmapDomain R R fun x => ⟨↑x, hij.1 x.2⟩) y' ∈ newSub
        apply Submodule.mem_sup_right
        rw [Submodule.mem_span_singleton]
        use 1
        rw [one_smul]
        simp only [Finsupp.lmapDomain_apply]
        -- The index renaming is the identity on the underlying elements.
        have : Finsupp.mapDomain (fun x => ⟨↑x, hij.1 x.2⟩) y' = y' := by
          apply Finsupp.ext
          intro a
          classical
          simp only [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.single_apply]
          rw [Finsupp.sum, Finset.sum_eq_single a]
          · simp only [ite_true]
          · intro b _ hne
            rw [if_neg]
            intro h
            apply hne
            cases a
            cases b
            simp_all only [Finsupp.mem_support_iff, ne_eq, not_true_eq_false]
          · intro ha
            rw [Finsupp.notMem_support_iff] at ha
            simp only [Subtype.coe_eta, ↓reduceIte, ha]
        exact this.symm

      have := @Module.DirectLimit.of_f R _ E E_preorder G E_deceq _ _ (fun i j h => trans h)
        i j hij (Submodule.Quotient.mk y')
      rw [this.symm, htrans_zero, map_zero]

    · -- Surjectivity: m is in the image of G({m}, 0) via the basis element e_m.
      intro m
      let e : E := ⟨⟨{m}, ⊥⟩, Submodule.fg_bot, by simp⟩
      let x : G e := Submodule.Quotient.mk (Finsupp.single ⟨m, Finset.mem_singleton_self m⟩ 1)
      use DirectLimit.of R E G (fun _ _ h => trans h) e x
      simp only [φ, DirectLimit.lift_of, toM]
      rw [Submodule.liftQ_apply]
      simp only [LinearMap.coe_comp, Function.comp_apply, emb, Finsupp.lmapDomain_apply]
      simp only [Finsupp.mapDomain_single, f, Finsupp.linearCombination_single, one_smul, id_eq]

  exact LinearEquiv.ofBijective φ φ_bij


/-- Direct limits of flat modules are flat.

The proof uses the equational criterion for flatness (`Module.flat_iff`): it suffices to show
that if two elements of N ⊗ M are equal after applying `N.subtype ⊗ id_M : N ⊗ M → P ⊗ M`,
then they are already equal in N ⊗ M.

The key is to commute tensor products with the filtered direct limit. Using
`TensorProduct.directLimitLeft`, we have:
  M ⊗ N ≅ colim (G i ⊗ N)    and    M ⊗ P ≅ colim (G i ⊗ P).

The map `N.subtype` induces a natural transformation `ih i : G i ⊗ N → G i ⊗ P`, and these
assemble into a map `liftNP : colim(G i ⊗ N) → colim(G i ⊗ P)`. Injectivity of `liftNP`
is proved by lifting to a common stage k and applying injectivity of `ih k` (which holds because
each `G k` is flat). -/
lemma Module.Flat.directLimit
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] [DecidableEq ι]
    (G : ι → Type u) [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    [∀ i, Module.Flat R (G i)]
    (f : ⦃i j : ι⦄ → i ≤ j → G i →ₗ[R] G j) [DirectedSystem G (fun _ _ h => f h)] :
    Module.Flat R (DirectLimit G (fun _ _ h => f h)) := by
  classical
  rw[Module.flat_iff]
  intro P _ _ _ N _ x y hxy
  let M := Module.DirectLimit G (fun i j h => f h)
  -- Swap isomorphisms: reorder the tensor factors.
  let swapN : TensorProduct R N M ≃ₗ[R] TensorProduct R M N := TensorProduct.comm R N M
  let swapP : TensorProduct R P M ≃ₗ[R] TensorProduct R M P := TensorProduct.comm R P M
  -- Colimit decompositions via directLimitLeft.
  let eN : TensorProduct R M N ≃ₗ[R]
    Module.DirectLimit (fun i => TensorProduct R (G i) N) (fun i j h => LinearMap.rTensor (↥N) (f h)) :=
    TensorProduct.directLimitLeft (fun i j h => f h) (↥N)
  let eP : TensorProduct R M P ≃ₗ[R]
    Module.DirectLimit (fun i => TensorProduct R (G i) P) (fun i j h => LinearMap.rTensor P (f h)) :=
    TensorProduct.directLimitLeft (fun i j h => f h) P
  -- rw_key: the inclusion N ↪ P commutes with the colimit decomposition at each stage.
  have rw_key (i : ι) (g : G i) (n : ↥N) :
      eP (swapP ((LinearMap.rTensor M N.subtype)
        (n ⊗ₜ[R] (Module.DirectLimit.of R ι G (fun i j h => f h) i g))))
      =
      (Module.DirectLimit.of R ι (fun i => TensorProduct R (G i) P)
        (fun i j h => LinearMap.rTensor P (f h)) i)
        (g ⊗ₜ[R] (N.subtype n)) := by
    simp only [LinearMap.rTensor_tmul]
    rw [TensorProduct.comm_tmul]
    rw [TensorProduct.directLimitLeft_tmul_of
      (R := R) (ι := ι) (G := G)
      (f := fun i j h => f h)
      (M := P)
      (i := i) (g := g) (m := (N.subtype n))]
  -- ih i: the map G i ⊗ N → G i ⊗ P induced by N ↪ P.
  let ih : ∀ i, TensorProduct R (G i) N →ₗ[R] TensorProduct R (G i) P :=
    fun i => LinearMap.lTensor (G i) (N.subtype)
  -- compat: ih is natural, i.e., rTensor commutes with lTensor.
  have compat :
    ∀ i j (hij : i ≤ j),
      (LinearMap.rTensor P (f hij)).comp (ih i) =
        (ih j).comp (LinearMap.rTensor (↥N) (f hij)) := by
    intro i j hij
    ext g n
    simp only [ih, LinearMap.rTensor_comp_lTensor,
      TensorProduct.AlgebraTensorModule.curry_apply,
      LinearMap.restrictScalars_self, TensorProduct.curry_apply,
      TensorProduct.map_tmul, Submodule.subtype_apply,
      LinearMap.lTensor_comp_rTensor]
  -- liftNP: the induced map colim(G i ⊗ N) → colim(G i ⊗ P).
  let liftNP :
    (Module.DirectLimit (fun i => TensorProduct R (G i) ↥N)
      (fun i j h => LinearMap.rTensor (↥N) (f h)))
      →ₗ[R]
    (Module.DirectLimit (fun i => TensorProduct R (G i) P)
      (fun i j h => LinearMap.rTensor P (f h))) :=
    Module.DirectLimit.lift R ι
      (fun i => TensorProduct R (G i) ↥N)
      (fun i j hij => LinearMap.rTensor (↥N) (f hij))
      (fun i =>
        (Module.DirectLimit.of R ι (fun i => TensorProduct R (G i) P)
          (fun i j h => LinearMap.rTensor P (f h)) i).comp (ih i))
      (by
        intro i j hij z
        simp only [LinearMap.coe_comp, Function.comp_apply]
        have hz' :
          (ih j) ((LinearMap.rTensor (↥N) (f hij)) z)
            = (LinearMap.rTensor P (f hij)) ((ih i) z) := by
          have h := congrArg (fun L => L z) (compat i j hij)
          dsimp only [LinearMap.comp_apply] at h
          exact h.symm
        rw [hz']
        have h :=
          Module.DirectLimit.of_f (R := R) (ι := ι)
            (G := fun i => TensorProduct R (G i) P)
            (f := fun i j h => LinearMap.rTensor P (f h))
            (i := i) (j := j) (hij := hij)
            (x := (ih i) z)
        exact h)
  -- ΦN, ΦP: the composites N ⊗ M → colim(G i ⊗ N) and P ⊗ M → colim(G i ⊗ P).
  let ΦN : TensorProduct R (↥N) M →
      DirectLimit (fun i ↦ TensorProduct R (G i) (↥N))
        (fun i j h ↦ LinearMap.rTensor (↥N) (f h)) :=
    fun z => eN (swapN z)
  let ΦP : TensorProduct R P M →
      DirectLimit (fun i ↦ TensorProduct R (G i) P)
        (fun i j h ↦ LinearMap.rTensor P (f h)) :=
    fun z => eP (swapP z)
  -- comm_all: ΦP ∘ (N.subtype ⊗ id) = liftNP ∘ ΦN, proved by induction on tensors.
  have comm_all :
      ∀ z,
        ΦP ((LinearMap.rTensor M N.subtype) z) = liftNP (ΦN z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
        simp only [map_zero, ΦP, ΦN]
    | add z₁ z₂ hz₁ hz₂ =>
        simp only [map_add, hz₁, hz₂, ΦP, ΦN]
    | tmul n m =>
        refine Module.DirectLimit.induction_on (R := R) (ι := ι) (G := G)
          (f := fun i j hij => f hij) (z := m) ?_
        intro i g
        dsimp only [LinearMap.rTensor_tmul, Submodule.subtype_apply, ΦP, ΦN]
        have hL :
            (↑n ⊗ₜ[R] (DirectLimit.of R ι G (fun i j hij ↦ f hij) i) g)
              =
            (LinearMap.rTensor M N.subtype)
              (n ⊗ₜ[R] (DirectLimit.of R ι G (fun i j hij ↦ f hij) i) g) := by
          simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply]
        rw [hL]
        have hN :
          eN (swapN (n ⊗ₜ[R] (DirectLimit.of R ι G (fun i j hij ↦ f hij) i) g))
            =
          (DirectLimit.of R ι (fun i ↦ TensorProduct R (G i) (↥N))
            (fun i j hij ↦ LinearMap.rTensor (↥N) (f hij)) i)
            (g ⊗ₜ[R] n) := by
          dsimp only [TensorProduct.comm_tmul, eN, swapN]
          rw [TensorProduct.directLimitLeft_tmul_of
            (R := R) (ι := ι) (G := G)
            (f := fun i j hij ↦ f hij)
            (M := (↥N))
            (i := i) (g := g) (m := n)]
        rw [hN]
        dsimp only [LinearMap.rTensor_tmul, Submodule.subtype_apply, liftNP]
        rw [Module.DirectLimit.lift_of]
        have hih :
            (ih i) (g ⊗ₜ[R] n) = (g ⊗ₜ[R] N.subtype n) := by
          dsimp only [LinearMap.lTensor_tmul, Submodule.subtype_apply, ih]
        simp only [LinearMap.comp_apply]
        rw [hih]
        exact rw_key i g n
  -- Transfer the hypothesis x = y across the commutative square to liftNP level.
  have hcolim : liftNP (ΦN x) = liftNP (ΦN y) := by
    have := congrArg (fun z => ΦP z) hxy
    have hx : ΦP ((LinearMap.rTensor M N.subtype) x) = liftNP (ΦN x) := comm_all x
    have hy : ΦP ((LinearMap.rTensor M N.subtype) y) = liftNP (ΦN y) := comm_all y
    calc
      liftNP (ΦN x) = ΦP ((LinearMap.rTensor M N.subtype) x) := hx.symm
      _ = ΦP ((LinearMap.rTensor M N.subtype) y) := this
      _ = liftNP (ΦN y) := hy
  -- ΦN is injective because swapN and eN are both equivalences.
  have hΦN_inj : Function.Injective ΦN := by
    intro a b hab
    apply (show Function.Injective swapN from swapN.injective)
    apply (show Function.Injective eN from eN.injective)
    exact hab
  -- N.subtype is injective (N is a submodule of P).
  have ninj : Function.Injective (N.subtype : (↥N →ₗ[R] P)) :=
    Submodule.injective_subtype N
  -- ih i is injective at each stage because G i is flat (flatness = lTensor preserves injections).
  have hih_inj : ∀ i : ι, Function.Injective (ih i) := by
    intro i
    have h :=
      (Module.Flat.lTensor_preserves_injective_linearMap
        (R := R) (M := G i)
        (f := (N.subtype : (↥N →ₗ[R] P))) ninj)
    change Function.Injective ⇑(LinearMap.lTensor (G i) N.subtype)
    exact h
  -- Reduce to injectivity of liftNP.
  have finish_of_liftNP_inj
      (hliftNP_inj : Function.Injective liftNP) : x = y := by
    have hΦN : ΦN x = ΦN y := hliftNP_inj hcolim
    exact hΦN_inj hΦN
  -- Injectivity of liftNP: reduce to a common stage k, apply ih k injectivity there.
  have hliftNP_inj : Function.Injective liftNP := by
    classical
    intro u v huv
    let GN : ι → Type u := fun i => TensorProduct R (G i) ↥N
    let fN : ⦃i j : ι⦄ → i ≤ j → GN i →ₗ[R] GN j :=
      fun i j hij => LinearMap.rTensor (↥N) (f hij)
    let GP : ι → Type u := fun i => TensorProduct R (G i) P
    let fP : ⦃i j : ι⦄ → i ≤ j → GP i →ₗ[R] GP j :=
      fun i j hij => LinearMap.rTensor P (f hij)
    let ofN : (i : ι) → GN i →ₗ[R] Module.DirectLimit GN (fun i j hij => fN hij) :=
      fun i => Module.DirectLimit.of R ι GN (fun i j hij => fN hij) i
    let ofP : (i : ι) → GP i →ₗ[R] Module.DirectLimit GP (fun i j hij => fP hij) :=
      fun i => Module.DirectLimit.of R ι GP (fun i j hij => fP hij) i
    -- Represent u, v as elements from individual stages i, j; find a common upper bound k.
    revert v
    refine Module.DirectLimit.induction_on (R := R) (ι := ι) (G := GN)
      (f := fun i j hij => fN hij) (z := u) ?_
    intro i ui v
    refine Module.DirectLimit.induction_on (R := R) (ι := ι) (G := GN)
      (f := fun i j hij => fN hij) (z := v) ?_
    intro j y huv
    have : IsDirected ι fun x1 x2 ↦ x1 ≤ x2 := by infer_instance
    rcases (this.directed i j) with ⟨k, hik, hjk⟩
    -- huv implies the images under ih agree at the colimit level.
    have huv' :
        (ofP i) ((ih i) ui) = (ofP j) ((ih j) y) := by
      have huv1 :
          liftNP ((Module.DirectLimit.of R ι GN (fun a b hab => fN hab) i) ui) =
            liftNP ((Module.DirectLimit.of R ι GN (fun a b hab => fN hab) j) y) := by
        simpa only [ofN] using huv
      have hl :
          liftNP ((Module.DirectLimit.of R ι GN (fun a b hab => fN hab) i) ui) =
            (Module.DirectLimit.of R ι GP (fun a b hab => fP hab) i) ((ih i) ui) := by
        simp only [liftNP, GN, GP, fN, fP, ih]
        simp only [DirectLimit.lift_of, LinearMap.coe_comp, Function.comp_apply]
      have hr :
          liftNP ((Module.DirectLimit.of R ι GN (fun a b hab => fN hab) j) y) =
            (Module.DirectLimit.of R ι GP (fun a b hab => fP hab) j) ((ih j) y) := by
        simp only [liftNP, GN, GP, fN, fP, ih]
        simp only [DirectLimit.lift_of, LinearMap.coe_comp, Function.comp_apply]
      calc
        (ofP i) ((ih i) ui)
            = liftNP ((Module.DirectLimit.of R ι GN (fun a b hab => fN hab) i) ui) := hl.symm
        _ = liftNP ((Module.DirectLimit.of R ι GN (fun a b hab => fN hab) j) y) := huv1
        _ = (ofP j) ((ih j) y) := hr
    -- Lift to the common stage k; images under fP agree there.
    have hk0 :
        (ofP k) ((fP hik) ((ih i) ui)) =
          (ofP k) ((fP hjk) ((ih j) y)) := by
      calc
        (ofP k) ((fP hik) ((ih i) ui))
            = (ofP i) ((ih i) ui) := by
              simp only [ofP, fP, DirectLimit.of_f]
        _ = (ofP j) ((ih j) y) := huv'
        _ = (ofP k) ((fP hjk) ((ih j) y)) := by
              simp only [ofP, fP, DirectLimit.of_f]
    -- By exists_eq_of_of_eq, there is a further stage l where they agree exactly.
    rcases (Module.DirectLimit.exists_eq_of_of_eq (R := R) (ι := ι) (G := GP)
      (f := fun a b hab => fP hab) (i := k) hk0) with ⟨l, hkl, hkl_eq⟩
    -- Naturality of ih: fP ∘ ih = ih ∘ fN at each stage.
    have hk_left :
        (fP hik) ((ih i) ui) = (ih k) ((fN hik) ui) := by
      have h := congrArg (fun L => L ui) (compat i k hik)
      simp only [LinearMap.comp_apply] at h
      exact h
    have hk_right :
        (fP hjk) ((ih j) y) = (ih k) ((fN hjk) y) := by
      have h := congrArg (fun L => L y) (compat j k hjk)
      simp only [LinearMap.comp_apply] at h
      exact h
    have hl_left :
        (fP hkl) ((ih k) ((fN hik) ui)) =
          (ih l) ((fN hkl) ((fN hik) ui)) := by
      have := congrArg (fun L => L ((fN hik) ui)) (compat k l hkl)
      simpa only [LinearMap.comp_apply, fN, fP] using this
    have hl_right :
        (fP hkl) ((ih k) ((fN hjk) y)) =
          (ih l) ((fN hkl) ((fN hjk) y)) := by
      have := congrArg (fun L => L ((fN hjk) y)) (compat k l hkl)
      simpa only [LinearMap.comp_apply, fN, fP] using this
    have hkl_eq' :
        (fP hkl) ((ih k) ((fN hik) ui)) =
          (fP hkl) ((ih k) ((fN hjk) y)) := by
      simpa only [hk_left, hk_right] using hkl_eq
    -- Use injectivity of ih l to conclude fN hkl commutes with equality.
    have hNl :
        (fN hkl) ((fN hik) ui) = (fN hkl) ((fN hjk) y) := by
      have h1 :
          (ih l) ((fN hkl) ((fN hik) ui)) =
            (ih l) ((fN hkl) ((fN hjk) y)) := by
        calc
          (ih l) ((fN hkl) ((fN hik) ui))
              = (fP hkl) ((ih k) ((fN hik) ui)) := by
                simpa using hl_left.symm
          _ = (fP hkl) ((ih k) ((fN hjk) y)) := hkl_eq'
          _ = (ih l) ((fN hkl) ((fN hjk) y)) := by
                simpa using hl_right
      exact (hih_inj l) h1
    -- Assemble: ofN i ui = ofN l (...) = ofN j y by transitivity through l.
    have h_of_i :
        (ofN i) ui = (ofN l) ((fN hkl) ((fN hik) ui)) := by
      calc
        (ofN i) ui = (ofN k) ((fN hik) ui) := by
          have h :=
            (Module.DirectLimit.of_f (R := R) (ι := ι) (G := GN)
              (f := fun a b hab => fN hab) (i := i) (j := k)
              (hij := hik) (x := ui)).symm
          simp only [fN] at h
          exact h
        _ = (ofN l) ((fN hkl) ((fN hik) ui)) := by
          have h :=
            (Module.DirectLimit.of_f (R := R) (ι := ι) (G := GN)
              (f := fun a b hab => fN hab) (i := k) (j := l)
              (hij := hkl) (x := (fN hik) ui)).symm
          simp only [fN] at h
          exact h
    have h_of_j :
        (ofN j) y = (ofN l) ((fN hkl) ((fN hjk) y)) := by
      calc
        (ofN j) y = (ofN k) ((fN hjk) y) := by
          have h :=
            (Module.DirectLimit.of_f (R := R) (ι := ι) (G := GN)
              (f := fun a b hab => fN hab) (i := j) (j := k)
              (hij := hjk) (x := y)).symm
          simp only [fN] at h
          exact h
        _ = (ofN l) ((fN hkl) ((fN hjk) y)) := by
          have h :=
            (Module.DirectLimit.of_f (R := R) (ι := ι) (G := GN)
              (f := fun a b hab => fN hab) (i := k) (j := l)
              (hij := hkl) (x := (fN hjk) y)).symm
          simp only [fN] at h
          exact h
    have h_of_l :
        (ofN l) ((fN hkl) ((fN hik) ui)) =
          (ofN l) ((fN hkl) ((fN hjk) y)) :=
      congrArg (fun t => (ofN l) t) hNl
    calc
      (ofN i) ui = (ofN l) ((fN hkl) ((fN hik) ui)) := h_of_i
      _ = (ofN l) ((fN hkl) ((fN hjk) y)) := h_of_l
      _ = (ofN j) y := h_of_j.symm
  exact finish_of_liftNP_inj hliftNP_inj


set_option maxHeartbeats 600000 in -- reaches max heartbeats below
/-- Given a flat module M and a finitely generated submodule N ≤ R^J whose elements map into
`ker(R^{M×ℤ} → M)`, we can enlarge J to a finite set J' and N to N' ≤ R^{J'} such that:
- J ⊆ J',
- N' is finitely generated and still maps into the kernel,
- R^{J'} / N' is free,
- the image of N in R^{J'} lands in N'.

### Construction

Since M is flat and R^J / N is finitely presented, `exists_factorization_of_isFinitelyPresented`
gives a factorization R^J/N → R^k → M of the natural map R^J/N → M. We introduce k fresh index
points `freshIdx 0, …, freshIdx (k-1)` in M × ℤ (with ℤ-coordinates above the maximum already
in J, ensuring they are new) and set J' = J ∪ {freshIdx i}. Define φ : R^{J'} → R^k by:
  - on a basis vector e_{j'} with j' ∈ J: apply h (the factorization map) to [e_{j'}],
  - on a basis vector e_{freshIdx i}: map to e_i.

The section s : R^k → R^{J'} sending e_i ↦ e_{freshIdx i} satisfies φ ∘ s = id, so φ is
split surjective. Setting N' = ker φ, the quotient R^{J'}/N' ≅ R^k is free.
Finite generation of N' follows because N' = im(id - s ∘ φ) is the image of a linear map from
the finitely generated module R^{J'}.

The compatibility N → N' holds because φ ∘ inc = h ∘ mkQ and N maps to 0 in R^J/N. -/
lemma Module.Flat.enlarge_to_free [Module.Flat R M]
    {J : Finset (M × ℤ)} {N : Submodule R (J →₀ R)} (hN : N.FG)
    (hN_ker : ∀ x ∈ N, Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ x ∈
      LinearMap.ker (Finsupp.linearCombination R (Prod.fst : M × ℤ → M))) :
    ∃ (J' : Finset (M × ℤ)) (hJJ' : J ⊆ J') (N' : Submodule R (J' →₀ R)) (_ : N'.FG),
      (∀ x ∈ N', Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ x ∈
        LinearMap.ker (Finsupp.linearCombination R (Prod.fst : M × ℤ → M))) ∧
      Module.Free R ((J' →₀ R) ⧸ N') ∧
      ∀ x ∈ N, Finsupp.lmapDomain R R (fun i => ⟨i.1, hJJ' i.2⟩) x ∈ N' := by
  classical

  -- Step 1: (J →₀ R) / N is finitely presented
  let Q := (J →₀ R) ⧸ N
  haveI : Module.FinitePresentation R Q :=
    Module.finitePresentation_of_surjective (Submodule.mkQ N)
      (Submodule.mkQ_surjective N) (by rw [Submodule.ker_mkQ]; exact hN)

  -- Step 2: The natural map to M
  let f_e : Q →ₗ[R] M := Submodule.liftQ N
    ((Finsupp.linearCombination R Prod.fst).comp (Finsupp.lmapDomain R R Subtype.val))
    (by
      intro x hx
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply]
      have := hN_ker x hx
      simp only [LinearMap.mem_ker, Finsupp.embDomain_eq_mapDomain] at this
      exact this)

  -- Step 3: Apply factorization theorem
  -- Flatness of M gives h : Q → R^k and g : R^k → M with g ∘ h = f_e.
  obtain ⟨k, h, g, hfac⟩ := Module.Flat.exists_factorization_of_isFinitelyPresented f_e

  -- Step 4: Pick k fresh indices in M × ℤ not already in J.
  -- maxZ is the maximum ℤ-coordinate in J (or 0 if J is empty).
  let maxZ : ℤ := if hJ : J.Nonempty then (J.image Prod.snd).max' (Finset.image_nonempty.mpr hJ) else 0

  -- Each fresh index has M-component = g(e_i) and ℤ-coordinate = maxZ + 1 + i, ensuring freshness.
  let freshIdx : Fin k → M × ℤ := fun i => (g (Finsupp.single i 1), maxZ + 1 + i)

  -- The fresh indices are not in J (their ℤ-coordinates exceed maxZ).
  have fresh_not_in_J : ∀ i, freshIdx i ∉ J := by
    intro i hi
    have : (freshIdx i).2 ≤ maxZ := by
      simp only [maxZ]
      split_ifs with hJ
      · exact Finset.le_max' _ _ (Finset.mem_image_of_mem Prod.snd hi)
      · exact (hJ ⟨freshIdx i, hi⟩).elim
    simp only [freshIdx] at this
    omega

  -- The fresh index map is injective (strictly increasing ℤ-coordinates).
  have fresh_inj : Function.Injective freshIdx := by
    intro i j hij
    simp only [freshIdx, Prod.mk.injEq] at hij
    omega

  -- Step 5: Define J' = J ∪ {freshIdx i | i < k}.
  let newIndices : Finset (M × ℤ) := Finset.univ.image freshIdx
  let J' := J ∪ newIndices
  have hJJ' : J ⊆ J' := Finset.subset_union_left

  have freshIdx_mem : ∀ i, freshIdx i ∈ J' := by
    intro i
    apply Finset.mem_union_right
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)

  -- Inverse of freshIdx on newIndices: for each new index, recover the Fin k it came from.
  let invFreshIdx : ∀ x ∈ newIndices, Fin k := fun x hx => by
    simp only [newIndices, Finset.mem_image, Finset.mem_univ, true_and] at hx
    exact hx.choose

  have invFreshIdx_spec : ∀ x (hx : x ∈ newIndices), freshIdx (invFreshIdx x hx) = x := by
    intro x hx
    simp only [invFreshIdx]
    have hx' : ∃ a, freshIdx a = x := by
      simp only [newIndices, Finset.mem_image, Finset.mem_univ, true_and] at hx
      exact hx
    exact hx'.choose_spec

  -- Step 6: Define φ : R^{J'} → R^k.
  -- On old indices j ∈ J: send e_j to h([e_j]) ∈ R^k (using the factorization).
  -- On new indices freshIdx i: send e_{freshIdx i} to e_i.
  let φ : (J' →₀ R) →ₗ[R] (Fin k →₀ R) :=
    Finsupp.linearCombination R (fun j' : J' =>
      if hj : j'.1 ∈ J
      then h (Submodule.Quotient.mk (Finsupp.single ⟨j'.1, hj⟩ 1))
      else
        have hj' : j'.1 ∈ newIndices := by
          have := j'.2
          simp only [J', Finset.mem_union] at this
          exact this.resolve_left hj
        Finsupp.single (invFreshIdx j'.1 hj') 1)

  -- Step 7: Let N' = ker(φ).
  let N' := LinearMap.ker φ

  -- Section: s : R^k → R^{J'} sends e_i to e_{freshIdx i}.
  let s : (Fin k →₀ R) →ₗ[R] (J' →₀ R) :=
    Finsupp.linearCombination R (fun i => Finsupp.single ⟨freshIdx i, freshIdx_mem i⟩ 1)

  -- φ ∘ s = id: the section is a right inverse to φ.
  have φ_s_eq_id : φ.comp s = LinearMap.id := by
    ext i a
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply]

    -- Force Lean to see the types of the 1s clearly
    let r1 : R := 1
    let e_i : Fin k →₀ R := Finsupp.single i r1

    -- Prove the bridge lemma using explicit types
    have he_i_lsingle : (Finsupp.lsingle i : R →ₗ[R] Fin k →₀ R) r1 = e_i := by
      simp only [e_i, r1, Finsupp.lsingle_apply]

    set e_i : Fin k →₀ R := Finsupp.single i 1 with he_i
    have hs : s e_i = Finsupp.single ⟨freshIdx i, freshIdx_mem i⟩ 1 := by
      simp only [s]
      rw [he_i, Finsupp.linearCombination_single]
      simp only [one_smul]

    -- φ(e_{freshIdx i}) = e_i because freshIdx i ∉ J, so φ uses the invFreshIdx branch.
    have hφ : φ (Finsupp.single ⟨freshIdx i, freshIdx_mem i⟩ 1) = e_i := by
      simp only [φ]
      rw [Finsupp.linearCombination_single]
      have h_not_in_J : ¬(⟨freshIdx i, freshIdx_mem i⟩ : {x // x ∈ J'}).1 ∈ J := fresh_not_in_J i
      simp only [h_not_in_J, dite_false]
      rw [one_smul]
      rw [he_i]
      congr
      apply fresh_inj
      rw [invFreshIdx_spec]
      exact Finset.mem_image_of_mem freshIdx (Finset.mem_univ i)
    rw [he_i_lsingle]
    rw [hs]
    rw [hφ]

  have φ_surj : Function.Surjective φ := by
    apply Function.RightInverse.surjective
    · intro x
      exact LinearMap.congr_fun φ_s_eq_id x

  -- Step 8: Verify the conditions.

  -- N' is FG: it equals the image of the projection p = id - s ∘ φ, which is a linear map
  -- from the finitely generated module R^{J'}.
  have hN'_fg : N'.FG := by
    let p := LinearMap.id - s.comp φ
    have hp_range : LinearMap.range p = N' := by
      ext x
      simp only [p, N', LinearMap.mem_ker, LinearMap.mem_range, LinearMap.sub_apply,
        LinearMap.id_apply, LinearMap.coe_comp, Function.comp_apply]
      constructor
      · rintro ⟨y, rfl⟩
        -- φ(y - s(φ(y))) = φ(y) - φ(s(φ(y))) = φ(y) - φ(y) = 0
        rw[LinearMap.map_sub]
        have : ∀ x : (Fin k →₀ R), φ (s x) = x := by
          intro x
          simpa [LinearMap.comp_apply] using (LinearMap.congr_fun φ_s_eq_id x)
        have : φ (s (φ y)) = φ y := by apply this
        rw[this]
        simp only [sub_self]
      · intro hx
        use x
        rw [hx, map_zero, sub_zero]
    rw [← hp_range]
    haveI : Module.Finite R (J' →₀ R) := Module.Finite.finsupp
    exact Module.Finite.iff_fg.mp (Module.Finite.range p)

  -- N' maps into ker(R^{M×ℤ} → M): use that f_M = g ∘ φ and ker(φ) ⊆ ker(f_M).
  have hN'_ker : ∀ x ∈ N', Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ x ∈
      LinearMap.ker (Finsupp.linearCombination R (Prod.fst : M × ℤ → M)) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    simp only [LinearMap.mem_ker, Finsupp.linearCombination_apply, Finsupp.sum_embDomain]
    let f_M := Finsupp.linearCombination R (fun (j' : ↥J') => (j' : M × ℤ).1)
    change f_M x = 0
    -- Key identity: f_M = g ∘ φ. Proved basis-by-basis using the factorization hfac.
    have h_map_eq : f_M = g ∘ₗ φ := by
      apply Finsupp.lhom_ext
      intro j'
      simp only [LinearMap.coe_comp, Function.comp_apply, f_M]
      intro b
      simp only [φ, Finsupp.linearCombination_single, LinearMap.map_smul]
      congr 1
      split_ifs with hj
      · -- Old index: j' ∈ J. Use hfac: g ∘ h = f_e, so g(h([e_{j'}])) = (j' : M×ℤ).fst.
        have h_eval := LinearMap.congr_fun hfac (Submodule.Quotient.mk (Finsupp.single ⟨↑j', hj⟩ 1))
        rw [← LinearMap.comp_apply]
        rw [← h_eval]
        rw [Submodule.liftQ_apply]
        simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lmapDomain_apply,
                 Finsupp.mapDomain_single, Finsupp.linearCombination_single, one_smul]
      · -- New index: j' = freshIdx i. Then g(e_i) = (freshIdx i).fst by definition.
        have hj' : ↑j' ∈ newIndices := by
          have h_mem := j'.2
          simp only [J', Finset.mem_union] at h_mem
          cases h_mem with
          | inl h_in_J => contradiction
          | inr h_in_new => exact h_in_new
        have h_inv := invFreshIdx_spec (↑j') hj'
        nth_rw 1 [← h_inv]
    rw [h_map_eq]
    simp [hx]

  -- R^{J'} / N' ≅ R^k is free (split surjection φ induces the isomorphism).
  have hN'_free : Module.Free R ((J' →₀ R) ⧸ N') := by
    let iso := LinearMap.quotKerEquivOfSurjective φ φ_surj
    exact Module.Free.of_equiv iso.symm

  -- The inclusion N → N': φ ∘ inc = h ∘ mkQ, and N maps to 0 under mkQ.
  have hN_sub : ∀ x ∈ N, Finsupp.lmapDomain R R (fun i => ⟨i.1, hJJ' i.2⟩) x ∈ N' := by
    intro x hx
    rw [LinearMap.mem_ker]
    let inc : (J →₀ R) →ₗ[R] (J' →₀ R) := Finsupp.lmapDomain R R (fun i => ⟨i.1, hJJ' i.2⟩)
    -- φ ∘ inc = h ∘ mkQ: verified basis-by-basis.
    have h_comm : φ.comp inc = h.comp (Submodule.mkQ N) := by
      apply Finsupp.lhom_ext
      intro j b
      simp only [LinearMap.coe_comp, Function.comp_apply, inc]
      rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      rw [Finsupp.linearCombination_single]
      rw [Submodule.mkQ_apply]
      dsimp only [SetLike.coe_mem, SetLike.eta, Lean.Elab.WF.paramLet]
      have hj_in_J : ↑j ∈ J := j.2
      split_ifs
      rw [← h.map_smul, ← Submodule.Quotient.mk_smul]
      rw [Finsupp.smul_single]
      rw [smul_eq_mul, mul_one]
    rw [← LinearMap.comp_apply, h_comm]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    -- x ∈ N implies [x] = 0 in Q = R^J / N.
    have hx' : (Submodule.Quotient.mk x : Q) = 0 := by
      simpa using hx
    change h (Submodule.Quotient.mk x) = 0
    rw [hx']
    rw[ map_zero]

  exact ⟨J', hJJ', N', hN'_fg, hN'_ker, hN'_free, hN_sub⟩

set_option maxHeartbeats 600000 in -- reaches max heartbeats below
/-- **Lazard's theorem**: A module is flat if and only if it is a filtered direct limit of finitely
generated free modules. Equivalently (since finite free = finitely presented + free), it is a
direct limit of finitely presented free modules.

### Proof sketch

`(⇒)` Start from `isDirectLimit_of_finitelyPresented`, which writes M = colim(R^{J_e}/N_e).
Upgrade the index category to `E_free` by restricting to pairs (J, N) where R^J/N is already
free (and still has FG N mapping into the kernel). Directed-ness of `E_free` uses
`enlarge_to_free`: given any two elements, form their join in the old poset (as in the
finitely-presented construction) and then apply `enlarge_to_free` to obtain a free-quotient
upper bound. The resulting direct limit is again M by the same bijection argument.

`(⇐)` A direct limit of flat modules is flat (`Module.Flat.directLimit`), and free modules are
flat, so the conclusion follows. The linear equivalence transports flatness via
`Module.Flat.of_linearEquiv`. -/
theorem Module.Flat.Lazard :
    Module.Flat R M ↔
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (_ : DecidableEq ι)
      (G : ι → Type u) (_ : ∀ i, AddCommGroup (G i)) (_ : ∀ i, Module R (G i))
      (_ : ∀ i, Module.FinitePresentation R (G i))
      (_ : ∀ i, Module.Free R (G i))
      (f : ⦃i j : ι⦄ → i ≤ j → G i →ₗ[R] G j) (_ : DirectedSystem G (fun _ _ h => f h)),
      Nonempty (DirectLimit G (fun _ _ h => f h) ≃ₗ[R] M) := by
  constructor
  · -- (⇒) Flat implies direct limit of free modules
    intro hFlat
    -- Use M × ℤ as index set (following Stacks Tag 058G).
    let I := M × ℤ
    let f : (I →₀ R) →ₗ[R] M := Finsupp.linearCombination R Prod.fst
    let K := LinearMap.ker f

    -- E_free: pairs (J, N) where R^J/N is free (and N maps into K).
    let E_free := { p : (J : Finset I) × Submodule R (J →₀ R) //
      p.2.FG ∧
      (∀ x ∈ p.2, Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ x ∈ K) ∧
      Module.Free R ((p.1 →₀ R) ⧸ p.2) }

    -- The ordering and directed structure (same as in isDirectLimit_of_finitelyPresented).
    let E_le : E_free → E_free → Prop := fun e₁ e₂ =>
      e₁.1.1 ⊆ e₂.1.1 ∧
      Submodule.map (Finsupp.lmapDomain R R Subtype.val) e₁.1.2 ≤
      Submodule.map (Finsupp.lmapDomain R R Subtype.val) e₂.1.2

    letI E_preorder : Preorder E_free := {
      le := E_le
      le_refl := fun e => ⟨Finset.Subset.refl _, le_refl _⟩
      le_trans := fun _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
      lt_iff_le_not_ge := fun _ _ => Iff.rfl
    }

    letI E_deceq : DecidableEq E_free := Classical.decEq E_free

    -- (∅, 0) with trivial quotient R^∅/0 = 0 (free of rank 0) is an element of E_free.
    have E_free_nonempty : Nonempty E_free := by
      refine ⟨⟨⟨∅, ⊥⟩, Submodule.fg_bot, by simp, ?_⟩⟩
      exact Module.Free.of_subsingleton R _

    -- Directedness: given e₁, e₂, form the join (J₁∪J₂, N₁⊔N₂) and apply enlarge_to_free.
    have E_free_directed : IsDirected E_free (· ≤ ·) := by
      constructor
      intro e₁ e₂
      haveI : DecidableEq I := Classical.decEq I
      let J : Finset I := e₁.1.1 ∪ e₂.1.1
      let ι₁ : (↥e₁.1.1 →₀ R) →ₗ[R] (↥J →₀ R) :=
        Finsupp.lmapDomain R R (fun x => ⟨x.1, Finset.mem_union_left _ x.2⟩)
      let ι₂ : (↥e₂.1.1 →₀ R) →ₗ[R] (↥J →₀ R) :=
        Finsupp.lmapDomain R R (fun x => ⟨x.1, Finset.mem_union_right _ x.2⟩)
      let N := Submodule.map ι₁ e₁.1.2 ⊔ Submodule.map ι₂ e₂.1.2
      have hN_fg : N.FG := Submodule.FG.sup (e₁.2.1.map ι₁) (e₂.2.1.map ι₂)
      have hN_ker : ∀ x ∈ N, Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ x ∈ K := by
        intro x hx
        rw [Submodule.mem_sup] at hx
        obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hx
        rw [Finsupp.embDomain_add]
        apply K.add_mem
        case h₁ =>
          rw [Submodule.mem_map] at hy₁
          obtain ⟨z₁, hz₁, rfl⟩ := hy₁
          have := e₁.2.2.1 z₁ hz₁
          convert this using 1
          simp only [Finsupp.embDomain_eq_mapDomain]
          rw [Finsupp.lmapDomain_apply]
          rw [←Finsupp.mapDomain_comp]
          rfl
        case h₂ =>
          rw [Submodule.mem_map] at hy₂
          obtain ⟨z₂, hz₂, rfl⟩ := hy₂
          have := e₂.2.2.1 z₂ hz₂
          convert this using 1
          simp only [Finsupp.embDomain_eq_mapDomain]
          rw [Finsupp.lmapDomain_apply]
          rw [← Finsupp.mapDomain_comp]
          rfl
      -- Upgrade to a free-quotient upper bound via enlarge_to_free.
      obtain ⟨J', hJJ', N', hN'_fg, hN'_ker, hN'_free, hN_to_N'⟩ :=
        Module.Flat.enlarge_to_free R M hN_fg hN_ker
      use ⟨⟨J', N'⟩, hN'_fg, hN'_ker, hN'_free⟩
      constructor
      · constructor
        · exact Finset.subset_union_left.trans hJJ'
        · intro x hx
          rw [Submodule.mem_map] at hx ⊢
          obtain ⟨y, hy, rfl⟩ := hx
          have hy_in_N : ι₁ y ∈ N := Submodule.mem_sup_left (Submodule.mem_map_of_mem hy)
          refine ⟨Finsupp.lmapDomain R R (fun i => ⟨i.1, hJJ' i.2⟩) (ι₁ y), hN_to_N' _ hy_in_N, ?_⟩
          simp only [ι₁, Finsupp.lmapDomain_apply]
          rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
          rfl
      · constructor
        · exact Finset.subset_union_right.trans hJJ'
        · intro x hx
          rw [Submodule.mem_map] at hx ⊢
          obtain ⟨y, hy, rfl⟩ := hx
          have hy_in_N : ι₂ y ∈ N := Submodule.mem_sup_right (Submodule.mem_map_of_mem hy)
          refine ⟨Finsupp.lmapDomain R R (fun i => ⟨i.1, hJJ' i.2⟩) (ι₂ y), hN_to_N' _ hy_in_N, ?_⟩
          simp only [ι₂, Finsupp.lmapDomain_apply]
          rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
          rfl

    letI : DecidableEq E_free := Classical.decEq _

    -- G(J, N) = R^J / N (now guaranteed free).
    let G : E_free → Type u := fun e => (e.1.1 →₀ R) ⧸ e.1.2

    -- Transition maps induced by inclusions J ↪ J'.
    let trans : ⦃i j : E_free⦄ → i ≤ j → G i →ₗ[R] G j := fun {i j} hij =>
      Submodule.mapQ i.1.2 j.1.2
      (Finsupp.lmapDomain R R (fun x => ⟨x.1, hij.1 x.2⟩))
      (by
      intro x hx
      rw [Submodule.mem_comap]
      have h1 : Finsupp.lmapDomain R R Subtype.val x ∈ Submodule.map (Finsupp.lmapDomain R R Subtype.val) i.1.2 :=
        Submodule.mem_map_of_mem hx
      have h2 : Finsupp.lmapDomain R R Subtype.val x ∈ Submodule.map (Finsupp.lmapDomain R R Subtype.val) j.1.2 :=
        hij.2 h1
      rw [Submodule.mem_map] at h2
      obtain ⟨y, hy, heq⟩ := h2
      have heq2 : Finsupp.lmapDomain R R Subtype.val (Finsupp.lmapDomain R R (fun x => ⟨x.1, hij.1 x.2⟩) x) =
                  Finsupp.lmapDomain R R Subtype.val x := by
        simp only [Finsupp.lmapDomain_apply]
        rw [← Finsupp.mapDomain_comp]
        rfl
      have hinj : Function.Injective (Finsupp.lmapDomain R R Subtype.val : (↥j.1.1 →₀ R) → (I →₀ R)) :=
        Finsupp.mapDomain_injective Subtype.val_injective
      have : y = Finsupp.lmapDomain R R (fun x => ⟨x.1, hij.1 x.2⟩) x := hinj (heq.trans heq2.symm)
      rw [← this]
      exact hy)

    have G_directed : DirectedSystem G (fun _ _ h => trans h) := by
      constructor
      · intro i x
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective i.1.2 x
        simp only [trans]
        rw [Submodule.mapQ_apply]
        congr 1
        rw [Finsupp.lmapDomain_apply]
        have : (fun x : ↥i.1.1 => ⟨x.1, (le_refl i).1 x.2⟩) = id := by
          ext ⟨val, prop⟩
          · rfl
          · rfl
        rw [this, Finsupp.mapDomain_id]
      · intro a b c hab hbc x
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective c.1.2 x
        simp only [trans]
        rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.mapQ_apply]
        congr 1
        rw [Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply]
        rw [← Finsupp.mapDomain_comp]
        rfl

    refine ⟨E_free, inferInstance, E_free_directed, E_free_nonempty, inferInstance,
            G, inferInstance, inferInstance, ?_, ?_, trans, G_directed, ?_⟩
    · -- finitely presented
      intro i
      exact Module.finitePresentation_of_surjective (Submodule.mkQ _)
        (Submodule.mkQ_surjective _) (by rw [Submodule.ker_mkQ]; exact i.2.1)
    · -- free
      intro i; exact i.2.2.2
    · -- equivalence: the colimit map colim G → M is a bijection.
      constructor
      let toM : ∀ e : E_free, G e →ₗ[R] M := by
        intro e
        apply Submodule.liftQ e.1.2 (f.comp (Finsupp.lmapDomain R R Subtype.val))
        intro x hx
        simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply]
        have := e.2.2.1 x hx
        simp only [Finsupp.embDomain_eq_mapDomain] at this
        convert this
      have toM_compat : ∀ (i j : E_free) (hij : i ≤ j) (x : G i), toM j (trans hij x) = toM i x := by
        intro i j hij x
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective i.1.2 x
        simp only [trans, toM]
        change f.comp (Finsupp.lmapDomain R R Subtype.val) ((Finsupp.lmapDomain R R fun x => ⟨x.1, hij.1 x.2⟩) x) =
              f.comp (Finsupp.lmapDomain R R Subtype.val) x
        simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lmapDomain_apply]
        rw [← Finsupp.mapDomain_comp]
        rfl
      let φ : DirectLimit G (fun _ _ h => trans h) →ₗ[R] M :=
        DirectLimit.lift R E_free G (fun _ _ h => trans h) toM toM_compat
      have φ_bij : Function.Bijective φ := by
        constructor
        · -- Injectivity: same argument as in isDirectLimit_of_finitelyPresented,
          -- but now use enlarge_to_free to find a free-quotient upper bound killing y'.
          rw [injective_iff_map_eq_zero]
          intro x hx
          obtain ⟨i, y, rfl⟩ := DirectLimit.exists_of x
          simp only [φ, DirectLimit.lift_of] at hx
          obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective i.1.2 y
          simp only [toM] at hx
          rw [Submodule.liftQ_apply, LinearMap.coe_comp, Function.comp_apply] at hx
          have hy'_in_K : Finsupp.lmapDomain R R Subtype.val y' ∈ K := by
            rw [LinearMap.mem_ker]
            exact hx
          -- Enlarge N to newSub = N ⊔ span{y'}.
          let newSub := i.1.2 ⊔ Submodule.span R {y'}
          have newSub_fg : newSub.FG := Submodule.FG.sup i.2.1 (Submodule.fg_span_singleton y')
          have newSub_in_K : ∀ x ∈ newSub,
            Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ x ∈ K := by
            intro x hx'
            rw [Submodule.mem_sup] at hx'
            obtain ⟨a, ha, b, hb, rfl⟩ := hx'
            rw [Finsupp.embDomain_add]
            apply K.add_mem
            · exact i.2.2.1 a ha
            · rw [Submodule.mem_span_singleton] at hb
              obtain ⟨r, rfl⟩ := hb
              rw [Finsupp.embDomain_eq_mapDomain, Finsupp.mapDomain_smul]
              apply Submodule.smul_mem
              rw [← Finsupp.embDomain_eq_mapDomain]
              convert hy'_in_K using 1
              simp only [Finsupp.lmapDomain_apply, Finsupp.embDomain_eq_mapDomain]
              rfl
          -- Apply enlarge_to_free to get j ∈ E_free with i ≤ j and [y'] = 0 in G(j).
          obtain ⟨J', hJ'J, N', hN'_fg, hN'_ker, hN'_free, hN_to_N'⟩ :=
            Module.Flat.enlarge_to_free R M newSub_fg newSub_in_K
          let j : E_free := ⟨⟨J', N'⟩, hN'_fg, hN'_ker, hN'_free⟩
          have hij : i ≤ j := ⟨hJ'J, by
            intro x hx
            rw [Submodule.mem_map] at hx ⊢
            obtain ⟨y, hy, rfl⟩ := hx
            refine ⟨Finsupp.lmapDomain R R (fun i => ⟨i.1, hJ'J i.2⟩) y, ?_, ?_⟩
            · apply hN_to_N'
              exact Submodule.mem_sup_left hy
            · simp only [Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
              rfl⟩
          have htrans_zero : trans hij (Submodule.Quotient.mk y') = 0 := by
            simp only [trans]
            rw [Submodule.mapQ_apply]
            rw [Submodule.Quotient.mk_eq_zero]
            apply hN_to_N'
            exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self y')

          have := @Module.DirectLimit.of_f R _ E_free E_preorder G E_deceq _ _ (fun i j h => trans h)
            i j hij (Submodule.Quotient.mk y')
          rw [this.symm, htrans_zero, map_zero]

        · -- Surjectivity: each m ∈ M comes from G({(m,0)}, 0).
          intro m
          let J : Finset I := {(m, 0)}
          let N : Submodule R (J →₀ R) := ⊥
          have hN_fg : N.FG := Submodule.fg_bot
          have hN_ker : ∀ x ∈ N, Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ x ∈ K := by
            intro x hx; rw [Submodule.mem_bot] at hx; subst hx; simp
          have hN_free : Module.Free R ((J →₀ R) ⧸ N) := by
            have hfree : Free R (↥J →₀ R) := inferInstance
            have hEquiv : ((↥J →₀ R) ⧸ N) ≃ₗ[R] (↥J →₀ R) := Submodule.quotEquivOfEqBot (M := ↥J →₀ R) (p := N) rfl
            apply Module.Free.of_equiv hEquiv.symm
          let e : E_free := ⟨⟨J, N⟩, hN_fg, hN_ker, hN_free⟩
          let x : G e := Submodule.Quotient.mk (Finsupp.single ⟨(m, 0), Finset.mem_singleton_self (m, 0)⟩ 1)
          use DirectLimit.of R E_free G (fun _ _ h => trans h) e x
          simp only [φ, DirectLimit.lift_of, toM]
          rw [Submodule.liftQ_apply]
          simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lmapDomain_apply]
          simp only [Finsupp.mapDomain_single, f, Finsupp.linearCombination_single, one_smul]
      exact LinearEquiv.ofBijective φ φ_bij
  · -- (⇐) Direct limit of free modules implies flat.
    -- Free modules are flat; flat is preserved by direct limits and linear equivalences.
    intro ⟨ι, _, _, _, _, G, _, _, _, hfree, f, _, ⟨equiv⟩⟩
    haveI : ∀ i, Module.Flat R (G i) := fun i => inferInstance
    haveI : Module.Flat R (DirectLimit G (fun _ _ h => f h)) := Module.Flat.directLimit R G f
    exact Module.Flat.of_linearEquiv equiv.symm
