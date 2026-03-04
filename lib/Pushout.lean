/-
Copyright (c) 2026 Liran Shaul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Liran Shaul

This file is part of the formalization project accompanying the paper:
  "Formalization in Lean of faithfully flat descent of projectivity"
  by Liran Shaul, Charles University in Prague.

We develop the theory of pushouts of R-linear maps, following Section 3 of the paper.
Given R-linear maps f : A →ₗ[R] B and g : A →ₗ[R] C between R-modules, their pushout
is the quotient

  Pushout f g = (B × C) / span{(f(a), -g(a)) | a ∈ A}

together with canonical maps Pushout.inl : B → Pushout f g and
Pushout.inr : C → Pushout f g satisfying the pushout condition inl ∘ f = inr ∘ g.

The main results proved here are:

  Pushout.condition     — the pushout square commutes: inl ∘ f = inr ∘ g.
  Pushout.desc          — the universal property: maps out of the pushout correspond to
                          pairs of maps agreeing on the image of A.
  Pushout.hom_ext       — uniqueness of maps out of the pushout determined by their
                          values on inl and inr.
  Pushout.quotientInrEquiv — the canonical isomorphism
                          Pushout(f,g) / im(inr) ≅ B / im(f),
                          used in the proof of dominates_iff_factors_through (Theorem 6.1
                          of the paper) to identify the cokernel of inr as finitely presented.
  Pushout.baseChangeEquiv  — the S-linear isomorphism
                          S ⊗[R] Pushout(f,g) ≅ Pushout(f_S, g_S)
                          (Theorem 3.1 of the paper), where f_S = id_S ⊗ f and g_S = id_S ⊗ g
                          are the base-changed maps.
  Pushout.baseChangeEquiv_inr — the commutativity of the base-change isomorphism with inr
                          (the diagram in Theorem 3.1 of the paper).
  Pushout.congrEquiv    — functoriality of the pushout: isomorphisms on B and C inducing
                          an isomorphism of pushouts.
-/

import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Prod

universe u

open TensorProduct


variable {R : Type u} [CommRing R]
variable {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [Module R A] [Module R B] [Module R C]
variable (N : Type u) [AddCommGroup N] [Module R N]
variable (f : A →ₗ[R] B) (g : A →ₗ[R] C)

/-- The pushout submodule T ⊆ B × C, defined as the R-span of
{(f(a), -g(a)) | a ∈ A}. The pushout Pushout f g is the quotient (B × C) / T. -/
def pushoutSubmodule (f : A →ₗ[R] B) (g : A →ₗ[R] C) : Submodule R (B × C) :=
    Submodule.span R (Set.range (fun a => (f a, -g a)))

/-- The linear map A →ₗ[R] B × C sending a to (f(a), -g(a)), whose range is the
pushout submodule. -/
def pushoutPairMap (f : A →ₗ[R] B) (g : A →ₗ[R] C) : A →ₗ[R] B × C :=
  LinearMap.prod f (-g)

/-- The pushout submodule equals the range of the pair map a ↦ (f(a), -g(a)).
This identification allows membership characterizations via `mem_pushoutSubmodule_iff`. -/
theorem pushoutSubmodule_eq_range (f : A →ₗ[R] B) (g : A →ₗ[R] C) :
    pushoutSubmodule f g = LinearMap.range (pushoutPairMap f g) := by
  apply le_antisymm
  · unfold pushoutSubmodule
    rw [Submodule.span_le]
    intro x ⟨a, ha⟩
    rw [← ha]
    exact ⟨a, rfl⟩
  · unfold pushoutSubmodule
    intro x ⟨a, ha⟩
    rw [← ha]
    apply Submodule.subset_span
    exact ⟨a, rfl⟩

/-- Membership criterion for the pushout submodule: x ∈ pushoutSubmodule f g if and only
if there exists a : A with (f(a), -g(a)) = x. -/
theorem mem_pushoutSubmodule_iff (f : A →ₗ[R] B) (g : A →ₗ[R] C) (x : B × C) :
    x ∈ pushoutSubmodule f g ↔ ∃ a : A, (f a, -g a) = x := by
  rw [pushoutSubmodule_eq_range]
  simp only [LinearMap.mem_range, pushoutPairMap, LinearMap.prod_apply]
  constructor
  · intro ⟨a, ha⟩
    exact ⟨a, ha⟩
  · intro ⟨a, ha⟩
    exact ⟨a, ha⟩

/-- The pushout of two R-linear maps f : A →ₗ[R] B and g : A →ₗ[R] C, defined concretely
as the quotient (B × C) / pushoutSubmodule f g. Elements are equivalence classes [(b, c)]
where (b, c) ~ (b', c') iff (b - b', c - c') = (f(a), -g(a)) for some a ∈ A. -/
def Pushout (f : A →ₗ[R] B) (g : A →ₗ[R] C) : Type u :=
    (B × C) ⧸ pushoutSubmodule f g

instance pushoutAddCommGroup (f : A →ₗ[R] B) (g : A →ₗ[R] C) : AddCommGroup (Pushout f g) :=
    Submodule.Quotient.addCommGroup (pushoutSubmodule f g)

instance pushoutModule (f : A →ₗ[R] B) (g : A →ₗ[R] C) : Module R (Pushout f g) :=
    Submodule.Quotient.module (pushoutSubmodule f g)

/-- The canonical left inclusion inl : B →ₗ[R] Pushout f g, sending b to [(b, 0)]. -/
def Pushout.inl (f : A →ₗ[R] B) (g : A →ₗ[R] C) : B →ₗ[R] Pushout f g :=
    (Submodule.mkQ _).comp (LinearMap.inl R B C)

/-- The canonical right inclusion inr : C →ₗ[R] Pushout f g, sending c to [(0, c)]. -/
def Pushout.inr (f : A →ₗ[R] B) (g : A →ₗ[R] C) : C →ₗ[R] Pushout f g :=
    (Submodule.mkQ _).comp (LinearMap.inr R B C)

/-- The pushout square commutes: inl ∘ f = inr ∘ g. This follows from the fact that
(f(a), 0) - (0, g(a)) = (f(a), -g(a)) lies in the pushout submodule by definition. -/
theorem Pushout.condition (f : A →ₗ[R] B) (g : A →ₗ[R] C) :
    (Pushout.inl f g).comp f = (Pushout.inr f g).comp g := by
  ext a
  unfold Pushout.inl Pushout.inr
  change Submodule.Quotient.mk (f a, 0) = Submodule.Quotient.mk (0, g a)
  rw [Submodule.Quotient.eq]
  have : (f a, (0 : C)) - (0, g a) = (f a, -g a) := by simp
  rw [this]
  exact Submodule.subset_span ⟨a, rfl⟩

/-- The universal property of the pushout: given R-linear maps b : B →ₗ[R] D and
c : C →ₗ[R] D with b ∘ f = c ∘ g, there is a unique map Pushout f g →ₗ[R] D making
both triangles commute. The map is constructed via `Submodule.liftQ` applied to b.coprod c,
after verifying that b.coprod c vanishes on the pushout submodule. -/
def Pushout.desc (f : A →ₗ[R] B) (g : A →ₗ[R] C)
      {D : Type u} [AddCommGroup D] [Module R D]
      (b : B →ₗ[R] D) (c : C →ₗ[R] D) (h : b.comp f = c.comp g) :
      Pushout f g →ₗ[R] D :=
    Submodule.liftQ _ (b.coprod c) (by
      simp only [pushoutSubmodule, Submodule.span_le]
      intro x hx
      obtain ⟨a, rfl⟩ := hx
      change b (f a) + c (-g a) = 0
      simp only [map_neg, add_neg_eq_zero]
      exact LinearMap.congr_fun h a)

/-- The map constructed by `Pushout.desc` commutes with inl: desc ∘ inl = b. -/
theorem Pushout.inl_desc (f : A →ₗ[R] B) (g : A →ₗ[R] C)
    {D : Type u} [AddCommGroup D] [Module R D]
    (b : B →ₗ[R] D) (c : C →ₗ[R] D) (h : b.comp f = c.comp g) :
    (Pushout.desc f g b c h).comp (Pushout.inl f g) = b := by
  ext x
  unfold Pushout.desc Pushout.inl
  simp only [LinearMap.comp_apply]
  change Submodule.liftQ _ (b.coprod c) _ (Submodule.Quotient.mk (x, 0)) = b x
  rw [Submodule.liftQ_apply]
  simp only [LinearMap.coprod_apply, map_zero, add_zero]

/-- The map constructed by `Pushout.desc` commutes with inr: desc ∘ inr = c. -/
theorem Pushout.inr_desc (f : A →ₗ[R] B) (g : A →ₗ[R] C)
    {D : Type u} [AddCommGroup D] [Module R D]
    (b : B →ₗ[R] D) (c : C →ₗ[R] D) (h : b.comp f = c.comp g) :
    (Pushout.desc f g b c h).comp (Pushout.inr f g) = c := by
  ext x
  unfold Pushout.desc Pushout.inr
  simp only [LinearMap.comp_apply]
  change Submodule.liftQ _ (b.coprod c) _ (Submodule.Quotient.mk (0, x)) = c x
  rw [Submodule.liftQ_apply]
  simp only [LinearMap.coprod_apply, map_zero, zero_add]

/-- Uniqueness in the universal property: any two maps out of the pushout that agree on
inl and inr are equal. Combined with `Pushout.desc`, this gives the usual universal
property: maps Pushout f g →ₗ[R] D are in bijection with pairs (b, c) satisfying
b ∘ f = c ∘ g. -/
theorem Pushout.desc_unique (f : A →ₗ[R] B) (g : A →ₗ[R] C)
    {D : Type u} [AddCommGroup D] [Module R D]
    (b : B →ₗ[R] D) (c : C →ₗ[R] D) (h : b.comp f = c.comp g)
    (φ : Pushout f g →ₗ[R] D)
    (hφb : φ.comp (Pushout.inl f g) = b)
    (hφc : φ.comp (Pushout.inr f g) = c) :
    φ = Pushout.desc f g b c h := by
  ext ⟨x⟩
  obtain ⟨bx, cx⟩ := x
  have hb : φ (Pushout.inl f g bx) = b bx := LinearMap.congr_fun hφb bx
  have hc : φ (Pushout.inr f g cx) = c cx := LinearMap.congr_fun hφc cx
  change φ (Submodule.Quotient.mk (bx, cx)) =
  Pushout.desc f g b c h (Submodule.Quotient.mk (bx, cx))
  -- Every element of the pushout is a sum of an inl and an inr part
  have key : (Submodule.Quotient.mk (bx, cx) : Pushout f g) =
          Pushout.inl f g bx + Pushout.inr f g cx := by
    change Submodule.Quotient.mk (bx, cx) =
        Submodule.Quotient.mk (bx, 0) + Submodule.Quotient.mk (0, cx)
    rw [← Submodule.Quotient.mk_add]
    simp
  rw [key, map_add, hb, hc]
  rw [map_add]
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, Pushout.inl_desc, Pushout.inr_desc]

/-- The pointwise version of the pushout condition: inl(f(a)) = inr(g(a)) in Pushout f g. -/
theorem Pushout.condition_apply (f : A →ₗ[R] B) (g : A →ₗ[R] C) (a : A) :
    Pushout.inl f g (f a) = Pushout.inr f g (g a) :=
  LinearMap.congr_fun (Pushout.condition f g) a

/-- The comparison map Pushout(f,g) ⊗ N → Pushout(f ⊗ id_N, g ⊗ id_N), constructed via
the universal properties of the tensor product and the pushout. This is used in the proof
of `dominates_iff_pushout_inr_universallyInjective` in lib.Domination. -/
def pushoutTensorHomR :
    Pushout f g ⊗[R] N →ₗ[R] Pushout (f.rTensor N) (g.rTensor N) :=
    TensorProduct.lift <|
      Pushout.desc f g
        ((TensorProduct.mk R B N).compr₂ (Pushout.inl (f.rTensor N) (g.rTensor N)))
        ((TensorProduct.mk R C N).compr₂ (Pushout.inr (f.rTensor N) (g.rTensor N)))
        (by
          ext a n
          simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.comp_apply]
          have h := Pushout.condition (f.rTensor N) (g.rTensor N)
          exact LinearMap.congr_fun h (a ⊗ₜ n)
        )

/-- The inverse comparison map Pushout(f ⊗ id_N, g ⊗ id_N) → Pushout(f,g) ⊗ N, constructed
via the universal property of the pushout applied to the maps id ⊗ inl and id ⊗ inr. -/
def pushoutTensorHomRInv :
    Pushout (f.rTensor N) (g.rTensor N) →ₗ[R] Pushout f g ⊗[R] N :=
    Pushout.desc (f.rTensor N) (g.rTensor N)
      (TensorProduct.map (Pushout.inl f g) LinearMap.id)
      (TensorProduct.map (Pushout.inr f g) LinearMap.id)
      (by
        ext a n
        change (TensorProduct.map (Pushout.inl f g) LinearMap.id) (f a ⊗ₜ n) =
            (TensorProduct.map (Pushout.inr f g) LinearMap.id) (g a ⊗ₜ n)
        simp only [TensorProduct.map_tmul, LinearMap.id_apply]
        have h := Pushout.condition f g
        have h' : (Pushout.inl f g) (f a) = (Pushout.inr f g) (g a) := LinearMap.congr_fun h a
        rw [h']
      )

/-- The forward direction of `Pushout.quotientInrEquiv`: the map
  Pushout(f,g) / im(inr) →ₗ[R] B / im(f)
induced by the projection B → B/im(f) composed with the universal property of the pushout.
The map is well-defined because inr lands in the kernel of the composite map
Pushout(f,g) → B/im(f) (since the zero map kills the inr component). -/
def Pushout.quotientInrToQuotientF (f : A →ₗ[R] B) (g : A →ₗ[R] C) :
    (Pushout f g ⧸ LinearMap.range (Pushout.inr f g)) →ₗ[R] (B ⧸ LinearMap.range f) :=
  Submodule.liftQ (LinearMap.range (Pushout.inr f g))
    (Pushout.desc f g (Submodule.mkQ (LinearMap.range f)) 0 (by
      ext a
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range_self f a))
    (by
      intro x hx
      obtain ⟨c, rfl⟩ := hx
      rw [LinearMap.mem_ker]
      rw [← LinearMap.comp_apply (Pushout.desc f g
      (Submodule.mkQ (LinearMap.range f)) 0 _) (Pushout.inr f g)]
      rw [Pushout.inr_desc]
      rfl)

/-- The backward direction of `Pushout.quotientInrEquiv`: the map
  B / im(f) →ₗ[R] Pushout(f,g) / im(inr)
obtained by lifting the quotient map B → Pushout(f,g)/im(inr) (which factors as the
composition of inl with the quotient by im(inr)) across im(f), using the pushout condition
to show that inl(f(a)) ∈ im(inr) for all a ∈ A. -/
def Pushout.quotientFToQuotientInr (f : A →ₗ[R] B) (g : A →ₗ[R] C) :
    (B ⧸ LinearMap.range f) →ₗ[R] (Pushout f g ⧸ LinearMap.range (Pushout.inr f g)) :=
  Submodule.liftQ (LinearMap.range f)
    (Submodule.mkQ (LinearMap.range (Pushout.inr f g)) ∘ₗ Pushout.inl f g)
    (by
      intro x hx
      obtain ⟨a, rfl⟩ := hx
      rw [LinearMap.mem_ker]
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
      rw [Pushout.condition_apply f g a]
      rw [Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range_self (Pushout.inr f g) (g a))

/-- Auxiliary lemma: the composite (desc ∘ inl) equals the quotient map mkQ,
used in the proof of `Pushout.quotientInrEquiv`. -/
lemma Pushout.desc_mkQ_zero_comp_inl (f : A →ₗ[R] B) (g : A →ₗ[R] C) :
    (Pushout.desc f g (Submodule.mkQ (LinearMap.range f)) 0 (by
      ext a
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range_self f a)).comp (Pushout.inl f g) =
    Submodule.mkQ (LinearMap.range f) :=
  Pushout.inl_desc f g _ _ _

/-- Auxiliary lemma: the composite (desc ∘ inr) is the zero map,
used in the proof of `Pushout.quotientInrEquiv`. -/
lemma Pushout.desc_mkQ_zero_comp_inr (f : A →ₗ[R] B) (g : A →ₗ[R] C) :
    (Pushout.desc f g (Submodule.mkQ (LinearMap.range f)) 0 (by
      ext a
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range_self f a)).comp (Pushout.inr f g) = 0 :=
  Pushout.inr_desc f g _ _ _

/-- Every element of Pushout f g is a sum of an inl part and an inr part:
[(b, c)] = inl(b) + inr(c). This decomposition is used repeatedly in the proofs of
the universal properties and the base-change isomorphism. -/
lemma Pushout.mk_eq_inl_add_inr (f : A →ₗ[R] B) (g : A →ₗ[R] C) (b : B) (c : C) :
    (Submodule.Quotient.mk (b, c) : Pushout f g) = Pushout.inl f g b + Pushout.inr f g c := by
  change Submodule.Quotient.mk (b, c) =
      Submodule.Quotient.mk (b, 0) + Submodule.Quotient.mk (0, c)
  rw [← Submodule.Quotient.mk_add]
  simp

/-- The canonical R-linear isomorphism Pushout(f,g) / im(inr) ≅ B / im(f). This result
is used in the proof of `dominates_iff_factors_through` (Theorem 6.1 of the paper) to
identify the cokernel of inr f g as finitely presented whenever B/im(f) is. The isomorphism
is constructed from `Pushout.quotientInrToQuotientF` and `Pushout.quotientFToQuotientInr`
and verified by checking the two composites are identity on generators. -/
def Pushout.quotientInrEquiv (f : A →ₗ[R] B) (g : A →ₗ[R] C) :
    (Pushout f g ⧸ LinearMap.range (Pushout.inr f g)) ≃ₗ[R] (B ⧸ LinearMap.range f) :=
  LinearEquiv.ofLinear
    (Pushout.quotientInrToQuotientF f g)
    (Pushout.quotientFToQuotientInr f g)
    (by
      ext b
      unfold quotientInrToQuotientF quotientFToQuotientInr
      simp only [LinearMap.comp_apply, LinearMap.id_apply, Submodule.liftQ_apply,
                 Submodule.mkQ_apply]
      rw [← LinearMap.comp_apply, Pushout.inl_desc]
      rfl)
    (by
      ext x
      obtain ⟨b, c⟩ := x
      unfold quotientInrToQuotientF quotientFToQuotientInr
      simp only [LinearMap.comp_apply,
      LinearMap.id_apply, Submodule.liftQ_apply, Submodule.mkQ_apply]
      change ((LinearMap.range f).liftQ
      ((LinearMap.range (Pushout.inr f g)).mkQ ∘ₗ Pushout.inl f g) _)
             ((Pushout.desc f g (Submodule.mkQ (LinearMap.range f)) 0 _)
             (Submodule.Quotient.mk (b, c))) =
             Submodule.Quotient.mk (Submodule.Quotient.mk (b, c))
      rw [Pushout.mk_eq_inl_add_inr, map_add]
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply]
      rw [Pushout.desc_mkQ_zero_comp_inl, Pushout.desc_mkQ_zero_comp_inr]
      simp only [Submodule.mkQ_apply, LinearMap.zero_apply, add_zero]
      simp only [Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      simp)

/-- Extensionality principle for maps out of the pushout: two maps φ, ψ : Pushout f g →ₗ[R] D
are equal if they agree on both inl and inr. This is the uniqueness part of the universal
property, restated as a convenient `ext`-style lemma. -/
theorem Pushout.hom_ext {R : Type u} [CommRing R]
    {A B C D : Type u}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [Module R A] [Module R B] [Module R C] [Module R D]
    (f : A →ₗ[R] B) (g : A →ₗ[R] C)
    (φ ψ : Pushout f g →ₗ[R] D)
    (hinl : φ.comp (Pushout.inl f g) = ψ.comp (Pushout.inl f g))
    (hinr : φ.comp (Pushout.inr f g) = ψ.comp (Pushout.inr f g)) :
    φ = ψ := by
  have h : (φ.comp (Pushout.inl f g)).comp f = (φ.comp (Pushout.inr f g)).comp g := by
    have cond := Pushout.condition f g
    calc (φ.comp (Pushout.inl f g)).comp f
        = φ.comp ((Pushout.inl f g).comp f) := by rfl
      _ = φ.comp ((Pushout.inr f g).comp g) := by rw [cond]
      _ = (φ.comp (Pushout.inr f g)).comp g := by rfl
  have hφ := Pushout.desc_unique f g (φ.comp (Pushout.inl f g))
    (φ.comp (Pushout.inr f g)) h φ rfl rfl
  have hψ := Pushout.desc_unique f g (φ.comp (Pushout.inl f g))
    (φ.comp (Pushout.inr f g)) h ψ hinl.symm hinr.symm
  rw [hφ, hψ]

/-- The S-linear isomorphism S ⊗[R] Pushout(f,g) ≅ Pushout(f_S, g_S), where
f_S = id_S ⊗ f : S ⊗[R] A →ₗ[S] S ⊗[R] B and g_S = id_S ⊗ g are the base-changed maps.
This is Theorem 3.1 of the paper.

The forward map is constructed by lifting the R-linear map
  Pushout(f,g) →ₗ[R] Pushout(f_S, g_S),  b ↦ inl(1 ⊗ b),  c ↦ inr(1 ⊗ c)
via the AlgebraTensorModule.lift (using the S-module structure on the target).
The backward map is constructed from the S-linear maps inl(S) and inr(S) on the base-changed
pushout. The two inverses are verified by checking on generators using `Pushout.hom_ext`. -/
noncomputable def Pushout.baseChangeEquiv
    {R : Type u} [CommRing R]
    {S : Type u} [CommRing S] [Algebra R S]
    {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : A →ₗ[R] C) :
    S ⊗[R] Pushout f g ≃ₗ[S] Pushout (LinearMap.baseChange S f) (LinearMap.baseChange S g) := by
  letI instR : Module R (Pushout (LinearMap.baseChange S f) (LinearMap.baseChange S g)) :=
    Module.compHom _ (algebraMap R S)
  haveI : IsScalarTower R S (Pushout (LinearMap.baseChange S f) (LinearMap.baseChange S g)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

  let inlR : B →ₗ[R] Pushout (LinearMap.baseChange S f) (LinearMap.baseChange S g) :=
    (Pushout.inl (LinearMap.baseChange S f) (LinearMap.baseChange S g)).restrictScalars R ∘ₗ
      TensorProduct.mk R S B 1
  let inrR : C →ₗ[R] Pushout (LinearMap.baseChange S f) (LinearMap.baseChange S g) :=
    (Pushout.inr (LinearMap.baseChange S f) (LinearMap.baseChange S g)).restrictScalars R ∘ₗ
      TensorProduct.mk R S C 1

  have cond : inlR ∘ₗ f = inrR ∘ₗ g := by
    ext a
    simp only [inlR, inrR, LinearMap.comp_apply, TensorProduct.mk_apply,
               LinearMap.restrictScalars_apply]
    exact Pushout.condition_apply (LinearMap.baseChange S f) (LinearMap.baseChange S g) (1 ⊗ₜ a)

  let descR : Pushout f g →ₗ[R] Pushout (LinearMap.baseChange S f) (LinearMap.baseChange S g) :=
    Pushout.desc f g inlR inrR cond

  -- The forward map: s ⊗ p ↦ s • descR(p), assembled via AlgebraTensorModule.lift
  let liftArg : S →ₗ[S] Pushout f g →ₗ[R] Pushout (LinearMap.baseChange S f)
    (LinearMap.baseChange S g) :=
    { toFun := fun s => s • descR
      map_add' := fun s t => by ext p; simp [add_smul]
      map_smul' := fun r s => by ext p; simp [mul_smul] }

  let forward : S ⊗[R] Pushout f g →ₗ[S] Pushout
    (LinearMap.baseChange S f) (LinearMap.baseChange S g) :=
    TensorProduct.AlgebraTensorModule.lift liftArg

  -- The backward map: constructed from the base-changed inl and inr via the universal property
  let backward : Pushout (LinearMap.baseChange S f)
    (LinearMap.baseChange S g) →ₗ[S] S ⊗[R] Pushout f g :=
      Pushout.desc (LinearMap.baseChange S f) (LinearMap.baseChange S g)
        (LinearMap.baseChange S (Pushout.inl f g))
        (LinearMap.baseChange S (Pushout.inr f g))
        (by
          apply LinearMap.ext
          intro x
          induction x with
          | tmul s a =>
            simp only [LinearMap.baseChange_tmul, LinearMap.comp_apply]
            rw [Pushout.condition_apply]
          | add x y hx hy => simp only [map_add, hx, hy]
          | zero => simp only [map_zero])

  refine LinearEquiv.ofLinear forward backward ?_ ?_
  · -- forward ∘ backward = id: check on inl and inr generators using Pushout.hom_ext
    apply Pushout.hom_ext (LinearMap.baseChange S f) (LinearMap.baseChange S g)
    · apply LinearMap.ext
      intro x
      induction x with
      | tmul s b =>
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        show forward (backward (Pushout.inl _ _ (s ⊗ₜ b))) = _
        have h1 : backward (Pushout.inl _ _ (s ⊗ₜ b)) = s ⊗ₜ (Pushout.inl f g b) := by
          simp only [backward, ← LinearMap.comp_apply, Pushout.inl_desc, LinearMap.baseChange_tmul]
        rw [h1]
        have h2 : forward (s ⊗ₜ (Pushout.inl f g b)) = s • descR (Pushout.inl f g b) := by
          simp only [forward, TensorProduct.AlgebraTensorModule.lift_apply, liftArg]
          rfl
        rw [h2]
        have h3 : descR (Pushout.inl f g b) = Pushout.inl _ _ (1 ⊗ₜ b) := by
          have : descR ∘ₗ Pushout.inl f g = inlR := Pushout.inl_desc f g inlR inrR cond
          rw [← LinearMap.comp_apply, this]
          simp only [inlR, LinearMap.comp_apply, TensorProduct.mk_apply,
                     LinearMap.restrictScalars_apply]
        rw [h3]
        rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add x y hx hy => simp only [map_add, hx, hy]
      | zero => simp only [map_zero]
    · apply LinearMap.ext
      intro x
      induction x with
      | tmul s c =>
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        show forward (backward (Pushout.inr _ _ (s ⊗ₜ c))) = _
        have h1 : backward (Pushout.inr _ _ (s ⊗ₜ c)) = s ⊗ₜ (Pushout.inr f g c) := by
          simp only [backward, ← LinearMap.comp_apply, Pushout.inr_desc, LinearMap.baseChange_tmul]
        rw [h1]
        have h2 : forward (s ⊗ₜ (Pushout.inr f g c)) = s • descR (Pushout.inr f g c) := by
          simp only [forward, TensorProduct.AlgebraTensorModule.lift_apply, liftArg]
          rfl
        rw [h2]
        have h3 : descR (Pushout.inr f g c) = Pushout.inr _ _ (1 ⊗ₜ c) := by
          have : descR ∘ₗ Pushout.inr f g = inrR := Pushout.inr_desc f g inlR inrR cond
          rw [← LinearMap.comp_apply, this]
          simp only [inrR, LinearMap.comp_apply, TensorProduct.mk_apply,
                     LinearMap.restrictScalars_apply]
        rw [h3]
        rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add x y hx hy => simp only [map_add, hx, hy]
      | zero => simp only [map_zero]
  · -- backward ∘ forward = id: check on pure tensors s ⊗ [(b,c)] using mk_eq_inl_add_inr
    apply TensorProduct.AlgebraTensorModule.ext
    intro s p
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    show backward (forward (s ⊗ₜ p)) = s ⊗ₜ p
    have h1 : forward (s ⊗ₜ p) = s • descR p := by
      simp only [forward, TensorProduct.AlgebraTensorModule.lift_apply, liftArg]
      rfl
    rw [h1]
    obtain ⟨⟨b, c⟩⟩ := p
    change backward (s • descR (Submodule.Quotient.mk (b, c))) =
           s ⊗ₜ (Submodule.Quotient.mk (b, c) : Pushout f g)
    rw [Pushout.mk_eq_inl_add_inr f g b c]
    simp only [map_add, map_smul]
    have hinl : descR (Pushout.inl f g b) = Pushout.inl _ _ (1 ⊗ₜ b) := by
      have : descR ∘ₗ Pushout.inl f g = inlR := Pushout.inl_desc f g inlR inrR cond
      rw [← LinearMap.comp_apply, this]
      simp only [inlR, LinearMap.comp_apply, TensorProduct.mk_apply,
      LinearMap.restrictScalars_apply]
    have hinr : descR (Pushout.inr f g c) = Pushout.inr _ _ (1 ⊗ₜ c) := by
      have : descR ∘ₗ Pushout.inr f g = inrR := Pushout.inr_desc f g inlR inrR cond
      rw [← LinearMap.comp_apply, this]
      simp only [inrR, LinearMap.comp_apply, TensorProduct.mk_apply,
      LinearMap.restrictScalars_apply]
    rw [hinl, hinr]
    have binl : backward (Pushout.inl _ _ (1 ⊗ₜ b)) = 1 ⊗ₜ (Pushout.inl f g b) := by
      simp only [backward, ← LinearMap.comp_apply, Pushout.inl_desc, LinearMap.baseChange_tmul]
    have binr : backward (Pushout.inr _ _ (1 ⊗ₜ c)) = 1 ⊗ₜ (Pushout.inr f g c) := by
      simp only [backward, ← LinearMap.comp_apply, Pushout.inr_desc, LinearMap.baseChange_tmul]
    rw[binl,binr]
    rw [← TensorProduct.tmul_add]
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The base-change isomorphism `Pushout.baseChangeEquiv` intertwines the two right
inclusions inr: the diagram
  S ⊗[R] C  --baseChange S (inr f g)-->  S ⊗[R] Pushout(f,g)
                                                    |
                                            baseChangeEquiv
                                                    |
                                                    ↓
  S ⊗[R] C  --inr(f_S, g_S)---------->  Pushout(f_S, g_S)
commutes. This is the commutativity statement in Theorem 3.1 of the paper and
`Pushout.baseChangeEquiv_inr` of the paper, used in the proof of
`dominates_iff_pushout_inr_universallyInjective` and Theorem 4.2. -/
lemma Pushout.baseChangeEquiv_inr
    {R : Type u} [CommRing R]
    {S : Type u} [CommRing S] [Algebra R S]
    {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : A →ₗ[R] C) :
    (↑(Pushout.baseChangeEquiv (S := S) f g) ∘ₗ
        LinearMap.baseChange S (Pushout.inr f g)) =
      Pushout.inr (LinearMap.baseChange S f) (LinearMap.baseChange S g) := by
  letI instR : Module R (Pushout (LinearMap.baseChange S f) (LinearMap.baseChange S g)) :=
    Module.compHom _ (algebraMap R S)
  haveI : IsScalarTower R S (Pushout (LinearMap.baseChange S f) (LinearMap.baseChange S g)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

  let inlR : B →ₗ[R] Pushout (LinearMap.baseChange S f) (LinearMap.baseChange S g) :=
    (Pushout.inl (LinearMap.baseChange S f) (LinearMap.baseChange S g)).restrictScalars R ∘ₗ
      TensorProduct.mk R S B 1
  let inrR : C →ₗ[R] Pushout (LinearMap.baseChange S f) (LinearMap.baseChange S g) :=
    (Pushout.inr (LinearMap.baseChange S f) (LinearMap.baseChange S g)).restrictScalars R ∘ₗ
      TensorProduct.mk R S C 1

  have cond : inlR ∘ₗ f = inrR ∘ₗ g := by
    ext a
    simp only [inlR, inrR, LinearMap.comp_apply, TensorProduct.mk_apply,
               LinearMap.restrictScalars_apply]
    exact Pushout.condition_apply (LinearMap.baseChange S f) (LinearMap.baseChange S g) (1 ⊗ₜ a)

  let descR : Pushout f g →ₗ[R] Pushout (LinearMap.baseChange S f) (LinearMap.baseChange S g) :=
    Pushout.desc f g inlR inrR cond

  apply TensorProduct.AlgebraTensorModule.ext
  intro s c
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe]

  -- Unfold the forward map on s ⊗ inr(c) and use the definition of descR on inr
  have h1 : baseChangeEquiv f g (s ⊗ₜ (Pushout.inr f g c)) = s • descR (Pushout.inr f g c) := by
    simp only [baseChangeEquiv, LinearEquiv.ofLinear_apply,
               TensorProduct.AlgebraTensorModule.lift_apply]
    rfl
  rw [h1]

  have h2 : descR (Pushout.inr f g c) = Pushout.inr _ _ (1 ⊗ₜ c) := by
    have : descR ∘ₗ Pushout.inr f g = inrR := Pushout.inr_desc f g inlR inrR cond
    rw [← LinearMap.comp_apply, this]
    simp only [inrR, LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.restrictScalars_apply]
  rw [h2]
  rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Functoriality of the pushout under isomorphisms on the output modules: given
isomorphisms eB : B ≃ₗ[R] B' and eC : C ≃ₗ[R] C' and maps f' = eB ∘ f, g' = eC ∘ g,
the pushout Pushout(f,g) is isomorphic to Pushout(f',g'). The isomorphism is constructed
via the universal property, using eB and eC to move between the two pushout squares. -/
def Pushout.congrEquiv {R : Type u} [CommRing R]
    {A B C B' C' : Type u}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup B'] [AddCommGroup C']
    [Module R A] [Module R B] [Module R C] [Module R B'] [Module R C']
    (f : A →ₗ[R] B) (g : A →ₗ[R] C)
    (eB : B ≃ₗ[R] B') (eC : C ≃ₗ[R] C')
    (f' : A →ₗ[R] B') (g' : A →ₗ[R] C')
    (hf : eB.toLinearMap ∘ₗ f = f') (hg : eC.toLinearMap ∘ₗ g = g') :
    Pushout f g ≃ₗ[R] Pushout f' g' := by
  have hf' : eB.symm.toLinearMap ∘ₗ f' = f := by
    rw [← hf]
    ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    exact eB.symm_apply_apply (f x)
  have hg' : eC.symm.toLinearMap ∘ₗ g' = g := by
    rw [← hg]
    ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    exact eC.symm_apply_apply (g x)
  have cond_fg : (Pushout.inl f' g' ∘ₗ eB.toLinearMap) ∘ₗ f =
                 (Pushout.inr f' g' ∘ₗ eC.toLinearMap) ∘ₗ g := by
    have cond := Pushout.condition f' g'
    calc (Pushout.inl f' g' ∘ₗ eB.toLinearMap) ∘ₗ f
        = Pushout.inl f' g' ∘ₗ (eB.toLinearMap ∘ₗ f) := by rfl
      _ = Pushout.inl f' g' ∘ₗ f' := by rw [hf]
      _ = Pushout.inr f' g' ∘ₗ g' := cond
      _ = Pushout.inr f' g' ∘ₗ (eC.toLinearMap ∘ₗ g) := by rw [hg]
      _ = (Pushout.inr f' g' ∘ₗ eC.toLinearMap) ∘ₗ g := by rfl
  have cond_f'g' : (Pushout.inl f g ∘ₗ eB.symm.toLinearMap) ∘ₗ f' =
                   (Pushout.inr f g ∘ₗ eC.symm.toLinearMap) ∘ₗ g' := by
    have cond := Pushout.condition f g
    calc (Pushout.inl f g ∘ₗ eB.symm.toLinearMap) ∘ₗ f'
        = Pushout.inl f g ∘ₗ (eB.symm.toLinearMap ∘ₗ f') := by rfl
      _ = Pushout.inl f g ∘ₗ f := by rw [hf']
      _ = Pushout.inr f g ∘ₗ g := cond
      _ = Pushout.inr f g ∘ₗ (eC.symm.toLinearMap ∘ₗ g') := by rw [hg']
      _ = (Pushout.inr f g ∘ₗ eC.symm.toLinearMap) ∘ₗ g' := by rfl
  let forward : Pushout f g →ₗ[R] Pushout f' g' :=
    Pushout.desc f g (Pushout.inl f' g' ∘ₗ eB.toLinearMap)
      (Pushout.inr f' g' ∘ₗ eC.toLinearMap) cond_fg
  let backward : Pushout f' g' →ₗ[R] Pushout f g :=
    Pushout.desc f' g' (Pushout.inl f g ∘ₗ eB.symm.toLinearMap)
      (Pushout.inr f g ∘ₗ eC.symm.toLinearMap) cond_f'g'
  refine LinearEquiv.ofLinear forward backward ?_ ?_
  · -- forward ∘ backward = id: verify on inl and inr generators
    apply Pushout.hom_ext f' g'
    · ext x
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      have h1 : backward (Pushout.inl f' g' x) = Pushout.inl f g (eB.symm x) := by
        change Pushout.desc f' g' _ _ cond_f'g' (Pushout.inl f' g' x) = _
        rw [← LinearMap.comp_apply, Pushout.inl_desc]
        rfl
      have h2 : forward (Pushout.inl f g (eB.symm x)) = Pushout.inl f' g' (eB (eB.symm x)) := by
        change Pushout.desc f g _ _ cond_fg (Pushout.inl f g (eB.symm x)) = _
        rw [← LinearMap.comp_apply, Pushout.inl_desc]
        rfl
      rw [h1, h2, eB.apply_symm_apply]
    · ext x
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      have h1 : backward (Pushout.inr f' g' x) = Pushout.inr f g (eC.symm x) := by
        change Pushout.desc f' g' _ _ cond_f'g' (Pushout.inr f' g' x) = _
        rw [← LinearMap.comp_apply, Pushout.inr_desc]
        rfl
      have h2 : forward (Pushout.inr f g (eC.symm x)) = Pushout.inr f' g' (eC (eC.symm x)) := by
        change Pushout.desc f g _ _ cond_fg (Pushout.inr f g (eC.symm x)) = _
        rw [← LinearMap.comp_apply, Pushout.inr_desc]
        rfl
      rw [h1, h2, eC.apply_symm_apply]
  · -- backward ∘ forward = id: verify on inl and inr generators
    apply Pushout.hom_ext f g
    · ext x
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      have h1 : forward (Pushout.inl f g x) = Pushout.inl f' g' (eB x) := by
        change Pushout.desc f g _ _ cond_fg (Pushout.inl f g x) = _
        rw [← LinearMap.comp_apply, Pushout.inl_desc]
        rfl
      have h2 : backward (Pushout.inl f' g' (eB x)) = Pushout.inl f g (eB.symm (eB x)) := by
        change Pushout.desc f' g' _ _ cond_f'g' (Pushout.inl f' g' (eB x)) = _
        rw [← LinearMap.comp_apply, Pushout.inl_desc]
        rfl
      rw [h1, h2, eB.symm_apply_apply]
    · ext x
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      have h1 : forward (Pushout.inr f g x) = Pushout.inr f' g' (eC x) := by
        change Pushout.desc f g _ _ cond_fg (Pushout.inr f g x) = _
        rw [← LinearMap.comp_apply, Pushout.inr_desc]
        rfl
      have h2 : backward (Pushout.inr f' g' (eC x)) = Pushout.inr f g (eC.symm (eC x)) := by
        change Pushout.desc f' g' _ _ cond_f'g' (Pushout.inr f' g' (eC x)) = _
        rw [← LinearMap.comp_apply, Pushout.inr_desc]
        rfl
      rw [h1, h2, eC.symm_apply_apply]

/-- The congruence isomorphism `Pushout.congrEquiv` intertwines the right inclusions inr:
(congrEquiv ...) ∘ inr f g = inr f' g' ∘ eC.
This lemma is needed when applying `congrEquiv` in contexts where the inr components
must be tracked explicitly. -/
lemma Pushout.congrEquiv_inr {R : Type u} [CommRing R]
    {A B C B' C' : Type u}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup B'] [AddCommGroup C']
    [Module R A] [Module R B] [Module R C] [Module R B'] [Module R C']
    (f : A →ₗ[R] B) (g : A →ₗ[R] C)
    (eB : B ≃ₗ[R] B') (eC : C ≃ₗ[R] C')
    (f' : A →ₗ[R] B') (g' : A →ₗ[R] C')
    (hf : eB.toLinearMap ∘ₗ f = f') (hg : eC.toLinearMap ∘ₗ g = g') :
    (Pushout.congrEquiv f g eB eC f' g' hf hg).toLinearMap ∘ₗ Pushout.inr f g =
    Pushout.inr f' g' ∘ₗ eC.toLinearMap := by
  ext x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  unfold congrEquiv
  simp only [LinearEquiv.ofLinear_apply]
  rw [← LinearMap.comp_apply, Pushout.inr_desc]
  rfl
