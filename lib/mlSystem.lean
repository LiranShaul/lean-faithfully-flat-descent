/-
Copyright (c) 2026 Liran Shaul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Liran Shaul

This file is part of the formalization project accompanying the paper:
  "Formalization in Lean of faithfully flat descent of projectivity"
  by Liran Shaul, Charles University in Prague.

We develop the theory of Mittag-Leffler inverse systems, following Section 5 of the paper
and the Stacks Project (Tag 0594). An inverse system (Fᵢ, fᵢⱼ) indexed by a preorder ι
satisfies the Mittag-Leffler condition if for each index i, the images im(fⱼᵢ : Fⱼ → Fᵢ)
stabilize as j increases.

The main results proved here are:

  nonempty_inverseLimit_of_countable_mittagLeffler (Theorem 5.1 of the paper):
    If ι is a countable directed preorder and (Fᵢ, fᵢⱼ) is a Mittag-Leffler inverse system
    with each Fᵢ nonempty, then the inverse limit lim←Fᵢ is nonempty. The proof proceeds
    by extracting a monotone cofinal sequence ℕ → ι, using the Mittag-Leffler condition to
    build a compatible family of elements along this sequence, and then extending to all of ι.

  surjective_limit_of_mittagLeffler_exact (Theorem 5.2 of the paper):
    For a right exact sequence Aᵢ → Bᵢ → Cᵢ → 0 of inverse systems of R-modules over a
    countable directed index set, if the system (Aᵢ) is Mittag-Leffler, then the induced
    map lim←Bᵢ → lim←Cᵢ is surjective. This is the key result connecting the Mittag-Leffler
    condition on inverse systems to the module theory developed in the rest of the project.

We also define `InverseLimit` concretely as a subtype of ∀ i, Fᵢ (rather than using
Mathlib's built-in InverseSystem.limit, which is defined as a limit over elements strictly
below a given index and is unsuitable for our purposes), and prove basic structural results
including the stability of the Mittag-Leffler condition under direct products.
-/

import Mathlib.Order.DirectedInverseSystem
import Mathlib.Data.Set.Image
import Mathlib.Data.Countable.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Module.Submodule.Range

variable {ι : Type*} [Preorder ι]

namespace InverseSystem

/-- An inverse system (F, f) indexed by a preorder ι satisfies the Mittag-Leffler condition
if for each index i, the images of the transition maps stabilize: there exists j ≥ i such
that for all k ≥ j, the image of fₖᵢ : Fₖ → Fᵢ equals the image of fⱼᵢ : Fⱼ → Fᵢ.

This is the definition of Tag 0594 of the Stacks Project and Definition 5 of Section 5
of the paper. -/
class IsMittagLeffler (F : ι → Type*) [∀ i, Nonempty (F i)]
    (f : ∀ ⦃i j⦄, i ≤ j → F j → F i) [InverseSystem f] where
  stabilization : ∀ i : ι, ∃ j : ι, ∃ (hij : i ≤ j),
    ∀ k : ι, ∀ (hjk : j ≤ k), Set.range (f (hij.trans hjk)) = Set.range (f hij)

/-- A variant of the Mittag-Leffler condition asserting that, for each i, the images
im(fₖᵢ) and im(fₗᵢ) eventually agree for all sufficiently large k, l ≥ j. This is
equivalent to `IsMittagLeffler` in directed index sets; see
`eventuallyStableImages.to_IsMittagLeffler`. -/
def eventuallyStableImages (F : ι → Type*) [∀ i, Nonempty (F i)]
    (f : ∀ ⦃i j⦄, i ≤ j → F j → F i) [InverseSystem f] : Prop :=
  ∀ i : ι, ∃ j : ι, ∃ (hij : i ≤ j),
    ∀ k₁ k₂ : ι, ∀ (hjk₁ : j ≤ k₁) (hjk₂ : j ≤ k₂),
      Set.range (f (hij.trans hjk₁)) = Set.range (f (hij.trans hjk₂))

/-- Another equivalent formulation of the Mittag-Leffler condition: for each i, the
intersection ⋂_{k ≥ i} im(fₖᵢ) is achieved as a single image im(fⱼᵢ) for some j ≥ i. -/
def hasStableIntersection (F : ι → Type*) [∀ i, Nonempty (F i)]
    (f : ∀ ⦃i j⦄, i ≤ j → F j → F i) [InverseSystem f] : Prop :=
  ∀ i : ι, ∃ j : ι, ∃ (hij : i ≤ j),
    (⋂ k : {k // i ≤ k}, Set.range (f k.2)) = Set.range (f hij)

/-- The inverse limit of an inverse system (F, f), defined concretely as the subtype of
compatible families: elements x : ∀ i, Fᵢ satisfying fᵢⱼ(xⱼ) = xᵢ for all i ≤ j.

We use this concrete definition rather than Mathlib's built-in InverseSystem.limit, which
is defined as a limit over elements strictly below a given index and is unsuitable for our
purposes (see Section 5 of the paper). -/
def InverseLimit {ι : Type*} [Preorder ι] {F : ι → Type*}
    (f : ∀ ⦃i j⦄, i ≤ j → F j → F i) : Type _ :=
  { x : ∀ i, F i // ∀ i j (hij : i ≤ j), f hij (x j) = x i }

/-- Given a morphism of inverse systems (a compatible family of maps φᵢ : Fᵢ → Gᵢ), the
induced map on inverse limits sends (xᵢ) to (φᵢ(xᵢ)). Compatibility of (φᵢ) with the
transition maps ensures the result is a compatible family in the target system. -/
def InverseLimit.map
    {ι : Type*} [Preorder ι]
    {F G : ι → Type*}
    (fF : ∀ ⦃i j⦄, i ≤ j → F j → F i) [InverseSystem fF]
    (fG : ∀ ⦃i j⦄, i ≤ j → G j → G i) [InverseSystem fG]
    (φ : ∀ i, F i → G i)
    (hcompat : ∀ i j (h : i ≤ j), fG h ∘ φ j = φ i ∘ fF h) :
    InverseLimit fF → InverseLimit fG :=
  fun x => ⟨fun i => φ i (x.val i), fun i j h => by
    have := congr_fun (hcompat i j h) (x.val j)
    simp only [Function.comp_apply] at this
    rw [this, x.property i j h]⟩


section Equivalences

variable {F : ι → Type*} [∀ i, Nonempty (F i)]
variable (f : ∀ ⦃i j⦄, i ≤ j → F j → F i) [InverseSystem f]

/-- The main Mittag-Leffler condition implies the pairwise variant: if images stabilize
against a fixed reference level j, then any two sufficiently high levels have the same image. -/
theorem IsMittagLeffler.to_eventuallyStableImages [IsMittagLeffler F f] :
    eventuallyStableImages F f := by
  intro i
  obtain ⟨j, hij, hstab⟩ := IsMittagLeffler.stabilization (F := F) (f := f) i
  use j, hij
  intros k₁ k₂ hjk₁ hjk₂
  rw [hstab k₁ hjk₁, hstab k₂ hjk₂]

/-- In a directed preorder, the pairwise variant implies the main Mittag-Leffler condition:
given that any two high levels give the same image, we recover the stabilization against a
fixed reference level by comparing each k to j itself. -/
theorem eventuallyStableImages.to_IsMittagLeffler [IsDirected ι (· ≤ ·)]
    (h : eventuallyStableImages F f) : IsMittagLeffler F f where
  stabilization i := by
    obtain ⟨j, hij, hstab⟩ := h i
    use j, hij
    intros k hjk
    have : hij.trans hjk = (hij.trans le_rfl).trans hjk := by simp
    rw [this]
    exact (hstab j k (le_refl j) hjk).symm

end Equivalences

section Examples

variable {F : ℕ → Type*} [∀ n, Nonempty (F n)]

/-- A surjective inverse system is automatically Mittag-Leffler: when every transition map
is surjective, the image of each fₖᵢ is the full set Fᵢ for all k ≥ i, so stabilization
holds trivially at j = i itself. -/
theorem surjective_is_mittag_leffler (f : ∀ ⦃i j⦄, i ≤ j → F j → F i) [InverseSystem f]
    (hsurj : ∀ i j (hij : i ≤ j), Function.Surjective (f hij)) :
    IsMittagLeffler F f where
  stabilization i := by
    use i, le_refl i
    intros k hik
    have h1 : Set.range (f hik) = Set.univ :=
      Set.range_eq_univ.mpr (hsurj i k hik)
    have h2 : Set.range (f (le_refl i)) = Set.univ :=
      Set.range_eq_univ.mpr (hsurj i i (le_refl i))
    rw [h1, h2]

end Examples

section Properties

/-- In a countable directed nonempty preorder, there exists a monotone cofinal sequence
j : ℕ → ι. The construction uses surjectivity of the enumeration ℕ → ι (from countability)
and builds j by taking j(n+1) to be a common upper bound of j(n) and e(n+1), where e is
the surjection. Monotonicity and cofinality then follow by induction. -/
lemma exists_monotone_cofinal_nat {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] [Countable ι] :
    ∃ j : ℕ → ι, Monotone j ∧ ∀ i, ∃ n, i ≤ j n := by
  have henum : ∃ e : ℕ → ι, Function.Surjective e :=
    countable_iff_exists_surjective.mp ‹Countable ι›
  obtain ⟨e, he_surj⟩ := henum
  let j : ℕ → ι := fun n =>
    Nat.rec (e 0) (fun k jk => (directed_of (· ≤ ·) jk (e (k + 1))).choose) n
  use j
  constructor
  · intro m n hmn
    induction n with
    | zero => simp [Nat.le_zero.mp hmn]
    | succ n ih =>
      cases Nat.lt_or_eq_of_le hmn with
      | inl hlt =>
        have hle : m ≤ n := Nat.lt_succ_iff.mp hlt
        have h1 : j m ≤ j n := ih hle
        have h2 : j n ≤ j (n + 1) := (directed_of (· ≤ ·) (j n) (e (n + 1))).choose_spec.1
        exact le_trans h1 h2
      | inr heq => rw [heq]
  · intro i
    obtain ⟨n, rfl⟩ := he_surj i
    use n
    induction n with
    | zero => rfl
    | succ n _ =>
      exact (directed_of (· ≤ ·) (j n) (e (n + 1))).choose_spec.2

/-- For an inverse system over ℕ whose successive transition maps are surjective, the
inverse limit is nonempty. The proof constructs a compatible family by recursion: start
with an arbitrary element x₀ : F 0, and at each step use surjectivity of f(n, n+1) to
lift the current element to F(n+1). Compatibility for general m ≤ n then follows by
induction using the composition axiom for the inverse system. -/
lemma nonempty_inverseLimit_nat_of_surjective
    {F : ℕ → Type*} [∀ n, Nonempty (F n)]
    (f : ∀ m n, m ≤ n → F n → F m)
    (hcomp : ∀ m n k (hmn : m ≤ n) (hnk : n ≤ k), f m k (hmn.trans hnk) = f m n hmn ∘ f n k hnk)
    (hid : ∀ n, f n n le_rfl = id)
    (hsurj : ∀ n, Function.Surjective (f n (n + 1) (Nat.le_succ n))) :
    Nonempty { x : ∀ n, F n // ∀ m n (h : m ≤ n), f m n h (x n) = x m } := by
  have hstep : ∀ n (y : F n), ∃ z : F (n + 1), f n (n + 1) (Nat.le_succ n) z = y :=
    fun n y => hsurj n y
  let x₀ : F 0 := Classical.arbitrary (F 0)
  let x : ∀ n, F n := fun n =>
    Nat.rec x₀ (fun k xk => (hstep k xk).choose) n
  have hx_compat_succ : ∀ n, f n (n + 1) (Nat.le_succ n) (x (n + 1)) = x n := fun n => by
    simp only [x]
    exact (hstep n (Nat.rec x₀ (fun k xk => (hstep k xk).choose) n)).choose_spec
  have hx_compat : ∀ m n (h : m ≤ n), f m n h (x n) = x m := by
    intro m n h
    induction n with
    | zero =>
      have : m = 0 := Nat.le_zero.mp h
      subst this
      simp only [hid]
      rfl
    | succ n ih =>
      cases Nat.lt_or_eq_of_le h with
      | inl hlt =>
        have hle : m ≤ n := Nat.lt_succ_iff.mp hlt
        have h1 := ih hle
        have h2 := hx_compat_succ n
        rw [hcomp m n (n + 1) hle (Nat.le_succ n)]
        simp only [Function.comp_apply]
        rw [h2, h1]
      | inr heq =>
        subst heq
        simp only [hid]
        rfl
  exact ⟨⟨x, hx_compat⟩⟩

/-- Auxiliary result: in a Mittag-Leffler inverse system over a directed preorder, for any
i ≤ j the stable image at i is surjected onto by the stable image at j under fᵢⱼ. This
is used in the proof of `nonempty_inverseLimit_of_countable_mittagLeffler` to build
compatible lifts along the cofinal sequence. -/
lemma mittagLeffler_stable_image_surjective
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {F : ι → Type*} [∀ i, Nonempty (F i)]
    (f : ∀ ⦃i j⦄, i ≤ j → F j → F i) [InverseSystem f]
    [IsMittagLeffler F f] (i j : ι) (hij : i ≤ j) :
    ∃ (A_i : Set (F i)) (A_j : Set (F j)),
      A_i.Nonempty ∧ A_j.Nonempty ∧
      Set.SurjOn (f hij) A_j A_i := by
  obtain ⟨k_i, hik, hstab_i⟩ := IsMittagLeffler.stabilization (F := F) (f := f) i
  obtain ⟨k_j, hjk, hstab_j⟩ := IsMittagLeffler.stabilization (F := F) (f := f) j
  obtain ⟨k, hk_ki, hk_kj⟩ := directed_of (· ≤ ·) k_i k_j
  let A_i := Set.range (f (hik.trans hk_ki))
  let A_j := Set.range (f (hjk.trans hk_kj))
  use A_i, A_j
  refine ⟨Set.range_nonempty _, Set.range_nonempty _, ?_⟩
  intro x hx
  simp only [A_i, Set.mem_range] at hx
  obtain ⟨z, rfl⟩ := hx
  use f (hjk.trans hk_kj) z
  constructor
  · simp only [A_j, Set.mem_range]
    exact ⟨z, rfl⟩
  · -- f hij applied to the stable image at j gives the stable image at i,
    -- using the composition axiom for the inverse system
    have h1 : f hij (f (hjk.trans hk_kj) z) = f (hij.trans (hjk.trans hk_kj)) z := by
      apply InverseSystem.map_map

    have h2 : f (hij.trans (hjk.trans hk_kj)) z = f (hik.trans hk_ki) z := rfl
    rw [h1, h2]


/-- If ι is a countable directed nonempty preorder and (Fᵢ, fᵢⱼ) is a Mittag-Leffler
inverse system with each Fᵢ nonempty, then the inverse limit lim←Fᵢ is nonempty.

This is Theorem 5.1 of the paper and the key foundational result of this section.

The proof proceeds in several steps:
  (1) Extract a monotone cofinal sequence j : ℕ → ι using `exists_monotone_cofinal_nat`.
  (2) For each n, use the ML stabilization index k(n) ≥ j(n) to define stable images
      A(n) ⊆ F(j(n)).
  (3) Show that the transition maps f(j(n), j(n+1)) map A(n+1) surjectively onto A(n),
      by combining stabilization indices via a common upper bound and using the ML condition.
  (4) Build a compatible family x : ∀ n, F(j(n)) by recursion, starting in A(0) and
      lifting at each step using the surjectivity established in (3).
  (5) Extend the compatible family from the cofinal sequence to all of ι by pulling back
      along the transition maps, using the composition axiom to verify compatibility. -/
theorem nonempty_inverseLimit_of_countable_mittagLeffler
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    [Countable ι]
    {F : ι → Type*} [∀ i, Nonempty (F i)]
    (f : ∀ ⦃i j⦄, i ≤ j → F j → F i) [InverseSystem f]
    [IsMittagLeffler F f] :
    Nonempty (InverseLimit f) := by
  -- Step 1: Get a monotone cofinal sequence j : ℕ → ι
  obtain ⟨j, hj_mono, hj_cofinal⟩ := exists_monotone_cofinal_nat (ι := ι)

  -- Step 2: For each index i, get its stabilization index from ML condition
  have hML := fun i => IsMittagLeffler.stabilization (F := F) (f := f) i

  -- Step 3: Build a compatible family along the cofinal sequence by exploiting ML surjectivity
  have h_exists_compat : ∃ x : ∀ n, F (j n),
      ∀ m n (h : m ≤ n), f (hj_mono h) (x n) = x m := by
    have hstab : ∀ n, ∃ k, ∃ (hjnk : j n ≤ k),
        ∀ l (hkl : k ≤ l), Set.range (f (hjnk.trans hkl)) = Set.range (f hjnk) :=
      fun n => hML (j n)

    let k : ∀ n, ι := fun n => (hstab n).choose
    let hjnk : ∀ n, j n ≤ k n := fun n => (hstab n).choose_spec.choose
    let hstab_eq : ∀ n l (hkl : k n ≤ l),
        Set.range (f ((hjnk n).trans hkl)) = Set.range (f (hjnk n)) :=
      fun n => (hstab n).choose_spec.choose_spec

    -- For each n, get a common upper bound for k(n) and j(n+1)
    have hcommon : ∀ n, ∃ l, k n ≤ l ∧ j (n + 1) ≤ l :=
      fun n => directed_of (· ≤ ·) (k n) (j (n + 1))

    let l : ∀ n, ι := fun n => (hcommon n).choose
    let hkl : ∀ n, k n ≤ l n := fun n => (hcommon n).choose_spec.1
    let hjl : ∀ n, j (n + 1) ≤ l n := fun n => (hcommon n).choose_spec.2

    -- The transition f : F(j(n+1)) → F(j(n)) maps the stable image at j(n+1) surjectively
    -- onto the stable image at j(n), allowing us to build the sequence by dependent choice
    have hsurj_stable : ∀ (n : ℕ), ∀ y ∈ Set.range (f (hjnk n)),
        ∃ z ∈ Set.range (f (hjnk (n + 1))), f (hj_mono (Nat.le_succ n)) z = y := by
      intro n y hy
      obtain ⟨w, rfl⟩ := hy
      obtain ⟨m, hlm, hkm⟩ := directed_of (· ≤ ·) (l n) (k (n + 1))
      -- Use stabilization at j(n) with bound m to rewrite the stable image
      have hjnm : j n ≤ m := (hjnk n).trans ((hkl n).trans hlm)
      have hstab_n_m := hstab_eq n m ((hkl n).trans hlm)
      have hy_in_m : f (hjnk n) w ∈ Set.range (f hjnm) := by rw [hstab_n_m]; exact ⟨w, rfl⟩
      obtain ⟨a, ha⟩ := hy_in_m
      have hjm : j (n + 1) ≤ m := (hjl n).trans hlm
      use f hjm a
      refine ⟨?_, ?_⟩
      · -- f hjm a lies in the stable image at j(n+1) by stabilization
        have hstab_n1 := hstab_eq (n + 1) m hkm
        rw [← hstab_n1]
        exact ⟨a, rfl⟩
      · -- The transition map at the consecutive level sends f hjm a to the target
        have := InverseSystem.map_map (f := f) (hj_mono (Nat.le_succ n)) hjm a
        rw [this]
        exact ha
    -- Start in A(0) and build the sequence by dependent choice
    have hA0_nonempty : (Set.range (f (hjnk 0))).Nonempty := Set.range_nonempty _

    let x_with_mem : ∀ n, { y : F (j n) // y ∈ Set.range (f (hjnk n)) } := fun n =>
      Nat.rec
        ⟨f (hjnk 0) (Classical.arbitrary (F (k 0))), ⟨Classical.arbitrary (F (k 0)), rfl⟩⟩
        (fun m ⟨xm, hxm⟩ =>
          ⟨(hsurj_stable m xm hxm).choose, (hsurj_stable m xm hxm).choose_spec.1⟩)
        n

    let x : ∀ n, F (j n) := fun n => (x_with_mem n).val
    have hx_in_stable : ∀ n, x n ∈ Set.range (f (hjnk n)) := fun n => (x_with_mem n).property

    use x
    intro m n hmn

    induction n with
    | zero =>
      have : m = 0 := Nat.le_zero.mp hmn
      subst this
      simp only [InverseSystem.map_self]
    | succ n ih =>
      cases Nat.lt_or_eq_of_le hmn with
      | inl hlt =>
        have hle : m ≤ n := Nat.lt_succ_iff.mp hlt
        -- The consecutive step compatibility follows from the surjectivity construction
        have hsucc : f (hj_mono (Nat.le_succ n)) (x (n + 1)) = x n := by
          have : x (n + 1) = (hsurj_stable n (x n) (hx_in_stable n)).choose := rfl
          exact (hsurj_stable n (x n) (hx_in_stable n)).choose_spec.2
        -- Combine with the inductive hypothesis using the composition axiom
        have hcomp : f (hj_mono hmn) (x (n + 1)) =
          f (hj_mono hle) (f (hj_mono (Nat.le_succ n)) (x (n + 1))) := by
          have := InverseSystem.map_map (f := f) (hj_mono hle) (hj_mono (Nat.le_succ n)) (x (n + 1))
          exact this.symm
        rw [hcomp, hsucc, ih hle]
      | inr heq =>
        subst heq
        simp only [InverseSystem.map_self]


  obtain ⟨x_seq, hx_compat⟩ := h_exists_compat

  -- Step 4: Extend the compatible family from the cofinal sequence to all of ι
  -- For any i, pick n with i ≤ j(n) and define x(i) = f(i, j(n))(x_seq(n))
  have h_extend : ∃ x : ∀ i, F i, ∀ i k (h : i ≤ k), f h (x k) = x i := by
    let x : ∀ i, F i := fun i =>
      let n := (hj_cofinal i).choose
      let hi_jn : i ≤ j n := (hj_cofinal i).choose_spec
      f hi_jn (x_seq n)
    use x
    intro i k hik
    let ni := (hj_cofinal i).choose
    let hi_jni : i ≤ j ni := (hj_cofinal i).choose_spec
    let nk := (hj_cofinal k).choose
    let hk_jnk : k ≤ j nk := (hj_cofinal k).choose_spec
    let n := max ni nk
    have hni_n : ni ≤ n := Nat.le_max_left ni nk
    have hnk_n : nk ≤ n := Nat.le_max_right ni nk
    have hxi : x_seq ni = f (hj_mono hni_n) (x_seq n) := (hx_compat ni n hni_n).symm
    have hxk : x_seq nk = f (hj_mono hnk_n) (x_seq n) := (hx_compat nk n hnk_n).symm
    change f hik (f hk_jnk (x_seq nk)) = f hi_jni (x_seq ni)
    rw [hxi, hxk]
    -- Collapse both sides to f _ (x_seq n) using the composition axiom;
    -- the results are equal by proof irrelevance of the index inequality
    have lhs_eq : f hik (f hk_jnk (f (hj_mono hnk_n) (x_seq n))) =
                  f (hik.trans (hk_jnk.trans (hj_mono hnk_n))) (x_seq n) := by
      have h1 := InverseSystem.map_map (f := f) hk_jnk (hj_mono hnk_n) (x_seq n)
      rw [h1]
      have h2 := InverseSystem.map_map (f := f) hik (hk_jnk.trans (hj_mono hnk_n)) (x_seq n)
      rw [h2]
    have rhs_eq : f hi_jni (f (hj_mono hni_n) (x_seq n)) =
                  f (hi_jni.trans (hj_mono hni_n)) (x_seq n) := by
      exact InverseSystem.map_map (f := f) hi_jni (hj_mono hni_n) (x_seq n)
    rw [lhs_eq, rhs_eq]
  obtain ⟨x, hx⟩ := h_extend

  -- Step 5: Package as an element of InverseLimit
  exact ⟨⟨x, hx⟩⟩


/-- For a right exact sequence Aᵢ →fᵢ Bᵢ →gᵢ Cᵢ → 0 of inverse systems of R-modules over a
countable directed nonempty index set, if the inverse system (Aᵢ) is Mittag-Leffler, then
the induced map lim←Bᵢ → lim←Cᵢ is surjective.

This is Theorem 5.2 of the paper. It is the central tool connecting the Mittag-Leffler
condition on inverse systems to the module theory of the project, and is applied in the
proof of the main projectivity theorem (Theorem I) via the compatible family of lifts
in lim← Hom(Gᵢ, N₂) described in Section 8 of the paper.

The proof: given c = (cᵢ) ∈ lim← Cᵢ, define Eᵢ = gᵢ⁻¹(cᵢ) ⊆ Bᵢ. The fibers Eᵢ are
nonempty (by surjectivity of gᵢ) and form an inverse system (Eᵢ, fBᵢⱼ|Eⱼ). We show
this system is Mittag-Leffler by transferring the ML condition on (Aᵢ) via the exactness
hypothesis: an element of the stable image at level i that does not lift to the stable
image at level j can be corrected by adding an element from range(fᵢ) = ker(gᵢ), using
the ML condition on (Aᵢ) to stay within the stable images. Apply
`nonempty_inverseLimit_of_countable_mittagLeffler` to get an element (eᵢ) ∈ lim← Eᵢ,
whose underlying family (eᵢ.val) ∈ lim← Bᵢ maps to c. -/
theorem surjective_limit_of_mittagLeffler_exact
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] [Countable ι]
    {R : Type*} [Ring R]
    {A B C : ι → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)] [∀ i, AddCommGroup (C i)]
    [∀ i, Module R (A i)] [∀ i, Module R (B i)] [∀ i, Module R (C i)]
    [∀ i, Nonempty (A i)] [∀ i, Nonempty (B i)] [∀ i, Nonempty (C i)]
    (fA : ∀ ⦃i j⦄, i ≤ j → A j →ₗ[R] A i) [InverseSystem (fun i j h => (fA h))]
    (fB : ∀ ⦃i j⦄, i ≤ j → B j →ₗ[R] B i) [InverseSystem (fun i j h => (fB h))]
    (fC : ∀ ⦃i j⦄, i ≤ j → C j →ₗ[R] C i) [InverseSystem (fun i j h => (fC h))]
    (f : ∀ i, A i →ₗ[R] B i)
    (g : ∀ i, B i →ₗ[R] C i)
    (hg_surj : ∀ i, Function.Surjective (g i))
    (hexact : ∀ i, LinearMap.range (f i) = LinearMap.ker (g i))
    (hf_compat : ∀ i j (h : i ≤ j) (a : A j), fB h (f j a) = f i (fA h a))
    (hg_compat : ∀ i j (h : i ≤ j) (b : B j), fC h (g j b) = g i (fB h b))
    [IsMittagLeffler A (fun i j h => (fA h))] :
    Function.Surjective (InverseLimit.map
      (fun i j h => (fB h))
      (fun i j h => (fC h))
      (fun i => (g i))
      (fun i j h => by
        ext x
        exact hg_compat i j h x)) := by

  intro c

  -- Define the fiber Eᵢ = gᵢ⁻¹(cᵢ) ⊆ Bᵢ
  let E : ∀ i, Set (B i) := fun i => {b : B i | g i b = c.val i}

  -- Each fiber is nonempty by surjectivity of gᵢ
  have hE_nonempty : ∀ i, (E i).Nonempty := by
    intro i
    have : ∃ b : B i, g i b = c.val i := by
      apply hg_surj i
    obtain ⟨b,bprop⟩ := this
    have : b ∈ E i := by
      simp only [E]
      apply bprop
    rw [@Set.nonempty_iff_ne_empty]
    by_contra h
    rw[h] at this
    exact this

  -- The transition maps fB restrict to maps Eⱼ → Eᵢ, using compatibility of g with fB and fC
  have hE_maps : ∀ i j (h : i ≤ j) (b : B j), b ∈ E j → fB h b ∈ E i := by
    intro i j hij b bEj
    simp only [E]
    simp only [E] at bEj
    have jFact : (g j b) = c.val j := by
      apply bEj
    have key : (g i) ((fB hij) b) = c.val i := by
      rw [← hg_compat i j hij b]
      rw [jFact]
      exact c.property i j hij
    apply key

  -- The restricted maps form an inverse system
  let fE : ∀ ⦃i j⦄, i ≤ j → (E j) → (E i) :=
    fun i j h ⟨b, hb⟩ => ⟨fB h b, hE_maps i j h b hb⟩

  have hE_inverseSystem : InverseSystem fE := by
    constructor
    · intro i ⟨b, hb⟩
      apply Subtype.ext
      simp only [fE]
      exact @InverseSystem.map_self ι _ B (fun i j h => (fB h)) _ i b
    · intro i j k hij hjk ⟨b, hb⟩
      apply Subtype.ext
      simp only [fE]
      exact @InverseSystem.map_map ι _ B (fun i j h => (fB h)) _ i j k hij hjk b

  haveI : ∀ i, Nonempty (E i) := fun i => ⟨⟨(hE_nonempty i).choose, (hE_nonempty i).choose_spec⟩⟩

  -- The fiber system (Eᵢ, fE) is Mittag-Leffler, inherited from (Aᵢ) via exactness:
  -- elements outside the stable image at j can be corrected by adding from range(fᵢ) = ker(gᵢ)
  have hE_ML : IsMittagLeffler (fun i => E i) fE := by
      constructor
      intro i
      obtain ⟨j, hij, hstab_A⟩ :=
        IsMittagLeffler.stabilization (F := A) (f := fun i j h => (fA h)) i
      use j, hij
      intro k hjk
      ext ⟨b, hb⟩
      simp only [Set.mem_range]
      constructor
      · -- Image from k is contained in image from j: restrict via fB hjk
        intro ⟨⟨z, hz⟩, hzeq⟩
        have hzb : fB (hij.trans hjk) z = b := congrArg Subtype.val hzeq
        have hfB_hjk_z_mem : fB hjk z ∈ E j := hE_maps j k hjk z hz
        use ⟨fB hjk z, hfB_hjk_z_mem⟩
        apply Subtype.ext
        simp only [fE]
        rw [← hzb]
        exact @InverseSystem.map_map ι _ B (fun i j h => (fB h)) _ i j k hij hjk z
      · -- Image from j is contained in image from k: lift using ML on (Aᵢ) and exactness
        intro ⟨⟨y, hy⟩, hyeq⟩
        have hyb : fB hij y = b := congrArg Subtype.val hyeq
        obtain ⟨e_k, he_k⟩ := hE_nonempty k
        have hfB_hjk_ek_mem : fB hjk e_k ∈ E j := hE_maps j k hjk e_k he_k
        -- y - fB hjk e_k ∈ ker(gⱼ) = range(fⱼ) by exactness
        have hdiff_ker : y - fB hjk e_k ∈ LinearMap.ker (g j) := by
          rw [LinearMap.mem_ker, map_sub, hy, hfB_hjk_ek_mem, sub_self]
        rw [← hexact j] at hdiff_ker
        obtain ⟨a_j, ha_j⟩ := hdiff_ker
        -- Use ML on (Aᵢ): fA hij a_j ∈ range(fA (hij.trans hjk))
        have ha_j_in_range : fA hij a_j ∈ Set.range (fA (hij.trans hjk)) := by
          rw [hstab_A k hjk]
          exact ⟨a_j, rfl⟩
        obtain ⟨a_k, ha_k⟩ := ha_j_in_range
        -- Correct e_k by adding f(k)(a_k); the result maps correctly under fB and lies in Eₖ
        let z := e_k + f k a_k
        have hz : z ∈ E k := by
          simp only [E, Set.mem_setOf_eq, z, map_add]
          have : (g k) (f k a_k) = 0 := by
            rw [← LinearMap.mem_ker, ← hexact k]
            exact ⟨a_k, rfl⟩
          rw [this, add_zero]
          exact he_k
        use ⟨z, hz⟩
        apply Subtype.ext
        simp only [fE, z, map_add]
        have h1 : fB (hij.trans hjk) (f k a_k) = f i (fA (hij.trans hjk) a_k) :=
          hf_compat i k (hij.trans hjk) a_k
        rw [h1, ha_k]
        have h2 : f i (fA hij a_j) = b - fB (hij.trans hjk) e_k := by
          rw [← hf_compat i j hij a_j, ha_j, map_sub, hyb]
          congr 1
          exact @InverseSystem.map_map ι _ B (fun i j h => (fB h)) _ i j k hij hjk e_k
        rw [h2, add_sub_cancel]

  -- Apply nonempty_inverseLimit_of_countable_mittagLeffler to get (eᵢ) ∈ lim← Eᵢ
  have hE_limit_nonempty : Nonempty (@InverseLimit ι _ (fun i => E i) fE) :=
      @nonempty_inverseLimit_of_countable_mittagLeffler ι _ _ _ _ (fun i => E i)
        (fun i => ⟨⟨(hE_nonempty i).choose, (hE_nonempty i).choose_spec⟩⟩) fE hE_inverseSystem hE_ML

  obtain ⟨⟨e, he_compat⟩⟩ := hE_limit_nonempty

  -- The underlying family (eᵢ.val) is a compatible family in lim← Bᵢ mapping to c
  let b : InverseLimit (fun i j h => (fB h)) := ⟨fun i => (e i).val, fun i j h => by
    have := he_compat i j h
    simp only [fE] at this
    exact congrArg Subtype.val this⟩

  use b
  apply Subtype.ext
  funext i
  simp only [InverseLimit.map]
  exact (e i).property


end Properties

section DirectSum

variable {F G : ι → Type*} [∀ i, Nonempty (F i)] [∀ i, Nonempty (G i)]
variable (f : ∀ ⦃i j⦄, i ≤ j → F j → F i) [InverseSystem f]
variable (g : ∀ ⦃i j⦄, i ≤ j → G j → G i) [InverseSystem g]

/-- The product of two inverse systems, with the transition maps acting componentwise
on pairs (xᵢ, yᵢ) ∈ Fᵢ × Gᵢ. -/
def prodMap : ∀ ⦃i j⦄, i ≤ j → (F j × G j) → (F i × G i) :=
  fun _ _ hij ⟨x, y⟩ => (f hij x, g hij y)

/-- The componentwise product of two inverse systems is itself an inverse system:
the identity and composition axioms follow from those of the component systems. -/
instance prodInverseSystem : InverseSystem (prodMap f g) where
  map_self := fun i x => Prod.ext (InverseSystem.map_self x.1) (InverseSystem.map_self x.2)
  map_map := by
    intro k j i hkj hji x
    exact Prod.ext
      (InverseSystem.map_map (f := f) hkj hji x.1)
      (InverseSystem.map_map (f := g) hkj hji x.2)

/-- The range of the product map (f × g) is the cartesian product of the ranges of f and g. -/
lemma Set.range_prod_map {α β γ δ : Type*} (f : α → γ) (g : β → δ) :
    Set.range (fun x : α × β => (f x.1, g x.2)) = Set.range f ×ˢ Set.range g := by
  ext ⟨c, d⟩
  simp only [Set.mem_range, Set.mem_prod, Prod.ext_iff]
  constructor
  · rintro ⟨⟨a, b⟩, rfl, rfl⟩
    exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  · rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    exact ⟨(a, b), rfl, rfl⟩

/-- The product of two inverse systems is Mittag-Leffler if and only if each component
system is Mittag-Leffler. The key step uses `Set.range_prod_map` to translate image
stabilization for the product into stabilization for each component separately. -/
theorem isMittagLeffler_prod_iff [IsDirected ι (· ≤ ·)] :
    IsMittagLeffler (fun i => F i × G i) (prodMap f g) ↔
    IsMittagLeffler F f ∧ IsMittagLeffler G g := by
  constructor
  · -- Forward: product ML → each component ML
    intro hprod
    constructor
    · constructor
      intro i
      obtain ⟨j, hij, hstab⟩ := hprod.stabilization i
      use j, hij
      intro k hjk
      have hprod_stab := hstab k hjk
      unfold prodMap at hprod_stab
      rw [Set.range_prod_map, Set.range_prod_map] at hprod_stab
      have heq := Set.prod_eq_prod_iff.mp hprod_stab
      rcases heq with ⟨h1, _⟩ | ⟨hempty, _⟩
      · exact h1
      · exfalso
        rcases hempty with h | h
        · have : (Set.range (f (hij.trans hjk))).Nonempty := Set.range_nonempty _
          exact this.ne_empty h
        · have : (Set.range (g (hij.trans hjk))).Nonempty := Set.range_nonempty _
          exact this.ne_empty h
    · constructor
      intro i
      obtain ⟨j, hij, hstab⟩ := hprod.stabilization i
      use j, hij
      intro k hjk
      have hprod_stab := hstab k hjk
      unfold prodMap at hprod_stab
      rw [Set.range_prod_map, Set.range_prod_map] at hprod_stab
      have heq := Set.prod_eq_prod_iff.mp hprod_stab
      rcases heq with ⟨_, h2⟩ | ⟨hempty, _⟩
      · exact h2
      · exfalso
        rcases hempty with h | h
        · have : (Set.range (f (hij.trans hjk))).Nonempty := Set.range_nonempty _
          exact this.ne_empty h
        · have : (Set.range (g (hij.trans hjk))).Nonempty := Set.range_nonempty _
          exact this.ne_empty h
  · -- Backward: each component ML → product ML
    -- Take the maximum of the two stabilization indices and use directedness
    intro ⟨hF, hG⟩
    constructor
    intro i
    obtain ⟨jF, hijF, hstabF⟩ := hF.stabilization i
    obtain ⟨jG, hijG, hstabG⟩ := hG.stabilization i
    obtain ⟨j, hjF, hjG⟩ := directed_of (· ≤ ·) jF jG
    use j, hijF.trans hjF
    intro k hjk
    unfold prodMap
    rw [Set.range_prod_map, Set.range_prod_map]
    have hF_eq : Set.range (f ((hijF.trans hjF).trans hjk)) = Set.range (f (hijF.trans hjF)) := by
      have h1 := hstabF k (hjF.trans hjk)
      have h2 := hstabF j hjF
      rw [h1, h2]

    have hG_eq : Set.range (g ((hijG.trans hjG).trans hjk)) = Set.range (g (hijG.trans hjG)) := by
      have h1 := hstabG k (hjG.trans hjk)
      have h2 := hstabG j hjG
      rw [h1, h2]
    rw [hF_eq, hG_eq]

end DirectSum

end InverseSystem
