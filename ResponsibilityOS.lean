import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Responsibility OS Kernel

This file contains the ADIC assurance core and exposes it as a
Lean-verified Responsibility OS Kernel.

The central idea is that inspectability can be formalized as preservation of
policy-relevant responsibility distinctions. Under a complete policy, preserving
all such distinctions is equivalent to faithfulness.

The total responsibility category is derived by the Grothendieck construction,
so operations and responsibility evidence travel together.

The positive part proves preservation and unique factorization properties for
the responsibility layer.

The counterexample gives a minimal trace policy under which forgetting the
responsibility layer fails to preserve a specified responsibility distinction.
The connection to any concrete governance deployment is outside this file.
-/

universe uO vO uF vF

namespace ResponsibilityOS

open CategoryTheory

attribute [local simp] CategoryTheory.eqToHom_map

variable {O : Type uO} [Category.{vO} O]

/-- Indexed assurance data over an operational category.

The total evidence category is not a parameter.  It is derived as the
Grothendieck construction of `toCatFunctor`. -/
structure IndexedAssurance (O : Type uO) [Category.{vO} O] where
  Fiber : O → Type uF
  fiberCategory : ∀ X : O, Category.{vF} (Fiber X)
  push :
    ∀ {X Y : O}, (X ⟶ Y) →
      @Functor (Fiber X) (fiberCategory X) (Fiber Y) (fiberCategory Y)
  pull :
    ∀ {X Y : O}, (X ⟶ Y) →
      @Functor (Fiber Y) (fiberCategory Y) (Fiber X) (fiberCategory X)
  adj : ∀ {X Y : O} (f : X ⟶ Y), push f ⊣ pull f
  push_id :
    ∀ X : O,
      push (𝟙 X) = @Functor.id (Fiber X) (fiberCategory X)
  push_comp :
    ∀ {X Y Z : O} (f : X ⟶ Y) (g : Y ⟶ Z),
      push (f ≫ g) =
        @Functor.comp
          (Fiber X) (fiberCategory X)
          (Fiber Y) (fiberCategory Y)
          (Fiber Z) (fiberCategory Z)
          (push f) (push g)
  pull_id :
    ∀ X : O,
      pull (𝟙 X) = @Functor.id (Fiber X) (fiberCategory X)
  pull_comp :
    ∀ {X Y Z : O} (f : X ⟶ Y) (g : Y ⟶ Z),
      pull (f ≫ g) =
        @Functor.comp
          (Fiber Z) (fiberCategory Z)
          (Fiber Y) (fiberCategory Y)
          (Fiber X) (fiberCategory X)
          (pull g) (pull f)
  standard : ∀ X : O, Fiber X
  standard_push :
    ∀ {X Y : O} (f : X ⟶ Y),
      (push f).obj (standard X) = standard Y
  /-- `beck_chevalley` is an external structural assumption, not derived from
  the other fields. -/
  beck_chevalley :
    ∀ {X' X Y' Y : O}
      (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y),
      u ≫ f = f' ≫ v →
        @Functor.comp
          (Fiber X) (fiberCategory X)
          (Fiber Y) (fiberCategory Y)
          (Fiber Y') (fiberCategory Y')
          (push f) (pull v) =
        @Functor.comp
          (Fiber X) (fiberCategory X)
          (Fiber X') (fiberCategory X')
          (Fiber Y') (fiberCategory Y')
          (pull u) (push f')

/-- ADIC assurance core: an indexed evidence structure over an operational
category. Operations carry audit traces, responsibility records, and judgment
grounds through forward handoff and backward audit. -/
abbrev ADICAssuranceCore (O : Type uO) [Category.{vO} O] :=
  IndexedAssurance.{uO, vO, uF, vF} O

namespace IndexedAssurance

variable (A : IndexedAssurance.{uO, vO, uF, vF} O)

attribute [local instance] IndexedAssurance.fiberCategory

/-- The Cat-valued functor whose Grothendieck construction is the evidence category. -/
def toCatFunctor : O ⥤ Cat.{vF, uF} where
  obj X := Cat.of (A.Fiber X)
  map {X Y} f := A.push f
  map_id X := A.push_id X
  map_comp {X Y Z} f g := A.push_comp f g

/-- The derived total evidence category. -/
abbrev EvidenceCategory (A : IndexedAssurance.{uO, vO, uF, vF} O) :=
  Grothendieck (A.toCatFunctor)

/-- Forget evidence and recover the base operational category. -/
def forget (A : IndexedAssurance.{uO, vO, uF, vF} O) : EvidenceCategory A ⥤ O :=
  Grothendieck.forget A.toCatFunctor

/-- The standard evidence section. -/
def standardSection (A : IndexedAssurance.{uO, vO, uF, vF} O) : O ⥤ EvidenceCategory A where
  obj X := ⟨X, A.standard X⟩
  map {X Y} f :=
    { base := f
      fiber := eqToHom (A.standard_push f) }
  map_id X := by
    refine Grothendieck.ext _ _ (by rfl) ?_
    dsimp [Grothendieck.id]
    simp
  map_comp {X Y Z} f g := by
    refine Grothendieck.ext _ _ (by rfl) ?_
    dsimp [Grothendieck.comp]
    simp [eqToHom_trans]

/-- The standard section forgets to the identity functor on operations. -/
theorem section_eq : A.standardSection ⋙ A.forget = 𝟭 O := by
  rfl

/-- A section of a forgetful functor is faithful. -/
def faithful_of_section
    {E : Type*} [Category E]
    (U : E ⥤ O) (S : O ⥤ E)
    (hsection : S ⋙ U = 𝟭 O) : S.Faithful where
  map_injective {X Y} f g hfg := by
    have hmap : (S ⋙ U).map f = (S ⋙ U).map g := by
      change U.map (S.map f) = U.map (S.map g)
      rw [hfg]
    have hmap_id : (𝟭 O).map f = (𝟭 O).map g := by
      rw [hsection] at hmap
      exact hmap
    simpa using hmap_id

/-- Standard evidence tracing is faithful. -/
theorem section_faithful : A.standardSection.Faithful :=
  faithful_of_section A.forget A.standardSection A.section_eq

/-- Opcartesian lift candidate supplied by the Grothendieck construction. -/
def opcartLift {X Y : O} (f : X ⟶ Y) (a : A.Fiber X) :
    (⟨X, a⟩ : EvidenceCategory A) ⟶ ⟨Y, (A.push f).obj a⟩ where
  base := f
  fiber := 𝟙 _

/-- Cartesian lift candidate built from the counit of `push f ⊣ pull f`. -/
def cartLift {X Y : O} (f : X ⟶ Y) (b : A.Fiber Y) :
    (⟨X, (A.pull f).obj b⟩ : EvidenceCategory A) ⟶ ⟨Y, b⟩ where
  base := f
  fiber := (A.adj f).counit.app b

/-- Strict split law for forward transport. -/
theorem push_opcart_split
    {X Y Z : O} (f : X ⟶ Y) (g : Y ⟶ Z) (a : A.Fiber X) :
    (A.push (f ≫ g)).obj a = (A.push g).obj ((A.push f).obj a) := by
  rw [A.push_comp f g]
  rfl

/-- Fiber-level universal property of the opcartesian lift: a map out of
`push (f ≫ g) a` is uniquely the same as a map out of
`push g (push f a)` after the split identification. -/
theorem opcart_univ
    {X Y Z : O} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : A.Fiber X) (c : A.Fiber Z)
    (γ : (A.push (f ≫ g)).obj a ⟶ c) :
    ∃! (δ : (A.push g).obj ((A.push f).obj a) ⟶ c),
      δ = eqToHom (A.push_opcart_split f g a).symm ≫ γ := by
  refine ⟨eqToHom (A.push_opcart_split f g a).symm ≫ γ, rfl, ?_⟩
  intro δ hδ
  exact hδ

/-- Strict split law for backward audit pullback. -/
theorem pull_cart_split
    {X Y Z : O} (f : X ⟶ Y) (g : Y ⟶ Z) (b : A.Fiber Z) :
    (A.pull (f ≫ g)).obj b = (A.pull f).obj ((A.pull g).obj b) := by
  rw [A.pull_comp f g]
  rfl

/-- Fiber-level universal property of the cartesian lift, expressed through
the adjunction `push f ⊣ pull f`. -/
theorem cart_univ
    {X Y Z : O} (f : X ⟶ Y) (k : Z ⟶ X)
    (b : A.Fiber Y) (c : A.Fiber Z)
    (α : (A.push (k ≫ f)).obj c ⟶ b) :
    ∃! (β : (A.push k).obj c ⟶ (A.pull f).obj b),
      β =
        (A.adj f).homEquiv ((A.push k).obj c) b
          (eqToHom (A.push_opcart_split k f c).symm ≫ α) := by
  refine ⟨
    (A.adj f).homEquiv ((A.push k).obj c) b
      (eqToHom (A.push_opcart_split k f c).symm ≫ α),
    rfl,
    ?_⟩
  intro β hβ
  exact hβ

/-- Total-category-level opcartesian universal property.

Any evidence morphism `h : ⟨X, a⟩ ⟶ ⟨Z, c⟩` whose base equals `f ≫ g`
factors uniquely through the opcartesian lift
`opcartLift f a : ⟨X, a⟩ ⟶ ⟨Y, push f a⟩`. The unique factoring
morphism has base `g` and fiber component determined by `h.fiber` after
the strict split identification. -/
theorem opcart_factor
    {X Y Z : O} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : A.Fiber X) (c : A.Fiber Z)
    (h : (⟨X, a⟩ : EvidenceCategory A) ⟶ ⟨Z, c⟩)
    (hbase : h.base = f ≫ g) :
    ∃! (δ : (⟨Y, (A.push f).obj a⟩ : EvidenceCategory A) ⟶ ⟨Z, c⟩),
        δ.base = g ∧
          A.opcartLift f a ≫ δ = h := by
  cases h with
  | mk hb hf =>
  dsimp at hbase
  subst hb
  let δ₀ : (⟨Y, (A.push f).obj a⟩ : EvidenceCategory A) ⟶ ⟨Z, c⟩ :=
    { base := g
      fiber := by
        change (A.push g).obj ((A.push f).obj a) ⟶ c
        exact eqToHom (A.push_opcart_split f g a).symm ≫ hf }
  refine ⟨δ₀, ⟨rfl, ?_⟩, ?_⟩
  · refine Grothendieck.ext
      (A.opcartLift f a ≫ δ₀)
      { base := f ≫ g, fiber := hf } (by rfl) ?_
    simp [δ₀, opcartLift, Grothendieck.comp]
  · intro δ hδ
    rcases hδ with ⟨hδbase, hδfact⟩
    refine Grothendieck.ext δ δ₀ hδbase ?_
    have hfib := congr_arg_heq
      (fun q : (⟨X, a⟩ : EvidenceCategory A) ⟶ ⟨Z, c⟩ => q.fiber)
      hδfact
    simp [opcartLift, Grothendieck.comp] at hfib
    exact eq_of_heq <|
      (eqToHom_comp_heq δ.fiber (by rw [hδbase])).trans <|
        hfib.trans (eqToHom_comp_heq hf (A.push_opcart_split f g a).symm).symm

/-- Total-category-level cartesian universal property.

Any evidence morphism `h : ⟨Z, c⟩ ⟶ ⟨Y, b⟩` whose base equals `k ≫ f`
factors uniquely through the cartesian lift
`cartLift f b : ⟨X, pull f b⟩ ⟶ ⟨Y, b⟩`. The unique factoring morphism
has base `k` and fiber component determined by the adjunction hom-equivalence
applied to `h.fiber`. -/
theorem cart_factor
    {X Y Z : O} (f : X ⟶ Y) (k : Z ⟶ X)
    (b : A.Fiber Y) (c : A.Fiber Z)
    (h : (⟨Z, c⟩ : EvidenceCategory A) ⟶ ⟨Y, b⟩)
    (hbase : h.base = k ≫ f) :
    ∃! (δ : (⟨Z, c⟩ : EvidenceCategory A) ⟶ ⟨X, (A.pull f).obj b⟩),
        δ.base = k ∧
          δ ≫ A.cartLift f b = h := by
  cases h with
  | mk hb hf =>
  dsimp at hbase
  subst hb
  set ev_wit :=
    (A.adj f).homEquiv ((A.push k).obj c) b
      (eqToHom (A.push_opcart_split k f c).symm ≫ hf)
    with ev_wit_def
  let δ₀ : (⟨Z, c⟩ : EvidenceCategory A) ⟶ ⟨X, (A.pull f).obj b⟩ :=
    { base := k
      fiber := by
        change (A.push k).obj c ⟶ (A.pull f).obj b
        exact ev_wit }
  refine ⟨δ₀, ⟨rfl, ?_⟩, ?_⟩
  · refine Grothendieck.ext
      (δ₀ ≫ A.cartLift f b)
      { base := k ≫ f, fiber := hf } (by rfl) ?_
    dsimp [δ₀, cartLift, Grothendieck.comp]
    rw [ev_wit_def, ← Adjunction.homEquiv_counit]
    change 𝟙 ((A.push (k ≫ f)).obj c) ≫
        eqToHom (A.push_opcart_split k f c) ≫
          ((A.adj f).homEquiv ((A.push k).obj c) b).symm
            (((A.adj f).homEquiv ((A.push k).obj c) b)
              (eqToHom (A.push_opcart_split k f c).symm ≫ hf)) =
      hf
    rw [Equiv.symm_apply_apply]
    simp
  · intro δ hδ
    rcases hδ with ⟨hδbase, hδfact⟩
    refine Grothendieck.ext δ δ₀ hδbase ?_
    have hfib := congr_arg_heq
      (fun q : (⟨Z, c⟩ : EvidenceCategory A) ⟶ ⟨Y, b⟩ => q.fiber)
      hδfact
    simp [cartLift] at hfib
    apply (((A.adj f).homEquiv ((A.push k).obj c) b).symm).injective
    dsimp [δ₀]
    rw [ev_wit_def]
    rw [Equiv.symm_apply_apply]
    rw [Adjunction.homEquiv_counit]
    rw [Functor.map_comp, eqToHom_map]
    rw [Category.assoc]
    exact eq_of_heq <|
      (eqToHom_comp_heq
        ((A.push f).map δ.fiber ≫ (A.adj f).counit.app b)
        (by rw [hδbase]; rfl)).trans <|
        hfib.trans (eqToHom_comp_heq hf (A.push_opcart_split k f c).symm).symm

end IndexedAssurance

/-- The Responsibility OS kernel is the ADIC assurance core viewed as a
composition-preserving responsibility layer. -/
abbrev Kernel (O : Type uO) [Category.{vO} O] :=
  ADICAssuranceCore.{uO, vO, uF, vF} O

attribute [local instance] IndexedAssurance.fiberCategory

/-- The total responsibility category: operations and responsibility evidence
travel together. -/
abbrev responsibilityCategory (K : Kernel.{uO, vO, uF, vF} O) : Type _ :=
  IndexedAssurance.EvidenceCategory K

/-- Forget the responsibility layer and recover the base operational category. -/
abbrev forgetOperations (K : Kernel.{uO, vO, uF, vF} O) :
    responsibilityCategory K ⥤ O :=
  IndexedAssurance.forget K

/-- The standard responsibility trace section. -/
abbrev standardTrace (K : Kernel.{uO, vO, uF, vF} O) :
    O ⥤ responsibilityCategory K :=
  IndexedAssurance.standardSection K

/-- The standard responsibility trace forgets to the identity operational process. -/
theorem responsibility_section_forgets_to_identity
    (K : Kernel.{uO, vO, uF, vF} O) :
    standardTrace K ⋙ forgetOperations K = 𝟭 O :=
  IndexedAssurance.section_eq K

/-- The standard responsibility trace is faithful: distinct operational
transitions remain distinct when carried with their responsibility trace. -/
theorem standard_trace_is_faithful
    (K : Kernel.{uO, vO, uF, vF} O) :
    (standardTrace K).Faithful :=
  IndexedAssurance.section_faithful K

/-- Forward responsibility handoff factors uniquely through the canonical
responsibility-carrying lift. -/
theorem forward_handoff_factors_uniquely
    (K : Kernel.{uO, vO, uF, vF} O)
    {X Y Z : O} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : K.Fiber X) (c : K.Fiber Z)
    (h : (⟨X, a⟩ : responsibilityCategory K) ⟶ ⟨Z, c⟩)
    (hbase : h.base = f ≫ g) :
    ∃! (δ : (⟨Y, (K.push f).obj a⟩ : responsibilityCategory K) ⟶ ⟨Z, c⟩),
        δ.base = g ∧
          IndexedAssurance.opcartLift K f a ≫ δ = h :=
  IndexedAssurance.opcart_factor K f g a c h hbase

/-- Backward audit factors uniquely through the canonical audit lift. -/
theorem backward_audit_factors_uniquely
    (K : Kernel.{uO, vO, uF, vF} O)
    {X Y Z : O} (f : X ⟶ Y) (k : Z ⟶ X)
    (b : K.Fiber Y) (c : K.Fiber Z)
    (h : (⟨Z, c⟩ : responsibilityCategory K) ⟶ ⟨Y, b⟩)
    (hbase : h.base = k ≫ f) :
    ∃! (δ : (⟨Z, c⟩ : responsibilityCategory K) ⟶ ⟨X, (K.pull f).obj b⟩),
        δ.base = k ∧
          δ ≫ IndexedAssurance.cartLift K f b = h :=
  IndexedAssurance.cart_factor K f k b c h hbase

/-- A policy specifying which evidence distinctions must remain inspectable. -/
structure ObservationPolicy
    (E : Type*) [Category E] where
  relevant :
    ∀ {X Y : E}, (X ⟶ Y) → (X ⟶ Y) → Prop
  sound :
    ∀ {X Y : E} {f g : X ⟶ Y}, relevant f g → f ≠ g

/-- A visible view is inspectable for a policy if it preserves every
policy-relevant distinction. -/
def PreservesPolicy
    {E O : Type*} [Category E] [Category O]
    (U : E ⥤ O) (P : ObservationPolicy E) : Prop :=
  ∀ {X Y : E} {f g : X ⟶ Y},
    P.relevant f g → U.map f ≠ U.map g

/-- Complete inspectability: every genuine evidence distinction is relevant. -/
def CompletePolicy
    (E : Type*) [Category E] : ObservationPolicy E where
  relevant := fun f g => f ≠ g
  sound := by
    intro X Y f g h
    exact h

/-- Preserving all evidence distinctions is exactly faithfulness. -/
theorem preserves_complete_policy_iff_faithful
    {E O : Type*} [Category E] [Category O]
    (U : E ⥤ O) :
    PreservesPolicy U (CompletePolicy E) ↔ U.Faithful := by
  constructor
  · intro h
    exact
      { map_injective := by
          intro X Y f g hmap
          by_contra hne
          exact (h hne) hmap }
  · intro hF
    intro X Y f g hne hmap
    exact hne (hF.map_injective hmap)

/-- Therefore, complete inspectability requires a faithful visible view. -/
theorem complete_inspectability_requires_faithful
    {E O : Type*} [Category E] [Category O]
    (U : E ⥤ O) :
    PreservesPolicy U (CompletePolicy E) → U.Faithful :=
  (preserves_complete_policy_iff_faithful U).mp

/-- Conversely, a non-faithful visible view cannot be completely inspectable. -/
theorem nonfaithful_view_not_completely_inspectable
    {E O : Type*} [Category E] [Category O]
    (U : E ⥤ O) :
    ¬ U.Faithful → ¬ PreservesPolicy U (CompletePolicy E) := by
  intro hNF hP
  exact hNF ((preserves_complete_policy_iff_faithful U).mp hP)

namespace CollapseCounterexample

/-!
## Collapse counterexample

This finite counterexample is independent from the indexed construction above:
it shows that forgetting the trace layer can identify distinct
governance-relevant evidence morphisms.
-/

/-- Evidence objects: one source and one target. -/
inductive EObj : Type
  | src : EObj
  | tgt : EObj

/-- Evidence morphisms: two distinct traces from source to target. -/
inductive EHom : EObj → EObj → Type
  | idSrc : EHom EObj.src EObj.src
  | idTgt : EHom EObj.tgt EObj.tgt
  | traceA : EHom EObj.src EObj.tgt
  | traceB : EHom EObj.src EObj.tgt

instance : Category EObj where
  Hom := EHom
  id := fun X =>
    match X with
    | .src => .idSrc
    | .tgt => .idTgt
  comp := fun {X Y Z} f g =>
    match f, g with
    | .idSrc, .idSrc => .idSrc
    | .idSrc, .traceA => .traceA
    | .idSrc, .traceB => .traceB
    | .traceA, .idTgt => .traceA
    | .traceB, .idTgt => .traceB
    | .idTgt, .idTgt => .idTgt
  id_comp := by intro X Y f; cases f <;> simp [CategoryStruct.id, CategoryStruct.comp]
  comp_id := by intro X Y f; cases f <;> simp [CategoryStruct.id, CategoryStruct.comp]
  assoc := by intro X Y Z W f g h; cases f <;> cases g <;> cases h <;> rfl

theorem traceA_ne_traceB : EHom.traceA ≠ EHom.traceB := by
  intro h
  cases h

/-- Operational objects: one source and one target. -/
inductive OObj : Type
  | src : OObj
  | tgt : OObj

/-- Operational morphisms: a single visible operation from source to target. -/
inductive OHom : OObj → OObj → Type
  | idSrc : OHom OObj.src OObj.src
  | idTgt : OHom OObj.tgt OObj.tgt
  | vis : OHom OObj.src OObj.tgt

instance : Category OObj where
  Hom := OHom
  id := fun X =>
    match X with
    | .src => .idSrc
    | .tgt => .idTgt
  comp := fun {X Y Z} f g =>
    match f, g with
    | .idSrc, .idSrc => .idSrc
    | .idSrc, .vis => .vis
    | .vis, .idTgt => .vis
    | .idTgt, .idTgt => .idTgt
  id_comp := by intro X Y f; cases f <;> simp [CategoryStruct.id, CategoryStruct.comp]
  comp_id := by intro X Y f; cases f <;> simp [CategoryStruct.id, CategoryStruct.comp]
  assoc := by intro X Y Z W f g h; cases f <;> cases g <;> cases h <;> rfl

/-- Forgetful operational view: both evidence traces become the same operation. -/
def U : EObj ⥤ OObj where
  obj := fun X =>
    match X with
    | .src => .src
    | .tgt => .tgt
  map := fun {X Y} f =>
    match f with
    | .idSrc => .idSrc
    | .idTgt => .idTgt
    | .traceA => OHom.vis
    | .traceB => OHom.vis
  map_id := by intro X; cases X <;> simp [CategoryStruct.id]
  map_comp := by
    intro X Y Z f g
    cases f <;> cases g <;> simp [CategoryStruct.comp, CategoryStruct.id]

theorem trace_distinction_collapses :
    EHom.traceA ≠ EHom.traceB ∧
      U.map EHom.traceA = U.map EHom.traceB := by
  exact ⟨traceA_ne_traceB, rfl⟩

theorem U_not_faithful : ¬ U.Faithful := by
  intro hF
  have hEq : EHom.traceA = EHom.traceB := hF.map_injective (by rfl)
  exact traceA_ne_traceB hEq

/-- The minimal observation policy for the collapse counterexample: the two
responsibility traces from `src` to `tgt` must remain distinguishable. -/
def tracePolicy : ObservationPolicy EObj where
  relevant := fun {X Y} f g =>
    match X, Y, f, g with
    | EObj.src, EObj.tgt, EHom.traceA, EHom.traceB => True
    | EObj.src, EObj.tgt, EHom.traceB, EHom.traceA => True
    | _, _, _, _ => False
  sound := by
    intro X Y f g h
    cases X <;> cases Y <;> cases f <;> cases g <;> simp at h
    · exact traceA_ne_traceB
    · intro hEq
      exact traceA_ne_traceB hEq.symm

/-- The two traces in the counterexample are policy-relevant. -/
theorem trace_policy_relevant :
    tracePolicy.relevant EHom.traceA EHom.traceB := by
  simp [tracePolicy]

/-- The operational view `U` does not preserve the minimal trace policy:
the two policy-relevant traces collapse to the same visible operation. -/
theorem U_does_not_preserve_trace_policy :
    ¬ PreservesPolicy U tracePolicy := by
  intro h
  exact (h trace_policy_relevant) rfl

/-- Finite counterexample: operational sameness does not imply governance
sameness.

Two morphisms representing distinct judgment grounds or responsibility paths
can map to the same visible operation under a forgetful functor. Therefore a
forgetful functor need not be faithful, and governance-relevant distinctions
can be permanently lost.

Paper interpretation: if AI governance requires those distinctions to remain
inspectable after composition, a faithful trace/evidence layer is structurally
required. This theorem establishes the counterexample component of the
necessity direction. -/
theorem forgetting_trace_layer_can_collapse_distinctions :
    ∃ (E : Type) (_ : Category.{0} E)
      (O : Type) (_ : Category.{0} O)
      (U : E ⥤ O),
      ¬ U.Faithful := by
  exact ⟨EObj, inferInstance, OObj, inferInstance, U, U_not_faithful⟩

end CollapseCounterexample

/-- If the responsibility layer is forgotten, governance-relevant distinctions
can collapse. -/
theorem forgetting_responsibility_layer_can_collapse_distinctions :
    ∃ (E : Type) (_ : Category.{0} E)
      (O : Type) (_ : Category.{0} O)
      (U : E ⥤ O),
      ¬ U.Faithful :=
  CollapseCounterexample.forgetting_trace_layer_can_collapse_distinctions

/-- If inspectability is formalized as preserving all responsibility
distinctions, an operational-only view can fail: there exists a finite
category-theoretic counterexample where forgetting the responsibility layer is
not faithful.

This is a kernel-level counterexample, not a legal, social, or empirical
claim about any concrete deployment. -/
theorem inspectable_governance_requires_faithful_responsibility_layer_counterexample :
    ∃ (E : Type) (_ : Category.{0} E)
      (O : Type) (_ : Category.{0} O)
      (U : E ⥤ O),
      ¬ U.Faithful :=
  forgetting_responsibility_layer_can_collapse_distinctions

/-- In the finite counterexample, the two distinct traces are relevant under
the explicit observation policy. -/
theorem trace_policy_distinction_is_relevant :
    CollapseCounterexample.tracePolicy.relevant
      CollapseCounterexample.EHom.traceA
      CollapseCounterexample.EHom.traceB :=
  CollapseCounterexample.trace_policy_relevant

/-- The operational view in the finite counterexample does not preserve the
explicit trace policy: the relevant trace distinction is collapsed. -/
theorem operational_view_does_not_preserve_trace_policy :
    ¬ PreservesPolicy
      CollapseCounterexample.U
      CollapseCounterexample.tracePolicy :=
  CollapseCounterexample.U_does_not_preserve_trace_policy

end ResponsibilityOS
