import substances math.fuzzy
open set topological_space classical
set_option pp.generalized_field_notation true
local attribute [instance] prop_decidable
noncomputable theory

-- tentative idea for formalizing ppc via intensional similarities
-- in a variant of nuclear trope theory

namespace ontology

variable {ω : ontology}

namespace iontology
/-- Intensional similarity relation -/
structure sim (Ω : ω.iontology) :=
  (r : Ω.ientity → Ω.ientity → ω.world → fuzzy)
  (reflexive : ∀ {e : Ω.ientity} {w}, e.exists w → r e e w = 1)
  (symmetric : ∀ {e₁ e₂}, r e₁ e₂ = r e₂ e₁)
  -- I think this follows from the stronger property of transitivity discussed by Zadeh
  (triangular : ∀ (w) e₁ e₂ e₃, ((r e₁ e₂ w) : ℝ) * (r e₂ e₃ w) ≤ r e₁ e₃ w)
  (tolerance : fuzzy  := 0)
  -- TODO: prove this as a theorem, follows from triangular inequality
  -- (subst : ∀ e₁ e₂, r e₁ e₂ = 1 → ∀ e₃, r e₁ e₃ = r e₂ e₃)
  -- these principles are probably wrong, will think about them later.
  -- consubstantial entities with the same essence are exactly similar
  -- (coessence : ∀ e₁ e₂, 0 < r e₁ e₂ → e₁ ≈ e₂ → r e₁ e₂ = 1)
  -- -- substances do not have the same essence as their accidents
  -- (essence : ∀ e₁ e₂, 0 < r e₁ e₂ → e₁ ≈ e₂ → e₁ ⇎ e₂ → ¬ e₁.up.compatible e₂)

attribute [class] sim
attribute [simp, refl] sim.reflexive
attribute [simp, symm] sim.symmetric

section basic
variables {Ω : ω.iontology} [sim : Ω.sim] (e : Ω.ientity)
include sim

/-- An entity is said to be **wholly dissimilar** to another if 
    their similarity is always 0. -/
def wdiss (e' : Ω.ientity) : Prop := ∀ w, 0 = sim.r e e' w

/-- An entity is said to be **similar** to another, 
    if it is not wholly dissimilar to it, i.e. if
    their similarity is strictly greater than 0. -/
def similar (e' : Ω.ientity) : Prop := ¬ wdiss e e'

/-- An entity is said to be **exactly similar** to, or **indiscernible** from, 
    another if their similarity is always 1. -/
def esimilar (e' : Ω.ientity) : Prop := ∀ w, 1 = sim.r e e' w

local infixr ` ≅ `:50 := similar
local infixr ` ≇ `:50 := wdiss
-- TODO: maybe set == notation for esimilar.

-- fuzzy needs has_Inf. Will need to migrate to newer
-- version of mathlib to make this work properly.
/-- Infimum degree of similarity between two entities.
    Introduced so we can get rid of possible worlds. -/
def ientity.sim (e₁ : Ω.ientity) (e₂ : Ω.ientity) : fuzzy := sorry --Inf $ sim.r e₁ e₂ '' univ

-- -- TODO: check later if this is indeed a good definition
-- /-- A **bare particular** is an entity wholly dissimilar to any entity distinct from itself. -/
-- def ientity.bare : Prop := ∀ e', e' ≠ e → e' ≇ e

-- /-- A **trope like** entity is a non-bare particular which is incompatible with any entity
--     distinct, similar and consubstantial to itself. -/
-- def ientity.trope_like : Prop := ¬ e.bare ∧ ∀ e', e' ≠ e → e' ≈ e → e' ≅ e → ¬ e'.up.compatible e

-- /-- A **strongly trope like** entity is an entity which is only similar to trope like entities. -/
-- def ientity.strope_like : Prop := ∀ e', e' ≅ e → e'.trope_like

-- /-- A **bare like** entity is an entity wholly dissimilar from all trope like entities,
--     which is however not necessarily a bare particular. -/
-- def ientity.substratum : Prop := ∀ e' : Ω.ientity, e'.trope_like → e' ≇ e


-- substrata in the same nucleus (i.e. equivalent) have the same essence
-- def substratum_sim : Prop := ∀ e₁ e₂ : Ω.ientity, e₁.substratum → e₂.substratum → e₁ ≡ e₂ → e₁ ≅ e₂
-- -- whatever 
-- def sim_closure : Prop := ∀ e₁ e₂ : Ω.ientity, e₁.trope → e₁ ≅ e₂ → e₂.trope

-- TODO: we may need a notion of the origin trope being more perfect than
-- the caused entity.
-- def ppc (c : Ω.ientity → Ω.ientity → ω.event) : Prop :=
--   ∀ e₁ e₂, ⋄c e₁ e₂ → 
--   ∃ trope, trope ≈ e₁ ∧ trope ≅ e₂ ∧ trope ≠ e₂ 
--   ∧ trope.strope_like ∧ c e₁ e₂ ⇒' trope.exists ∧ 
--   ∀ e₃, c e₃ trope ∩ c e₁ e₂ ⇒ c e₃ e₂

-- needs has_Inf
/-- Infimum possible degree of similarity among entities of a set. -/
def inf_sim (C : set Ω.ientity) : fuzzy := sorry --Inf {d : fuzzy | ∃ (w : ω.world) e₁ e₂ ∈ C, sim.r e₁ e₂ w = d}

/-- Infimum degree of similarity among entities in a possible world. -/
def sim.inf_sim_at (sim : Ω.sim) (w : ω.world) : fuzzy := sorry --Inf {d : fuzzy | ∃ e₁ e₂ ∈ w, sim.r e₁ e₂ w = d}

-- needs has_Sup
/-- Supremum possible degree of similarity among entities of a set. -/
def sup_sim (C : set Ω.ientity) : fuzzy := sorry -- Sup {d : fuzzy | ∃ (w : ω.world) e₁ e₂ ∈ C, e₁ ≠ e₂ ∧ sim.r e₁ e₂ w = d}

/-- Supremum degree of similarity among distinct entities in a possible world. -/
def sim.sup_sim_at (sim : Ω.sim) (w : ω.world) : fuzzy := sorry -- Sup {d : fuzzy | ∃ e₁ e₂ ∈ w, e₁ ≠ e₂ ∧ sim.r e₁ e₂ w = d}

-- needs has_Sup
/-- Supremum possible degree of similarity between a set and an entity. -/
def sdsim (e : Ω.ientity) (C : set Ω.ientity) : fuzzy := sorry --Sup {d : fuzzy | ∃ (w : ω.world) e' ∈ C, sim.r e e' w = d}

/-- Supremum degree of similarity between an entity and the entities which exist in a possible world. -/
def sdsim_at (e : Ω.ientity) (w : ω.world) : fuzzy := sorry --Sup {d : fuzzy | ∃ e' ∈ w, sim.r e e' w = d}

/-- A **resemblance class** is a set of entities which always resemble each other at least as much as they
    might resemble any entity outside of the set. -/
def rclass (C : set Ω.ientity) : Prop := 
  ∀ e ∈ C, sdsim e (-C) ≤ inf_sim C

/-- A **strict resemblance class** is a set of entities which always resemble each other more than they
    might resemble any entity outside of the set. -/
def srclass (C : set Ω.ientity) : Prop := 
  ∀ e ∈ C, sdsim e (-C) < inf_sim C

-- don't know if we will need it. Left incomplete
-- /-- A **local resemblance class** is a set of entities which, within some world `w`, 
--     resemble each other more than they
--     resemble, in `w`, any entity outside of the set. -/
-- def lrclass (C : set Ω.ientity) (w : ω.world) : Prop := 
--   ∀ e ∈ C, sdsim e (-C) ≤ inf_sim C

/-- A set of entities is **simply independent** if its distinct elements are pairwise independent, i.e. incomparable. -/
def sindependent (C : set Ω.ientity) : Prop := ∀ e₁ e₂ ∈ C, e₁ ≠ e₂ → e₁ ≢ e₂

/-- A **clique** of degree **d**, or d-clique, is a set 
    of entities which are similar to each 
    other to degree at least **d** in any possible world. -/
def clique (d : fuzzy) (C : set Ω.ientity) : Prop :=
  ∀ (w : ω.world) (e₁ e₂ : Ω.ientity), 
  e₁ ∈ C → e₂ ∈ C → d ≤ sim.r e₁ e₂ w

/-- An **existential clique** of degree **d**, or d-eclique, is a set 
    of entities which are similar to each 
    other to degree at least **d** in any possible
    world in which both exist.
    Every clique is an existential clique, 
    but the converse need not hold. -/
def eclique (d : fuzzy) (C : set Ω.ientity) : Prop :=
  ∀ (w : ω.world) (e₁ e₂ : Ω.ientity), 
  e₁ ∈ C → e₂ ∈ C → e₁.exists w → e₂.exists w →
  d ≤ sim.r e₁ e₂ w

/-- A **maximum clique** of degree **d**, or d-mclique, is a d-clique which cannot be enlarged. -/
def mclique (d : fuzzy) (C : set Ω.ientity) : Prop :=
  clique d C ∧ ∀ C' : set Ω.ientity, clique d C' → C ⊆ C' → C = C'

/-- An **analogical clique** of degree **d**, or d-aclique, is a d-mclique
    which is also a resemblance class. -/
def aclique (d : fuzzy) (C : set Ω.ientity) : Prop :=
  mclique d C ∧ rclass C

/-- A **strict analogical clique** of degree **d**, or d-aclique, is a d-mclique
    which is also a strict resemblance class. -/
def saclique (d : fuzzy) (C : set Ω.ientity) : Prop :=
  mclique d C ∧ srclass C

/-- A **near perfect clique** of degree **d**, or d-npclique, is an infinite d-saclique. -/
def npclique (d : fuzzy) (C : set Ω.ientity) : Prop :=
  set.infinite C ∧ saclique d C

/-- An entity is a **trope** if and only if its similarity to any other 
    entities does not vary across time and worlds (beyond the allowed tolerance). -/
def ientity.trope (e : Ω.ientity) : Prop := ∀ e' w w', abs ((sim.r e e' w : ℝ) - sim.r e e' w') ≤ sim.tolerance

-- TODO: consider bumping the definition below to full independence 
-- (lack of entailment between aggregates, lack of generic dependences) later.
-- Also consider specifying that the clique should not contain entities from
-- different corners of the ontological square. 
-- These are some of the conditions I term "univocity conditions".
-- For now, it won't matter much to produce a very strict definition of univocity
-- for perfect cliques. The basic idea of them can be expressed just 
-- with the following conditions.

/-- A **perfect clique** of degree **d**, or d-pclique, is a simply independent d-npclique,
    which does not contain both tropes and non-tropes. -/
def pclique (d : fuzzy) (C : set Ω.ientity) : Prop :=
  npclique d C ∧ sindependent C ∧ 
  ¬ ∃ e t : Ω.ientity, e ∈ C ∧ t ∈ C ∧ t.trope ∧ ¬e.trope

/-- The **degrees of analogy** of an entity **e** is the set of degrees for which **e** has a near perfect clique.
    An entity is said to be analogically similar to **e** if it resembles the things resembling **e** to at least
    some of these degrees. -/
def ientity.danalogy (e : Ω.ientity) : set fuzzy := {d : fuzzy | ∃ (C : set Ω.ientity), e ∈ C ∧ npclique d C}

/-- The **analogies** of an entity **e** is the set of near perfect cliques containing **e**.
    An entity is said to analogically similar to **e** if it shares a near perfect clique with **e**. -/
def ientity.analogies (e : Ω.ientity) : set $ set Ω.ientity := {C : set Ω.ientity | ∃ d, e ∈ C ∧ npclique d C}

/-- The **degrees of genera** of an entity **e** is the set of degrees for which **e** has a perfect clique.
    An entity is said to be in one of the same genus as **e** if it resembles the things resembling **e** to at least
    some of these degrees. -/
def ientity.dgenera (e : Ω.ientity) : set fuzzy := {d : fuzzy | ∃ (C : set Ω.ientity), e ∈ C ∧ pclique d C}

/-- The **genera** of an entity **e** is the set of perfect cliques containing **e**.
    An entity is said to be in one of the same genus as **e** if it shares a perfect clique with **e**. -/
def ientity.genera (e : Ω.ientity) : set $ set Ω.ientity := {C : set Ω.ientity | ∃ d, e ∈ C ∧ pclique d C}

/-- An entity is said to be **quasi-unintelligible** if it does not admit analogies of degree greater than 0.
    In this case, it either has no essence, or at least its essence cannot be explained by 
    resemblance nominalism, but only by trope-resemblance nominalism. -/
def ientity.qunint (e : Ω.ientity) : Prop := ¬ ∃ d ∈ e.danalogy, (0 : fuzzy) < d

/-- An entity is said to be **unintelligible** if it quasi-unintelligible and is not 
    existentially equivalent to any non-quasi-unintelligible tropes.
    If it were equivalent to some such tropes, i.e. if it had *essential* tropes,
    its essence might be explainable in terms of the essences of its tropes.
    An unintelligible entity however has no essence of any sort. -/
def ientity.unint (e : Ω.ientity) : Prop :=
  e.qunint ∧ ∀ t : Ω.ientity, t.trope → t ⇔ e → t.qunint

/-- An entity is said to be **partially intelligible** if it is not unintelligible. -/
def ientity.pint (e : Ω.ientity) : Prop := ¬ e.unint

/-- An entity is said to be **bare** if it is not a member of any genus.
    In this case, it either has no univocal essence, or at least its essence cannot be explained by 
    resemblance nominalism, but only by trope-resemblance nominalism. -/
def ientity.bare (e : Ω.ientity) : Prop := e.genera = ∅

/-- An entity is said to be **fully bare** if it is
    bare and is not existentially equivalent to any non-bare tropes.
    If it were equivalent to some non-bare tropes, i.e. if it had *essential* tropes, 
    its essence might be explainable in terms of the essences of its tropes. 
    A fully bare entity however has no univocal essence of any sort (other than its haecceity). -/
def ientity.fbare (e : Ω.ientity) : Prop := 
  e.bare ∧ ∀ t : Ω.ientity, t.trope → t ⇔ e → t.bare

/-- An entity is said to be **normal** if it has a genus. -/
def ientity.normal (e : Ω.ientity) : Prop := e.genera.nonempty

/-- An entity is said to be (fully) **intelligible** if it is
    partially intelligible and normal if it is a trope.
    We should expect all entities to be intelligible. -/
def ientity.int (e : Ω.ientity) : Prop := e.pint ∧ e.trope → e.normal

-- TODO: revise the following two definitions to use genera directly in case they don't
-- define what is intended:

/-- An entity is said to be **generically unclassifiable** if it doesn't have a greatest genus. -/
def ientity.gunclass (e : Ω.ientity) : Prop := ¬ ∃ d ∈ e.dgenera, ∀ d' ∈ e.dgenera, d ≤ d'

/-- An entity is said to be **specifically unclassifiable** if it doesn't have an infima species. -/
def ientity.sunclass (e : Ω.ientity) : Prop := ¬ ∃ d ∈ e.dgenera, ∀ d' ∈ e.dgenera, d' ≤ d

/-- An entity is said to be **partially unclassifiable** if it is either 
    specifically or generically unclassifiable. -/
def ientity.punclass (e : Ω.ientity) : Prop := e.gunclass ∨ e.sunclass

/-- An entity is said to be **unclassifiable** if it is both 
    specifically or generically unclassifiable. -/
def ientity.unclass (e : Ω.ientity) : Prop := e.gunclass ∧ e.sunclass

/-- An entity is said to be **classifiable** if it is not partially unclassifiable. -/
def ientity.class (e : Ω.ientity) : Prop := ¬ e.punclass

/-- An entity is said to be **partially classifiable** if it is not unclassifiable. -/
def ientity.pclass (e : Ω.ientity) : Prop := ¬ e.unclass

/-- An entity is said to be **fully classifiable** if it is normal and has a finite number of genera.
    It can then be classified taxonomically without appeal to its tropes. -/
def ientity.fclass (e : Ω.ientity) : Prop := e.genera.finite ∧ e.normal

end basic

section principles

variables {Ω : ω.iontology} [sim : Ω.sim]
include sim

def esse_of_possibilia : Prop := ∀ (e₁ e₂ : Ω.ientity), 0 < e₁.sim e₂

end principles

section basic_theorems

variables {Ω : ω.iontology} [sim : Ω.sim]
include sim

/-- **Universal Analogy of Being** -/
lemma uab : ∀ e, ∃ (d : fuzzy) (C : set Ω.ientity), aclique d C ∧ e ∈ C :=
  begin
    intros e, use [0, univ], simp,
    constructor, constructor,
      simp [clique], intros,
        admit,
      intros, apply eq_of_subset_of_subset,
      assumption,
      simp,
    clear e, simp [rclass], intro e,
    suffices c : sdsim e ∅ = 0, 
      rw c,
      -- needs appropriate type classes for this to work:
      admit, --exact zero_le (inf_sim univ),
    admit,
  end

-- TODO: It seems that we could prove the following result for acliques, 
-- if we assume full blown transitivity of the similarity relation. 
-- The principle is that the similarity between x and z, is ≤ to the
-- least of the similarities between x and y, and z and y, for all y. This implies that if 
-- the similarities between x and y, and z and y, are the same, then the similarity between x and z
-- should be at least as high. In the second lemma we however know that the similarity between 
-- t₁ and t₂ is strictly capped at d, and yet that they should both be at least d-similar to t, which
-- is absurd given transitivity, but not given mere triangularity.

-- TODO: It seems possible that we might also just be able to prove that under transitivity
-- all acliques are sacliques. This remains to be investigated.

-- admits are only due to the type classes problem.
lemma saclique_disjoint : ∀ d (C C' : set Ω.ientity), C ≠ C' → saclique d C → saclique d C' → C ∩ C' = ∅ :=
  begin
    intros d C C' neq h₁ h₂,
    have c₁ : ∃ t₁ ∈ C, t₁ ∉ C',
      by_contradiction contra,
      push_neg at contra,
      replace h₁ := h₁.1.2,
      replace h₂ := h₂.1.1,
      specialize h₁ C' h₂ contra,
      contradiction,
    have c₂ : ∃ t₂ ∈ C', t₂ ∉ C,
      by_contradiction contra,
      push_neg at contra,
      replace h₂ := h₂.1.2,
      replace h₁ := h₁.1.1,
      specialize h₂ C h₁ contra,
      cases h₂, contradiction,
    by_contradiction contra,
    simp [ext_iff] at contra,
    obtain ⟨t, h₁t, h₂t⟩ := contra,
    obtain ⟨t₁, h₁t₁, h₂t₁⟩ := c₁,
    obtain ⟨t₂, h₁t₂, h₂t₂⟩ := c₂,
    replace h₁ := h₁.2, simp [srclass] at h₁,
    specialize h₁ t h₁t,
    replace h₂ := h₂.2, simp [srclass] at h₂,
    specialize h₂ t h₂t,
    have c₁ : t.sim t₂ ≤ sdsim t (-C), admit,
    have c₁' : inf_sim (C) ≤ t.sim t₁, admit,
    have c₁'' : t.sim t₂ < t.sim t₁,
      have := lt_of_le_of_lt c₁ h₁,
      exact lt_of_lt_of_le this c₁',
    have c₂ : t.sim t₁ ≤ sdsim t (-C'), admit,
    have c₂' : inf_sim (C') ≤ t.sim t₂, admit,
    have c₂'' : t.sim t₁ < t.sim t₂,
      have := lt_of_le_of_lt c₂ h₂,
      exact lt_of_lt_of_le this c₂',
    have c₃ := lt_trans c₁'' c₂'',
    simp [lt_irrefl] at c₃,
    contradiction,
  end

lemma saclique_not_subset : ∀ d d' (C C' : set Ω.ientity), C ≠ C' → saclique d C → saclique d' C' → C ∩ C' ≠ ∅ → d ≤ d' → ¬ C ⊆ C' := sorry

lemma saclique_ssubset : ∀ d d' (C C' : set Ω.ientity), saclique d C → saclique d' C' → C ∩ C' ≠ ∅ → d ≤ d' → C' ⊆ C :=
  begin
    intros d d' C C' h₁ h₂ h₃ h₄,
    by_cases h : C = C', cases h, refl,
    have c₁ : ∃ t₁ ∈ C, t₁ ∉ C',
      by_contradiction absurd,
      push_neg at absurd,
      have c := saclique_not_subset d d' C C' h h₁ h₂ h₃ h₄,
      contradiction,
    by_contradiction contra,
    simp [has_subset.subset, set.subset] at contra,
    simp [ext_iff] at h₃,
    obtain ⟨t, h₁t, h₂t⟩ := h₃,
    obtain ⟨t₁, h₁t₁, h₂t₁⟩ := c₁,
    obtain ⟨t₂, h₁t₂, h₂t₂⟩ := contra,
    replace h₁ := h₁.2, simp [srclass] at h₁,
    specialize h₁ t h₁t,
    replace h₂ := h₂.2, simp [srclass] at h₂,
    specialize h₂ t h₂t,
    have c₁ : t.sim t₂ ≤ sdsim t (-C), admit,
    have c₁' : inf_sim (C) ≤ t.sim t₁, admit,
    have c₁'' : t.sim t₂ < t.sim t₁,
      have := lt_of_le_of_lt c₁ h₁,
      exact lt_of_lt_of_le this c₁',
    have c₂ : t.sim t₁ ≤ sdsim t (-C'), admit,
    have c₂' : inf_sim (C') ≤ t.sim t₂, admit,
    have c₂'' : t.sim t₁ < t.sim t₂,
      have := lt_of_le_of_lt c₂ h₂,
      exact lt_of_lt_of_le this c₂',
    have c₃ := lt_trans c₁'' c₂'',
    simp [lt_irrefl] at c₃,
    contradiction,

  end


end basic_theorems

section being

-- We lift tropes to a structure to generate a namespace for dot notation:
structure trope (Ω : ω.iontology) [sim : Ω.sim] :=
  (up : Ω.ientity)
  (p : up.trope)
variables {Ω : ω.iontology} [sim : Ω.sim] (t : Ω.trope)
include sim

/-- A **proper trope** is a normal trope incompatible with any distinct consubstantial trope in the same genus as itself. -/
def trope.proper (t : Ω.trope) : Prop := 
  t.normal ∧ ∀ (C) d ∈ t.genera, ptclique d C t → 
  ∀ t' ∈ C, t' ≠ t → t'.up ≈ t.up → ¬⋄(t'.up.exists ∩ t.up.exists) 

/-- A **composable trope** is an improper normal trope. 
    Composable tropes "compose" to achieve some characteristic rather 
    than being singularly responsible for the characteristic.
    A 1kg composable trope, for instance, could be composed with another 1kg composable trope,
    to characterize its object as being 2kg. -/
def trope.composable (t : Ω.trope) : Prop := ¬t.proper ∧ t.normal

/-- A **complemented trope** is a proper trope for which there exists another distinct consubstantial proper trope sharing a genus. -/
def trope.complemented (t : Ω.trope) : Prop := 
  t.proper ∧ ∃ (C : set Ω.trope) d ∈ t.genera, t ∈ C ∧ ptclique d C ∧ 
  ∃ t' ∈ C, t' ≠ t ∧ t'.up ≈ t.up ∧ t'.proper

/-- An **eminent** trope is a composable trope non-vacuously 
    compatible with all complemented tropes in all of its genera.
    Naturally, they are not consubstantial to these complemented tropes.
    Mental tropes are eminent tropes, for consider the trope in virtue of which you are thinking about a square, 
    this appears to be composable with a trope in virtue of which you are thinking about a circle, 
    since they compose to characterize you as thinking about some square and some circle 
    (I do not mean to say you are thinking about a squared-circle). These tropes are members of the 
    same genus of "mental geometric figure tropes". Furthermore,
    these tropes are compatible with the existence of extra-mental squares and circles, 
    which are objects characterized by complemented "square" and "circular" tropes. 
    It is unclear to us whether there are any non-eminent composable tropes, or any non-mental eminent tropes. -/
def trope.eminent (t : Ω.trope) : Prop := 
  t.composable ∧ ∀ (C) d ∈ t.genera, ptclique d C t → 
  (∃ (t' : Ω.trope), t' ∈ C ∧ t'.complemented) ∧ 
  ∀ (t' : Ω.trope), t' ∈ C → t'.complemented → ⋄(t'.up.exists ∩ t.up.exists)

/-- A **formal** trope is a non-eminent normal trope. -/
def trope.formal (t : Ω.trope) : Prop := ¬t.eminent ∧ t.normal





end being


end iontology



end ontology
