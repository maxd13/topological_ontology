import substances math.fuzzy
open set topological_space classical
set_option pp.generalized_field_notation true
local attribute [instance] prop_decidable
noncomputable theory

-- tentative idea for formalizing ppc via intensional similarities
-- in nuclear trope theory

namespace ontology

variable {ω : ontology}

namespace iontology
-- TODO: this needs to be adapted to use possible worlds.
-- In this case, we need to assume similarity has existential import,
-- i.e. that a thing must exist in order to be similar to anything.
-- In this case, we need to redefine a trope-like entity 
-- to be invariant with respect to similarity, i.e.
-- given any entity e, trope t, and worlds w₁ w₂,
-- in which both exist, the similarity of t and e in w₁ is the
-- same as the similarity between t and e in w₂. 
-- We can then redefine "strongly trope-like" to just "trope".
/-- Intensional similarity relation -/
structure sim (Ω : ω.iontology) :=
  (r : Ω.ientity → Ω.ientity → fuzzy)
  (reflexive : ∀ {e}, r e e = 1)
  (symmetric : ∀ {e₁ e₂}, r e₁ e₂ = r e₂ e₁)
  (triangular : ∀ e₁ e₂ e₃, ((r e₁ e₂) : ℝ) * (r e₂ e₃) ≤ r e₁ e₃)
  -- TODO: prove this as a theorem, follows from triangular inequality
  (subst : ∀ e₁ e₂, r e₁ e₂ = 1 → ∀ e₃, r e₁ e₃ = r e₂ e₃)
  -- these principles are probably wrong, will think about them later.
  -- consubstantial entities with the same essence are exactly similar
  -- (coessence : ∀ e₁ e₂, 0 < r e₁ e₂ → e₁ ≈ e₂ → r e₁ e₂ = 1)
  -- -- substances do not have the same essence as their accidents
  -- (essence : ∀ e₁ e₂, 0 < r e₁ e₂ → e₁ ≈ e₂ → e₁ ⇎ e₂ → ¬ e₁.up.compatible e₂)

attribute [class] sim
attribute [simp, refl] sim.reflexive
attribute [simp, symm] sim.symmetric

variables {Ω : ω.iontology} [sim : Ω.sim] (e : Ω.ientity)
include sim

/-- An entity is said to be **wholly dissimilar** to another if 
    their similarity is 0. -/
def wdiss (e' : Ω.ientity) : Prop := 0 = sim.r e e'

/-- An entity is said to be **specifically similar** to another, 
    or to have the same specific essence, if 
    it is not wholly dissimilar to it, i.e. if
    their similarity is strictly greater than 0. -/
def similar (e' : Ω.ientity) : Prop := ¬ wdiss e e'

/-- An entity is said to be **exactly similar** to, or **ontologically indistinguishable** from, 
    another if their similarity is 1. -/
def esimilar (e' : Ω.ientity) : Prop := 1 = sim.r e e'

local infixr ` ≅ `:50 := similar
local infixr ` ≇ `:50 := wdiss
-- TODO: maybe set == notation for esimilar.

-- TODO: check later if this is indeed a good definition
/-- A **bare particular** is an entity wholly dissimilar to any entity distinct from itself. -/
def ientity.bare : Prop := ∀ e', e' ≠ e → e' ≇ e

/-- A **trope like** entity is a non-bare particular which is incompatible with any entity
    distinct, similar and consubstantial to itself. -/
def ientity.trope_like : Prop := ¬ e.bare ∧ ∀ e', e' ≠ e → e' ≈ e → e' ≅ e → ¬ e'.up.compatible e

/-- A **strongly trope like** entity is an entity which is only similar to trope like entities. -/
def ientity.strope_like : Prop := ∀ e', e' ≅ e → e'.trope_like

/-- A **bare like** entity is an entity wholly dissimilar from all trope like entities,
    which is however not necessarily a bare particular. -/
def ientity.substratum : Prop := ∀ e' : Ω.ientity, e'.trope_like → e' ≇ e



-- substrata in the same nucleus (i.e. equivalent) have the same essence
-- def substratum_sim : Prop := ∀ e₁ e₂ : Ω.ientity, e₁.substratum → e₂.substratum → e₁ ≡ e₂ → e₁ ≅ e₂
-- -- whatever 
-- def sim_closure : Prop := ∀ e₁ e₂ : Ω.ientity, e₁.trope → e₁ ≅ e₂ → e₂.trope

-- TODO: we may need a notion of the origin trope being more perfect than
-- the caused entity.
def ppc (c : Ω.ientity → Ω.ientity → ω.event) : Prop :=
  ∀ e₁ e₂, ⋄c e₁ e₂ → 
  ∃ trope, trope ≈ e₁ ∧ trope ≅ e₂ ∧ trope ≠ e₂ 
  ∧ trope.strope_like ∧ c e₁ e₂ ⇒' trope.exists ∧ 
  ∀ e₃, c e₃ trope ∩ c e₁ e₂ ⇒ c e₃ e₂

end iontology



end ontology
