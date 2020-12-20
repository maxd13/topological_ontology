import substances
universe u
open set topological_space classical
local attribute [instance] prop_decidable

namespace ontology

variable {ω : ontology}

-- Next we must talk about properties
section properties

-- A property is a function which outputs an event for an entity, 
-- i.e. the event of the entity having the property.
@[reducible, alias]
def property (ω : ontology) :=  ω.entity → ω.event

-- An analogical property, or aproperty, outputs an avent instead.
-- i.e the avent of the entity having the property, which it can posses to a greater or lesser extent.
-- This is analogy in the sense of intrinsic attribution.
@[reducible, alias]
def aproperty (ω : ontology) := ω.entity → ω.avent

variable (p : ω.property)

-- Apparently Lean already infers correctly the proper notation for this (which is amazing),
-- even though it does not elaborate the full boolean algebra instance.
-- instance boolean_property : boolean_algebra ω.property := sorry

/-! Now, a property which, unlike an aproperty, does not return an avent is in some sense univocal,
 but this univocity might occur in two different ways: in language alone, or both in language and in reality.
 The latter we call univocal properties properly speaking, while the former we call *hidden* or *abstracted* 
 analogical properties. The difference between these two is that real univocal properties preserve hierarchical
 distinctions in being, while abstracted, "fake", univocal properties ignore such ontological distinctions.
 So essentially we say that a property is univocal in a possible world if and only if the entities which exemplify 
 it in that world are incomparable with respect to existential entailment.
-/

-- TODO: change this definition to use existential entailment notation when it becomes available.
def property.lunivocal : ω.event := 
    { w |
      ∀ e₁ e₂, w ∈ p e₁ ∩ p e₂ → ¬ e₁.exist ⊂ e₂.exist ∧ ¬ e₁.exist ⊃ e₂.exist
    }
@[reducible]
def property.lhidden := -p.lunivocal
@[reducible]
def property.univocal := p.lunivocal.necessary
@[reducible]
def property.hidden := p.lhidden.necessary

/- The whole point of the Thomistic theory of the analogy of being consists 
   in the realization that existence is a hidden analogy abstracted away from a deeper
   aproperty: Being.
-/

def existence (ω : ontology) : ω.property := λe, e.exist

-- In any possible world with at least 2 entities (hence at least one contingent entity) 
-- existence is a hidden analogy.
theorem analogical_existence : ∀ w e₁ e₂, e₁ ≠ e₂ → e₁ ∈ w → e₂ ∈ w → w ∈ ω.existence.lhidden := sorry

instance property_inhabited : inhabited ω.property := ⟨ω.existence⟩


-- a property is exemplifiable if there is some entity which has that property in some possible world.
@[reducible]
def property.exemplifiable  : Prop := ∃ e, (p e).nonempty

-- an entity is said to possibly exemplify a property if it does so in some possible world
@[reducible]
def entity.pexemplifies (e : ω.entity) := (p e).nonempty 

-- a property is existential if an entity having the property implies its existence
@[reducible]
def property.existential := ∀ e, p e ⊆ e.exist

-- the common (sensical) properties
structure property.common : Prop :=
    (axiom₀ : p.exemplifiable)
    (axiom₁ : p.existential)

-- A common property is positive if in any possible world in which an entity has the property,
-- there exists something in that world (e.g. an accident) to ground the property.
structure property.positive extends property.common p : Prop := 
    (axiom₂ : ∀ e, is_open (p e))

-- a property is essential of an entity if the entity has that property in any and only the possible worlds
-- in which it exists. Which is to say that the entity is in a sense a "fixed point" of the property
@[reducible]
def property.essential_of (e : ω.entity) := p e = e.exist
@[reducible]
def property.inessential_of (e : ω.entity) := p e ≠ e.exist

-- a property is essential in itself if it is essential of all entities which may possibly exemplify it.
@[reducible]
def property.essential := ∀ e, (p e).nonempty → p.essential_of e
-- It is inessential in itself if it is everywhere inessential
@[reducible]
def property.inessential := ∀ e, (p e).nonempty → p.inessential_of e

-- a positive property is possessed if it "talks about" its subject,
-- which is to say that it is an accident or essential of a substance,
-- or essential of an accident.
structure property.possessed extends property.positive p : Prop  :=
    (axiom₃ : ∀ (e : ω.entity) (h : e.pexemplifies p), 
              let r := (entity.mk (p e) (axiom₂ e) h) in
              e.perfect → r.subsists e
    )
    (axiom₄ : ∀ (e : ω.entity), e.pexemplifies p → e.imperfect → p.essential_of e)

-- A possessed property is accidental of an entity if it is not essential.
-- From this we can infer (informally) that a property is either essential or accidental
-- of an entity or does not "talk about" an entity at all 
-- (or at least does not "talk about" all entities to which it is predicated).
@[reducible]
def property.accidental_of (e : ω.entity) := p.possessed ∧ p.inessential_of e
@[reducible]
def property.accidental := p.possessed ∧ p.inessential

-- Notice there can be possessed properties which are neither essential nor accidental in themselves,
-- but only with respect to a particular entity (it is in this sense that some say heat is
-- essential of fire but accidental of burning coal). But with respect to any particular entity
-- a possessed property is either essential or accidental. Notice also that this sort of property
-- is (almost) never univocal, because predicating something of both a substance and its accidents is never univocal.

-- a "proper" property, or a property in a more "proper" sense of the word,
-- is an univocal possessed property 
structure property.proper extends property.possessed p : Prop :=
    (axiom₅ : p.univocal)

-- The haecceity of an entity is an essential proper property from which all its essential properties
-- follow.
variable (e : ω.entity)

def entity.haecceity  : ω.property := λx w, x ∈ w ∧ x = e

theorem haecceity_essential : e.haecceity.essential := sorry
theorem haecceity_proper : e.haecceity.proper := sorry
theorem haecceity_follows_essential : p.essential_of e → e.haecceity ≤ p  := sorry

-- a property is communicable if it can be possibly exemplified by more than one entity
def property.communicable := ∃ e₁ e₂ : ω.entity,
                             e₁ ≠ e₂ ∧
                             e₁.pexemplifies p ∧
                             e₂.pexemplifies p

def property.incommunicable := ¬ p.communicable

-- haecceity is of course incommunicable
lemma haecceity_incommunicable : e.haecceity.incommunicable := sorry

-- A normal, "everyday", property like "being red" 
-- (when e.g. it is predicated of substances, and not of "red" accidents)
-- is a communicable proper property.
structure property.normal extends property.proper p : Prop :=
    (axiom₆ : p.communicable)


-- Don't know if this is true
-- there are counterexamples when S contains contradictory properties
-- but otherwise maybe an adaptation of this lemma is true
-- lemma inf_normal_normal : ∀ S : set ω.property, (∀ p : ω.property, p ∈ S → p.normal) → (Inf S).normal :=
--     begin
--         intros S h,
--         have ne : S.nonempty,
--             admit,
--         obtain ⟨p, hp⟩ := ne,
--         have pn := h p hp,
--         constructor,
--             admit,
--         obtain ⟨e₁,e₂,neq, he₁,he₂⟩  := pn.axiom₆,
--     end


-- The specific essence, or species, of an entity is a normal essencial property from which
-- all its normal essential properties follow.
def property.species_of := e.pexemplifies p ∧
                           p.normal ∧ 
                           p.essential ∧
                           ∀ p', e.pexemplifies p' → 
                                p'.normal →  
                                p'.essential →
                                p ≤ p'

def property.species := ∃ e, p.species_of e
def entity.has_species := ∃ p : ω.property, p.species_of e

-- An entity has at most one species
lemma unique_species : ∀ p₁ p₂ : ω.property, (∃ e, p₁.species_of e ∧ p₂.species_of e) → p₁ = p₂ := sorry

end properties

end ontology