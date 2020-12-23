import properties
noncomputable theory
universe u
open set topological_space classical
local attribute [instance] prop_decidable


namespace ontology

section causes
variables {ω : ontology} (x y : ω.event) (e₁ e₂ : ω.entity)

-- integral parthood
def substance.part_of (s₁ s₂ : ω.substance) : ω.event := sorry

-- counterfactual dependence
@[reducible]
def event.depends : ω.event := 
    { w |
      w ∈ x ∧
      w ∈ y ∧
      ∀ w' < w, w' ∉ y → w' ∉ x
    }

-- counterfactual entanglement
@[reducible]
def event.entangled : ω.event := x.depends y ∩ y.depends x

-- counterfactual strong (or one sided) dependence
-- could also be called "event causation", but we reserve
-- the name "cause" for a more qualified definition.
@[reducible]
def event.sdepends : ω.event := x.depends y - y.depends x

-- counterfactual independence
@[reducible]
def event.independent : ω.event := -x.depends y ∩ -y.depends x

-- the same relations recast for entities
@[reducible]
def entity.depends : ω.event := e₁.exists.depends e₂.exists
@[reducible]
def entity.entangled : ω.event := e₁.depends e₂ ∩ e₂.depends e₁
@[reducible]
def entity.sdepends : ω.event := e₁.depends e₂ - e₂.depends e₁
@[reducible]
def entity.independent : ω.event := -e₁.depends e₂ ∩ -e₂.depends e₁

-- vertical causation 
@[reducible]
def substance.causes (s : ω.substance) (e : ω.event) : ω.event := e.sdepends s.val.exists
@[reducible]
def entity.caused_by (e : ω.event) (s : ω.substance): ω.event := s.causes e


-- efficient vertical causation
def substance.ecauses (s : ω.substance) (e : ω.entity) : ω.event := 
  s.causes e.exists ∩
  -s.part_of e.substance ∩
  -e.substance.part_of s


-- compositional causation (we say s "compositionally causes" e)
def substance.ccauses (s : ω.substance) (e : ω.entity) : ω.event := 
  s.causes e.exists ∩
  s.part_of e.substance ∩
  -e.substance.part_of s

-- formal causation
def substance.forcauses (s : ω.substance) (e : ω.entity) : ω.event := 
  s.ccauses e ∩
  s.causes e.substance.val.exists

-- material causation
def substance.mcauses (s : ω.substance) (e : ω.entity) : ω.event := 
  s.ccauses e ∩
  -s.causes e.substance.val.exists

-- final causation
def substance.fincauses (s : ω.substance) (e : ω.entity) : ω.event := 
  s.causes e.exists ∩
  -s.part_of e.substance ∩
  e.substance.part_of s

def entity.caused (e : ω.entity) : ω.event := 
  {w | ∃ s : ω.substance, s.causes e.exists w }

def entity.uncaused (e : ω.entity) : ω.event := -e.caused

end causes

variable (ω : ontology)

-- the principle of sufficient reason, as an event 
def epsr : ω.event := 
  {w : ω.world | ∀ (e : ω.entity), e.contingent → e ∈ w → e.caused w}

-- the principle of sufficient reason
def psr : Prop := ω.epsr = univ

-- the platonic principle, as an event
def epp : ω.event := 
  { w | ∀ e : ω.entity,
    e.caused w → ∃ s : ω.substance,
    w ∈ s.val.uncaused ∩ s.causes e.exists
  }

-- the platonic principle
def pp : Prop := ω.epp = univ

-- the thomistic principle of sufficent reason/causality
def tpsr : Prop := 
  ∀ (s : ω.substance) (p : ω.property) (h₁ : p.proper) (h₂ : ¬ p.essential_of s.val) (w ∈ p s.val), 
  ∃ c : ω.substance, c.causes (p s.val) w

-- the efficient version of tpsr
-- the thomistic principle of sufficent reason/causality
def etpsr : Prop := 
  ∀ (s : ω.substance) (p : ω.property) (h₁ : p.proper) (h₂ : ¬ p.essential_of s.val) (w ∈ p s.val),
  -- p s.val cast to an entity
  let r := (entity.mk (p s.val) 
           (by apply h₁.axiom₂; exact e) 
           (by dunfold event.possible set.nonempty; use w; assumption))
  in ∃ c : ω.substance, c.ecauses r w


end ontology