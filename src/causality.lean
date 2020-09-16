import ontology
universe u
open set topological_space classical
local attribute [instance] prop_decidable


namespace ontology

variables {ω : ontology} (e₁ e₂ : ω.entity) (w : ω.world)

-- counterfactual dependence
def entity.depends : ω.event := 
    { w |
      e₁ ∈ w ∧
      e₂ ∈ w ∧
      ∀ w' < w, e₂ ∉ w' → e₁ ∉ w'
    }

-- counterfactual entanglement
def entity.entangled : ω.event := { w | e₁.depends e₂ w ∧ e₂.depends e₁ w }

end ontology