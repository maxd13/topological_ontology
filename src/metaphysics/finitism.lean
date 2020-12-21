import substances
universe u
open set topological_space classical
local attribute [instance] prop_decidable

namespace ontology

variable (ω : ontology)

-- substantially finite worlds are worlds with finitely many substances
def sfinite := {w : ω.world | w.substances.finite}

-- weakly substantially finitistic ontologies are ontologies with at least one substantially finite world
def wsfinitistic : Prop := ω.sfinite.nonempty

end ontology