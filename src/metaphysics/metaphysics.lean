import metaphysics.causality metaphysics.finitism
universe u
open set topological_space classical
local attribute [instance] prop_decidable

namespace ontology
    
  variables {ω : ontology} (s : ω.substance)

  -- (strong) Platonism is the doctrine 
  -- that there are simple substances
  def splatonism (ω : ontology) := ∃ s : ω.substance, s.simple


end ontology