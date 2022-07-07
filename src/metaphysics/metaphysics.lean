import metaphysics.causality metaphysics.finitism
universe u
open set topological_space classical
local attribute [instance] prop_decidable

-- THIS FILE IS A WORK IN PROGRESS. 
-- FOR NOW IT IS ONLY USED TO "EXPORT" FILES
-- IN THIS MODULE JOINTLY TO OTHER MODULES.

namespace ontology
    
  variables {ω : ontology} (s : ω.substance)

  /-- (strong) Platonism is the doctrine 
      that there are simple substances. -/
  def splatonism (ω : ontology) := ∃ s : ω.substance, s.simple

  def suniversal_hylemorphism := ¬∃ s : ω.substance, s.simple
  def universal_hylemorphism := ¬∃ s : ω.substance, s.contingent ∧ s.simple

  /- The (contingent) universe is the supremum of all contingent
      things. It is the fact that there are contingent entities. -/
  -- def «universe» (ω : ontology) : ω.substance :=  
  --   Sup {e : ω.substance | e.contingent} --h, sorry⟩


end ontology