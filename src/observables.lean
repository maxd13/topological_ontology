import ontology math.fuzzy
open set topological_space classical
local attribute [instance] prop_decidable

namespace ontology

-- TODO: consider redefining events as observables
-- later, and changing notation to support it.
-- This would be a major refactoring, but one
-- which does not change the essence of the system,
-- so we defer it to after the project is close
-- to the end.

  variables (ω : ontology)

  abbreviation observable (α : Sort*) 
                [topological_space α] 
                [has_none α]
                := ω.world → α

  abbreviation event' := ω.observable Prop

  @[simp]
  lemma event'_eq_event : ω.event' = ω.event := 
  by simp [ontology.event, set]

  abbreviation quantity := ω.observable (option ℝ)

section observables

  variables {ω} {α : Type*} [topological_space α] 
            [has_none α] (o : ω.observable α)

  abbreviation observable.perfect := continuous o

  /- observables are coerced to their domain of definition -/
  instance has_coe_observable_event : has_coe (ω.observable α) ω.event := ⟨flip has_mem.mem⟩

end observables

  -- We now talk about analogical (fuzzy) events, or "avents".
  -- OBSERVATION: We could have called them aevents, which would be in keeping with our naming style.
  -- But then since in Latin this just sounds like "events" we preferred to invent a new word.
  abbreviation avent :=  ω.observable fuzzy



end ontology