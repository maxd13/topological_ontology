import substances
universe u
open set topological_space classical
local attribute [instance] prop_decidable

-- THIS FILE IS A WORK IN PROGRESS.

namespace ontology

variable (ω : ontology)

/-- A possible world is **(X := Substantially) finite** if it has finitely many (X := substance). -/
def lsfinite (X : set ω.entity := entity.perfect) : ω.event := 
  {w : ω.world | {e : ω.entity | e ∈ X ∧ e.exists w}.finite}

/-- A possible world is **Ultrafinite** if it has only a finite number of entities. -/
@[reducible, simp]
def lufinite := ω.lsfinite univ

-- Global definitions:

/-- **Ultrafinitistic** ontologies are ontologies in which only a finite number of entities exist in each world. -/
def ultrafin : Prop := □ω.lufinite

/-- **Weakly Ultrafinitistic** ontologies are ontologies in which there is a possible world with only a finite number of entities. -/
def wultrafin : Prop := ⋄ω.lufinite

/-- **Substantially Finitistic** ontologies are ontologies in which only a finite number of (X := substance) exist in each world. -/
def sfin (X : set ω.entity := entity.perfect) : Prop := □ω.lsfinite X

/-- **Weakly Substantially Finitistic** ontologies are ontologies with at least one (X := substantially) finite world. -/
def wsfin (X : set ω.entity := entity.perfect) : Prop := ⋄ω.lsfinite X

end ontology