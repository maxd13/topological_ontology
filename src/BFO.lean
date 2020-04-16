import tactic.tidy
universe u
open set

-- A formalization of BFO

namespace BFO

variable (α : Type u)

--  class has_BFO_continuants :=
--     (continuant : set α)
--     (generically_dependent_continuant : set α)
--     (independent_continuant : set α)
--     (imaterial_entity : set α)
--     (continuant_fiat_boundary : set α)
--     (one_dimensional_cfb : set α)
--     (two_dimensional_cfb : set α)


-- only a declaration of primitive terms
class BFO_primitive_terms :=
    (continuant : set α)
    (temporal_region : set α)
    (material_entity : set α)
    (zero_dimensional_cfb : set α)
    (one_dimensional_cfb : set α)
    (two_dimensional_cfb : set α)
    (three_dimensional_cfb : set α)
    (spatial_region : set α)
    (zero_dimensional_sre : set α)
    (one_dimensional_sre : set α)
    (two_dimensional_sre : set α)
    (three_dimensional_sre : set α)
    (quality : set α)
    (realizable_entity : set α)
    (role : set α)
    (disposition : set α)
    (function : set α)
    (occurent : set α)
    (history : set α)

local postfix ` ˣ `:1025 := (@subtype α)

-- #check BFO_primitive_terms.continuant




class BFO_continuant extends BFO_primitive_terms α  :=
    (continuant_part_of : temporal_regionˣ → continuantˣ → continuantˣ → Prop)
    (axiom120_001 : ∀ t, is_antisymm continuantˣ (continuant_part_of t))




end BFO