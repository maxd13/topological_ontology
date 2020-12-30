import topology.instances.real
open set topological_space classical
local attribute [instance] prop_decidable


/-! # Fuzzy Set Theory -/

-- [0, 1] interval
@[reducible]
def fuzzy := subtype $ Icc (0 : ℝ) 1

universes u v
@[reducible]
def fset (α : Type u) := α → fuzzy

def fset_of {α : Type u} (p : α → fuzzy) : fset α :=
p

#check (infer_instance : has_coe fuzzy ℝ)
#check (infer_instance : linear_order fuzzy)
#check (infer_instance : topological_space fuzzy)
instance has_zero_fuzzy : has_zero fuzzy := ⟨⟨(0 : ℝ), by apply mem_Icc.2; norm_num⟩⟩


class has_none (α : Sort*) := 
  (none : α)

instance has_none_Prop : has_none Prop := ⟨false⟩
instance has_none_bool : has_none bool := ⟨ff⟩
instance has_none_fuzzy : has_none fuzzy := ⟨0⟩
instance has_none_option (α) : has_none (option α) := ⟨none⟩ 
instance has_none_roption (α) : has_none (roption α) := ⟨none⟩ 
instance has_none_mem (α : Type*) (β : Type*) [has_none β] : has_mem α (α → β) :=
  ⟨λ x f, f x ≠ has_none.none⟩


-- The canonical topological space of option types, is simply
-- the coinduced topology. This should already have been defined.
instance option.topological_space (α) [t : topological_space α] : topological_space (option α) :=
  coinduced some t

/- **Relation's TODOs**
     TODO: create (or make sure already exists) 
     a `has_none` typeclass so that `option α` and
     `roption α` both have an instance of has_none
     for any type α. This will be useful in order to
     declare some non-option types which have "none"
     such as `false` for `Prop`, `ff` for `bool`, and
     `0` for the `[0, 1]` real interval 
     (to be used with fuzzy set theory), 
     but not for the `0` of the reals, for instance,
     since it is not the same thing to say that a 
     real-valued function has value `0` at a point
     and that it is not defined at the point.
     This way, functions to a `has_none` type can
     be interpreted as partial functions even when
     they are total. What this class intends to 
     provide above all is an automatic generalization 
     of the concept of set membership for has_none
     types, we intend to add the following instance:

     `instance (α β) [has_none β] : has_mem α (α → β)`

     We can also add an extensionality lemma for said
     functions via funext if we want to. This code
     should probably be moved to the math directory
     
     TODO: consider that both `observables`
     and `perfections`, to be defined in 
     observables.lean, should be typeclasses as well.
     The first should be `class observable α : Prop`,
     containing an `observable.carrier : Type*`
     which `has_none` and is a `topological_space`
     (and maybe a T0 one)
     and an axiom specifying that α is equal to 
     the type of functions from possible worlds 
     to the carrier. `perfections` should be defined
     as:

     `def perfection {α} [observable α] (x : α)`

     And specify that x is a perfection iff 
     when cast to a map between topological spaces
     it is continuous and does not map all its domain
     to `none`. We should likewise have a typeclass
     like this for merely measurable functions.
     Maybe we should call them `measureables`.
     Note that all these definitions are supposed to
     depend on an ontology `ω`. 
     An alternative to doing this
     would be to generalize the whole theory to use
     observables as the primary notion rather than
     events. This would be a major change, but
     one worth considering.

     TODO: create a relations.lean module
     in which a typeclass for n-ary relations
     is created, and binary and unary (predicates)
     relations are separately defined and added to
     the typeclass. This way, many results about the
     particular cases can be proved from a general 
     theory of n-ary relations, and we don't have to
     worry about extending our theories of monadic 
     and dyadic relations to a general case later.
     Relations are to be defined 
     **between observables**, with typed relations 
     having type signatures for the types of 
     observables, and untyped relations having the same
     observable type for all its arguments. 
     Achieving full generality here is desirable,
     but **not an absolute priority** in the project,
     so use sorrys and TODOs extensively here.

     TODO: rename properties.lean to essences.lean, 
           and only discuss there the    


     TODO: Move these TODOs to their appropriate locations.
     Only delete any of the TODOs from here when all of them are
     completed.
  -/