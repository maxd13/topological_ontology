import states observables
open set topological_space classical
local attribute [instance] prop_decidable
noncomputable theory

-- TODO: rename this file to essence.lean (maybe)
-- THIS FILE IS A WORK IN PROGRESS.

namespace ontology

variable {ω : ontology}

section relations

  variable (ω)

  -- abbreviation property (α := Prop) [topological_space α] [has_none α] := ω.observable α → ω.observable α
  abbreviation property (α : Type := Prop) [topological_space α] := ω.entity → ω.world → α

  def property.positive  {ω : ontology}{α : Type} [topological_space α] (p : ω.property α) : Prop := ∀ e, continuous (p e)

  abbreviation relation (α := Prop) [topological_space α] [has_none α] := 
    ω.observable α → ω.observable α → ω.observable α

  def {u} nary (α β : Type u) : ℕ → Type u
  | 0 := β
  | (n+1) := α → (nary n)

  def {u} tnary (β : Type u) : (list $ Type u) → Type u
  | [] := β
  | (hd::tl) := hd → (tnary tl)

  abbreviation nrelation (n : ℕ) (α := Prop) [topological_space α] [has_none α] := 
    nary (ω.observable α) (ω.observable α) n

  example : (ω.nrelation 2) = ω.relation := rfl

end relations

-- Next we must talk about predicates
section predicates

/-- A predicate is a function which outputs an event for an entity, 
    i.e. the event of the entity having the predicate. -/
abbreviation predicate (ω : ontology) :=  ω.entity → ω.event

/-- An analogical predicate, or apredicate, outputs an aevent instead of an event.
    i.e the aevent of the entity having the predicate, which it can posses to a greater or lesser extent.
    This is analogy in the sense of **intrinsic attribution**.
    See thomistic manuals for a deeper informal discussion of intrinsic attribution.
   -/
abbreviation apredicate (ω : ontology) := ω.entity → ω.aevent

variable (p : ω.predicate)

-- Apparently Lean already infers correctly the proper notation for boolean algebra operations
-- (which is amazing), even though it does not elaborate the full boolean algebra instance.
-- we may consider defining this instance properly in the future, but for now, we just use the notation.
-- instance boolean_predicate : boolean_algebra ω.predicate := sorry

/-! Now, a predicate which, unlike an apredicate, does not return an aevent is in some sense univocal,
 but this univocity might occur in two different ways: in language alone, or both in language and in reality.
 The latter we call univocal predicates properly speaking, while the former we call *hidden* or *abstracted* 
 analogical predicates. The difference between these two is that real univocal predicates preserve hierarchical
 distinctions in being, while abstracted, "fake", univocal predicates ignore such ontological distinctions.
 So essentially we say that a predicate is univocal in a possible world if and only if the entities which exemplify 
 it in that world are incomparable with respect to existential entailment.
-/

-- TODO: change this definition to use existential entailment notation when it becomes available.
def predicate.lunivocal : ω.event := 
    { w |
      ∀ e₁ e₂, w ∈ p e₁ ∩ p e₂ → ¬ e₁.exists ⊂ e₂.exists ∧ ¬ e₁.exists ⊃ e₂.exists
    }
@[reducible]
def predicate.lhidden := -p.lunivocal
@[reducible]
def predicate.univocal := p.lunivocal.necessary
@[reducible]
def predicate.hidden := p.lhidden.necessary

/- The whole point of the Thomistic theory of the analogy of being consists 
   in the realization that existence is a hidden analogy abstracted away from a deeper
   apredicate: Being.
-/
def existence (ω : ontology) : ω.predicate := entity.exists

-- In any possible world with at least 2 entities (hence at least one contingent entity) 
-- existence is a hidden analogy.
theorem analogical_existence : ∀ w e₁ e₂, e₁ ≠ e₂ → e₁ ∈ w → e₂ ∈ w → w ∈ ω.existence.lhidden := sorry

instance predicate_inhabited : inhabited ω.predicate := ⟨ω.existence⟩


/-- a predicate `p` is **exemplifiable** if there is some `entity` which can possibly be `p`. -/
@[reducible]
def predicate.exemplifiable : Prop := ∃ e, ⋄(p e)

-- an entity is said to possibly exemplify a predicate if it does so in some possible world
@[reducible]
def entity.pexemplifies (e : ω.entity) := ⋄(p e)

-- a predicate is existential if an entity having the predicate implies its existence
@[reducible]
def predicate.existential := ∀ e, p e ⊆ e.exists

-- the common (sensical) predicates
structure predicate.common : Prop :=
    (axiom₀ : p.exemplifiable)
    (axiom₁ : p.existential)

-- A common predicate is positive if in any possible world in which an entity has the predicate,
-- there exists something in that world (e.g. an accident) to ground the predicate.
structure predicate.positive extends predicate.common p : Prop := 
    (axiom₂ : ∀ e, is_open (p e))

/-- A predicate is said to be ***de re* necessary** of an entity if the entity has that predicate in
    all and only the possible worlds in which it exists.
    Which is also to say that the entity is a *fixed point* of the predicate. -/
@[reducible]
def predicate.dere_of (e : ω.entity) := p e = e.exists
/-- Negation of `predicate.dere_of` -/
@[reducible]
def predicate.ndere_of (e : ω.entity) := p e ≠ e.exists

/-- A predicate is ***de re* necessary** in itself if it is *de re* necessary of all entities which may possibly 
    exemplify it. -/
@[reducible]
def predicate.dere := ∀ e, ⋄(p e) → p.dere_of e
/-- A predicate is `adere` or **anti-*de re* necessary** if it fails to be *de re* necessary everywhere. -/
@[reducible]
def predicate.adere := ∀ e, ⋄(p e) → p.ndere_of e

/-- A positive predicate is possessed if it "talks about" its subject,
    which is to say that it is an accident or essential of a substance,
    or essential of an accident. -/
structure predicate.possessed extends predicate.positive p : Prop  :=
    (axiom₃ : ∀ (e : ω.entity) (h : e.pexemplifies p), 
              let r := (entity.mk (p e) (axiom₂ e) h) in
              e.perfect → r.subsists e
    )
    (axiom₄ : ∀ (e : ω.entity), e.pexemplifies p → e.imperfect → p.dere_of e)

/-- The *significatum* or *res significata* is the entity signified by a possessed predicate `p`,
    i.e. the entity such that its existence causes the truth of the predication
    for some entity `e`. -/
def predicate.possessed.sign {p : ω.predicate} (h : p.possessed) 
                                     {e : ω.entity} (ne : e.pexemplifies p) 
                                     : ω.entity := ⟨p e, h.axiom₂ e, ne⟩

/-  Intensionally, the previous definition is intended to be open to the idea
    that the *significatum* of a predicate with respect to an entity
    might be an intensional entity, and which entity it is might
    even vary across possible worlds. Nevertheless, any two intensional
    *siginificata* of a *de re* necessary predicate must be existentially
    equivalent, so for this case the definition returns the corresponding extensional
    entity. Introducing intensional *significata* for extensional predicates
    would require an additional primitive beyond the introduction of an intensional
    ontology, but it might be useful for e.g. defending an **intensional** distinction between
    essence and existence/being (*esse*), if one is of the interpretation that the Thomistic distinction
    is an intensional one. We however are not of this latter position, so we prefer
    rather to introduce an **extensional** distinction between essence and existence,
    that we present further below. -/

-- TODO: consider changing the name of these definitions in the future to potentially
-- avoid the same Kit Finean "essence is not de re necessity" objection we wished to avoid
-- when renaming "essential" to "dere". 

-- A possessed predicate is accidental of an entity if it is not essential.
-- From this we can infer (informally) that a predicate is either essential or accidental
-- of an entity or does not "talk about" an entity at all 
-- (or at least does not "talk about" all entities to which it is predicated).
@[reducible]
def predicate.accidental_of (e : ω.entity) := p.possessed ∧ p.ndere_of e
@[reducible]
def predicate.accidental := p.possessed ∧ p.adere

-- Notice there can be possessed predicates which are neither essential nor accidental in themselves,
-- but only with respect to a particular entity (it is in this sense that some say heat is
-- essential of fire but accidental of burning coal). But with respect to any particular entity
-- a possessed predicate is either essential or accidental. Notice also that this sort of predicate
-- is (almost) never univocal, because predicating something of both a substance and its accidents is never univocal.

-- a "proper" predicate, or a predicate in a more "proper" sense of the word,
-- is an univocal possessed predicate 
structure predicate.proper extends predicate.possessed p : Prop :=
    (axiom₅ : p.univocal)

variables (e : ω.entity) (ev : ω.event)

def predicate.bindp  : ω.predicate := 
  assume e₂, if e = e₂ then ev else p e₂

def predicate.localize : ω.predicate := (⊥ : ω.predicate).bindp e (p e)

variables (e) (p) (ev)

@[reducible, simp]
def entity.bindp : ω.predicate := p.bindp e ev

@[reducible, simp]
def entity.localize (p : ω.predicate) : ω.predicate := p.localize e

/-- The existence of an entity is the "existence" predicate localized to that entity. 
    It is an essential proper predicate from which all of its essential predicates
    follow, or as Aquinas puts it, existence (esse) is the greatest
    perfection of a thing, as it actualizes its very essence. -/
def entity.existence : ω.predicate := ω.existence.localize e

-- Note: "esse" used above is often translated as "existence" but this translation
-- has been disputed (see works of Cornelio Fabro CSS for an idea). More properly,
-- we consider "esse" to refer to "being" in Thomistic philosophy, which we shall 
-- define further down.

theorem existence_dere : e.existence.dere := sorry
theorem existence_proper : e.existence.proper := sorry
theorem existence_follows_dere : p.dere_of e → e.existence ≤ p  := sorry

/-- The haecceity of an entity is its incommunicable individual essence. 
    It differs from the existence of an entity in that while the existence 
    is *de re* necessary, the haecceity is absolutely necessary, or alternatively,
    haecceity predication does not have existential import, while
    existential predication (obviously) does. 
    However, for the necessary being existence and haecceity coincide. -/
def entity.haecceity : ω.predicate := λ e₂, {w | e = e₂}

theorem existence_haecceity_distinction : e.existence = e.haecceity ↔ e.necessary :=
  begin
    simp [ entity.existence
         , entity.haecceity
         , predicate.localize
         , predicate.bindp
         , existence
         , function.funext_iff
         , -entity_ext_iff
         ],
    constructor; intro h,
      ext w,
      simp [nbe, univ, has_mem.mem, set.mem],
      specialize h e w,
      replace h := h.2,
      simp at h,
      exact h true.intro,
    intros e₂ w,
    by_cases c : e = e₂; simp [c],
      rw h at c,
      simp [nbe, ext_iff] at c,
      specialize c w,
      exact ⟨λ_,true.intro, λ_,c⟩,
    refine ⟨_, false.elim⟩,
    intro hyp,
    simp [ has_bot.bot
         , order_bot.bot
         , bounded_lattice.bot
         , complete_lattice.bot
         ] at hyp,
    exact hyp,
  end

-- a predicate is communicable if it can be possibly exemplified by more than one entity
def predicate.communicable := ∃ e₁ e₂ : ω.entity,
                             e₁ ≠ e₂ ∧
                             e₁.pexemplifies p ∧
                             e₂.pexemplifies p

def predicate.incommunicable := ¬ p.communicable

-- the individual existence of an entity is of course incommunicable
lemma existence_incommunicable : e.existence.incommunicable := sorry

-- and so is its haecceity
lemma haecceity_incommunicable : e.haecceity.incommunicable := sorry

-- A normal, "everyday", predicate like "being red" 
-- (when e.g. it is predicated of substances, and not of "red" accidents)
-- is a communicable proper predicate.
structure predicate.normal extends predicate.proper p : Prop :=
    (axiom₆ : p.communicable)

-- Don't know if this is true
-- there are counterexamples when S contains contradictory predicates
-- but otherwise maybe an adaptation of this lemma is true
-- lemma inf_normal_normal : ∀ S : set ω.predicate, (∀ p : ω.predicate, p ∈ S → p.normal) → (Inf S).normal :=
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


-- The specific essence, or species, of an entity is a normal essential predicate from which
-- all its normal essential predicates follow.
def predicate.species_of := e.pexemplifies p ∧
                           p.normal ∧ 
                           p.dere ∧
                           ∀ p', e.pexemplifies p' → 
                                p'.normal →  
                                p'.dere →
                                p ≤ p'

def predicate.species := ∃ e, p.species_of e
def entity.has_species := ∃ p : ω.predicate, p.species_of e

-- An entity has at most one species
lemma unique_species : ∀ p₁ p₂ : ω.predicate, (∃ e, p₁.species_of e ∧ p₂.species_of e) → p₁ = p₂ := sorry

-- Now, essence is predicated in multiple ways, the foremost
-- of which is in the sense of species. However, among
-- things which have no species, essence only signifies haecceity,
-- leading us to the following definition:

/-- A predicate is the essence of an entity if it is either its specific essence or its haecceity. -/
def entity.is_essence := p.species_of e ∨ p = e.haecceity

-- We can then prove essence × existence distinction as well:
theorem existence_essence_distinction : e.is_essence e.existence ↔ e.necessary := sorry

end predicates

section apredicates

  variables (p : ω.apredicate) (e : ω.entity)

  def apredicate.sup := Sup (subtype.val '' (range $ p e))
  def apredicate.inf := Inf (subtype.val '' (range $ p e))
  def apredicate.max := Sup ⋃ e, (subtype.val '' (range $ p e))
  -- def apredicate.min := Inf ⋃ e, (subtype.val '' (range $ p e)) -- I think maybe this is always 0
  def apredicate.complete := p.max = 1

  def apredicate.existential := ∀ e, ↑(p e) ⊆ e.exists

end apredicates


section happiness

  variables (e : ω.entity) (p : ω.apredicate)

  /-- An `entity` is said to be **happy**, or **naturally perfect**, w.r.t some apredicate `p` in possible world `w` 
      if it attains the greatest degree of `p` it can achieve, at `w`. -/
  def entity.happy : ω.event := {w | e.exists w ∧ ↑(p e w) = p.sup e}

  /-- An `entity` is said to be **wholesome** w.r.t some apredicate `p`
      if it can possibly be happy w.r.t. `p`. -/
  def entity.wholesome := ⋄e.happy p

  /-- An `entity` is said to be **miserable** w.r.t some apredicate `p`
      if it cannot possibly be happy w.r.t. `p`. -/
  def entity.miserable := ¬ e.wholesome p

  -- TODO: maybe this one should be generalized to arbitrary observables.
  def entity.invariantly := ∀ w₁ w₂, e.exists w₁ → e.exists w₂ → p e w₁ = p e w₂
  def entity.invariantly_happy := e.invariantly p ∧ e.wholesome p
  def entity.absolutely_happy := □e.happy p

  /-- A **maximally perfectible** `entity` w.r.t some apredicate `p` is one which  
      can possibly be progressively perfected in the direction of attaining 
      the greatest degree of `p` that is possible for any entity to have. -/
  def entity.mperfectible := p.sup e = p.max

  /-- A **completely perfectible** `entity` w.r.t some apredicate `p` is one which  
      can possibly attain the greatest conceivable degree of `p`. -/
  def entity.cperfectible := ∃ w, p e w = 1

  /-- An `entity` is said to be **exemplary** w.r.t some apredicate `p` in some possible world `w` 
      if it is maximally perfectible in itself and happy at `w`. -/
  def entity.exemplary : ω.event := {w | e.mperfectible p ∧ e.happy p w}

  /-- An `entity` is said to be an **exemplary cause of `p`**, or an **examplar** w.r.t some apredicate `p`, 
      if it can possibly attain the greatest degree of `p` that is possible for any entity to achieve.
      i.e. it is an entity which is possibly `exemplary`. -/
  @[reducible, simp]
  def entity.ecause := ⋄e.exemplary p

  /-- An apredicate is **exemplarily caused** if it admits an `exemplar`. I.e., an
      `entity` which  can possibly attain the greatest degree of `p` that is 
      possible for any entity to have. -/
  def apredicate.ecaused := ∃ e : ω.entity, e.ecause p

  /-- An `entity` is said to be **absolutely exemplary**, or **maximally perfect**, w.r.t some apredicate `p`
      if it is exemplary in every possible world. -/
  @[reducible, simp]
  def entity.absolutely_exemplary := □e.exemplary p
  /-- "**Maximally perfect**" is an alias for `absolutely_exemplary`. -/
  @[reducible, simp, alias]
  def entity.mperfect := e.absolutely_exemplary
  

  /-! # The Intuition behind exemplary causes. 

      The property of real numbers of being "close" to a given
      number, say `5`, is an analogical predicate which admits an exemplary cause, 
      namely `5`. We can define this predicate as something like `close₅(x) = 1 ÷ (∥x - 5∥ + 1)`,
      as we can see that `close₅(5) = 1`, `∥x∥ ⇒ +∞, close₅(x) ⇒ 0`, `∀x, 0 ≤ close₅(x) ≤ 1`. 
      This predicate defines a so called "fuzzy set" of real numbers:
      the real numbers which are "close" to `5`. 
      The number `5` is called an **exemplary cause** of the predicate `close₅` 
      because, given the fact that it attains the greatest conceivable degree of `close₅`,
      it also serves as an ultimate criteria of comparison for determining the extent to which a real number is
      close to `5`, i.e. a number will attain higher degrees of `close₅` precisely to the extent to which
      it is close to `5`. `close₅` can then be deemed a *measure of similarity to a point*, namely the point
      `5`, the **exemplar**.

      What other kinds of predicates are measures of similarity to a point in a similar way? It appears
      that natural and moral perfections are good candidates for being exemplarily caused.
      We have an intuitive grasp, for instance, of what a good, or healthy, dog is, insofar as we can imagine
      a "perfect" dog. The dog of our dreams is one which, perhaps, 
      is very strong, playful, healthy and active, lives by a healthy diet, 
      is cheerful, gets a lot of sunlight, exercises regularly,
      is a very effective apologetics minister by
      putting the fear of God into the hearts of burglars and trespassers,
      is docile, etc...
      It is the kind of dog you would likely see portrayed in a dog food commercial, or 
      something of the sort. He is the exemplar of what the natural powers of dogs
      can achieve when they operate in the most perfect way possible. It is an ideal dog,
      and just like with any ideal we can't help but measure other dogs with respect it. 
      There are then clearly different degrees to which a dog can fully achieve the potential 
      of its nature, so that we can even say, that the exemplar dog is a dog 
      *in the proper sense of the word*, or absolutely, *simpliciter*, without qualification,
      while dogs not measuring up to its standards are only dogs in a more limited sense of the word,
      with qualification, relatively, or *secundum quid*. All dogs can in a sense be said to 
      *participate* of the exemplar dog to the extent that they are similar to it, in a way reminiscent
      to how things were supposed by Plato to participate in their Platonic forms.
  
  -/


  theorem inner_life_of_the_absolutely_exemplary : e.absolutely_exemplary p ↔ e.absolutely_happy p := sorry

  lemma necessary_of_abs_exemplary : e.absolutely_exemplary p → e.necessary := sorry

end happiness


section being

/-! # The Analogy of Being

   We have seem that existence is not truly an univocal property, but a hidden analogy.
   This is obvious from the consideration that substances possess a higher degree
   of existence than their accidents, insofar as the accidents do not subsist of themselves,
   but must inhere in a substance. The analogical nature of existence formally follows 
   from the fact that accidents entail the existence of their substances.
   
   As such we should expect there to be an analogical predicate from which existence is abstracted,
   and with respect to which "existence" will, in a sense, come by degrees. However,
   because we typically think of existence as an univocal property, having no degrees, 
   we shall name this "existence" which comes by degrees **being**, rather than existence.
   Another, way to see that this "being" has degrees is to consider that being is identical
   in reality to other two so called *transcendental properties* which quite clearly have degrees, namely
   unity and actuality, which are called so because anything that exists is one individual unified thing 
   and also actual. And this we can show not only by comparing accidents to substances, but also from
   comparing substances to substances.
   
   We observe in reality that things are more or less unified and more or less actual;
   the first we notice from the fact that all natural entities have an intrinsic unification principle which
   unifies their parts more or less, allowing the entity to be more or less complex. At the bottom of the hierarchy
   of unity we have gases, for which the unification principle is the weakest insofar as whatever 
   unifies gases in a whole is not strong enough to give them a definite shape, which is rather imposed from
   without, by an external container. Next we have liquids which possess greater solidity, and hence unification,
   than gases, but are still not unified enough to possess their own shape; though they already exhibit some
   resistance against compression. We then have solids which are unified enough to have their own shapes
   and are often much more resistant to compression and various pressures than the previous. 
   Plasmas are however harder to classify since the ancients would equate them with fire, which was considered 
   the most perfect of the 4 elements, though fire has a less stable shape than a solid, so it is unclear whether
   they should be considered more perfect than solids or not. After the minerals, however, we have living organisms
   which are much more unified and complex than any minerals, and among them we have animals which exhibit 
   even greater complexity and unification, and finally we have humans, which unify physical and metaphysical
   substances into the same whole. 

   On the other hand, we have among these levels also greater degrees of actuality, since a thing is able
   to act more perfectly insofar as it is more actual, and yet anything is actual insofar as it exists. A natural
   entity is more actual to the extent that it has more energy and is habitually capable of using this energy
   to perform more complex vital operations. It is in this respect that fire/plasma is the most perfect state of
   inanimate matter, but any living organism is more perfect than it insofar as its energy does not come in the
   form of useless heat, but of direct and complex vital operations.

   It is furthermore the case that natural substances vary in perfection with respect to time,
   becoming more or less perfect depending on the circumstances. A good man can be said to be more 
   perfect than a bad one, in a moral sense of the word "perfect", while a healthy man can be said 
   to be more perfect than an unhealthy one, in a more natural or biological sense of the word.

   These considerations suffice for showing that natural entities exhibit greater or lesser degrees of perfection,
   but we must also extend this consideration to metaphysical entities. Metaphysical entities which have no parts,
   spatial extension and, specially, accidents, are more perfect than natural entities, not on account of a greater
   amount of complexity or energy, but on account of their greater unification and actuality. Unification
   in natural entities which have parts is exhibited in complexity insofar as a greater unifying principle is required
   to amalgamate a multiplicity of disparate entities into a single unified whole; however the more unified
   a substance is the less will their parts behave like disparate or independent entities to begin with.
   As the unity of a substance increases, its parts become so intertwined with it that
   they begin to exhibit fundamental ontological dependencies to the whole, and vice-versa. 
   This is already observable in the case of living animals,
   for which the removal of an organ causes the death of the same organ,
   and often the death of the animal, in a very short period of time;
   unless artificial means are used to keep them alive.
   In the limit, this ontological dependencies would grow to become full existential dependencies,
   so that it would be impossible to distinguish a substance from its parts by extensional means,
   and we could simply say that the substance has no parts, because it has "absorved" all of its "parts"
   within itself. A substance of this sort would exhibit greater unification than any natural
   entity, even though it would be absolutely simple.

   With respect to extension, metaphysical substances are more perfect, insofar as to have extension
   is but to be limited to a particular (compact, connected) region of space, outside of which 
   the substance has no existence, while a substance without extension can be said to exist in all points
   of space without limits, as we shall later formalize (in geometry.lean). Furthermore it is obvious
   that simple substances, which have no accidents, are more perfect than composite substances, not only
   because of the provable facts that (1) no simple substance existentially depends on a composite, (2)
   if a simple substance can possibly exist, 
   all composite substances will depend on at least one simple substance (i.e. God), 
   but also due to the consideration that being the multiplicity of states the origin of a multiplicity
   of different ways of existing and of passive potentiality, and being the multiplicity of possible accidents
   the origin of the multiplicity of states, it is clear that a substance without accidents has no 
   passive potentiality (outside perhaps of a potentiality for existence or non-existence) and no multiplicity
   of ways of existing, hence being much more unified and actual than any substance with accidents.

   At last, metaphysical entities which are necessary are clearly more perfect than contingent ones, 
   just as any substance which depends on another, should be less perfect than this other. 
   These considerations suffice to show then that even among metaphysical substances,
   or when comparing metaphysical substances to natural ones, there are differing degrees of
   unification, actuality and, hence, also perfection and being. -/

  /-- The **Being**, **analogy of being**, or *actus essendi* of an ontology is an `apredicate` **is** 
      which gives to every possible entity in every possible world the degree of being,
      or degree of perfection, that the entity has in that world.
      This perfection, or degree of being, is also a measurement of the degree of actuality of an entity,
      as it varies across possible worlds. Entities which are invariant with respect to
      being, are less fleeting, and as such more actual, while entities which vary greatly in being
      are more fleeting, more potential and, hence, less perfect in being. They are also less unified, 
      less truthful, less good, less beautiful, etc... for all the so called *transcendentals of being*. -/
  structure being (ω : ontology) := 
    (is : ω.apredicate) 
    -- Being is synonymous with existence, 
    -- in the sense that an entity can only have
    -- being in any capacity or amount whatsoever
    -- if it exists, and to exist is nothing other
    -- than to participate in being to some extent
    -- or to some capacity. Existence is abstracted
    -- from being.
    (axiom₁ : ∀ e, ↑(is e) = e.exists)
    -- Being respects the hierarchies of ontological dependencies,
    -- indeed it is the very **origin** of said hierarchies. The most
    -- basic relation of ontological dependency is existential entailment,
    -- so entities which depend existentially on another shall be less perfect than
    -- that other, in any possible worlds in which they exist.
    (axiom₂ : ∀ e₁ e₂ : ω.entity, e₁ ≠ e₂ → e₁.exists ⇒ e₂.exists → is e₁ < is e₂)
    -- Being is complete, for it if were not then the maximum degree
    -- of perfection attainable by an entity would necessarily fall short
    -- of 100% of the maximum degree of perfection attainable by an entity, which is absurd.
    -- i.e., an entity that has degree of perfection 1.0 in any possible world
    -- is to be interpreted as having attained the maximum possible degree of perfection
    -- any entity could possibly achieve.
    (axiom₃ : is.complete)
    -- A substance is more or less perfect across possible worlds only because of the variability
    -- of the accidents inhering in it, so in worlds in which a substance has the same state
    -- it should have the same degree of perfection also.
    (axiom₄ : ∀ (s : ω.substance) (w₁ w₂), s.equiv w₁ w₂ → is s.up w₁ = is s.up w₂)
    -- Furthermore, in worlds in which more things subsist in a substance, it should also 
    -- be more perfect, for the perfection of the subsistent entities should, in some
    -- sense, "add up" to an increase in the overall perfection of the substance.
    (axiom₅ : ∀ (s : ω.substance) (w₁ w₂), s.state w₁ ⊂ s.state w₂ → is s.up w₁ < is s.up w₂)
    -- Furthermore, states were not defined for accidents since nothing subsists in them.
    -- It should follow that accidents have being invariantly, for without variation of
    -- accidents there can be no variation of perfection.
    (axiom₆ : ∀ (a : ω.accident), a.up.invariantly is)
    -- In any possible world in which a simple substance exists, it is more perfect
    -- than all composite substances existing in the same world.
    -- Note: this does not assume that it is possible for simple substances to exist,
    -- only that **if** they do exist, they are more perfect than the composites.
    -- We will show later that the possible existence of simple substances is logically 
    -- equivalent to the existence of a (possibly non-classical) God. We however
    -- do not need this axiom to show that God is more perfect than composite things,
    -- for this follows from axiom 2, but rather we only need it to show that other, contingent,
    -- simple substances are more perfect than composite substances.
    (axiom₇ : ∀ (s₁ : ω.substance) (w), s₁.simple → s₁.exists w → 
      ∀ (s₂ : ω.substance), s₂.composite → s₂.exists w → is s₂.up w < is s₁.up w)
    -- If two entities are of the same species, it should be 
    -- possible for both to achieve exactly the same levels of
    -- perfection. TODO: number this axiom and make sure the numbering is consistent
    -- with pextensions.
    (axiom_to_number : ∀ (e₁ e₂ : ω.entity) (p : ω.predicate), p.species_of e₁ → p.species_of e₂ → range (is e₁) = range (is e₂))

  variable (b : ω.being)
  open predicate

  -- The necessary being is maximally perfectible w.r.t. any analogy of being.
  -- Only needed axiom₂ for this proof.
  lemma nbe_mperfectible : ω.nbe.mperfectible b.is :=
    begin
      simp [entity.mperfectible],
      symmetry,
      apply cSup_intro,
      -- goal 1
        obtain ⟨w⟩ := ω.wne,
        use b.is ω.nbe w,
        simp,
        constructor,
          exact (b.is (nbe ω) w).property,
        use ω.nbe, use w,
      -- goal 2
      intros r H,
      simp at H,
      obtain ⟨e, hr, w, eq⟩ := H,
      set rhs := apredicate.sup b.is (nbe ω),
      let r₂ := b.is ω.nbe w,
      transitivity r₂.val, swap,
        apply le_cSup, swap,
          simp [range, image],
          constructor,
            exact r₂.property,
          use w,
        simp [bdd_above, upper_bounds],
        use 1, simp, intros r₃ hr₃ _,
        simp [set.Icc] at hr₃,
        exact hr₃.right,
      by_cases h : e = ω.nbe,
        simp [r₂],
        rw [←h, eq],
      have c := b.axiom₂ e ω.nbe h _, swap,
        simp [ontology.nbe, set.subset],
      replace c := c.left w,
      rw eq at c,
      exact c,
      -- goal 3
      intros r hr,
      obtain ⟨r₂, hr₂, c⟩ := exists_lt_of_lt_cSup _ hr,
      use r₂,
      simp [range, image] at hr₂,
      simp [hr₂, c],
      use ω.nbe,
      exact hr₂,
      obtain ⟨w⟩ := ω.wne,
        use b.is ω.nbe w,
        simp,
        constructor,
          exact (b.is (nbe ω) w).property,
        use w,
    end

  /-- Misery begets misery. A wholesome entity should not depend on a miserable one.
      analogies of `being` satisfying this principle are said to be **proportionally happy**, for they
      satisfy a form of proportionate causality with respect to happiness. -/
  def being.phappy : Prop := ∀ (e₁ e₂ : ω.entity) w, e₁.happy b.is w → (e₁.exists ⇒ e₂.exists) → e₂.happy b.is w

  /-- An analogy of `being` is said to be **wholesome** if some `entity` is `wholesome` with respect to it. -/
  def being.wholesome : Prop := ∃ e : ω.entity, e.wholesome b.is

  /-- An analogy of `being` is said to be **absolutely exemplary** if some `entity` is `absolutely exemplary` with respect to it. -/
  def being.absolutely_exemplary : Prop := ∃ e : ω.entity, e.absolutely_exemplary b.is

  -- exemplary

  /-- An analogy of `being` is said to be **Exemplarily Caused** if it is exemplifiable.
      I.e. if some `entity` is an **exemplary cause** (`ecause`) of being. -/
  def being.ecaused : Prop := b.is.ecaused

  lemma ecaused_of_phappy_and_wholesome : b.phappy → b.wholesome → b.ecaused := sorry

  lemma exemplar_nbe_of_ecaused : b.ecaused → ω.nbe.ecause b.is := sorry

  /-- The perfection of a multitude of entities should increase with the number of entities.
      Analogies of `being` satisfying this principle are called **composable**. -/
  def being.composable := ∀ (s : set ω.entity) (e : ω.entity) (w₁ w₂ : ω.world),
                            e ∉ s →
                            e = Sup s →
                            w₁.entities ∩ s ⊂ w₂.entities ∩ s →
                            b.is e w₁ < b.is e w₂


  /-- An analogy of `being` is said to be **essentially exemplary** if it is essential for entities to be exemplary 
      with respect to it.
      Nothing could explain otherwise why an entity would be exemplary in one world
      but not in some other.
       -/
  def being.eexemplary  : Prop := dere (flip entity.exemplary b.is)

  lemma abs_exemplary_intro {b : ω.being} : b.ecaused → b.eexemplary → b.absolutely_exemplary := sorry
  lemma nbe_eq1_of_abs_exemplary {b : ω.being} : b.absolutely_exemplary → ∀ w, b.is ω.nbe w = 1  := sorry

  /-- A **quasi-participated** `being` is essentially exemplary and exemplarily caused. -/
  @[reducible, simp]
  def being.qparticipated := b.ecaused ∧ b.eexemplary

  def being.participated := b.composable ∧ b.qparticipated

  def participated (ω : ontology) := ∃ b : ω.being, b.participated
  def composable (ω : ontology) := ∃ b : ω.being, b.composable
  def exemplary (ω : ontology) := ∃ b : ω.being, b.absolutely_exemplary

  lemma exemplary_of_participated : ω.participated → ω.exemplary := 
    begin
      rintro ⟨b, hbc, hbs, hbes⟩,
      use b,
      exact abs_exemplary_intro hbs hbes,
    end


section pextension

  /-- A **Platonic Extension** equips every property of a certain kind (e.g. normal) with an analogical extension, 
      satisfying certain properties. These include possessing the predicate in a more perfect way
      than whatever possesses it in the usual way, i.e. "formally".
       This is done so that the concept of **eminence** can be defined. -/
  structure pextension (ω : ontology) (prop : ω.predicate → Prop := predicate.normal) extends being ω := 
    -- To every univocal, normal, predicate there corresponds some
    -- analogical predicate
    (extended : Π (p : ω.predicate) (h : prop p), ω.apredicate)
    -- from which it was at least partially abstracted.
    -- This means all entities having the predicate have the analogical predicate, in some
    -- capacity, or to some extent.
    (axiom₈  : ∀ (p : ω.predicate) (h : prop p) e, p e ⊆ ↑(extended p h e))
    -- However, whatever has the apredicate to some capacity but does not have the predicate,
    -- has the predicate to a strictly greater or more perfect extent than anything which can possibly
    -- have the predicate.
    (axiom₉  : ∀ (p : ω.predicate) (h : prop p) e₁ w₁, w₁ ∈ ↑(extended p h e₁) - p e₁ → 
      ∀ e₂ w₂, p e₂ w₂ → extended p h e₂ w₂ < extended p h e₁ w₁)
    -- The apredicate is always existential
    (axiom₁₀  : ∀ (p : ω.predicate) (h : prop p), (extended p h).existential) 
    -- Equality in being implies equality in the perfection of the analogical extension
    (axiom₁₁  : ∀ (p : ω.predicate) (h : prop p) e (w₁ w₂), is e w₁ = is e w₂ → extended p h e w₁ = extended p h e w₂)
    -- We stipulate also that the class of predicates prop, has to satisfy certain conditions in order to admit
    -- a platonic extension. All of these conditions are satisfied by the default (predicate.normal).
    (condition₁ : ∃ p, prop p)
    (condition₂ : ∀ (p : ω.predicate), prop p → p.exemplifiable)

  variables {prop : ω.predicate → Prop} (ext : ω.pextension prop) (p : ω.predicate) (h : prop p)

  def entity.eminently (e : ω.entity) : ω.event := {w | ¬ p e w ∧ ext.extended p h e w ≠ 0 }

  def entity.eminent (e : ω.entity) : Prop := e.eminently ext p h = e.exists

  def pextension.non_trivial := ∃ (p : ω.predicate) [h : prop p] (e : ω.entity), ⋄e.eminently ext p h


end pextension



end being

end ontology