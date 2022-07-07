import metaphysics.counterfactuals states
open set topological_space classical
set_option pp.generalized_field_notation true
local attribute [instance] prop_decidable
noncomputable theory


namespace ontology

variables {ω : ontology}

/-! # Multiplicity of Meanings, Correctness of definitions, and Defaults

   In what follows we must keep in mind that "cause" and "explanation", just like
   many other philosophical concepts, have multiple
   valid and philosophically relevant meanings. So whenever we introduce some notion of
   causation or explanation, this does not commit us to the position that no other such
   notions could be further introduced; as indeed we ourselves have introduced more than
   a single one of these notions. In particular, if another philosopher introduces
   a completely different notion we are not prima facie committed 
   to any special position regarding that notion.
   We should not multiply disagreements among philosophers beyond necessity,
   and so we should not assume that simply because a philosopher has said something
   different from what we have said about causality that we must disagree with him.
   For it could be that (1) if the two different positions refer to one and the same concept,
   or phenomenon, of causality, still the positions may not be contrary of themselves,
   and so it might be logically consistent to hold both together. Furthermore, 
   it might even be the case that (1.1) one of them logically entails the other,
   or that (1.2) one can be otherwise reduced to the other, or that (1.3) 
   they are logically equivalent; and this can be the case even when the
   positions appear to be saying very different things, but further logical 
   analysis can be used to show that deep down they are saying essentially the same
   thing. Finally, it could be that (2) the two positions refer to two genuinely 
   distinct, complementary, and irreducible concepts of causality, and so 
   a potential disagreement can be resolved by accepting both concepts as distinct 
   and equally valid meanings that the same word can take; just as, for example, 
   Aristotle accepts 4 distinct meanings of the concept of "cause". And when (2) is at all plausible
   its adoption is to be preferred over disagreement with another philosopher 
   who has given plausible reasons as to why his position must be true, unless we are able
   to sufficiently explain to him that the plausibility behind the reasons he adduces is not due to his theory of
   causality being true, but that it can be better explained by our own theory. Proceeding in this way we can keep
   disagreements to a minimum, leaving greater room for cooperation.
   
   Furthermore, at least *some* of the arguments we will introduce, e.g. about the existence of God,
   will not really depend on the assumption
   that any notion of cause we introduce is the "correct" notion of cause, or that it even captures
   the pre-theoretical phenomenon of causality in any capacity at all; and this is because some arguments can be made
   to the extent that if such and such talk of "causes" (e.g. the causal terminology of Aristotle) 
   is logically consistent with our background `ontology` then some important 
   consequences may follow from this logical consistency assumption alone. 
   And this would be furthermore so even if we had good evidence that such "talk" does not capture what people 
   regularly intend to mean by causes, or even if we were non-cognitivists about causality,
   who thought that any talk of "causes" is always meaningless gibberish
   which refers to nothing in reality; so long as it was logically consistent
   meaningless gibberish this would still be enough for the purposes of these arguments, as we shall
   later show. Hence, with respect to these arguments, disagreements about the true nature of causality
   would be ultimately irrelevant.
   
   Though admittedly, perhaps, some theories of the meaning of causality that are introduced
   by philosophers better capture the phenomena and are more parsimonious, 
   or more useful for metaphysics, than others; so that in this respect there can
   indeed be disagreement among philosophers about which theory of causality better captures
   its true nature. Indeed, in the extreme case, it may be proposed by one philosopher that the theory
   espoused by another philosopher is not only worse than his own, but that 
   it is meaningless, or that it does not qualify as a theory of causality at all.
   However, we believe that formalization suffices
   to resolve charges of "meaninglessness" made against philosophical theories,
   so that if a theory of causality is formalized, then unless it says something clearly preposterous,
   utterly implausible, self-evidently false, or completely irrelevant to the phenomenon at hand,
   it will be very hard to dismiss it as not being a theory of causality at all in the first place.
   So the bar should be pretty low on what counts as a valid meaning, definition or theory of causality,
   provided it is a formal definition/theory.

   But when we judge among theories which are clearly valid theories of causality,
   which theory is better, we must be presupposing, or at
   least it may be convenient to presuppose, that the question only makes sense
   relative to some standard. Some ideal notion of causality which captures the
   phenomenon better than any alternative notion, or in other words, some 
   ideal notion of causality which is *correct by definition*. We can then judge 
   a theory's correctness as a definition of causality by the extent to which the theory
   is similar to the ideal one which is correct by definition. 
   
   Why am I saying all of this? Well, it turns out that the Lean theorem prover
   already provides us with a nice mechanism for talking about the "ideal" notion of
   causality. Suppose that a philosopher wants to make the claim that some such notion of
   causality `X : ω.cause` is the correct notion of causality for the ontology `ω`, 
   he can do this by using the `inhabited` type:

   ```instance correct_notion_of_causality : inhabited ω.cause := ⟨X⟩```

   If a philosopher uses this library to formalize his theory of causality
   as the instance `X` of the `ω.cause` type, and then adds the line above to his code,
   he will be able to refer to `X` by the expression `default ω.cause`. 
   We can then adopt the convention that the `default` value 
   of a type defining a controversial philosophical concept,
   is to be used to refer to the ideal version of the concept which is correct by definition.
   So when the philosopher adds the line above to his code he will effectively be claiming
   that `X` **is the correct definition/true nature of causality**. If however another instance of 
   `inhabited ω.cause` had previously been defined by another philosopher, `default ω.cause`
   will become ambiguous. A philosopher will be able to check whether any
   philosopher using the library has disagreed with him about the true meaning of causality
   by verifying whether there are any other definitions of an instance of `inhabited ω.cause` 
   in the code, a process which can surely be automatized in the future.

   The point of this is that we can concentrate real disagreements of philosophy into the problem
   of defining a single unique instance of the inhabited class for every controversial concept of philosophy. 
   Until a philosopher has proposed a definition of `inhabited ω.cause`, he will not have said anything controversial
   about causality even if he introduced a myriad different definitions of possible causal structures, made
   assumptions about them, and proved theorems from the assumptions. Even if he introduces a definition very
   distinct and incompatible with my own, until he declares it to be the uniquely correct definition of causality,
   he will simply be talking about something wholly different from what I am talking about when I am talking about
   causality. Our disagreements can then be at most disagreements about the meanings of words, i.e. "semantic" ones,
   but not about the phenomenon itself, so that **any true disagreement of philosophers about the meaning of a**
   **concept will ultimately boil down to the question of defining the `default` version of that concept**,
   i.e. of defining what the `default` meaning of the concept should be. And if furthermore all disagreements of
   philosophy also boil down to disagreements about the meanings of concepts. then of course 
   **any true disagreement of philosophers will ultimately boil down to the question of defining**
   **the `default` version of some concept**.

   Hence to sumarize the main points of each of the above paragraphs, in order:
    1. We need not disagree about the true nature of causality just because I have introduced a 
       theory of causality which appears to be different from your own theory,
       or which might even at first appear to contradict it.
    2. Even if we do disagree about the true nature of causality, this might be irrelevant to some of
       of the arguments I will present, which cannot be blocked by this sort of disagreement. Even some
       cosmological proofs of the existence of God will not be answerable in this way.
    3. Even if we were to ask the question "What is the true nature of causality", just out of curiosity,
       and even if we disagreed about the answer, we could confine all our disagreement 
       in a single place, in the definition of `inhabited ω.cause`. And anything else that we did
       say about causality which did not make reference to `default ω.cause` would not have directly concerned
       the "true nature of causality", and hence could not constitute a disagreement about it.
    4. The idea of confining our disagreement to a particular instance of a type class has natural support 
       from the language of the Lean prover. In the future we may be able to do some automation 
       so that a philosopher can easily find out all alternative proposals for the definition of `default ω.cause`.
    5. **Any true disagreement of philosophers will ultimately boil down to the question of defining**
       **the `default` version of some concept**.
    6. Extra: Despite all of this, it just might be the case that I lucked out and just happened to 
       find the true nature of causality using one of the definitions I will present.
       That is not so implausible, even though the definitions I will provide are only tentative
       at best for the purpose of discovering "the true nature". So despite all I've said, if you disagree
       with me, one plausible solution out of this conundrum would be to just claim that you are wrong (you fool).
       But avoiding having to claim this directly is really 90% of the purpose of writing this massive wall of
       text to being with, so that I can avoid any ontological responsibility for introducing
       assumptions; like the good coward that I am ;).

   Now, we cannot know prior to investigation, whether there is a single meaning 
   of causality which explains all others, and in terms of which all others can be
   reduced, or if there are several. Aristotle famously defended the latter view with
   his doctrine of the 4 causes, in which all 4 causal concepts are primitive and 
   irreducible to each another. If this view is correct, then instead of 
   defining a single default theory of causality, we should primarily seek to partition
   the possible causal structures into subtypes and provide a separate `default`
   for each subtype. So for instance, we could define `ω.efficient_cause` as an extension
   of the `ω.cause` structure which we define below with further axioms which characterize
   efficient causes, and then define an instance of `inhabited ω.efficient_cause`. 
   This would also not pose problems if we wanted to keep an already existing 
   definition of `inhabited ω.cause` because
   if we properly partition `ω.cause` into subtypes then `default ω.cause` would have to "belong"
   to one of these subtypes, say `ω.efficient_cause`, 
   and so by setting this `default` we would be claiming philosophically
   that the most used, fundamental, or relevant, notion of cause is also an `ω.efficient_cause`, i.e. an efficient 
   sort of cause, even if not all causes could be reduced to efficient causes.
   And so, because we can make sense of the meaning of `default ω.cause` even in the context
   of there being subtypes of `ω.cause` with their own `default`s, we need not remove the `inhabited ω.cause` 
   instance definition from Lean just because we introduced a new subtype of `ω.cause`.

   What I have said in this section about causality applies really to **any** philosophical concept
   whatsoever whose theory or definition can possibly be disputed among philosophers.
   This them provides us with a general method for doing philosophy which is greatly
   enhanced by the usage of a theorem prover. 

-/

/-- Explanatory structure, used to define Leibniz's concept of **explanation**.
    Notice however that what Leibniz's called explanation Aristotle would have 
    called "cause". -/
structure explanation (ω : ontology) :=
  (explains : ω.event → ω.event → ω.event)
  (nontrivial : ∃ e₁ e₂, ⋄explains e₁ e₂)
  (transitive : ∀ e₁ e₂ e₃, explains e₁ e₂ ∩ explains e₂ e₃ ⇒ explains e₁ e₃)
  (axiom₀ : ∀ {e w}, (∃ e', explains e' e w) → e.occurs w)
  /-- Events which possess some explanation as to why they occur must occur in the first place. -/
  add_decl_doc explanation.axiom₀

namespace explanation 

  variable (ε : ω.explanation)

  /-- Events need to occur in order to explain another event.
      Explanatory structures satisfying this principle are called **simultaneous**
      because they require the *explanans* to be simultaneous to the
      *explanandum*. This is the most relevant property
      to distinguish between different meanings of "explanation". -/
  def simultaneous := ∀ {e w}, (∃ e', ε.explains e e' w) → e.occurs w

  /-- An event is a substratum if any of its explanations have to be simultaneous
      to it.  -/
  def substratum (e : ω .event) := ∀ e', ε.explains e' e ⇒ e'

  /-  The meaning of the above definition is given by
      the consideration of the similarity
      of the event `e` to the event of the existence of the
      material substratum of physical things, insofar as the cause or explanation
      of the existence of this material substratum cannot be something 
      that occurred in the past, but rather it must be something simultaneous
      to this substratum.
      The theory behind this is that only configurations of the material
      substratum `m` could possibly be caused in world `w` 
      by something `e` which no longer exists in `w`, 
      and this happens precisely when `e` is the cause of 
      some motion in some previous possible world `w₀` 
      which ultimately lead to the configuration `m` existing in `w`.
      So we say that the potter is the cause of a clay pot even when the potter
      is dead and no longer exists, only because of the fact that, 
      at some point in the past, the potter was the simultaneous cause of some
      motion of clay which changed the material configuration of the clay
      until the point that it became a pot. The fundamental kind of
      causation as such is simultaneous causation, as non-simultaneous cases 
      can be reduced to the simultaneous ones.

      After the clay became a pot, it 
      no longer needed the potter for continuing to be a pot, but this is so
      only because the pot is nothing but a configuration of the underlying clay. 
      Some things however, like the fundamental particles of physics, or any
      sort of fundamental material substratum that is proposed for things,
      cannot be reduced to configurations of further material substrata,
      and so could not possibly be caused like the potter causes the pot. 
      As such, to the extent that these things are caused at all, their cause
      must be simultaneous to them. Furthermore, it may just be that many other
      things besides material substrata behave like this, for instance processes
      and motions, so we are not claiming that every event that is a `substratum`,
      in accordance with our definition, needs to be a material substratum at all,
      the reason for the naming is only due to the fact that it shares this property
      with a material substratum. 
      
      We would like to avoid having to formally define what "motion" is,
      and give a formal account of temporal considerations here, because 
      that would simply complicate the discussion, so instead 
      we are making this argument informally for now.
      
  -/

  /-- An event **simultaneously explains** another event if it explains it and 
      it must be simultaneous with that particular event in order to explain it. -/
  def simexplains (e₁ e₂ : ω.event) : ω.event := ε.explains e₁ e₂ ∩ {w | ε.explains e₁ e₂ ⇒ e₁}

  -- Note that in the right of the `∩` in the previous definition we are just lifting a `Prop` to an
  -- `ω.event`. If the `Prop` is true, `simexplains` just reduces to `explains`, otherwise
  -- it is the empty set, i.e. the impossible event.

  /-- The (explanatory) **Principle of Sufficient Reason**, as an event. -/
  def epsr (kind := @event.contingent ω) : ω.event := 
    {w : ω.world | ∀ (e : ω.event), kind e → e.occurs w → ∃ e', ε.explains e' e w}

  /-- The (explanatory) **Weak Principle of Sufficient Reason**, as an event. -/
  def ewpsr (kind := @event.contingent ω) : ω.event := 
    {w : ω.world | ∀ (e : ω.event), kind e → e.occurs w → ∃ e', ⋄ε.explains e' e}

  /-- The (explanatory) **Principle of Sufficient Reason**. -/
  def psr (kind := @event.contingent ω) : Prop := □ε.epsr kind

  -- Note: by introducing the default argument in the definition, 
  -- we get that calling `ε.psr` without arguments will claim "every contingent event has an explanation",
  -- but by providing the additional "kind" argument, you get a localized `psr` which claims
  -- "every entity of a certain *kind* has an explanation".

  /-- A **stronger** version of the (explanatory) **Principle of Sufficient Reason**, as an event.
      It claims that "Every event has an explanation". -/
  def sepsr : ω.event := ε.epsr univ 

  /-- A **stronger** version of the (explanatory) **Principle of Sufficient Reason**. -/
  def spsr : Prop := □ε.sepsr



end explanation

/-- Causal structure, used to define the concept of causation. 
    A causal structure is an irreflexive explanatory structure. -/
structure cause (ω : ontology) extends explanation ω :=
  (irreflexive : ∀ e, ¬⋄explains e e)

namespace cause

  variable (c : ω.cause)

  def up := c.to_explanation
  @[reducible, simp, alias, inline]
  def causes := c.explains

  -- Note: We would rather repeat some definitions of explanations, since
  -- we will mostly be talking about causes, so we try to minimize usage of `cause.up`.

  /-- Events need to occur in order to cause another event.
      Causal structures satisfying this principle are called **simultaneous**
      because they require the cause to be simultaneous to the
      effect. This is the most relevant property
      to distinguish between different meanings of "cause".
      Metaphysical causality should be expected to be primarily simultaneous,
      while the physical causality of the special sciences often presupposes
      that causes are temporally prior to their effects, rather than simultaneous. -/
  def simultaneous := ∀ {e w}, (∃ e', c.causes e e' w) → e.occurs w

  /-- An event is a substratum if any of its causes have to be simultaneous
      to it.  -/
  def substratum (e : ω .event) := ∀ (e'), c.causes e' e ⇒ e'

  /-- An event is a substratum locally in some possible world 
      if any of its causes in that world have to occur in that world
      in order to cause it.  -/
  def esubstratum (e : ω .event) : ω.event := {w | ∀ (e'), c.causes e' e w → e'.occurs w}

  /-- An event `e₁` **simultaneously causes** another event `e₂` if `e₁` causes `e₂` and 
      `e₁` needs to be simultaneous with `e₂` in order to cause it. -/
  def simcauses (e₁ e₂ : ω.event) : ω.event := c.causes e₁ e₂ ∩ {w | c.causes e₁ e₂ ⇒ e₁}

  /-- The **Principle of Substratum** for events, as an event. 
      It reads: "Events of a certain kind (contingent) are substrata.". -/
  def eps' (kind := @event.contingent ω) : ω.event := {w | ∀ e, kind e → e.occurs w → c.substratum e}
  /-- The **Principle of Substratum** for events. 
      It reads: "Events of a certain kind (contingent) are substrata.". -/
  def ps' (kind := @event.contingent ω) : Prop := □c.eps' kind
  /-- The **Principle of Substratum** (for entities), as an event. 
      It reads: "Entities of a certain kind (contingent) are substrata.". -/
  def eps (kind := @entity.contingent ω) : ω.event := {w | ∀ e, kind e → e.exists w → c.substratum e}
  /-- The **Principle of Substratum** (for entities). 
      It reads: "Entities of a certain kind (contingent) are substrata.". -/
  def ps (kind := @entity.contingent ω) : Prop := □c.eps kind

  /-- The **Principle of Singleton Substratum**, as an event. 
      It states that the event of the world being
      exactly like it is is a substratum. -/
  def epss : ω.event := {w | c.substratum {w}}

  /-- The **Principle of Singleton Substratum**. 
      It states that the event of the world being
      exactly like it is is a substratum. -/
  def pss : Prop := □c.epss

  def caused (e : ω.event) : ω.event := {w | ∃ e', c.causes e' e w}
  def simcaused (e : ω.event) : ω.event := {w | ∃ e', c.simcauses e' e w}
  def is_cause (e : ω.event) : ω.event := {w | ∃ e', c.causes e e' w}
  def uncaused (e : ω.event) : ω.event := -c.caused e

  /-- An **Exact cause** is an event which causes everything that is consubstantial 
      to some entity in some possible world.
      The event is said to **exact** the entity because it is,
      in a sense, a fully qualified cause of the underlying substance being in the state
      it is in. -/
  def exacts (e : ω.event) (e₁ : ω.entity) : ω.event := 
    {w | ∀ e₂ : ω.entity, e₂ ≈ e₁ → e₂.exists w → c.causes e e₂ w}

  /-- **External cause**. -/
  def excauses (e : ω.event) (e₁ : ω.entity) : ω.event := 
    c.causes e e₁ ∩ {w | ¬ ∃ e₂ : ω.entity, e₂.exists = e ∧ e₁ ≈ e₂}

  def ppc₀ : Prop := ∀ (e : ω.event) (e₁ : ω.entity), c.simcauses e e₁ ⇒ c.excauses e e₁
  
  /-- **Strictly Existential cause**. -/
  def secauses (e : ω.event) (e₁ : ω.entity) : ω.event := 
    c.causes e e₁ ∩ {w | ¬ ∃ e₂ : ω.entity, e₂ ≠ e₁ ∧ e₁ ≈ e₂ ∧ c.causes e e₂ w}

  /-- **Existential cause**. -/ -- needs some work, appears trivial.
  def ecauses (e : ω.event) (e₁ : ω.entity) : ω.event := c.secauses e e₁ ∪ c.exacts e e₁

  def entitative : Prop := ∀ {e}, ⋄c.is_cause e → e.existential
  def effentitative : Prop := ∀ {e}, ⋄c.caused e → e.existential
  def substantive : Prop := ∀ {e}, ⋄c.is_cause e → e.substantive
  /-- **Causal Realism** is the intensional proposition which claims that whatever
      entity can cause real entities must itself be real. -/
  def realistic (Ω : ω.iontology) : Prop := ∀ (e₁ e₂ : ω.entity), e₂.real Ω → ⋄c.causes e₁ e₂ → e₁.real Ω
  
  def consubstantial : Prop := ∀ e (e₁ : ω.entity), c.causes e e₁ ⇒ c.exacts e e₁
  
  section conjunctive
    def conjunctive : Prop := ∀ e e₁ e₂, c.causes e (e₁ ∩ e₂) = c.causes e e₁ ∩ c.causes e e₂
    def conjunctive₁ : Prop := ∀ e e₁ e₂, c.causes e (e₁ ∩ e₂) ⇒ c.causes e e₁ ∩ c.causes e e₂
    def conjunctive₂ : Prop := ∀ e e₁ e₂, c.causes e e₁ ∩ c.causes e e₂ ⇒ c.causes e (e₁ ∩ e₂)

    def conjunctive' : Prop := 
      ∀ e e₁ e₂ : ω.event,
      e₁.contingent → e₂.contingent → c.causes e (e₁ ∩ e₂) = c.causes e e₁ ∩ c.causes e e₂
    def conjunctive₁' : Prop := 
      ∀ e e₁ e₂ : ω.event, 
      e₁.contingent → e₂.contingent → c.causes e (e₁ ∩ e₂) ⇒ c.causes e e₁ ∩ c.causes e e₂
    
    def conjunctive₂' : Prop := 
      ∀ e e₁ e₂ : ω.event, 
      e₁.contingent → e₂.contingent → c.causes e e₁ ∩ c.causes e e₂ ⇒ c.causes e (e₁ ∩ e₂)

    def conjunctive₁'' : Prop := 
      ∀ e e₁ e₂ : ω.event, e₁ ≢ e₂ → c.causes e (e₁ ∩ e₂) ⇒ c.causes e e₁ ∩ c.causes e e₂
    
    def econjunctive₁'' : Prop := 
      ∀ e e₁ e₂ : ω.event, e₁.entitative → e₁ ≢ e₂ → c.causes e (e₁ ∩ e₂) ⇒ c.causes e e₁
      
  
  end conjunctive

  def disjunctive : Prop := ∀ e e₁ e₂, c.causes e (e₁ ∪ e₂) = c.causes e e₁ ∪ c.causes e e₂
  def subadditive : Prop := ∀ e e₁ e₂, c.causes e (e₁ ∪ e₂) ⇒ c.causes e e₁ ∪ c.causes e e₂
  def superadditive : Prop := ∀ e e₁ e₂, c.causes e e₁ ∪ c.causes e e₂ ⇒ c.causes e (e₁ ∪ e₂)

  /-- Causal monotonicity -/
  def monotone : Prop := ∀ e e₁ e₂ : ω.event, e₁ ⇒ e₂ → c.causes e e₁ ⇒ c.causes e e₂

  /-- Contingent causal monotonicity -/
  def cmonotone : Prop := 
    ∀ e e₁ e₂ : ω.event, e₁.contingent → e₂.contingent → 
    e₁ ⇒ e₂ → c.causes e e₁ ⇒ c.causes e e₂
  
  def K : Prop := ∀ e e₁ e₂, c.causes e (e₁ ⟶ e₂) ⇒ ((c.causes e e₁) ⟶ c.causes e e₂)
  def axiom₄₀ : Prop := ∀ e₁ e₂, c.causes e₁ e₂ ⇒ c.causes e₁ (c.causes e₁ e₂)
  def axiom₄₁ : Prop := ∀ e, c.caused e ⇒ c.caused (c.caused e)
  def axiom₄₂ : Prop := ∀ e₁ e₂, c.causes e₁ e₂ = c.causes e₁ (c.caused e₂)
  lemma T : ∀ {e}, c.caused e ⇒ e := by
    rintros e w ⟨e₂, h⟩; exact c.axiom₀ ⟨e₂, h⟩

  @[simp]
  lemma caused_causes : ∀ {e₁ e₂}, c.causes e₁ e₂ ⇒ c.caused e₂ := 
    assume e₁ _ _ h, ⟨e₁,h⟩

  @[simp]
  lemma occured_causes : ∀ {e₁ e₂}, c.causes e₁ e₂ ⇒ e₂ := by
    intros e₁ e₂ w hw; apply c.T; apply c.caused_causes hw
  
  -- has some similarities to the Gale-Pruss argument
  lemma cause_all_of_cause_singleton : c.conjunctive₁' → ∀ {w e}, c.causes e {w} w →
                                       ∀ e' : ω.event, e'.contingent → e'.occurs w → c.causes e e' w
                                       := begin
    intros h₁ w e h₂ e' h₃ h₄,
    by_cases h₅ : ({w} : ω.event).contingent, swap,
      simp [nbe, ext_iff] at h₃,
      replace h₃ := h₃.2,
      obtain ⟨w', hw'⟩ := h₃,
      simp [nbe, ext_iff] at h₅,
      specialize h₅ w',
      rw h₅ at hw',
      contradiction,
    replace h₁ := h₁ e {w} e',
    suffices c₃ : {w} = {w} ∩ e',
      rw ←c₃ at h₁,
      specialize h₁ h₅ h₃ h₂,
      exact h₁.2,
    ext w', simp,
    refine ⟨λh, ⟨h,_⟩, and.left⟩,
    cases h,
    exact h₄,
  end


  /-- A substance **Freely causes** some event if it simultaneously causes it and it is possible
      for it to not have simultaneously caused it even while remaining in the same state and in
      the same context in which the causation took place. -/
  def fcauses (s : ω.substance) (e : ω.event) : ω.event := 
    { w | c.simcauses s e w ∧ ∀ (context : ω.event), 
      c.simcauses s e ⇒ context → c.simcauses s e ≠ context →
      ∃ w', w' ≠ w ∧ s.state w' = s.state w ∧ context.occurs w' ∧
      ¬c.simcauses s e w'
    }
  
  def has_will (s : ω.substance) : Prop := ∃ e, ⋄c.fcauses s e

  /-- The event of a substance `s` being **free** w.r.t. some 
      causal structure `c` is the set of all possible worlds `w` in which
      `s` exists and there is some possible event `e` which:
      1. It is possible that `s` can freely cause `e` from the state it is in at `w`.
      2. The existence of no entity can preclude `s` from freely causing `e` in `w`.
      3. No possible entity can be the cause that `s` does not freely cause `e` in `w`.
      -/
  def efree (s : ω.substance) : ω.event := 
    { w | s.exists w ∧ ∃ e, ⋄(c.fcauses s e ∩ s.equiv w) ∧
      w ∈ ✦(c.fcauses s e) ∧ ¬∃ e', c.causes e' (-(c.fcauses s e)) w
    }
  
  /-- A substance `s` is said to be **free** w.r.t. some 
      causal structure `c` if in any possible world `w` in which
      `s` exists there is always some possible event `e` which:
      1. It is possible that `s` can freely cause `e` from the state it is in at `w`.
      2. The existence of no entity can preclude `s` from freely causing `e` in `w`.
      3. No possible entity can be the cause that `s` does not freely cause `e` in `w`.
      -/
  def free (s : ω.substance) : Prop := s ⇒ c.efree s

  /-- The causal version of the **Principle of Sufficient Reason**, as an event. -/
  @[reducible, simp]
  def epsr (kind := @event.contingent ω) : ω.event := c.up.epsr kind
  /-- The causal version of the **Weak Principle of Sufficient Reason**, as an event. -/
  @[reducible, simp]
  def ewpsr (kind := @event.contingent ω) : ω.event := c.up.ewpsr kind

  /-- The causal version of the **Principle of Sufficient Reason**. -/
  def psr (kind := @event.contingent ω) : Prop := □c.epsr kind

  /-- The **Principle of Causality**, as an event. This is the `psr` restricted to entities. -/
  def epc (kind := @entity.contingent ω) : ω.event := 
    {w : ω.world | ∀ (e : ω.entity), kind e → e.exists w → c.caused e w}
  /-- The **Principle of Causality**. This is the `psr` restricted to entities. -/
  def pc (kind := @entity.contingent ω) : Prop := □c.epc kind


  theorem Gale_Pruss : c.conjunctive₁' → c.ewpsr ⇒ c.epsr :=
    begin
      intros h₀ w h₁,
      specialize h₁ {w}, simp [ext_iff] at h₁,
      by_cases hyp : ∃ w', w' ≠ w,
        obtain ⟨w', hw'⟩ := hyp,
        specialize h₁ w' hw', clear hw' w',
        obtain ⟨C, w', h⟩ := h₁,
        have c₁ := c.axiom₀ ⟨C, h⟩, 
        simp at c₁, cases c₁, clear c₁,
        have c₁ := c.cause_all_of_cause_singleton h₀ h,
        intros e he₁ he₂, use C, apply c₁; assumption,
      clear h₀ h₁,
      intros e he, exfalso,
      simp [entity.contingent, ext_iff] at he,
      obtain ⟨⟨w', hw'⟩, w'', hw''⟩ := he,
      push_neg at hyp,
      have c₁ := hyp w',
      have c₂ := hyp w'', 
      cases c₁, cases c₂, clear hyp c₁ c₂,
      contradiction,
    end


  /-- The **Platonic Principle** for events, as an event.
      This principle is a consequence of the doctrine
      of the impossibility of an infinite regress of 
      (*per se* ordered, simultaneous) causes. 
      It can be interpreted as a logically weaker form
      of stating essentially the same principle.
      It can be read as saying 
      "Everything (of some kind) that is caused is ultimately caused by something uncaused". -/
  def epp' (kind := λe:ω.event,true) : ω.event := 
    {w | ∀ e, kind e → c.caused e w → ∃ e', w ∈ c.uncaused e' ∩ c.causes e' e}
  /-- The **Platonic Principle** for events.
      This principle is a consequence of the doctrine
      of the impossibility of an infinite regress of 
      (*per se* ordered, simultaneous) causes. 
      It can be interpreted as a logically weaker form
      of stating essentially the same principle.
      It can be read as saying 
      "Everything (of some kind) that is caused is ultimately caused by something uncaused". -/
  def pp' (kind := λe:ω.event,true) : Prop := □c.epp' kind
  /-- The **Platonic Principle** (for entities), as an event.
      This principle is a consequence of the doctrine
      of the impossibility of an infinite regress of 
      (*per se* ordered, simultaneous) causes. 
      It can be interpreted as a logically weaker form
      of stating essentially the same principle.
      It can be read as saying 
      "Everything (of some kind) that is caused is ultimately caused by something uncaused". -/
  def epp (kind := λe:ω.entity,true) : ω.event := 
    {w | ∀ (e : ω.entity), kind e → c.caused e w → ∃ e', w ∈ c.uncaused e' ∩ c.causes e' e}
  /-- The **Platonic Principle** (for entities).
      This principle is a consequence of the doctrine
      of the impossibility of an infinite regress of 
      (*per se* ordered, simultaneous) causes. 
      It can be interpreted as a logically weaker form
      of stating essentially the same principle.
      It can be read as saying 
      "Everything (of some kind) that is caused is ultimately caused by something uncaused". -/
  def pp (kind := λe:ω.entity,true) : Prop := □c.epp kind

  /- **Fun fact:** the platonic principle is also a way to state the impossibility of an infinite
     regress in a way to make the classical arguments which depend on it tractable within the
     confines of Aristotelian logic. Aristotelian logic is not really equipped to discuss 
     the order-theoretical questions which arise in the discussion of regress problems.
     For instance, it appears to be impossible to derive Zorn's lemma from the axiom 
     of choice using only Aristotelian syllogisms. However, using the platonic principle,
     many arguments can be exposed using simple BARBARA syllogisms. 
     
     We do not necessarily mean to imply, however, that this principle is more or less evident
     than the impossibility of regress. If the impossibility of regress seems more evident than this
     principle to the reader, we can use that assumption to prove the principle rather than to assume
     this principle as a premisse in our arguments. However, the proof of this principle does depend
     on Zorn's lemma, which is equivalent to the axiom of choice.
     Indeed, this proof can be seen as a mere restatement of the lemma. 
  -/

  /-- An entity is a **First Cause** in some possible world `w` if it is the cause 
      of every other event occurring in `w` (except itself). -/
  def first_cause' (e : ω.entity) : ω.event := 
    {w | e.exists w ∧ ∀ e' : ω.event, e'.occurs w → e.exists ≠ e' → c.causes e e' w}

  /-- An entity is a **First Cause** in some possible world `w` if it is the cause 
      of every other entity existing in `w` (except itself). -/
  def first_cause (e : ω.entity) : ω.event := 
    {w | e.exists w ∧ ∀ e' ∈ w, e ≠ e' → c.causes e e' w}
  
  def omnipotent (e : ω.entity) : Prop := □c.first_cause e

  /-- **John Duns Scotus** was the first philosopher (we are aware of) to propose
      to join the ontological (i.e. modal) and cosmological arguments. 
      A proof of `c.dscotus` is a proof that it is possible that the
      necessary being is a `first_cause`. -/
  @[reducible, simp]
  def dscotus : Prop := ⋄c.first_cause ω.nbe

  /-- Any cosmological argument can have its premisses weakened by the ontological argument 
      so as to prove a `dscotus`.
      In other words, given any argument for the existence
      of a first cause, if the event
      of its premisses being (jointly) true can possibly occur,
      then it must be at least possible
      for there to be a first cause. -/
  theorem scotus_theorem : ∀ {argument : ω.event}, argument ⇒ c.first_cause ω.nbe → ⋄argument → c.dscotus :=
    by rintros arg h₁ ⟨w, hw⟩; use w; exact h₁ hw

  lemma first_cause_of_nocontingent : ∀ {w}, (¬∃ e : ω.entity, e.contingent ∧ e.exists w) → c.first_cause ω.nbe w :=
    begin
      intros w h,
      push_neg at h,
      simp [cause.first_cause, nbe],
      refine ⟨by simp [univ],_⟩,
      unfold_coes, simp,
      intros e h₃ h₄,
      replace h₄ := ne.symm h₄,
      specialize h e,
      simp [nbe, h₄] at h,
      contradiction,
    end
  
  lemma first_cause_of_parmenides : ∀ {w}, (∀ w', w' = w) → c.first_cause ω.nbe w :=
    begin
      intros w h,
      apply c.first_cause_of_nocontingent,
      rintro ⟨e, h₁, h₂⟩,
      suffices c : □e, contradiction,
      simp [nbe, ext_iff],
      intro w', specialize h w',
      rwa h,
    end

  /-- An event is said to be a **Contingent Substratum** if
      it is both `contingent` and a `substratum` (Duh).
      -/
  def csubstratum (e : ω.event) : Prop := e.contingent ∧ c.substratum e

  /-- **Kind Contingent Substrata** is the event of there being contingent substrata of 
      some specific kind in a possible world `w`.
      By default, the event simply claims that there are
      contingent substrata in `w`. -/
  def kcsubstrata (kind := λe:ω.event,true) : ω.event := 
    {w | ∃ su, kind su ∧ su.occurs w ∧ c.csubstratum su}

  /-- The **Principle of Contingent Substratum**, as an event.
      It reads: "If there are entities of some kind (contingent) then 
      there is an event (existential) 
      which is a Contingent Substratum 
      (maybe because it is a contingent material substratum of entities of *that* kind, 
      or something of the sort, or maybe for some other reason)". -/
  def epcs (kind₁ := @entity.contingent ω)  (kind₂ := @event.existential ω) : ω.event := 
    {w | (∃ e, kind₁ e ∧ e.exists w) → c.kcsubstrata kind₂ w}
  /-- The **Principle of Contingent Substratum**.
      It reads: "If there are entities of some kind (contingent) then 
      there is an event (existential) 
      which is a Contingent Substratum 
      (maybe because it is a contingent material substratum of entities of *that* kind, 
      or something of the sort, or maybe for some other reason)". -/
  def pcs (kind₁ := @entity.contingent ω)  (kind₂ := @event.existential ω) := □c.epcs kind₁ kind₂

  /-- The **Principle of Substratum Causality**, as an event. 
      It reads: "If there are contingent substrata of a 
      certain kind (existential), then any event which is the cause
      of all contingent substrata of that kind (other than the thing itself)
      is the cause of all events of that kind (other than the thing itself)."
      -/
  def epsc (kind := @event.existential ω) : ω.event := 
    {w | c.kcsubstrata kind w → ∀ e,
         (∀ su, c.csubstratum su → su ≠ e → kind su → su.occurs w → c.causes e su w) →
         (∀ su, su ≠ e → su.contingent → kind su → su.occurs w → c.causes e su w)
    }
  
  def ultimate_substratum (e : ω.event) : Prop := 
    c.csubstratum e ∧ ∀ e' : ω.entity, c.causes e' e ⇒ c.first_cause e'
  
  /- The **Beginning of Philosophy** is said to have occurred 
     When Thales of Miletus famously declared "All is Water".
     We say that the beginning of philosophy occurs at a possible world
     `w` just in case Thales was right at `w`
     (although "water" can be anything that you want it to be). -/
  def bphilosophy (water := λe:ω.event,true) : ω.event := 
    {w | ∃ u, water u ∧ u.occurs w ∧ c.ultimate_substratum u}

  -- Notice that by default water is "everything" (as per Thales),
  -- but then you can get more specific about what water is if you want.

  /-- The **Principle of Ultimate Substratum**, as an event.
      It reads: "If there are entities of some kind (contingent) then 
      there is an event (of some other kind, like water) 
      which is an Ultimate Substratum 
      (maybe because it is an ultimate material substratum of entities of *that* kind, 
      or something of the sort, or maybe for some other reason)". -/
  def epus (kind := @entity.contingent ω)  (water := λe:ω.event,true) : ω.event := 
    {w | (∃ e, kind e ∧ e.exists w) → c.bphilosophy water w}

  /-- The **Principle of Ultimate Substratum**.
      It reads: "If there are entities of some kind (contingent) then 
      there is an event (of some other kind, like water) 
      which is an Ultimate Substratum
      (maybe because it is an ultimate material substratum of entities of *that* kind, 
      or something of the sort, or maybe for some other reason)". -/
  def pus (kind := @entity.contingent ω)  (water := λe:ω.event,true) := □c.epus kind water

  /-- An event `e` is said to be **Causally Grounded** w.r.t. a causal structure `c`,
      and possible world `w`, if there is some event in `w` which may possibly cause `e` to occur. -/
  def cground (e : ω.event) : ω.event := {w | ∃ e' : ω.event, e'.occurs w ∧ ⋄c.causes e' e}

  /-- An **Aristotelian-Causal Account of Modality**, for events, is the set of all possible worlds 
      `w` in which for any given possible event `e`, it either occurs in `w` or some event
      in `w` can possibly cause `e` to occur. -/
  def acam' : ω.event := {w | ∀ e : ω.event, ⋄e → e.occurs w ∨ c.cground e w}
  -- Notice the converse of the (`→`) in the above definition is trivial.

  /-- A **Non-Negative Aristotelian-Causal Account of Modality**, for events, is the set of all possible worlds 
      `w` in which for any not purely negative event `e`, it either occurs in `w` or some event
      in `w` can possibly cause `e` to occur. -/
  def nnacam : ω.event := {w | ∀ e : ω.event, e.npnegative → e.occurs w ∨ c.cground e w}


  /-- An **Aristotelian-Causal Account of Modality** (for entities) is the set of all possible worlds 
      `w` in which for any given possible entity `e`, it either exists in `w` or some event
      in `w` can possibly cause `e` to exist. -/
  def acam : ω.event := {w | ∀ (e : ω.entity), e.exists w ∨ c.cground e w}
     
  /-- This is an extra auxiliary principle that is needed in Pruss's 
      "nature of modality" argument.
      It reads "If all but one world satisfies the `psr`
      and the one that is left is also Aristotelian-Causal, then this world also satisfies the `psr`."
      The "Aristotelian-Causal" part is a weakening of the original thesis. -/
  def prussian_principle₁ : Prop := ∀ (w : ω.world), c.acam' w → (∀ w', w' ≠ w → c.epsr.occurs w') → c.epsr.occurs w
  /-- This is an extra auxiliary principle that is needed in Pruss's 
      "nature of modality" argument.
      It reads "If some world `w` is Aristotelian-Causal, and all worlds containing an entity not in the `w` 
      satisfy the `pc`, then `w` also satisfies the `pc`."
      The "Aristotelian-Causal" part is a weakening of the original thesis,
      but this principle appears to be stronger than `prussian_principle₁`. -/
  def prussian_principle₂ : Prop := ∀ (w : ω.world), c.acam w → (∀ w', (∃ e ∈ w', e ∉ w) → c.epc.occurs w') → c.epc.occurs w
  
  /-- Independence principle needed in one interpretation of Pruss's argument. 
      It reads "No contingent event is necessarily impossible to cause, 
      and the mere fact there are no causes necessitating a contingent event's occurrence 
      does not necessitate this event's occurrence". 
      The second part of the conjunction is analytical. -/
  lemma prussian_independence : □c.acam' → ∀ e : ω.event, e.contingent → e ≢ c.uncaused e :=
    begin
      intros h e he, 
      simp only [incomparable_entailment, comparable_entailment], 
      simp [event.contingent, event.necessary, ext_iff] at he,
      obtain ⟨he, ⟨w, hw⟩⟩ := he,
      push_neg, constructor; intro absurd,
        simp [event.contingent, event.necessary, ext_iff, cause.acam'] at h,
        specialize h w e he, 
        simp [hw, cause.cground, set_of] at h,
        obtain ⟨C, h₁, ⟨w', hw'⟩⟩ := h,
        have c₀ := c.axiom₀ ⟨C, hw'⟩,
        specialize absurd c₀,
        simp [cause.uncaused, cause.caused] at absurd,
        specialize absurd C, contradiction,
      -- the second part doesn't need acam', 
      -- and is in fact analytical
      suffices c₀ : c.uncaused e w,
        specialize absurd c₀, contradiction, 
        clear absurd,
      simp [cause.uncaused, cause.caused, has_neg.neg, compl], 
      simp [set_of],
      intros C absurd, 
      replace absurd := c.axiom₀ ⟨C, absurd⟩,
      contradiction,
    end

  
  /-- The least Pruss has to assume, as an additional premise, to conclude the `psr` from 
      the necessity of `acam'`. -/
  def prussian_minimal_extra_assumption : Prop := 
    ∀ e C : ω.event, e.contingent → 
    c.causes C (e ∩ c.uncaused e) ⇒ c.causes C e

  theorem pruss_nature_of_modality_argument₀ : c.conjunctive₁'' → □c.acam' → c.psr :=
    begin
      intros conj h, simp [cause.psr, ext_iff, explanation.epsr], 
      have indep := c.prussian_independence h,
      intros w, by_contradiction contra,
      push_neg at contra,
      obtain ⟨E, h₁, w', h₂, ⟨h₃, h₄⟩⟩ := contra,
      let «E*» := c.uncaused E ∩ E,
      simp [cause.acam', ext_iff] at h,
      have c₀ : w ∈ «E*»,
        refine ⟨_, h₃⟩,
        simpa [cause.uncaused, cause.caused],
      specialize h w' «E*» ⟨w, c₀⟩,
      simp [h₂, cause.cground, set_of] at h,
      obtain ⟨C, h₅, ⟨w'', h₆⟩⟩ := h,
      simp [«E*»] at h₆,
      specialize conj C E (c.uncaused E) _, swap,
        apply (indep E), 
        simp [event.contingent, event.necessary, ext_iff],
        exact ⟨⟨w, h₃⟩,⟨w', h₂⟩⟩,
      simp only [inter_comm] at h₆,
      specialize conj h₆, clear h₆,
      obtain ⟨h₆, h₇⟩ := conj,
      replace h₇ := c.axiom₀ ⟨C, h₇⟩,
      simp [cause.uncaused, cause.caused] at h₇,
      specialize h₇ C,
      contradiction,
    end

  theorem pruss_nature_of_modality_argument₀' : c.prussian_minimal_extra_assumption → □c.acam' → c.psr :=
    begin
      intros min h, simp [cause.psr, ext_iff, explanation.epsr], 
      intros w, by_contradiction contra,
      push_neg at contra,
      obtain ⟨E, h₁, w', h₂, ⟨h₃, h₄⟩⟩ := contra,
      let «E*» := c.uncaused E ∩ E,
      simp [cause.acam', ext_iff] at h,
      have c₀ : w ∈ «E*»,
        refine ⟨_, h₃⟩,
        simpa [cause.uncaused, cause.caused],
      specialize h w' «E*» ⟨w, c₀⟩,
      simp [h₂, cause.cground, set_of] at h,
      obtain ⟨C, h₅, ⟨w'', h₆⟩⟩ := h,
      simp [«E*»] at h₆,
      specialize min E C _, swap,
        simp [event.contingent, event.necessary, ext_iff],
        exact ⟨⟨w, h₃⟩,⟨w', h₂⟩⟩,
      simp only [inter_comm] at h₆,
      specialize min h₆, 
      replace h₆ := c.axiom₀ ⟨C, h₆⟩,
      simp [cause.uncaused, cause.caused] at h₆,
      replace h₆ := h₆.2 C,
      contradiction,
    end  

  theorem pruss_nature_of_modality_argument₁ : c.conjunctive₁'' → 
    c.prussian_minimal_extra_assumption → c.prussian_principle₁ 
    → ⋄c.acam' → c.psr :=
    begin
      intros conj min pruss h,
      obtain ⟨actual_world, ha⟩ := h,
      suffices c₀ : ∀ w', w' ≠ actual_world → c.epsr.occurs w',
        have c₁ := pruss actual_world ha c₀,
        simp [cause.psr, ext_iff], intro w,
        by_cases h : w = actual_world,
          rw h, exact c₁,
        exact c₀ w h,
        clear pruss,
      intros w hw,
      by_contradiction contra,
      simp [cause.epsr, explanation.epsr, ext_iff] at contra,
      obtain ⟨E, h₀, h₁, h₂, h₃⟩ := contra,
      by_cases h : E.occurs actual_world,
        let nonactuality : ω.event := -{actual_world},
        let F := E ∩ nonactuality,
        let «F*» := F ∩ c.uncaused F,
        have c₀ : w ∈ F,
          refine ⟨h₂, _⟩,
          simp [nonactuality, hw],
        have c₁ : E ≢ nonactuality,
          simp only [incomparable_entailment, comparable_entailment], 
          push_neg, constructor; intro absurd,
            specialize absurd h,
            simp [nonactuality] at absurd,
            contradiction,
          obtain ⟨world, hworld⟩ := h₁,
          by_cases aux : world = actual_world,
            cases aux, contradiction,
          have : world ∈ nonactuality,
            simp [nonactuality, aux],
          specialize absurd this,
          contradiction,
        have c₂ : ∀ (C : ω.event), ¬c.causes C F w,
          intros C absurd,
          have c' := conj C E nonactuality c₁ absurd,
          replace c' := c'.1,
          specialize h₃ C,
          contradiction,
        have c₃ : ⋄«F*»,
          refine ⟨w, c₀, _⟩,
          simpa [cause.uncaused, cause.caused],
        have c₄ : actual_world ∉ «F*»,
          intro absurd, simp [«F*», F] at absurd,
          contradiction,
        clear c₁ c₂,
        simp [cause.acam'] at ha,
        specialize ha «F*» c₃, clear c₃,
        simp [c₄, cause.cground, set_of] at ha, clear c₄,
        obtain ⟨C, actual_C, w', hw'⟩ := ha,
        specialize min F C _, swap,
          simp [event.contingent, event.necessary, ext_iff],
          refine ⟨⟨w, c₀⟩, actual_world, _⟩, simp [h],
        specialize min hw',
        replace hw' := c.axiom₀ ⟨C, hw'⟩,
        replace hw' := hw'.2,
        simp [cause.uncaused, cause.caused] at hw',
        specialize hw' C, contradiction,
      -- second case
      let «F*» := E ∩ c.uncaused E,
      have c₃ : ⋄«F*»,
          refine ⟨w, h₂, _⟩,
          simpa [cause.uncaused, cause.caused],
      have c₄ : actual_world ∉ «F*»,
        intro absurd, simp [«F*»] at absurd,
        replace absurd := absurd.1, 
        contradiction,
      simp [cause.acam'] at ha,
      specialize ha «F*» c₃, clear c₃,
      simp [c₄, cause.cground, set_of] at ha, clear c₄,
      cases ha, replace ha := ha.1,
        contradiction,
      obtain ⟨C, actual_C, w', hw'⟩ := ha,
      specialize min E C _, swap,
        simp [event.contingent, event.necessary, ext_iff],
        exact ⟨⟨w, h₂⟩, actual_world, h⟩,
      specialize min hw',
      replace hw' := c.axiom₀ ⟨C, hw'⟩,
      replace hw' := hw'.2,
      simp [cause.uncaused, cause.caused] at hw',
      specialize hw' C, contradiction,
    end

  
  theorem pruss_nature_of_modality_argument₁' : c.conjunctive₁' → c.prussian_principle₁ → ⋄c.acam' → c.psr :=
    begin
      intros conj pruss h,
      obtain ⟨actual_world, ha⟩ := h,
      suffices c₀ : ∀ w', w' ≠ actual_world → c.epsr.occurs w',
        have c₁ := pruss actual_world ha c₀,
        simp [cause.psr, ext_iff], intro w,
        by_cases h : w = actual_world,
          rw h, exact c₁,
        exact c₀ w h,
      intros w hw,
      simp [explanation.epsr],
      intros e pe ce he, clear pe,
      have c₁ : ¬c.epsr.occurs w → ∃ F : ω.event, ⋄F ∧ ¬F.occurs actual_world ∧ ¬⋄c.cground F,
          intro brute,
          symmetry' at hw,
          use {w}, simp [hw, set.nonempty],
          by_contradiction contra,
          push_neg at contra,
          obtain ⟨w', ⟨e',he', h'⟩⟩ := contra,
          obtain ⟨w'', hw''⟩ := h',
          have c₁ := c.occured_causes hw'',
          simp at c₁,
          rw c₁ at hw'', clear c₁ w'', rename hw'' c₁,
          simp [cause.epsr, explanation.epsr] at brute,
          obtain ⟨ev, h₁, ⟨h₂, h₃,h₄⟩⟩ := brute,
          specialize h₄ e',
          replace c₁ := c.cause_all_of_cause_singleton conj c₁,
          specialize c₁ ev ⟨h₁,h₂⟩ h₃,
          contradiction,
      by_cases h : c.epsr.occurs w,
        simp [cause.epsr, explanation.epsr] at h,
        specialize h e (nonempty_of_mem he) ce he,
        exact h,
      replace c₁ := c₁ h,
      obtain ⟨F, pF, naF, hF⟩ := c₁,
      simp [cause.acam'] at ha,
      specialize ha F pF,
      simp at naF, simp [naF] at ha,
      simp [set.nonempty] at hF,
      specialize hF actual_world,
      contradiction,
    end


  -- This section is named after my friend Miguel Luis, which suggested an objection to Pruss's argument to me.
  section miguels_objection

    /-- Independence principle needed in one interpretation of the cold flame argument. 
        It reads "No contingent *not purely negative* event is necessarily impossible to cause, 
        and the mere fact there are no causes necessitating a contingent event's occurrence 
        does not necessitate this event's occurrence". 
        The second part of the conjunction is analytical. -/
    lemma miguels_independence : □c.nnacam → ∀ e : ω.event, e.contingent → e.npnegative → e ≢ c.uncaused e :=
      begin
        intros h e he miguel, 
        simp only [incomparable_entailment, comparable_entailment], 
        simp [event.contingent, event.necessary, ext_iff] at he,
        obtain ⟨he, ⟨w, hw⟩⟩ := he,
        push_neg, constructor; intro absurd,
          simp [event.contingent, event.necessary, ext_iff, cause.nnacam] at h,
          specialize h w e miguel,
          simp [hw, cause.cground, set_of] at h,
          obtain ⟨C, h₁, ⟨w', hw'⟩⟩ := h,
          have c₀ := c.axiom₀ ⟨C, hw'⟩,
          specialize absurd c₀,
          simp [cause.uncaused, cause.caused] at absurd,
          specialize absurd C, contradiction,
        -- the second part doesn't need nnacam, 
        -- and is in fact analytical
        suffices c₀ : c.uncaused e w,
          specialize absurd c₀, contradiction, 
          clear absurd,
        simp [cause.uncaused, cause.caused, has_neg.neg, compl], 
        simp [set_of],
        intros C absurd, 
        replace absurd := c.axiom₀ ⟨C, absurd⟩,
        contradiction,
      end


    /-- The **Principle of Non-Negative Uncaused Existence** claims
        that the uncaused existence of any entity is not a purely negative event. -/
    def pnnue : Prop := ∀ (e : ω.entity), (↑e ∩ c.uncaused e).npnegative

    /-- This is a weaker version of Pruss's argument restricted to non-purely-negative states of affairs, concluding the pc.
        It indeed appears possible to conclude here something stronger than the `pc`, namely a `psr` restricted
        to non-purely-negative events. --/
    theorem cold_flame_argument : c.econjunctive₁'' → c.pnnue → □c.nnacam → c.pc :=
      begin
          intros conj pnnue h, simp [cause.pc, cause.epc, ext_iff, nbe], 
          have indep := c.miguels_independence h,
          intros w, by_contradiction contra,
          push_neg at contra,
          obtain ⟨E, w', h₂, ⟨h₃, h₄⟩⟩ := contra,
          let «E*» := ↑E ∩ (c.uncaused E),
          simp [cause.nnacam, ext_iff] at h,
          have c₀ : «E*».npnegative, 
            simp [«E*»],
            exact pnnue E,
          specialize h w' «E*» c₀,
          cases h, replace h := h.1, contradiction,
          simp [cause.cground, set_of] at h,
          obtain ⟨C, h₅, ⟨w'', h₆⟩⟩ := h,
          simp [«E*»] at h₆,
          specialize conj C E (c.uncaused E) E.entitative _, swap,
            apply (indep E), 
            simp [event.contingent, event.necessary, ext_iff],
            exact ⟨⟨w, h₃⟩,⟨w', h₂⟩⟩,
              by_contradiction contra,
              push_neg at contra,
              apply contra.2,
              exact ⟨E.existential, contra.1⟩,
          specialize conj h₆, 
          replace h₆ := c.axiom₀ ⟨C, h₆⟩,
          simp [cause.uncaused, cause.caused] at h₆,
          replace h₆ := h₆.2,
          specialize h₆ C,
          contradiction,
        end

    /-! The idea behind the name of this argument is that if we reject the `psr` for negative events,
        we could still endorse `nnacam` instead of `acam'`, since it looks like something such as a cold flame,
        i.e. a flame devoid of heat, is not a purely negative event (if possible), and hence should be 
        require to be causable, or actual, in order to be possible. Even if it is insisted that 
        the absence of heat is a negative event which, as such, is not caused, 
        via `econjunctive₁''` at least the flame as such should be caused, from the fact 
        the cold flame as a whole is caused; the flame is both caused and devoid of heat.
        If the principle of causality is false, then generalizing this idea 
        from a cold flame to an uncaused flame, we obtain,
        by the same logic, a caused flame devoid of cause, which is absurd. -/



  end miguels_objection
end cause

-- ALL FOLLOWING SECTIONS ARE VERY MUCH A WORK IN PROGRESS.

section counterfactuals

  variable (ω)

  /- A **Counterfactual Theory of (Hierarchical) Causality** is one which, beginning from
      a theory of counterfactuals, defines hierarchical causality as "If `e₂` is removed, then `e₁` is removed",
      i.e. there is strong counterfactual dependence between `e₁` and `e₂`. -/
  -- def ctc (c : ω.cfr := default ω.cfr) : ω.cause := begin
  --   refine ⟨⟨c.sdepends, _, _⟩, _⟩,
  --    intros,
  --    simp [cfr.sdepends, cfr.depends],
  --    unfold_coes,
  -- end
  
  -- TODO: Another interpretation of "If `e₁` is removed, then `e₂` is removed" 
  -- could be given in terms of `entity.removed` for a causal relation in which
  -- only entities were involved in causation.

end counterfactuals

section four_causes
  -- variable {ω}
  
  structure cause.mcause (c : ω.cause) : Prop :=
    (axiom₀ : c.substantive)
    (axiom₁ : c.consubstantial)
    (axiom₂ : c.effentitative)
    (axiom₃ : c.simultaneous)
    (axiom₄ : ¬∃ s, c.has_will s)
    (axiom₅ : ∀ (e : ω.entity), ⋄c.is_cause e → e.composite)
    (axiom₆ : ∀ (s : ω.substance), ⋄c.caused s → s.composite)
    (axiom₇ : c.conjunctive₂')
    (axiom₈ : c.pp)
    (axiom₉ : ∀ (s₁ s₂ : ω.substance) w, c.causes s₁ s₂ w → s₂.equiv w ≤ s₁.equiv w)
    (axiom₁₀ : ∀ s₁ s₂ : ω.substance, ⋄(-c.causes s₁ s₂ ∩ s₁ ∩ s₂))

  def cause.uhylemorphism (c : ω.cause) : ω.event := { w | c.mcause ∧ c.epc (λe, e.perfect ∧ e.contingent) w}

  variables {c : ω.cause}
  
  def cause.mcause.atom (mc : c.mcause) (s : ω.substance) := ⋄c.is_cause s ∧ ¬⋄c.caused s
  def cause.mcause.immaterial (mc : c.mcause) (e : ω.entity) := e.exists ∩ c.uncaused e
  
  /-- **Principle of Immaterial Substratum** -/
  def cause.mcause.pis (mc : c.mcause) (ec : ω.cause) : ω.event := 
    {w | ∀ (e : ω.entity), mc.immaterial e w → ec.substratum e}
  
  def cause.mcause.base (ec : c.mcause) (s : ω.substance) : ω.event := 
    {w | ∀ e, c.caused e w → c.causes s e w}

  
  structure cause.mcause.ecompatible (mc : c.mcause) (ec : ω.cause) : Prop :=
    (axiom₁ : ∀ (s : ω.substance), ⋄c.is_cause s → ¬ec.has_will s)
    (axiom₂ : □ mc.pis ec)
    
  class cause.effcause (c : ω.cause) : Prop :=
    (axiom₀ : c.substantive)
    (axiom₁ : c.conjunctive₁'')
    -- (axiom₂ : c.pp' (λe, c.substratum e))
    -- (axiom₃ : c.psr)
    (axiom₄ : □c.acam')
    

  -- def ecause.aristotelian : Prop := 
    

  --   variables (s : ω.substance) (e : ω.entity)

  --   -- integral parthood
  --   def substance.part_of (s₁ s₂ : ω.substance) : ω.event := sorry

  --   -- efficient vertical causation
  --   def substance.ecauses : ω.event := 
  --     s.causes e.exists ∩
  --     -s.part_of e.substance ∩
  --     -e.substance.part_of s


  --   -- compositional causation (we say s "compositionally causes" e)
  --   def substance.ccauses : ω.event := 
  --     s.causes e.exists ∩
  --     s.part_of e.substance ∩
  --     -e.substance.part_of s

  --   -- formal causation
  --   def substance.forcauses : ω.event := 
  --     s.ccauses e ∩
  --     s.causes e.substance.exists

  --   -- material causation
  --   def substance.mcauses : ω.event := 
  --     s.ccauses e ∩
  --     -s.causes e.substance.exists

  --   -- final causation
  --   def substance.fincauses : ω.event := 
  --     s.causes e.exists ∩
  --     -s.part_of e.substance ∩
  --     e.substance.part_of s

end four_causes

section principles

  variable (ω)

  -- -- the thomistic principle of sufficent reason/causality
  -- def tpsr : Prop := 
  --   ∀ (s : ω.substance) (p : ω.predicate) (h₁ : p.proper) (h₂ : ¬ p.dere_of s.up) (w ∈ p s.up), 
  --   ∃ c : ω.substance, c.causes (p s.up) w

  -- -- the efficient version of tpsr
  -- -- the thomistic principle of sufficent reason/causality
  -- def etpsr : Prop := 
  --   ∀ (s : ω.substance) (p : ω.predicate) (h₁ : p.proper) (h₂ : ¬ p.dere_of s.up) (w ∈ p s.up),
  --   -- p s.up cast to an entity
  --   let r := (entity.mk (p s.up) 
  --           (by apply h₁.axiom₂; exact e) 
  --           (by use w; assumption))
  --   in ∃ c : ω.substance, c.ecauses r w

end principles

section time

  variables {ω} (c : ω.cause)

  structure event.factor (e : ω.event) :=
    (begins : ω.event)
    (continues : ω.event)
    (disjoint : begins ∩ continues = ∅)
    (factor : begins ∪ continues = e)
    (nontrivial₁ : ⋄begins)
    (nontrivial₂ : ⋄continues)

  def cause.dircauses (e₁ : ω.event) {e₂ : ω.event} (f : e₂.factor) := c.simcauses e₁ f.begins

  def event.factor.direct {e₂ : ω.event} (f : e₂.factor) (c : ω.cause) := c.substratum f.begins

  def cause.indcauses (e₁ : ω.event) {e₂ : ω.event} (f : e₂.factor) := 
    (c.causes e₁ f.begins) ∩ -(c.simcauses e₁ f.begins)

  def cause.sindcauses (e₁ : ω.event) {e₂ : ω.event} (f : e₂.factor) := 
    { w | c.causes e₁ f.continues w ∧ ¬ c.simcauses e₁ f.continues w ∧ ⋄c.indcauses e₁ f }

  def cause.wnoninertial (c : ω.cause) {e : ω.event} (f : e.factor) : Prop := c.substratum f.continues

  def cause.noninertial (c : ω.cause) {e : ω.event} (f : e.factor) : Prop := 
    c.substratum f.continues ∧ f.continues ⇒ c.caused f.continues

  def cause.inertial (c : ω.cause) {e : ω.event} (f : e.factor) : Prop := ¬ c.noninertial f

  structure cause.tfactor (c : ω.cause) {e : ω.event} (f : e.factor) : Prop:=
    (axiom₁ : ∀ ca, f.begins ⇒ c.causes ca f.begins ⟷ c.causes ca e)
    (axiom₂ : ∀ ca, f.continues ⇒ c.causes ca f.continues ⟷ c.causes ca e)

  def cause.pind₁ {e : ω.event} (f : e.factor) : Prop := 
    c.tfactor f ∧
    ∀ (ca : ω.event), c.causes ca e ∩ -ca ⇒ c.sindcauses ca f ∪ c.indcauses ca f

  -- def cause.pind₂ : Prop := 

  def cause.pcem (c : ω.cause) {c' : ω.cause} (mc : c'.mcause) : ω.event :=
    {w | ∀ e : ω.entity, c'.caused e w → ∃ f : e.exists.factor, c.tfactor f ∧ f.direct c ∧
      ∀ ca mca, c.causes ca f.continues ⇒ c'.causes mca e ⟶ c.causes ca mca
    }

  /-- An event is said to be **Weakly Directly Non-Inertially Temporally Factorizable**
      if it admits a direct weakly non-inertial temporal factorization (Duh). -/
  def cause.wdnitf (c : ω.cause) (e : ω.event) := ∃ f : e.factor, f.direct c ∧ c.tfactor f ∧ c.wnoninertial f

  /-- An event is said to be **Directly Non-Inertially Temporally Factorizable**
      if it admits a direct non-inertial temporal factorization (Duh). -/
  def cause.dnitf (c : ω.cause) (e : ω.event) := ∃ f : e.factor, f.direct c ∧ c.tfactor f ∧ c.noninertial f

  /-- An event is said to be **Directly Temporally Factorizable**
      if it admits a direct temporal factorization (Duh). -/
  def cause.dtf (c : ω.cause) (e : ω.event) := ∃ f : e.factor, f.direct c ∧ c.tfactor f

  def cause.direct' : ω.event :=
    {w | ∀ e : ω.event, e.occurs w → c.dtf e}

  def cause.direct : ω.event :=
    {w | ∀ e : ω.entity, e.exists w → c.dtf e}

  def cause.nidirect : ω.event :=
    {w | ∀ e : ω.entity, e.exists w → c.dnitf e}

  def cause.wdnidirect : ω.event :=
    {w | ∀ e : ω.entity, e.exists w → c.wdnitf e}


  -- lemma wdnitf_lemma : c.ps (λe, c.wnitf e) :=
  --   begin

  --   end

  -- lemma quasi_simultaneity_of_wnidirect : □c.wdnidirect → c.ps univ :=
  --   begin
  --     intro h,
  --     simp [ext_iff] at h,
  --     simp [cause.ps, ext_iff, cause.eps],
  --     intros w₁ e₁ aux h₁ e₂ w₂ h₂,
  --     clear aux h₁ w₁,
  --     have c₀ := c.occured_causes h₂,
  --     specialize h w₂ e₁ c₀,
  --     obtain ⟨f, hf₁, hf₂⟩ := h,
  --     unfold_coes at h₂,
  --     by_cases h : f.begins w₂,
  --       have c := hf₁.axiom₂ e₂ h,
  --       replace c := c.2,
  --       unfold_coes at c,
  --       simp [h₂] at c,
  --       replace c := hf₁.axiom₁ e₂ c,
  --       exact c,
  --     rw ←f.factor at c₀,
  --     simp at c₀,
  --     cases c₀, contradiction,
  --     clear h,
  --     replace c₀ := hf₁.axiom₃ e₂ c₀,
  --     replace c₀ := c₀.2,
  --     unfold_coes at c₀,
  --     simp [h₂] at c₀,
  --     replace hf₂ := hf₂ e₂ c₀,
  --     exact hf₂,
  --   end

end time

end ontology