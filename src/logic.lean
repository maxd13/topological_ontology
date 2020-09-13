import order.complete_boolean_algebra tactic
universe u

noncomputable theory
local attribute [instance] classical.prop_decidable

namespace logic
open set tactic classical

section signature

-- The type of signatures, which defines a first-order language with modalities.
-- It has room for defining your
-- own preferred variable type.
@[derive inhabited]
structure signature : Type (u+1) :=
    (modality : Type u := pempty)
    (arity : modality → ℕ := λ_, 0)
    (functional_symbol : set modality := ∅)
    (relational_symbol : set modality := ∅)
    (logical_symbol : set modality := ∅)
    (necessary_symbol : set modality := ∅)
    (essential_symbol : set modality := ∅)

variable (σ : signature)

-- the type of functional symbols of arity n
def signature.nary (σ : signature) (n : ℕ) := subtype {f : σ.functional_symbol | σ.arity f = n}

-- the type of relational symbols of arity n
def signature.nrary (σ : signature) (n : ℕ) := subtype {r : σ.relational_symbol | σ.arity r = n}

-- the type of modal symbols of arity n
def signature.nmary (n : ℕ) := subtype {r : σ.modality | σ.arity r = n}

-- the predicate defining, and the type of, constants
def is_constant (f : σ.functional_symbol) := σ.arity f = 0
def signature.const (σ : signature) := σ.nary 0

-- the type of formulas in the language
inductive signature.formula 
| var : ℕ → signature.formula
| mod   {n : ℕ} (box : σ.nmary n) (v : fin n → signature.formula) :  signature.formula
| all  :  ℕ →  signature.formula →  signature.formula
| if_then  :  signature.formula →  signature.formula →  signature.formula
| equation : signature.formula →  signature.formula →  signature.formula
| false    :  signature.formula

instance inh_formula : inhabited σ.formula := ⟨formula.var (default ℕ)⟩
-- @[reducible, simp]
instance nat_coe_formula : has_coe ℕ σ.formula := ⟨formula.var⟩


-- modalities interpretation
structure signature.structure (σ : signature) (ω : Type u) := 
    (I : Π {n}, σ.nmary n → (fin n → set ω) → set ω)
    (ne : nonempty ω)

-- variable interpretation/assignment
def vasgn (ω : Type u) := ℕ → set ω

end signature

section notations

 variable {σ : signature}

 -- a convenient notation to set up for if_then
 reserve infixr ` ⇒ `:55
 class has_if_then (α : Type u) := (exp : α → α → α)
 infixr ⇒ := has_if_then.exp

 -- a convenient notation to set up for iff
 reserve infixr ` ⇔ `:55
 class has_iff (α : Type u) := (exp : α → α → α)
 infixr ⇔ := has_iff.exp

 -- a convenient notation to set up for equality (which is semantically different from iff)
 reserve infixr ` ≡ `:60
 class has_eq (α : Type u) := (eq : α → α → α)
 infixr ≡ := has_eq.eq

 -- a convenient notation to set up for inequality
 reserve infixr ` ≢ `:60
 class has_neq (α : Type u) := (neq : α → α → α)
 infixr ≢ := has_neq.neq
 
 instance signature.formula.has_if_then : has_if_then  σ.formula := ⟨signature.formula.if_then⟩
 instance signature.formula.has_eq : has_eq σ.formula := ⟨signature.formula.equation⟩

 -- definition of connectives
 @[reducible, simp]
 def signature.formula.not (φ :  σ.formula)   := φ ⇒ formula.false
 @[reducible, simp]
 def signature.formula.or  (φ ψ :  σ.formula) := φ.not ⇒ ψ
 @[reducible, simp]
 def signature.formula.and (φ ψ :  σ.formula) := (φ.not.or ψ.not).not
 @[reducible, simp]
 def signature.formula.iff (φ ψ :  σ.formula) := (φ ⇒ ψ).and (ψ ⇒ φ)
 @[reducible, simp]
 def signature.formula.neq (φ ψ :  σ.formula) := (φ ≡ ψ).not
 @[reducible, simp]
 def signature.formula.exists (φ : σ.formula) (x : ℕ) := (formula.all x φ.not).not
 @[reducible, simp]
 def signature.formula.strictly_below (φ ψ :  σ.formula) := (φ ⇒ ψ).and (φ.neq ψ)

 instance signature.formula.has_neg : has_neg σ.formula := ⟨signature.formula.not⟩
 instance signature.formula.has_sup : has_sup σ.formula := ⟨signature.formula.or⟩
 instance signature.formula.has_inf : has_inf σ.formula := ⟨signature.formula.and⟩
 instance signature.formula.has_iff : has_iff  σ.formula := ⟨signature.formula.iff⟩
 instance signature.formula.has_neq : has_neq σ.formula := ⟨signature.formula.neq⟩
 instance signature.formula.has_bot : has_bot σ.formula := ⟨signature.formula.false⟩
 instance signature.formula.has_top : has_top σ.formula := ⟨⊥ ⇒ ⊥⟩

 infixr `⇒'`:55 := signature.formula.strictly_below

 @[reducible, simp]
 def signature.formula.necessary (φ : σ.formula) : σ.formula := φ ≡ ⊤
 @[reducible, simp]
 def signature.formula.possible (φ : σ.formula) : σ.formula := φ.not.necessary.not
 @[reducible, simp]
 def signature.formula.entails (φ ψ : σ.formula) : σ.formula := (φ ⇒ ψ).necessary
 @[reducible, simp]
 def signature.formula.strictly_entails (φ ψ : σ.formula) : σ.formula := (φ ⇒ ψ).necessary ⊓ φ ≢ ψ

 -- a convenient notation to set up for necessity
 reserve prefix ` □ `:100
 class has_box (α : Type u) := (box : α → α)
 prefix □ := has_box.box

 -- a convenient notation to set up for possibility
 reserve prefix ` ⋄ `:100
 class has_diamond (α : Type u) := (diamond : α → α)
 prefix ⋄ := has_diamond.diamond

 -- a convenient notation to set up for entailment
 reserve infix ` ⟹ `:55
 class has_ent (α : Type u) := (ent : α → α → α)
 infix ⟹ := has_ent.ent

 instance signature.formula.has_box : has_box σ.formula := ⟨signature.formula.necessary⟩
 instance signature.formula.has_diamond : has_diamond σ.formula := ⟨signature.formula.possible⟩
 instance signature.formula.has_ent : has_ent σ.formula := ⟨signature.formula.entails⟩

 infixr `⟹'`:55 := signature.formula.strictly_entails

 end notations

variables {σ : signature} {ω : Type u}

-- bind the value of a variable to `S` in an assignment 
-- (generates a new assignment).
def vasgn.bind (asg : vasgn ω) (x : ℕ) (S : set ω) : vasgn ω :=
    λy, if y = x then S else asg y


def signature.structure.ref' (M : σ.structure ω) : σ.formula → vasgn ω → set ω
| (formula.var x) asg := asg x
| (@formula.mod _ 0 box v) asg := M.I box fin_zero_elim
| (@formula.mod _ (n+1) box v) asg := M.I box (λ k, signature.structure.ref' (v k) asg)
| (formula.all x φ) asg := ⋂ S : set ω, signature.structure.ref' φ (asg.bind x S)
| (formula.if_then φ ψ) asg := -(signature.structure.ref' φ asg) ∪ (signature.structure.ref' ψ asg)
| (formula.equation φ ψ) asg := if (signature.structure.ref' φ asg) = (signature.structure.ref' ψ asg) 
                                then univ 
                                else ∅
| formula.false _ := ∅

@[simp]
def signature.structure.satisfies' (M : σ.structure ω) : ω → σ.formula → vasgn ω → Prop
| w φ asg := w ∈ (M.ref' φ asg)

@[simp]
def signature.structure.satisfies (M : σ.structure ω) : ω → σ.formula → Prop
| w φ := ∀ asg, M.satisfies' w φ asg

@[simp]
def signature.structure.valid' (M : σ.structure ω) : σ.formula → vasgn ω → Prop
| φ asg := ∀ w, M.satisfies' w φ asg

@[simp]
def signature.structure.possible' (M : σ.structure ω) : σ.formula → vasgn ω → Prop
| φ asg := ∃ w, M.satisfies' w φ asg

@[simp]
def signature.structure.valid (M : σ.structure ω) : σ.formula → Prop
| φ := ∀ w, M.satisfies w φ

@[simp]
def tautology (φ : σ.formula) : Prop := 
    ∀ {ω : Type u} (M : σ.structure ω), M.valid φ

@[simp]
def logical (φ : σ.formula) : Prop :=
    ∀ {ω : Type u} (M : σ.structure ω) asg, M.valid' φ asg ∨ M.valid' (-φ) asg

-- TODO: specify a free variable for quantification
def signature.formula.isPworld (φ : σ.formula) : σ.formula := 
    formula.all 0 $
    (↑0 ⟹' φ) ⟹ ↑0 ≡ ⊥

variables {M : σ.structure ω} (φ ψ: σ.formula) (asg : vasgn ω)

-- lemma logical_pworld : logical φ.isPworld :=
--     begin
--         dunfold logical,
--         intros,
--         let r := M.ref' φ asg,
--         let r_singleton := ∃ w, {w} = r,
--         by_cases r_singleton,
--             left,
--             dunfold signature.structure.valid',
--             dunfold signature.structure.satisfies',
--             obtain ⟨w, h⟩ := h,
--             intro w',

--             dunfold signature.formula.isPworld,
--             dunfold signature.structure.ref',
--             simp,
--             intros,
--             simp [ signature.structure.ref'
--                  , coe
--                  , lift_t
--                  , has_lift_t.lift
--                  , coe_t
--                  , has_coe_t.coe
--                  , coe_b
--                  , has_neg.neg
--                  , vasgn.bind
--                  ],
--             by_cases c₀ : i = ∅, 
--                 simp [c₀],
--                 set r₂ := signature.structure.ref' M φ (λ (y : ℕ), ite (y = 0) ∅ (asg y)),
--                 have c₁ : (M.ref' (has_coe.coe 0) (λ (y : ℕ), ite (y = 0) ∅ (asg y))) = ∅ := sorry,
--                 simp [c₁],
--                 by_cases c₂ : ∅ = r₂; simp [c₂],
--             have c₁ : (M.ref' (has_coe.coe 0) (λ (y : ℕ), ite (y = 0) i (asg y))) = i := sorry,
--             set r₂ := signature.structure.ref' M φ (λ (y : ℕ), ite (y = 0) i (asg y)),
--             simp [c₁, c₀],
--             by_cases c₃ : compl i ∪ r₂ = univ; 
--             simp [c₃],
--                 admit,

--     end

            -- dunfold signature.structure.ref',
            -- simp,
            -- by_cases c₀ : i = ∅,
            --     right,
            --     simp [c₀],
            -- left,
            -- dunfold signature.structure.ref',
            -- simp,
            -- intros,    
            
            -- intros,
            -- dunfold signature.structure.ref',
            -- simp,
            -- left,
            -- intros,
        -- intros,
        -- -- induction φ;
        -- -- simp [vasgn.bind, signature.structure.ref'],
        -- right,
        -- intros,
        -- dunfold vasgn.bind,
        -- simp,
        -- existsi -(singleton w),
        -- push_neg,
        -- -- have c : {w} ≠ ∅ := sorry,
        -- -- simp[c],
        -- constructor,
        --     constructor,
        --         intro h,
        --         admit,
            
        -- dunfold signature.structure.ref',
        -- simp,
        -- left,
        -- intros,
        -- right,
        -- intros,
    -- end

theorem necessity_logical : logical φ.necessary :=
    begin
        simp,
        intros,
        dunfold signature.structure.ref',
        simp,
        set r := M.ref' φ asg,
        by_cases c₀ : r = univ; simp [c₀],
    end

theorem possibility_logical : logical φ.possible :=
    begin
        simp,
        intros,
        dunfold signature.structure.ref',
        simp,
        set r := M.ref' φ asg,
        by_cases c₀ : -r = univ; simp [c₀],
    end

theorem definability_of_validity' : M.valid' φ asg ↔ M.valid' (□φ) asg :=
    begin
        simp,
        dunfold signature.structure.ref',
        simp,
        set r := signature.structure.ref' M φ asg,
        by_cases c₀ : r = univ; simp [c₀],
        constructor; intro h,
            have c₁ : r = univ,
                ext, constructor; intro hyp, triv,
                exact h x,
            contradiction,
        intro w,
        specialize h w,
        contradiction,
    end

theorem necessity_valid_iff_possible : M.valid' (□φ) asg ↔ M.possible' (□φ) asg :=
    begin
        simp,
        dunfold signature.structure.ref',
        simp,
        set r := signature.structure.ref' M φ asg,
        by_cases c₀ : r = univ; simp [c₀];
        obtain ⟨w⟩ := M.ne;
        existsi w;
        triv,
    end

theorem necessity_T : tautology (□φ ⇒ φ) :=
    begin
        simp,
        intros,
        dunfold signature.structure.ref',
        simp,
        set r := signature.structure.ref' M φ asg,
        by_cases c₀ : r = univ; simp [c₀],
    end

theorem necessity_K : tautology (□(φ ⇒ ψ) ⇒ □φ ⇒ □ψ) :=
    begin
        simp,
        intros,
        dunfold signature.structure.ref',
        simp,
        set r₁ := M.ref' φ asg,
        set r₂ := M.ref' ψ asg,
        by_cases c₀ : r₁ = univ; simp [c₀],
        by_cases c₁ : r₂ = univ; simp [c₁],
    end

theorem necessity_4 : tautology (□φ ⇒ □□φ) :=
    begin
        simp,
        intros,
        dunfold signature.structure.ref',
        simp,
        set r := M.ref' φ asg,
        by_cases c₀ : r = univ; simp [c₀],
    end

theorem necessity_5 : tautology (⋄φ ⇒ □⋄φ) :=
    begin
        simp,
        intros,
        dunfold signature.structure.ref',
        simp,
        set r₁ := M.ref' φ asg,
        by_cases c₀ : -r₁ = univ; simp [c₀],
    end

theorem necessity_necessitation : tautology.{u} φ → tautology.{u} □φ :=
    begin
        simp,
        intros,
        dunfold signature.structure.ref',
        simp,
        set r := M.ref' φ asg,
        by_cases c₀ : r = univ; simp [c₀],
        specialize a M,
        have c₁ : r = univ,
                ext, constructor; intro h, triv,
                exact a x asg,
        contradiction,
    end

-- should be in the standard library but isn't.
theorem Inter_eq_univ_iff : ∀ {α I} {s : set α} {f : I → set α}, ((⋂ i : I, f i) = univ) ↔ ∀ i, f i = univ :=
    begin
        intros,
        constructor; intro h,
            intro i,
            ext, constructor; intro H, triv,
            rw ←h at H,
            simp at H,
            exact H i,
        ext, constructor; intro H, triv,
        simp,
        intro i,
        rw h i,
        triv,
    end

theorem necessity_converse_barcan : ∀ x : ℕ, tautology (□formula.all x φ ⇒ formula.all x □φ) :=
    begin
        simp,
        intros,
        dunfold signature.structure.ref',
        simp,
        by_cases c₀ : (⋂ (S : set ω), signature.structure.ref' M φ (vasgn.bind asg x S)) = univ;
        simp [c₀],
        intro i,
        have c₁ := Inter_eq_univ_iff.mp c₀ i,
        simp [c₁],
        assumption,
    end


end logic