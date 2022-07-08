use array_tool::vec::{Intersect, Union, Uniq};
use itertools::*;
use rpds::HashTrieSet as Set;
use std::{fmt::format, ops};

#[derive(Debug, Clone)]
pub enum Term {
    Int(isize),
    Float(f64),
    Bool(bool),
    /// x
    Var {
        name: String,
    },
    /// λu.e
    Lambda {
        parameter: String,
        body: Box<Term>,
    },
    /// e e′
    Application {
        function: Box<Term>,
        argument: Box<Term>,
    },
    /// let o = e in e′
    Let {
        name: String,
        value: Box<Term>,
        body: Box<Term>,
    },
}

/// Known as "Simple Types (τ)" in the paper
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct SimpleType {
    kind: TypeKind,
    arguments: Vec<SimpleType>,
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
enum TypeKind {
    ///  C τ1 ...τn
    TypeConstructor(String),
    ///  α τ1 ...τn
    TypeVariable(String),
}

impl TypeKind {
    fn print(&self) -> String {
        match self {
            TypeKind::TypeConstructor(c) => format!("TypeConstructor({})", c),
            TypeKind::TypeVariable(a) => format!("TypeVariable({})", a),
        }
    }
}

/// ∆ ::= {oi : τi}. τ
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct ConstrainedType {
    constraints: Constraints,
    r#type: SimpleType,
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct Constraints(Vec<Constraint>);

impl Constraints {
    /// The restriction of a set of constraints κ to a set of type variables V , denoted by κ|V ,
    /// is defined inductively as follows:
    fn restrictions(&self, v: &TypeVariables) -> Constraints {
        match self.0.split_first() {
            // ∅|V =∅
            None => Constraints(vec![]),
            Some((head, tail)) => {
                // {o:τ}|V =if tv(τ)∩V =∅ then ∅ else {o:τ}
                let Constraint { name: o, r#type: t } = head;
                if t.free_type_variables().intersect(v).is_empty() {
                    Constraints(vec![])
                } else {
                    Constraints(vec![Constraint {
                        name: o.clone(),
                        r#type: t.clone(),
                    }])
                }
                // ({o:τ}∪κ′)|V ={o:τ}|V ∪ κ′|V
                .union(Constraints(tail.to_vec()).restrictions(v))
            }
        }
    }

    /// The closure of restricting a set of constraints κ to a set of type variables V , denoted by κ|∗V , is defined as follows:
    fn closure_restrictions(&self, v: &TypeVariables) -> Constraints {
        let k_v = self.restrictions(&v);
        // κ|V if tv(κ|V) ⊆ V
        if k_v.free_type_variables().is_subset_of(&v) {
            k_v
        }
        // κ|∗tv(κ|V) otherwise
        else {
            self.closure_restrictions(&k_v.free_type_variables())
        }
    }

    fn applied_by(&self, substitutions: &Substitutions) -> Constraints {
        Constraints(
            self.0
                .iter()
                .map(|constraint| constraint.applied_by(substitutions))
                .collect(),
        )
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn substitute_type(&self, type_variable: &String, with_type: &SimpleType) -> Constraints {
        Constraints(
            self.0
                .iter()
                .map(|constraint| constraint.substitute_type(type_variable, with_type))
                .collect(),
        )
    }

    fn union(&self, other: Constraints) -> Constraints {
        Constraints(self.0.union(other.0))
    }

    fn free_type_variables(&self) -> TypeVariables {
        TypeVariables(
            self.0
                .iter()
                .flat_map(|constraint| constraint.free_type_variables().0)
                .unique()
                .collect(),
        )
    }

    fn print(&self) -> String {
        format!(
            "{{{}}}",
            self.0
                .iter()
                .map(Constraint::print)
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct Constraint {
    name: String,
    r#type: SimpleType,
}

/// Known as "Types" in the paper.
/// σ ::= ∀αi. ∆
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct Type {
    /// Quantified type variables
    type_variables: TypeVariables,
    constrained_type: ConstrainedType,
}

impl Type {
    fn print(&self) -> String {
        let type_variables = if self.type_variables.is_empty() {
            "".to_string()
        } else {
            format!(
                "forall {}.",
                self.type_variables
                    .0
                    .iter()
                    .map(|type_variable| type_variable.to_string())
                    .collect::<Vec<String>>()
                    .join(", ")
            )
        };
        let constraints = if self.constrained_type.constraints.is_empty() {
            "".to_string()
        } else {
            format!("{{{}}}", self.constrained_type.constraints.print())
        };
        format!(
            "{}{}{}",
            type_variables,
            constraints,
            self.constrained_type.r#type.print()
        )
    }
    fn is_simple_type(&self) -> bool {
        self.type_variables.is_empty() && self.constrained_type.constraints.is_empty()
    }
    fn instantiate(&self, state: &mut State) -> ConstrainedType {
        self.type_variables
            .0
            .iter()
            .fold(self.constrained_type.clone(), |result, a| {
                result.substitute_type(a, &type_variable(state.fresh_type_variable()))
            })
    }

    /// Sσ denotes the type obtained by substituting S(α) for each occurrence of free type variable α in σ
    fn applied_by(&self, substitutions: &Substitutions) -> Type {
        Type {
            type_variables: self.type_variables.clone(),
            constrained_type: ConstrainedType {
                constraints: self.constrained_type.constraints.applied_by(substitutions),
                r#type: self.constrained_type.r#type.applied_by(substitutions),
            },
        }
    }

    fn free_type_variables(&self) -> TypeVariables {
        self.constrained_type.free_type_variables() - self.type_variables.clone()
    }

    fn new_simple_type(simple_type: SimpleType) -> Type {
        Type {
            type_variables: TypeVariables(vec![]),
            constrained_type: ConstrainedType {
                constraints: Constraints(vec![]),
                r#type: simple_type,
            },
        }
    }
}

impl ConstrainedType {
    fn new_simple_type(simple_type: SimpleType) -> Self {
        ConstrainedType {
            constraints: Constraints(vec![]),
            r#type: simple_type,
        }
    }
    fn substitute_type(&self, type_variable: &String, with_type: &SimpleType) -> ConstrainedType {
        ConstrainedType {
            constraints: self.constraints.substitute_type(type_variable, with_type),
            r#type: self.r#type.substitute_type(type_variable, with_type),
        }
    }

    fn free_type_variables(&self) -> TypeVariables {
        self.constraints
            .free_type_variables()
            .union(self.r#type.free_type_variables())
    }

    fn print(&self) -> String {
        format!("{}. {}", self.constraints.print(), self.r#type.print())
    }

    fn alpha_conversion(&self) -> Self {
        let mut state = State::new();
        self.applied_by(&Substitutions::from_vector(
            self.free_type_variables()
                .0
                .iter()
                .map(|a| Substitution::SubstituteType {
                    old: a.to_string(),
                    new: type_variable(format!("''{}", state.fresh_type_variable())),
                })
                .collect(),
        ))
    }

    fn applied_by(&self, substitutions: &Substitutions) -> ConstrainedType {
        ConstrainedType {
            constraints: self.constraints.applied_by(substitutions),
            r#type: self.r#type.applied_by(substitutions),
        }
    }
}

impl Constraint {
    fn substitute_type(&self, type_variable: &String, with_type: &SimpleType) -> Constraint {
        Constraint {
            name: self.name.clone(),
            r#type: self.r#type.substitute_type(type_variable, with_type),
        }
    }

    fn applied_by(&self, substitutions: &Substitutions) -> Constraint {
        Constraint {
            name: self.name.clone(),
            r#type: self.r#type.applied_by(substitutions),
        }
    }

    fn free_type_variables(&self) -> TypeVariables {
        self.r#type.free_type_variables()
    }

    fn print(&self) -> String {
        format!("{}: {}", self.name, self.r#type.print())
    }
}

impl SimpleType {
    fn substitute_type(&self, type_variable: &String, with_type: &SimpleType) -> SimpleType {
        let kind = match &self.kind {
            TypeKind::TypeVariable(name) => {
                if name.eq(type_variable) {
                    // Assert that there is no arguments for this type,
                    // because substitution can only happen for type variable,
                    // not constructor variable
                    assert!(self.arguments.is_empty());
                    return with_type.clone();
                } else {
                    TypeKind::TypeVariable(name.clone())
                }
            }
            c @ TypeKind::TypeConstructor(_) => c.clone(),
        };
        SimpleType {
            kind,
            arguments: self
                .arguments
                .clone()
                .into_iter()
                .map(|argument| argument.substitute_type(type_variable, with_type))
                .collect(),
        }
    }

    fn substitute_type_kind(&self, type_variable: &str, new_type_kind: &TypeKind) -> SimpleType {
        SimpleType {
            kind: match &self.kind {
                c @ TypeKind::TypeConstructor(_) => c.clone(),
                TypeKind::TypeVariable(name) => {
                    if name.eq(type_variable) {
                        new_type_kind.clone()
                    } else {
                        TypeKind::TypeVariable(name.to_string())
                    }
                }
            },
            arguments: self
                .arguments
                .clone()
                .into_iter()
                .map(|argument| argument.substitute_type_kind(type_variable, new_type_kind))
                .collect(),
        }
    }

    fn contains(&self, name: &str) -> bool {
        (match &self.kind {
            TypeKind::TypeConstructor(c) => false,
            TypeKind::TypeVariable(a) => a.eq(name),
        }) || self
            .arguments
            .iter()
            .any(|argument| argument.contains(name))
    }

    fn applied_by(&self, substitutions: &Substitutions) -> SimpleType {
        match substitutions {
            Substitutions::Identity => self.clone(),
            Substitutions::Compose { left, right } => right.apply(self).applied_by(left),
        }
    }

    fn free_type_variables(&self) -> TypeVariables {
        let mut result = match &self.kind {
            TypeKind::TypeConstructor(_) => vec![],
            TypeKind::TypeVariable(a) => vec![a.clone()],
        };
        result.extend(
            self.arguments
                .iter()
                .flat_map(|argument| argument.free_type_variables().0)
                .collect::<Vec<String>>(),
        );
        TypeVariables(result)
    }

    fn as_type(self) -> Type {
        Type {
            type_variables: TypeVariables(vec![]),
            constrained_type: ConstrainedType {
                constraints: Constraints(vec![]),
                r#type: self,
            },
        }
    }

    fn print(&self) -> String {
        let arguments = self
            .arguments
            .iter()
            .map(|argument| argument.print())
            .collect::<Vec<String>>()
            .join(", ");
        let name = match &self.kind {
            TypeKind::TypeConstructor(c) => c,
            TypeKind::TypeVariable(a) => a,
        };

        if arguments.is_empty() {
            return name.clone();
        }

        format!("{}<{}>", name, arguments)
    }
}

/// The type inference algorithm uses typing environments A, which are sets of elements x : (σ,Γ).
/// Pair (σ,Γ) is called an entry for x in A. We write A(x) for the set of entries of x in A, and
/// At(x) for the set of first elements (i.e. the types) in these entries.
pub struct TypingEnvironment {
    elements: Set<TypingEnvElement>,
}

impl TypingEnvironment {
    pub fn new() -> Self {
        TypingEnvironment {
            elements: Set::new(),
        }
    }

    /// We write A(x) for the set of entries of x in A
    fn entries_of(&self, name: &String) -> Vec<TypingEntry> {
        self.elements
            .iter()
            .filter_map(|element| {
                if &element.name == name {
                    Some(element.entry.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    /// At(x) for the set of first elements (i.e. the types) in these entries.
    fn types_of(&self, x: &String) -> Vec<Type> {
        self.entries_of(x)
            .into_iter()
            .map(|entry| entry.r#type)
            .collect()
    }

    fn add_entry(&self, name: String, entry: TypingEntry) -> TypingEnvironment {
        TypingEnvironment {
            elements: self.elements.insert(TypingEnvElement { name, entry }),
        }
    }
}

/// x : (σ,Γ)
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct TypingEnvElement {
    name: String,
    entry: TypingEntry,
}

impl TypingEnvElement {
    fn new(name: String, r#type: Type) -> Self {
        TypingEnvElement {
            name: name.clone(),
            entry: TypingEntry {
                r#type: r#type.clone(),
                context: TypingContext(Set::new().insert(Typing {
                    variable: name,
                    r#type,
                })),
            },
        }
    }
}

/// Pair (σ,Γ) is called an entry for x in A
#[derive(PartialEq, Eq, Clone, Debug)]
struct TypingEntry {
    r#type: Type,
    context: TypingContext,
}

impl std::hash::Hash for TypingEntry {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.r#type.hash(state);
    }
}

/// A typing context Γ is a set of pairs x : σ (a let-bound variable can occur more than once in a
/// typing context). A pair x : σ is called a typing for x; if {x : σi}i=1..n is the set of typings
/// for x in Γ, then Γ(x) = {σi}i=1..n is the set of types of x in Γ
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct TypingContext(Set<Typing>);

impl TypingContext {
    fn print(&self) -> String {
        format!(
            "[{}]",
            self.0
                .iter()
                .map(|typing| typing.print())
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
    fn types_of(&self, name: &String) -> Set<Type> {
        self.0
            .iter()
            .filter_map(|typing| {
                if typing.variable.eq(name) {
                    Some(typing.r#type.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    fn union(&self, context: &Self) -> Self {
        TypingContext(context.0.iter().fold(self.0.clone(), |result, typing| {
            result.insert(typing.clone())
        }))
    }

    fn substitute_type(
        &self,
        old_term_variable: &String,
        new_term_variable: &String,
    ) -> TypingContext {
        TypingContext(self.0.into_iter().fold(Set::new(), |result, entry| {
            result.insert(Typing {
                variable: if entry.variable.eq(old_term_variable) {
                    new_term_variable.clone()
                } else {
                    entry.variable.clone()
                },
                r#type: entry.r#type.clone(),
            })
        }))
    }

    /// u:τu ∈Γ1 and u:τu′ ∈Γ2
    fn intersected_variables(&self, other: &Self) -> Vec<(SimpleType, SimpleType)> {
        self.0
            .iter()
            .flat_map(|x| {
                other.0.iter().filter_map(|y| {
                    if y.variable == x.variable
                        && y.r#type.is_simple_type()
                        && x.r#type.is_simple_type()
                    {
                        Some((
                            x.r#type.constrained_type.r#type.clone(),
                            y.r#type.constrained_type.r#type.clone(),
                        ))
                    } else {
                        None
                    }
                })
            })
            .collect()
    }

    /// SΓ denotes {x : Sσ | x : σ ∈ Γ}
    fn applied_by(&self, substitutions: &Substitutions) -> TypingContext {
        TypingContext(
            self.0
                .into_iter()
                .map(|entry| Typing {
                    variable: entry.variable.clone(),
                    r#type: entry.r#type.applied_by(substitutions),
                })
                .collect(),
        )
    }

    fn free_type_variables(&self) -> TypeVariables {
        TypeVariables(
            self.0
                .into_iter()
                .filter_map(|entry| match &entry.r#type.constrained_type.r#type.kind {
                    TypeKind::TypeConstructor(_) => None,
                    TypeKind::TypeVariable(a) => Some(a.clone()),
                })
                .collect(),
        )
    }
}

/// A pair x : σ is called a typing for x
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct Typing {
    variable: String,
    r#type: Type,
}

pub struct State {
    /// Used for generating fresh type variable
    fresh_type_variable_index: usize,
    /// Used for generating fresh term variable
    fresh_term_variable_index: usize,
}

impl State {
    pub fn new() -> State {
        State {
            fresh_type_variable_index: 0,
            fresh_term_variable_index: 0,
        }
    }
    fn fresh_type_variable(&mut self) -> String {
        let result = format!("'{}", self.fresh_type_variable_index);
        self.fresh_type_variable_index += 1;
        result
    }
    fn fresh_term_variable(&mut self) -> String {
        let result = format!("#{}", self.fresh_term_variable_index);
        self.fresh_term_variable_index += 1;
        result
    }
}

/// The type inference algorithm.
pub fn ppc(
    term: Term,
    A: &TypingEnvironment,
) -> Result<(ConstrainedType, TypingContext), InferError> {
    ppc_helper(term, A, &mut State::new())
}

/// The type inference algorithm helper.
pub fn ppc_helper(
    term: Term,
    A: &TypingEnvironment,
    state: &mut State,
) -> Result<(ConstrainedType, TypingContext), InferError> {
    match term {
        Term::Int(_) => Ok((
            ConstrainedType::new_simple_type(int()),
            TypingContext(Set::new()),
        )),
        Term::Float(_) => Ok((
            ConstrainedType::new_simple_type(float()),
            TypingContext(Set::new()),
        )),
        Term::Bool(_) => Ok((
            ConstrainedType::new_simple_type(boolean()),
            TypingContext(Set::new()),
        )),

        // PPc(x,A) = ptε(x,A)
        Term::Var { name: x } => Ok(pte(x, A, state)),

        // PPc(λu.e,A) =
        Term::Lambda {
            parameter: u,
            body: e,
        } => {
            // let (κ. τ, Γ ) = PPc(e, A)
            let (
                ConstrainedType {
                    constraints: k,
                    r#type: t,
                },
                gamma,
            ) = ppc_helper(*e, A, state)?;
            //  if u:τ′ ∈ Γ,for some τ′
            if let Some(scheme) = gamma
                .types_of(&u)
                .into_iter()
                .collect::<Vec<&Type>>()
                .first()
            //    then (κ. τ′ → τ, Γ − {u : τ′})
            {
                if scheme.type_variables.is_empty()
                    && scheme.constrained_type.constraints.is_empty()
                {
                    let t_prime = scheme.constrained_type.r#type.clone();
                    return Ok((
                        ConstrainedType {
                            constraints: k,
                            r#type: function_type(t_prime, t),
                        },
                        TypingContext(gamma.0.remove(&Typing {
                            variable: u.clone(),
                            r#type: scheme.clone().clone(),
                        })),
                    ));
                }
            }

            //    else (κ. α → τ, Γ ), where α is a fresh type variable
            let a = type_variable(state.fresh_type_variable());
            Ok((
                ConstrainedType {
                    constraints: k,
                    r#type: function_type(a, t),
                },
                gamma,
            ))
        }

        // PPc(e1 e2,A) =
        Term::Application {
            function: e1,
            argument: e2,
        } => {
            println!("e1 = {:#?}", e1);
            println!("e2 = {:#?}", e2);

            // let (κ1 . τ1 , Γ1) = PPc (e1 , A)
            let (
                ConstrainedType {
                    constraints: k1,
                    r#type: t1,
                },
                gamma1,
            ) = ppc_helper(*e1, A, state)?;

            println!("t1 = {}", t1.print());
            println!("gamma1 = {}", gamma1.print());

            // (κ2 . τ2 , Γ2) = PPc (e2 , A)
            let (
                ConstrainedType {
                    constraints: k2,
                    r#type: t2,
                },
                gamma2,
            ) = ppc_helper(*e2, A, state)?;

            println!("t2 = {}", t2.print());
            println!("gamma2 = {}", gamma2.print());

            // S=unify({τu =τu′ |u:τu ∈ Γ1 and u:τu′ ∈ Γ2} ∪ {τ1 =τ2 → α})
            // where α is a fresh type variable
            let a = type_variable(state.fresh_type_variable());
            let equations = {
                let mut equations: Vec<Equation> = gamma1
                    .intersected_variables(&gamma2)
                    .into_iter()
                    .map(|(left, right)| Equation { left, right })
                    .collect();

                equations.push(Equation {
                    left: t1,
                    right: function_type(t2, a.clone()),
                });
                equations
            };

            println!(
                "equations = [{}]",
                equations
                    .iter()
                    .map(Equation::print)
                    .collect::<Vec<String>>()
                    .join(", ")
            );

            let s = unify(equations)?;

            println!("s = {}", s.print());

            // Γ′ =SΓ1 ∪ SΓ2
            let gamma_prime = gamma1.applied_by(&s).union(&gamma2.applied_by(&s));
            println!("gamma_prime = {}", gamma_prime.print());

            // ss =sat(Sκ1 ∪ Sκ2,Γ′)
            let ss = sat(k1.applied_by(&s).union(k2.applied_by(&s)), &gamma_prime);

            println!("k1 = {}", k1.print());
            println!("Sκ1 = {}", k1.applied_by(&s).print());
            println!(
                "Sκ1 ∪ Sκ2 = {}",
                k1.applied_by(&s).union(k2.applied_by(&s)).print()
            );

            println!(
                "ss = {}",
                ss.iter()
                    .map(|s| s.print())
                    .collect::<Vec<String>>()
                    .join(", ")
            );

            // if ss =∅ then fail
            match ss.split_first() {
                None => Err(InferError::NotSatifiable),
                Some((head, tail)) => {
                    // else
                    // let S∆ = intesection ss,
                    let s_delta = intersection(NonEmpty(head.clone(), tail.to_vec()));

                    println!("S∆ = {}", s_delta.print());

                    // Γ=S∆Γ′,
                    let gamma = gamma_prime.applied_by(&s_delta);

                    // τ=S∆Sα,
                    let t = a.applied_by(&s).applied_by(&s_delta);
                    println!("t = {}", t.print());

                    //V =tv(τ,Γ),
                    let v = t.free_type_variables().union(gamma.free_type_variables());

                    //κ=unresolved(S∆S(κ1 ∪κ2),Γ)
                    let k = unresolved(k1.union(k2).applied_by(&s).applied_by(&s_delta), &gamma);

                    println!(
                        "tv(S∆Sκ1) = {}",
                        k1.applied_by(&s)
                            .applied_by(&s_delta)
                            .free_type_variables()
                            .print()
                    );

                    // if ambiguous(tv(S∆Sκ1),κ,V)
                    if ambiguous(
                        k1.applied_by(&s).applied_by(&s_delta).free_type_variables(),
                        &k,
                        &v,
                    )
                    // then fail
                    {
                        panic!("Fail")
                    }
                    // else (κ|∗V .τ,Γ)
                    else {
                        println!("k = {}", k.print());
                        println!("v = {}", v.print());
                        Ok((
                            ConstrainedType {
                                constraints: k.closure_restrictions(&v),
                                r#type: t,
                            },
                            gamma,
                        ))
                    }
                }
            }
        }

        // PPc(let o = e1 in e2,A) =
        Term::Let {
            name: o,
            value: e1,
            body: e2,
        } => {
            // let (κ1 . τ1 , Γ1 ) = P Pc (e1 , A)
            let (
                ConstrainedType {
                    constraints: k1,
                    r#type: t1,
                },
                gamma1,
            ) = ppc_helper(*e1, A, state)?;

            // σ = close(κ1. τ1, Γ1)
            let theta = close(
                ConstrainedType {
                    constraints: k1.clone(),
                    r#type: t1,
                },
                &gamma1,
            );

            // in if ρc(σ,At(o)) does not hold then fail
            if !overloadable(&theta, A.types_of(&o)) {
                return Err(InferError::CannotBeOverloaded {
                    name: o.clone(),
                    r#type: theta,
                    existing_types: A.types_of(&o),
                });
            }

            // else let A′ = A ∪ {o:(σ,Γ1)}
            let A_prime = A.add_entry(
                o,
                TypingEntry {
                    r#type: theta,
                    context: gamma1.clone(),
                },
            );

            // (κ2. τ2, Γ2) = PPc(e2, A′)
            let (
                ConstrainedType {
                    constraints: k2,
                    r#type: t2,
                },
                gamma2,
            ) = ppc_helper(*e2, &A_prime, state)?;

            // S =unify({τu =τu′ | u:τu ∈Γ1,u:τu′ ∈Γ2})
            let s = unify(
                gamma1
                    .intersected_variables(&gamma2)
                    .into_iter()
                    .map(|(left, right)| Equation { left, right })
                    .collect(),
            )?;

            // Γ′ =SΓ1 ∪SΓ2
            let gamma_prime = gamma1.applied_by(&s).union(&gamma2.applied_by(&s));

            // ss=sat(Sκ1 ∪ Sκ2, Γ′)
            let ss = sat(k1.applied_by(&s).union(k2.applied_by(&s)), &gamma_prime);

            // in if S=∅ then fail
            let ss = match ss.split_first() {
                None => Err(InferError::NotSatifiable),
                Some((head, tail)) => Ok(NonEmpty(head.clone(), tail.to_vec())),
            }?;

            // else let S∆ =intersect S,
            let s_delta = intersection(ss);

            // Γ=S∆Γ′,
            let gamma = gamma_prime.applied_by(&s_delta);

            // τ=S∆Sτ2
            let t = t2.applied_by(&s).applied_by(&s_delta);

            // V =tv(τ,Γ),
            let v = t.free_type_variables().union(gamma.free_type_variables());

            // κ = unresolved(S∆S(κ1 ∪κ2),Γ)
            let k = unresolved(k1.union(k2).applied_by(&s).applied_by(&s_delta), &gamma);

            // in (κ|∗V .τ,Γ)
            Ok((
                ConstrainedType {
                    constraints: k.closure_restrictions(&v),
                    r#type: t,
                },
                gamma,
            ))
        }
    }
}

/// The overloading policy is given by (redefining ρ as) ρc:
///
/// ρc (o : ∀αj . κ. τ , T ) =
///   T = ∅ or
///   tv(∀αj.κ.τ)=∅ and for each σ=∀(βk).κ′.τ′ ∈T unify({τ = τ′}) fails and tv(σ) = ∅
fn overloadable(
    Type {
        type_variables: alpha,
        constrained_type:
            ConstrainedType {
                constraints: k,
                r#type: t,
            },
    }: &Type,
    T: Vec<Type>,
) -> bool {
    T.is_empty()
        || (Type {
            type_variables: alpha.clone(),
            constrained_type: ConstrainedType {
                constraints: k.clone(),
                r#type: t.clone(),
            },
        }
        .free_type_variables()
        .is_empty()
            && T.iter().all(
                |theta @ Type {
                     constrained_type:
                         ConstrainedType {
                             r#type: t_prime, ..
                         },
                     ..
                 }| {
                    unify(vec![Equation {
                        left: t.clone(),
                        right: t_prime.clone(),
                    }])
                    .is_err()
                        && theta.free_type_variables().is_empty()
                },
            ))
}

/// Rule (LET) uses function close, to quantify simple and constrained types over type variables
/// that are not free in a typing context:
/// ```
/// close(∆, Γ ) = ∀αj . ∆, where {αj } = tv(∆) − tv(Γ ).
/// ```
fn close(delta: ConstrainedType, gamma: &TypingContext) -> Type {
    Type {
        type_variables: delta.free_type_variables() - gamma.free_type_variables(),
        constrained_type: delta,
    }
}

/// ambiguous(V1,κ,V)=
///   V′ ̸!= ∅ and V′ ⊆ V1
///     where V′ = tv(κ) − tv(κ|∗V )
fn ambiguous(v1: TypeVariables, k: &Constraints, v: &TypeVariables) -> bool {
    let v_prime = k.free_type_variables() - k.closure_restrictions(&v).free_type_variables();
    !v_prime.is_empty() && v_prime.is_subset_of(&v1)
}

fn unresolved(constraints: Constraints, gamma: &TypingContext) -> Constraints {
    match constraints.0.split_first() {
        // unresolved (∅, Γ ) = ∅
        None => Constraints(vec![]),
        // unresolved({o:τ}∪κ,Γ) =
        Some((Constraint { name: o, r#type: t }, k)) => {
            // where κ′ =
            let k_prime: Constraints = match sat(
                Constraints(vec![Constraint {
                    name: o.clone(),
                    r#type: t.clone(),
                }]),
                &gamma,
            )
            .as_slice()
            {
                //   if sat({o : τ},Γ) = {S}, for some S,
                [s] => {
                    // where ∀αj.κ′.τ′ ∈ Γ(o), Sτ = Sτ′
                    let types_of_o = gamma.types_of(o);
                    let Type {
                        constrained_type:
                            ConstrainedType {
                                constraints: k_prime,
                                ..
                            },
                        ..
                    } = types_of_o
                        .into_iter()
                        .find(
                            |Type {
                                 constrained_type:
                                     ConstrainedType {
                                         r#type: t_prime, ..
                                     },
                                 ..
                             }| {
                                t.applied_by(&s).eq(&t_prime.applied_by(&s))
                            },
                        )
                        .expect("Should not be possible");

                    //   then unresolved(Sκ′,Γ),
                    unresolved(k_prime.applied_by(&s), gamma)
                }
                //   else {o : τ}
                _ => Constraints(vec![Constraint {
                    name: o.clone(),
                    r#type: t.clone(),
                }]),
            };

            // κ′ ∪ unresolved(κ,Γ)
            k_prime.union(unresolved(Constraints(k.to_vec()), gamma))
        }
    }
}

/// The intersection of a set of substitutions S, denoted by intersection(S), is defined as follows:
fn intersection(ss: NonEmpty<Substitutions>) -> Substitutions {
    match ss.1.split_first() {
        // intersection {S} = S
        None => ss.0,
        // intersection ({S}∪SS)=S|V where V ={α| S(α)=S′(α),and S′ = intersection(SS)}
        Some((head, tail)) => {
            let s = ss.0;
            let ss = NonEmpty(head.clone(), tail.to_vec());
            let s_prime = intersection(ss);
            let v: Vec<String> = s.flat_map(&|x| {
                s_prime.flat_map(&|y| {
                    if x.eq(y) {
                        vec![x.type_variable()]
                    } else {
                        vec![]
                    }
                })
            });
            s.restrictions(&v)
        }
    }
}

fn sat(k: Constraints, gamma: &TypingContext) -> Vec<Substitutions> {
    match k.0.as_slice() {
        // sat(∅,Γ) = {id}
        [] => vec![Substitutions::Identity],

        // sat({o:τ},Γ)= U [...]
        // {S| S=Unify({τ=τi},V)and sat(Sκi,SΓ)̸=∅} where V = tv(τi) − ({(αj)i} ∪ tv(τ)) and σi = ∀(αj)i. κi. τi
        [Constraint { name: o, r#type: t }] => {
            gamma
                .types_of(o)
                .iter()
                .filter_map(|theta_i| {
                    // σi = ∀(αj)i. κi. τi
                    let Type {
                        type_variables: a_j_i,
                        constrained_type:
                            ConstrainedType {
                                constraints: k_i,
                                r#type: t_i,
                            },
                    } = theta_i;

                    // V = tv(τi) − ({(αj)i} ∪ tv(τ))
                    let v = t_i.free_type_variables() - a_j_i.union(t.free_type_variables());

                    // S=Unify({τ=τi},V)
                    let s = match Unify(
                        vec![Equation {
                            left: t.clone(),
                            right: t_i.clone(),
                        }],
                        v,
                    ) {
                        Ok(s) => s,
                        Err(_) => return None,
                    };

                    // ... and sat(Sκi,SΓ)̸=∅
                    if sat(k_i.applied_by(&s), &gamma.applied_by(&s)).is_empty() {
                        None
                    } else {
                        Some(s)
                    }
                })
                .collect::<Vec<Substitutions>>()
        }

        [Constraint { name: o, r#type: t }, k @ ..] => {
            // sat({o:τ}∪κ,Γ)=U Si∈sat({o:τ},Γ) U Sij∈sat(Siκ,SiΓ){Sij ◦Si}
            //
            let sis = sat(
                Constraints(vec![Constraint {
                    name: o.clone(),
                    r#type: t.clone(),
                }
                .clone()]),
                gamma,
            );
            sis.into_iter()
                .flat_map(|si| {
                    let sijs = sat(
                        Constraints(k.to_vec()).applied_by(&si),
                        &gamma.applied_by(&si),
                    );
                    sijs.into_iter()
                        .map(|sij| sij.compose(&si))
                        .collect::<Vec<Substitutions>>()
                })
                .collect::<Vec<Substitutions>>()
                .unique()
        }
    }
}

#[derive(PartialEq, Eq, Clone)]
enum Substitutions {
    /// Remember that right comes before left in function composition
    Compose {
        left: Box<Substitutions>,
        right: Substitution,
    },
    Identity,
}

impl Substitutions {
    fn from_vector(substitutions: Vec<Substitution>) -> Self {
        match substitutions.split_first() {
            None => Substitutions::Identity,
            Some((first, rest)) => Substitutions::Compose {
                left: Box::new(Substitutions::from_vector(rest.to_vec())),
                right: first.clone(),
            },
        }
    }
    fn print(&self) -> String {
        format!("[{}]", self.print_())
    }

    fn print_(&self) -> String {
        match self {
            Substitutions::Compose { left, right } => {
                // Remember that right comes before left
                // So to ease reading, we print the one that comes first on the left
                format!("{}, {}", right.print(), left.print_())
            }
            Substitutions::Identity => "".to_string(),
        }
    }

    fn compose(&self, right: &Substitutions) -> Substitutions {
        match right {
            Substitutions::Compose { left, right } => Substitutions::Compose {
                left: Box::new(left.compose(self)),
                right: right.clone(),
            },
            Substitutions::Identity => self.clone(),
        }
    }

    fn flat_map<F, T>(&self, f: &F) -> Vec<T>
    where
        F: Fn(&Substitution) -> Vec<T>,
    {
        match self {
            Substitutions::Compose { left, right } => {
                let mut result = left.flat_map(f);
                result.extend(f(&right));
                result
            }
            Substitutions::Identity => vec![],
        }
    }

    fn restrictions(&self, v: &Vec<String>) -> Substitutions {
        match self {
            Substitutions::Compose { left, right } => {
                let right = match right {
                    Substitution::SubstituteType { old, new } => {
                        if v.contains(old) {
                            Some(Substitution::SubstituteType {
                                old: old.clone(),
                                new: new.clone(),
                            })
                        } else {
                            None
                        }
                    }
                    Substitution::SubstituteTypeKind { old, new } => {
                        if v.contains(old) {
                            Some(Substitution::SubstituteTypeKind {
                                old: old.clone(),
                                new: new.clone(),
                            })
                        } else {
                            None
                        }
                    }
                };
                match right {
                    Some(right) => Substitutions::Compose {
                        left: Box::new(left.restrictions(v)),
                        right,
                    },
                    None => left.restrictions(v),
                }
            }
            Substitutions::Identity => Substitutions::Identity,
        }
    }
}

/// A type substitution (or simply substitution) is a function from type variables to simple
/// types or type constructors, that differ from the identity function (id) only on finitely
/// many variables
#[derive(Debug, PartialEq, Eq, Clone)]
enum Substitution {
    SubstituteType {
        /// Type variable
        old: String,
        new: SimpleType,
    },
    SubstituteTypeKind {
        /// Type variable
        old: String,
        new: TypeKind,
    },
}

#[derive(Debug, Clone)]
struct Equation {
    left: SimpleType,
    right: SimpleType,
}

fn unify(equations: Vec<Equation>) -> Result<Substitutions, InferError> {
    // unify(E) = Unify(E, ∅)
    Unify(equations, TypeVariables(vec![]))
}

#[derive(Debug, PartialEq, Eq)]
pub enum InferError {
    RecursiveSubstitution,
    CannotUnify {
        left: String,
        right: String,
    },
    NotSatifiable,
    CannotBeOverloaded {
        name: String,
        r#type: Type,
        existing_types: Vec<Type>,
    },
}

#[derive(PartialEq, Eq, Debug, Clone, Hash)]
struct TypeVariables(Vec<String>);

impl TypeVariables {
    fn print(&self) -> String {
        format!(
            "[{}]",
            self.0
                .iter()
                .map(|v| v.clone())
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
}

fn Unify(
    equations: Vec<Equation>,
    type_variables: TypeVariables,
) -> Result<Substitutions, InferError> {
    match equations.split_first() {
        // Unify(∅,V)= id
        None => Ok(Substitutions::Identity),

        // Unify(E∪{Cτ1...τn=C′τ1′...τm′ },V)=
        Some((
            Equation {
                left:
                    SimpleType {
                        kind: TypeKind::TypeConstructor(c),
                        arguments: c_arguments,
                    },
                right:
                    SimpleType {
                        kind: TypeKind::TypeConstructor(c_prime),
                        arguments: c_prime_arguments,
                    },
            },
            equations,
        )) => {
            //if C ̸≡ C′ then fail
            if c.ne(c_prime) {
                Err(InferError::CannotUnify {
                    left: c.to_string(),
                    right: c_prime.to_string(),
                })
            }
            // else Unify(E ∪ {τ1 =τ1′,...,τn =τn′},V)
            else {
                assert!(c_arguments.len().eq(&c_prime_arguments.len()));
                let mut equations = equations.to_vec();
                equations.extend(
                    c_arguments
                        .iter()
                        .zip(c_prime_arguments.iter())
                        .map(|(left, right)| Equation {
                            left: left.clone(),
                            right: right.clone(),
                        })
                        .collect::<Vec<Equation>>(),
                );
                Unify(equations, type_variables)
            }
        }

        // Unify(E ∪ {α = τ }, V ) =
        Some((
            Equation {
                left:
                    SimpleType {
                        kind: TypeKind::TypeVariable(a),
                        arguments,
                    },
                right: t,
            }
            | Equation {
                right:
                    SimpleType {
                        kind: TypeKind::TypeVariable(a),
                        arguments,
                    },
                left: t,
            },
            equations,
        )) if arguments.is_empty() => {
            // if α≡τ then Unify(E,V)
            if type_variable(a.clone()).eq(t) {
                Unify(equations.to_vec(), type_variables)
            }
            // else if α occurs in τ then fail
            else if t.contains(a) {
                Err(InferError::RecursiveSubstitution)
            }
            // else if α ∈ V then
            else if type_variables.contains(a) {
                match t {
                    // if τ≡β where β /∈ V
                    SimpleType {
                        kind: TypeKind::TypeVariable(b),
                        arguments,
                    } if !type_variables.contains(b) && arguments.is_empty() => {
                        // then Unify(E[α/β],V)◦(β→α)
                        let a = type_variable(a.clone());
                        Ok(Substitutions::Compose {
                            left: Box::new(Unify(
                                substitute_type(equations.to_vec(), b, &a),
                                type_variables,
                            )?),
                            right: Substitution::SubstituteType {
                                old: b.to_string(),
                                new: a.clone(),
                            },
                        })
                    }
                    _ => panic!("Failed"),
                }
            }
            // else Unify(E[τ/α], V) ◦ (α → τ)
            else {
                Ok(Substitutions::Compose {
                    left: Box::new(Unify(
                        substitute_type(equations.to_vec(), a, t),
                        type_variables,
                    )?),
                    right: Substitution::SubstituteType {
                        old: a.to_string(),
                        new: t.clone(),
                    },
                })
            }
        }

        // Unify(E ∪ {α τ1...τn = χ τ1′...τm′ },V)=
        Some((
            Equation {
                left:
                    SimpleType {
                        kind: TypeKind::TypeVariable(a),
                        arguments: a_arguments,
                    },
                right:
                    SimpleType {
                        kind: x_kind,
                        arguments: x_arguments,
                    },
            }
            | Equation {
                left:
                    SimpleType {
                        kind: x_kind,
                        arguments: x_arguments,
                    },
                right:
                    SimpleType {
                        kind: TypeKind::TypeVariable(a),
                        arguments: a_arguments,
                    },
            },
            equations,
        )) => {
            //if m != n then fail else
            if a_arguments.len() != x_arguments.len() {
                panic!()
            }
            // Unify(E[χ/α]∪{τ1 =τ1′,...,τn =τn′}[χ/α],V)◦(α→χ)
            let mut equations = equations.to_vec();
            equations.extend(
                a_arguments
                    .iter()
                    .zip(x_arguments.iter())
                    .map(|(left, right)| Equation {
                        left: left.clone(),
                        right: right.clone(),
                    })
                    .collect::<Vec<Equation>>(),
            );

            Ok(Substitutions::Compose {
                left: Box::new(Unify(
                    substitute_type_kind(equations.to_vec(), a, x_kind),
                    type_variables,
                )?),
                right: Substitution::SubstituteTypeKind {
                    old: a.clone(),
                    new: x_kind.clone(),
                },
            })
        }
    }
}

fn substitute_type_kind(
    equations: Vec<Equation>,
    type_variable: &String,
    new_type_kind: &TypeKind,
) -> Vec<Equation> {
    equations
        .to_vec()
        .into_iter()
        .map(|equation| equation.substitute_type_kind(type_variable, new_type_kind))
        .collect()
}

fn substitute_type(
    equations: Vec<Equation>,
    type_variable: &String,
    with_type: &SimpleType,
) -> Vec<Equation> {
    equations
        .to_vec()
        .into_iter()
        .map(|equation| equation.substitute_type(type_variable, with_type))
        .collect()
}

fn type_variable(name: String) -> SimpleType {
    SimpleType {
        kind: TypeKind::TypeVariable(name),
        arguments: vec![],
    }
}

fn function_type(input: SimpleType, output: SimpleType) -> SimpleType {
    SimpleType {
        kind: TypeKind::TypeConstructor("->".to_string()),
        arguments: vec![input, output],
    }
}

fn named_type(name: String, arguments: Vec<SimpleType>) -> SimpleType {
    SimpleType {
        kind: TypeKind::TypeConstructor(name),
        arguments,
    }
}

fn int() -> SimpleType {
    named_type("int".to_string(), vec![])
}

fn float() -> SimpleType {
    named_type("float".to_string(), vec![])
}

fn boolean() -> SimpleType {
    named_type("boolean".to_string(), vec![])
}

/// Expression ptε(x,A) computes both type and context for x in A, similarly to pt(x,Γ),
/// introducing fresh type variables for let-bound variables as defined below:
fn pte(
    name: String,
    env: &TypingEnvironment,
    state: &mut State,
) -> (ConstrainedType, TypingContext) {
    match env.entries_of(&name).split_first() {
        // if A(x) = ∅ then (α, {x : α}), where α is a fresh type variable
        None => {
            let a = ConstrainedType {
                constraints: Constraints(vec![]),
                r#type: type_variable(state.fresh_type_variable()),
            };
            let context = TypingContext(Set::new().insert(Typing {
                variable: name,
                r#type: Type {
                    type_variables: TypeVariables(vec![]),
                    constrained_type: a.clone(),
                },
            }));
            (a, context)
        }
        // if A(x)={(∀αj.κ.τ,Γ)} then(κ.τ,Γ),
        //   with quantified type variables {αj} renamed as fresh type variables
        Some((
            TypingEntry {
                r#type: scheme,
                context,
            },
            [],
        )) => (scheme.instantiate(state), context.clone()),
        // else ({x′ : lcg({τi})}. lcg({τi}), U Γi[x′/x]),
        //   where A(x)={(∀(αj)i.κi.τi,Γi)} and x′ is a fresh term variable
        Some((head, tail)) => {
            let x_prime = state.fresh_term_variable();
            let lcgti = lcg(
                NonEmpty(
                    head.r#type.constrained_type.r#type.clone(),
                    tail.iter()
                        .map(|entry| entry.r#type.constrained_type.r#type.clone())
                        .collect(),
                ),
                state,
            );
            println!("pte name = {}", name);
            println!("head.context = {}", head.context.print());
            (
                ConstrainedType {
                    constraints: Constraints(vec![Constraint {
                        name: x_prime.clone(),
                        r#type: lcgti.clone(),
                    }]),
                    r#type: lcgti,
                },
                tail.iter().fold(
                    head.context.substitute_type(&name, &x_prime),
                    |result, entry| result.union(&entry.context.substitute_type(&name, &x_prime)),
                ),
            )
        }
    }
}

struct NonEmpty<T>(T, Vec<T>);

fn lcg(types: NonEmpty<SimpleType>, state: &mut State) -> SimpleType {
    match (types.0, types.1.split_first()) {
        (t, None) => t,
        (t1, Some((t2, types))) => match Vec::from(types).split_first() {
            None => lcgp(&t1, t2, state),
            Some((t3, types)) => lcgp(
                &lcgp(&t1, t2, state),
                &lcg(NonEmpty(t3.clone(), Vec::from(types)), state),
                state,
            ),
        },
    }
}

fn lcgp(t1: &SimpleType, t2: &SimpleType, state: &mut State) -> SimpleType {
    match (t1, t2) {
        (
            SimpleType {
                kind: t1_kind,
                arguments: t1_arguments,
            },
            SimpleType {
                kind: t2_kind,
                arguments: t2_arguments,
            },
        ) => {
            if t1_arguments.len() != t2_arguments.len() {
                return type_variable(state.fresh_type_variable());
            }
            let lcg0 = match (&t1_kind, &t2_kind) {
                (TypeKind::TypeConstructor(a), TypeKind::TypeConstructor(b)) if a == b => {
                    TypeKind::TypeConstructor(a.clone())
                }
                _ => TypeKind::TypeVariable(state.fresh_type_variable()),
            };

            // This vector is needed to implement this:
            //   ...and type variables are renamed so that α ≡ α′ whenever there exist τa, τb such that
            //   lcgp(τa, τb) = α and lcgp(τa, τb) = α′
            let mut generated_type_variables: Vec<(
                Set<SimpleType>,
                /*type variable name*/ String,
            )> = vec![];
            let lcgi =
                t1_arguments
                    .iter()
                    .zip(t2_arguments.iter())
                    .map(|(t1_arg, t2_arg)| {
                        if let Some(a) = generated_type_variables.iter().find_map(
                            |(types, type_variable_name)| {
                                if types
                                    .eq(&Set::new().insert(t1_arg.clone()).insert(t2_arg.clone()))
                                {
                                    Some(type_variable_name)
                                } else {
                                    None
                                }
                            },
                        ) {
                            return type_variable(a.clone());
                        }
                        match lcgp(t1_arg, t2_arg, state) {
                            SimpleType {
                                kind: TypeKind::TypeVariable(a),
                                arguments,
                            } => {
                                generated_type_variables.push((
                                    Set::new().insert(t1_arg.clone()).insert(t2_arg.clone()),
                                    a.clone(),
                                ));
                                SimpleType {
                                    kind: TypeKind::TypeVariable(a),
                                    arguments,
                                }
                            }
                            other => other,
                        }
                    })
                    .collect();

            SimpleType {
                kind: lcg0,
                arguments: lcgi,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    // Note this useful idiom: importing names from outer (for mod tests) scope.
    use super::*;

    #[test]
    fn test_apply_substitution_1() {
        // substitutions = [a ~> b, b ~> c, ]
        let substitutions = Substitutions::from_vector(vec![
            Substitution::SubstituteType {
                old: "a".to_string(),
                new: type_variable("b".to_string()),
            },
            Substitution::SubstituteType {
                old: "b".to_string(),
                new: type_variable("c".to_string()),
            },
        ]);

        // k = {x: a -> a}
        let k = Constraints(vec![Constraint {
            name: "x".to_string(),
            r#type: function_type(
                type_variable("a".to_string()),
                type_variable("a".to_string()),
            ),
        }]);

        // S(k) should be {x: c -> c}
        let expected_sk = Constraints(vec![Constraint {
            name: "x".to_string(),
            r#type: function_type(
                type_variable("c".to_string()),
                type_variable("c".to_string()),
            ),
        }]);

        let actual_sk = k.applied_by(&substitutions);

        assert_eq!(actual_sk.print(), expected_sk.print())
    }

    #[test]
    fn test_unify_1() {
        // equations = [(a -> a) = (b -> c)]
        // expected substitutions = [a ~> b, b ~> c]

        let equations = vec![Equation {
            left: function_type(
                type_variable("a".to_string()),
                type_variable("a".to_string()),
            ),
            right: function_type(
                type_variable("b".to_string()),
                type_variable("c".to_string()),
            ),
        }];

        let result = unify(equations);

        let expected = Ok(Substitutions::from_vector(vec![
            Substitution::SubstituteType {
                old: "a".to_string(),
                new: type_variable("b".to_string()),
            },
            Substitution::SubstituteType {
                old: "b".to_string(),
                new: type_variable("c".to_string()),
            },
        ])
        .print());

        assert_eq!(result.map(|substitutions| substitutions.print()), expected)
    }

    #[test]
    /// lcg({Int → Int,Bool → Bool}) = α → α
    fn test_lcg_1() {
        fn int() -> SimpleType {
            named_type("Int".to_string(), vec![])
        }
        fn bool() -> SimpleType {
            named_type("Bool".to_string(), vec![])
        }
        let int_to_int = named_type("->".to_string(), vec![int(), int()]);
        let bool_to_bool = named_type("->".to_string(), vec![bool(), bool()]);

        fn alpha() -> SimpleType {
            type_variable("'0".to_string())
        }
        let expected_type = named_type("->".to_string(), vec![alpha(), alpha()]);
        assert_eq!(
            lcg(NonEmpty(int_to_int, vec![bool_to_bool]), &mut State::new()),
            expected_type
        );
    }

    #[test]
    /// lcg({Tree Int, List Int}) = α Int
    fn test_lcg_2() {
        let int = named_type("Int".to_string(), vec![]);
        let tree_of_int = named_type("Tree".to_string(), vec![int.clone()]);
        let list_of_int = named_type("List".to_string(), vec![int.clone()]);

        let expected_type = SimpleType {
            kind: TypeKind::TypeVariable("'0".to_string()),
            arguments: vec![int],
        };
        assert_eq!(
            lcg(NonEmpty(tree_of_int, vec![list_of_int]), &mut State::new()),
            expected_type
        );
    }

    #[test]
    /// lcg({Tree β, List β}) = α α′
    fn test_lcg_3() {
        let beta = type_variable("β".to_string());
        let tree_of_beta = named_type("Tree".to_string(), vec![beta.clone()]);
        let list_of_beta = named_type("List".to_string(), vec![beta.clone()]);

        let expected_type = SimpleType {
            kind: TypeKind::TypeVariable("'0".to_string()),
            arguments: vec![type_variable("'1".to_string())],
        };
        assert_eq!(
            lcg(
                NonEmpty(tree_of_beta, vec![list_of_beta]),
                &mut State::new()
            ),
            expected_type
        )
    }

    #[test]
    /// To elucidate the meaning of sat, consider a typing context Γ that has overloaded symbols f
    /// and one, with typings (f : Int → Float), (f : Float → Int), (one : Int) and (one : Float).
    ///
    /// Then sat({f : α → β,one : α},Γ) is a set with two substitutions, say {S1,S2},
    /// where S1 = (α → Int,β → Float)
    ///   and S2 = (α → Float, β → Int).
    fn test_sat_1() {
        let gamma = TypingContext(
            Set::new()
                .insert(Typing {
                    variable: "f".to_string(),
                    r#type: function_type(int(), float()).as_type(),
                })
                .insert(Typing {
                    variable: "f".to_string(),
                    r#type: function_type(float(), int()).as_type(),
                })
                .insert(Typing {
                    variable: "one".to_string(),
                    r#type: int().as_type(),
                })
                .insert(Typing {
                    variable: "one".to_string(),
                    r#type: float().as_type(),
                }),
        );

        let s1 = Substitutions::Compose {
            left: Box::new(Substitutions::Compose {
                left: Box::new(Substitutions::Identity),
                right: Substitution::SubstituteType {
                    old: "b".to_string(),
                    new: int(),
                },
            }),
            right: Substitution::SubstituteType {
                old: "a".to_string(),
                new: float(),
            },
        }
        .print();
        let s2 = Substitutions::Compose {
            left: Box::new(Substitutions::Compose {
                left: Box::new(Substitutions::Identity),
                right: Substitution::SubstituteType {
                    old: "b".to_string(),
                    new: float(),
                },
            }),
            right: Substitution::SubstituteType {
                old: "a".to_string(),
                new: int(),
            },
        }
        .print();

        // {f : α → β,one : α}
        let k = Constraints(vec![
            Constraint {
                name: "f".to_string(),
                r#type: function_type(
                    type_variable("a".to_string()),
                    type_variable("b".to_string()),
                ),
            },
            Constraint {
                name: "one".to_string(),
                r#type: type_variable("a".to_string()),
            },
        ]);

        let mut actual = sat(k, &gamma)
            .iter()
            .map(Substitutions::print)
            .collect::<Vec<String>>();
        actual.sort();
        assert_eq!(actual, vec![s1, s2]);
    }

    #[test]
    /// Created by myself to test for negative cases
    fn test_sat_2() {
        fn int() -> SimpleType {
            named_type("int".to_string(), vec![])
        }
        fn float() -> SimpleType {
            named_type("float".to_string(), vec![])
        }
        let gamma = TypingContext(
            Set::new()
                .insert(Typing {
                    variable: "f".to_string(),
                    r#type: function_type(int(), float()).as_type(),
                })
                .insert(Typing {
                    variable: "one".to_string(),
                    r#type: float().as_type(),
                }),
        );

        // {f : α → β,one : α}
        let k = Constraints(vec![
            Constraint {
                name: "f".to_string(),
                r#type: function_type(
                    type_variable("a".to_string()),
                    type_variable("b".to_string()),
                ),
            },
            Constraint {
                name: "one".to_string(),
                r#type: type_variable("a".to_string()),
            },
        ]);
        assert!(sat(k, &gamma).is_empty());
    }

    #[test]
    fn appendix_example_1() {
        // In a typing context Γ with typings, say, f : Int → Int and f : Float → Float, term:
        //
        //   λx. let y = f x in x
        //
        // has type {f : α → α}.α → α, not α → α.

        let env = TypingEnvironment {
            elements: Set::new()
                .insert(TypingEnvElement::new(
                    "f".to_string(),
                    Type::new_simple_type(function_type(int(), int())),
                ))
                .insert(TypingEnvElement::new(
                    "f".to_string(),
                    Type::new_simple_type(function_type(float(), float())),
                )),
        };

        let term = Term::Lambda {
            parameter: "x".to_string(),
            body: Box::new(Term::Let {
                name: "y".to_string(),
                value: Box::new(Term::Application {
                    function: Box::new(Term::Var {
                        name: "f".to_string(),
                    }),
                    argument: Box::new(Term::Var {
                        name: "x".to_string(),
                    }),
                }),
                body: Box::new(Term::Var {
                    name: "x".to_string(),
                }),
            }),
        };

        let a = type_variable("'0".to_string());
        let expected_type = Ok(ConstrainedType {
            constraints: Constraints(vec![Constraint {
                name: "#0".to_string(),
                r#type: function_type(a.clone(), a.clone()),
            }]),
            r#type: function_type(a.clone(), a.clone()),
        }
        .alpha_conversion()
        .print());

        assert_eq!(
            ppc(term.clone(), &env).map(|result| result.0.alpha_conversion().print()),
            expected_type
        );

        // An application of this term to another of type Int (or Float) is well-typed.
        assert_eq!(
            ppc(
                Term::Application {
                    function: Box::new(term.clone()),
                    argument: Box::new(Term::Int(0))
                },
                &env
            )
            .map(|result| result.0),
            Ok(ConstrainedType::new_simple_type(int()))
        );

        assert_eq!(
            ppc(
                Term::Application {
                    function: Box::new(term.clone()),
                    argument: Box::new(Term::Float(0.0))
                },
                &env
            )
            .map(|result| result.0),
            Ok(ConstrainedType::new_simple_type(float()))
        );

        // while an application to a term of type Bool, for example, is not.
        assert_eq!(
            ppc(
                Term::Application {
                    function: Box::new(term),
                    argument: Box::new(Term::Bool(true))
                },
                &env
            ),
            Err(InferError::NotSatifiable)
        );
    }
}
impl Equation {
    fn print(&self) -> String {
        format!("{} = {}", self.left.print(), self.right.print())
    }
    fn substitute_type(&self, type_variable: &String, with_type: &SimpleType) -> Equation {
        Equation {
            left: self.left.substitute_type(type_variable, with_type),
            right: self.right.substitute_type(type_variable, with_type),
        }
    }

    fn substitute_type_kind(&self, type_variable: &str, new_type_kind: &TypeKind) -> Equation {
        Equation {
            left: self.left.substitute_type_kind(type_variable, new_type_kind),
            right: self
                .right
                .substitute_type_kind(type_variable, new_type_kind),
        }
    }
}

fn vect_difference<T: Eq + Clone>(v1: &Vec<T>, v2: &Vec<T>) -> Vec<T> {
    v1.iter().filter(|&x| !v2.contains(x)).cloned().collect()
}

impl ops::Sub<TypeVariables> for TypeVariables {
    type Output = TypeVariables;

    fn sub(self, rhs: TypeVariables) -> Self::Output {
        TypeVariables(vect_difference(&self.0, &rhs.0))
    }
}

impl Substitution {
    fn print(&self) -> String {
        match self {
            Substitution::SubstituteType { old, new } => {
                format!("{} ~> {}", old, new.print())
            }
            Substitution::SubstituteTypeKind { old, new } => {
                format!("{} ~>> {}", old, new.print())
            }
        }
    }

    fn type_variable(&self) -> String {
        match self {
            Substitution::SubstituteType { old, .. } => old.to_string(),
            Substitution::SubstituteTypeKind { old, .. } => old.to_string(),
        }
    }

    fn apply(&self, simple_type: &SimpleType) -> SimpleType {
        match self {
            Substitution::SubstituteType { old, new } => match &simple_type.kind {
                TypeKind::TypeConstructor(c) => SimpleType {
                    kind: TypeKind::TypeConstructor(c.clone()),
                    arguments: simple_type
                        .arguments
                        .iter()
                        .map(|argument| self.apply(argument))
                        .collect(),
                },
                TypeKind::TypeVariable(a) => {
                    if a.eq(old) {
                        new.clone()
                    } else {
                        simple_type.clone()
                    }
                }
            },
            Substitution::SubstituteTypeKind { old, new } => match &simple_type.kind {
                TypeKind::TypeConstructor(x) | TypeKind::TypeVariable(x) => {
                    let kind = if x.eq(old) {
                        new.clone()
                    } else {
                        simple_type.kind.clone()
                    };
                    SimpleType {
                        kind,
                        arguments: simple_type
                            .arguments
                            .iter()
                            .map(|argument| self.apply(argument))
                            .collect(),
                    }
                }
            },
        }
    }
}

impl TypeVariables {
    fn is_subset_of(&self, v: &TypeVariables) -> bool {
        use std::collections::HashSet;

        let xs: HashSet<String> = HashSet::from_iter(self.0.clone().into_iter());
        xs.is_subset(&HashSet::from_iter(v.0.clone().into_iter()))
    }

    fn contains(&self, a: &String) -> bool {
        self.0.contains(a)
    }

    fn intersect(&self, other: &TypeVariables) -> TypeVariables {
        TypeVariables(self.0.intersect(other.0.clone()))
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn union(&self, other: TypeVariables) -> TypeVariables {
        TypeVariables(self.0.union(other.0))
    }
}
impl Typing {
    fn print(&self) -> String {
        format!("{}: {}", self.variable, self.r#type.print())
    }
}
