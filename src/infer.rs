use array_tool::vec::{Intersect, Union, Uniq};
use rpds::HashTrieSet as Set;

pub enum Term {
    Int(isize),
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
                if t.free_type_variables().intersect(v.to_vec()).is_empty() {
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

    fn union(&self, s: Constraints) -> Constraints {
        todo!()
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
    type_variables: TypeVariables,
    constrained_type: ConstrainedType,
}

impl Type {
    fn is_simple_type(&self) -> bool {
        self.type_variables.is_empty() && self.constrained_type.constraints.is_empty()
    }
    fn instantiate(&self, state: &mut State) -> ConstrainedType {
        self.type_variables
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
}

impl ConstrainedType {
    fn substitute_type(&self, type_variable: &String, with_type: &SimpleType) -> ConstrainedType {
        ConstrainedType {
            constraints: self.constraints.substitute_type(type_variable, with_type),
            r#type: self.r#type.substitute_type(type_variable, with_type),
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
}

impl SimpleType {
    fn substitute_type(&self, type_variable: &String, with_type: &SimpleType) -> SimpleType {
        SimpleType {
            kind: match &self.kind {
                c @ TypeKind::TypeConstructor(_) => c.clone(),
                TypeKind::TypeVariable(name) => TypeKind::TypeVariable(if name.eq(type_variable) {
                    // Assert that there is no arguments for this type,
                    // because substitution can only happen for type variable,
                    // not constructor variable
                    assert!(self.arguments.is_empty());
                    type_variable.to_string()
                } else {
                    name.clone()
                }),
            },
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
                .flat_map(|argument| argument.free_type_variables())
                .collect::<TypeVariables>(),
        );
        result
    }

    fn as_type(self) -> Type {
        Type {
            type_variables: vec![],
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
}

/// x : (σ,Γ)
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct TypingEnvElement {
    name: String,
    entry: TypingEntry,
}

/// Pair (σ,Γ) is called an entry for x in A
#[derive(PartialEq, Eq, Clone, Debug)]
struct TypingEntry {
    scheme: Type,
    context: TypingContext,
}

impl std::hash::Hash for TypingEntry {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.scheme.hash(state);
    }
}

/// A typing context Γ is a set of pairs x : σ (a let-bound variable can occur more than once in a
/// typing context). A pair x : σ is called a typing for x; if {x : σi}i=1..n is the set of typings
/// for x in Γ, then Γ(x) = {σi}i=1..n is the set of types of x in Γ
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct TypingContext(Set<Typing>);

impl TypingContext {
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
}

/// A pair x : σ is called a typing for x
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct Typing {
    variable: String,
    r#type: Type,
}

impl TypingEnvironment {
    fn types_of(&self, name: &String) -> Vec<TypingEntry> {
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
    env: &TypingEnvironment,
    state: &mut State,
) -> Result<(ConstrainedType, TypingContext), InferError> {
    match term {
        // PPc(x,A) = ptε(x,A)
        Term::Var { name } => Ok(pte(name, env, state)),

        // PPc(λu.e,A) =
        Term::Lambda { parameter: u, body } => {
            // let (κ. τ, Γ ) = P Pc(e, A)
            let (
                ConstrainedType {
                    constraints: k,
                    r#type: t,
                },
                gamma,
            ) = ppc(*body, env, state)?;
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
            // let (κ1 . τ1 , Γ1) = PPc (e1 , A)
            let (
                ConstrainedType {
                    constraints: k1,
                    r#type: t1,
                },
                gamma1,
            ) = ppc(*e1, env, state)?;

            // (κ2 . τ2 , Γ2) = PPc (e2 , A)
            let (
                ConstrainedType {
                    constraints: k2,
                    r#type: t2,
                },
                gamma2,
            ) = ppc(*e2, env, state)?;

            // S=unify({τu =τu′ |u:τu ∈ Γ1 and u:τu′ ∈ Γ2} ∪ {τ1 =τ2 → α})
            // where α is a fresh type variable
            let equations = {
                let mut equations: Vec<Equation> = gamma1
                    .intersected_variables(&gamma2)
                    .into_iter()
                    .map(|(left, right)| Equation { left, right })
                    .collect();

                let a = type_variable(state.fresh_type_variable());
                equations.push(Equation {
                    left: t1,
                    right: function_type(t2, a),
                });
                equations
            };
            let s = unify(equations)?;

            // Γ′ =SΓ1 ∪ SΓ2
            let gamma_prime = gamma1.applied_by(&s).union(&gamma2.applied_by(&s));

            // ss =sat(Sκ1 ∪ Sκ2,Γ′)
            let ss = sat(k1.applied_by(&s).union(k2.applied_by(&s)), &gamma_prime);

            // if ss =∅ then fail
            match ss.split_first() {
                None => Err(InferError::NotSatifiable),
                Some((head, tail)) => {
                    // else
                    // let S∆ = intesection ss,
                    let s_delta = intersection(NonEmpty(head.clone(), tail.to_vec()));
                    // Γ=S∆Γ′,
                    // τ=S∆Sα,
                    //V =tv(τ,Γ), κ=unresolved(S∆S(κ1 ∪κ2),Γ)
                    todo!()
                }
            }
        }
        Term::Let { name, value, body } => todo!(),
        Term::Int(_) => todo!(),
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
            todo!()
        }
    }
}

fn sat(k: Constraints, gamma: &TypingContext) -> Vec<Substitutions> {
    match k.0.split_first() {
        // sat(∅,Γ) = {id}
        None => vec![Substitutions::Identity],

        Some((head, tail)) => {
            let Constraint { name: o, r#type: t } = head;
            match tail.split_first() {
                // sat({o:τ},Γ)= U [...]
                // {S| S=Unify({τ=τi},V)and sat(Sκi,SΓ)̸=∅} where V = tv(τi) − ({(αj)i} ∪ tv(τ)) and σi = ∀(αj)i. κi. τi
                None => gamma
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
                        let v = vect_difference(
                            &t_i.free_type_variables(),
                            &a_j_i.union(t.free_type_variables()),
                        );

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
                    .collect(),
                // sat({o:τ}∪κ,Γ)=U Si∈sat({o:τ},Γ) U Sij∈sat(Siκ,SiΓ){Sij ◦Si}
                Some(_) => {
                    let k = Constraints(tail.to_vec());
                    let sis = sat(Constraints(vec![head.clone()]), gamma);
                    sis.into_iter()
                        .flat_map(|si| {
                            let sijs = sat(k.applied_by(&si), &gamma.applied_by(&si));
                            sijs.into_iter()
                                .map(|sij| sij.compose(&si))
                                .collect::<Vec<Substitutions>>()
                        })
                        .collect::<Vec<Substitutions>>()
                        .unique()
                }
            }
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
    fn print(&self) -> String {
        match self {
            Substitutions::Compose { left, right } => {
                format!("{}, {}", left.print(), right.print())
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
}

/// A type substitution (or simply substitution) is a function from type variables to simple
/// types or type constructors, that differ from the identity function (id) only on finitely
/// many variables
#[derive(Debug, PartialEq, Eq, Clone)]
enum Substitution {
    SubstituteType { old: String, new: SimpleType },
    SubstituteTypeKind { old: String, new: TypeKind },
}

#[derive(Debug, Clone)]
struct Equation {
    left: SimpleType,
    right: SimpleType,
}

fn unify(equations: Vec<Equation>) -> Result<Substitutions, InferError> {
    // unify(E) = Unify(E, ∅)
    Unify(equations, vec![])
}

#[derive(Debug)]
pub enum InferError {
    RecursiveSubstitution,
    CannotUnify { left: String, right: String },
    NotSatifiable,
}

type TypeVariables = Vec<String>;

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

/// Expression ptε(x,A) computes both type and context for x in A, similarly to pt(x,Γ),
/// introducing fresh type variables for let-bound variables as defined below:
fn pte(
    name: String,
    env: &TypingEnvironment,
    state: &mut State,
) -> (ConstrainedType, TypingContext) {
    match env.types_of(&name).split_first() {
        // if A(x) = ∅ then (α, {x : α}), where α is a fresh type variable
        None => {
            let a = ConstrainedType {
                constraints: Constraints(vec![]),
                r#type: type_variable(state.fresh_type_variable()),
            };
            let context = TypingContext(Set::new().insert(Typing {
                variable: name,
                r#type: Type {
                    type_variables: vec![],
                    constrained_type: a.clone(),
                },
            }));
            (a, context)
        }
        // if A(x)={(∀αj.κ.τ,Γ)} then(κ.τ,Γ),
        //   with quantified type variables {αj} renamed as fresh type variables
        Some((TypingEntry { scheme, context }, [])) => (scheme.instantiate(state), context.clone()),
        // else ({x′ : lcg({τi})}. lcg({τi}), U Γi[x′/x]),
        //   where A(x)={(∀(αj)i.κi.τi,Γi)} and x′ is a fresh term variable
        Some((head, tail)) => {
            let x_prime = state.fresh_term_variable();
            let lcgti = lcg(
                NonEmpty(
                    head.scheme.constrained_type.r#type.clone(),
                    tail.iter()
                        .map(|entry| entry.scheme.constrained_type.r#type.clone())
                        .collect(),
                ),
                state,
            );
            (
                ConstrainedType {
                    constraints: Constraints(vec![Constraint {
                        name: state.fresh_term_variable(),
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

    fn named_type(name: String, arguments: Vec<SimpleType>) -> SimpleType {
        SimpleType {
            kind: TypeKind::TypeConstructor(name),
            arguments,
        }
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
        assert_eq!(actual, vec![s2, s1]);
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
}
impl Equation {
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

    fn apply(&self, simple_type: &SimpleType) -> SimpleType {
        match self {
            Substitution::SubstituteType { old, new } => match &simple_type.kind {
                TypeKind::TypeConstructor(_) => simple_type.clone(),
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
                        arguments: simple_type.arguments.clone(),
                    }
                }
            },
        }
    }
}
