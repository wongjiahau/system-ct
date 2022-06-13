use rpds::{HashTrieMap as Map, HashTrieSet as Set};

enum Term {
    /// x
    Var { name: String },
    /// λu.e
    Lambda { parameter: String, body: Box<Term> },
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
struct Type {
    kind: TypeKind,
    arguments: Vec<Type>,
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
enum TypeKind {
    Named(String),
    TypeVariable(String),
}

/// ∆ ::= {oi : τi}. τ
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct ConstrainedType {
    constraints: Vec<Constraint>,
    r#type: Type,
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct Constraint {
    name: String,
    r#type: Type,
}

/// Known as "Types" in the paper.
/// σ ::= ∀αi. ∆
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct Scheme {
    type_variables: Vec<String>,
    constrained_type: ConstrainedType,
}

impl Scheme {
    fn instantiate(&self, state: &mut State) -> ConstrainedType {
        self.type_variables
            .iter()
            .fold(self.constrained_type.clone(), |result, type_variable| {
                result.rename(type_variable, &state.fresh_type_variable())
            })
    }
}

impl ConstrainedType {
    fn rename(self, old: &String, new: &String) -> ConstrainedType {
        ConstrainedType {
            constraints: self
                .constraints
                .into_iter()
                .map(|constraint| constraint.rename(old, new))
                .collect(),
            r#type: self.r#type.rename(old, new),
        }
    }
}

impl Constraint {
    fn rename(self, old: &String, new: &String) -> Constraint {
        Constraint {
            name: new.clone(),
            r#type: self.r#type.rename(old, new),
        }
    }
}

impl Type {
    fn rename(self, old: &String, new: &String) -> Type {
        Type {
            kind: self.kind,
            arguments: self
                .arguments
                .into_iter()
                .map(|argument| argument.rename(old, new))
                .collect(),
        }
    }
}

/// The type inference algorithm uses typing environments A, which are sets of elements x : (σ,Γ).
/// Pair (σ,Γ) is called an entry for x in A. We write A(x) for the set of entries of x in A, and
/// At(x) for the set of first elements (i.e. the types) in these entries.
struct TypingEnvironment {
    elements: Set<TypingEnvElement>,
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct TypingEnvElement {
    name: String,
    entry: TypingEntry,
}

#[derive(PartialEq, Eq, Clone, Debug)]
struct TypingEntry {
    scheme: Scheme,
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
struct TypingContext(Set<Typing>);

impl TypingContext {
    fn types_of(&self, name: &String) -> Set<Scheme> {
        self.0
            .iter()
            .filter_map(|typing| {
                if typing.name.eq(name) {
                    Some(typing.scheme.clone())
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

    fn substitute(&self, old_term_variable: &String, new_term_variable: &String) -> TypingContext {
        TypingContext(self.0.into_iter().fold(Set::new(), |result, entry| {
            result.insert(Typing {
                name: if entry.name.eq(old_term_variable) {
                    new_term_variable.clone()
                } else {
                    entry.name.clone()
                },
                scheme: entry.scheme.clone(),
            })
        }))
    }
}

/// A pair x : σ is called a typing for x
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct Typing {
    name: String,
    scheme: Scheme,
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

struct State {
    /// Used for generating fresh type variable
    fresh_type_variable_index: usize,
    /// Used for generating fresh term variable
    fresh_term_variable_index: usize,
}

impl State {
    fn new() -> State {
        State {
            fresh_type_variable_index: 0,
            fresh_term_variable_index: 0,
        }
    }
    fn fresh_type_variable(&mut self) -> String {
        let result = format!("'{}", self.fresh_type_variable_index);
        self.fresh_type_variable_index += 1;
        return result;
    }
    fn fresh_term_variable(&mut self) -> String {
        let result = format!("#{}", self.fresh_term_variable_index);
        self.fresh_term_variable_index += 1;
        return result;
    }
}

/// The type inference algorithm.
fn ppc(term: Term, env: TypingEnvironment, state: &mut State) -> (ConstrainedType, TypingContext) {
    match term {
        // PPc(x,A) = ptε(x,A)
        Term::Var { name } => pte(name, env, state),

        // PPc(λu.e,A) =
        Term::Lambda { parameter: u, body } => {
            // let (κ. τ, Γ ) = P Pc(e, A)
            let (
                ConstrainedType {
                    constraints: k,
                    r#type: t,
                },
                gamma,
            ) = ppc(*body, env, state);
            //  if u:τ′ ∈ Γ,for some τ′
            if let Some(scheme) = gamma
                .types_of(&u)
                .into_iter()
                .collect::<Vec<&Scheme>>()
                .first()
            //    then (κ. τ′ → τ, Γ − {u : τ′})
            {
                if scheme.type_variables.is_empty()
                    && scheme.constrained_type.constraints.is_empty()
                {
                    let t_prime = scheme.constrained_type.r#type.clone();
                    return (
                        ConstrainedType {
                            constraints: k,
                            r#type: function_type(t_prime, t),
                        },
                        TypingContext(gamma.0.remove(&Typing {
                            name: u.clone(),
                            scheme: scheme.clone().clone(),
                        })),
                    );
                }
            }

            //    else (κ. α → τ, Γ ), where α is a fresh type variable
            let a = type_variable(state.fresh_type_variable(), vec![]);
            (
                ConstrainedType {
                    constraints: k,
                    r#type: function_type(a, t),
                },
                gamma,
            )
        }

        Term::Application { function, argument } => todo!(),
        Term::Let { name, value, body } => todo!(),
    }
}

fn type_variable(name: String, arguments: Vec<Type>) -> Type {
    Type {
        kind: TypeKind::TypeVariable(name),
        arguments,
    }
}

fn function_type(input: Type, output: Type) -> Type {
    Type {
        kind: TypeKind::Named("->".to_string()),
        arguments: vec![input, output],
    }
}

/// Expression ptε(x,A) computes both type and context for x in A, similarly to pt(x,Γ),
/// introducing fresh type variables for let-bound variables as defined below:
fn pte(
    name: String,
    env: TypingEnvironment,
    state: &mut State,
) -> (ConstrainedType, TypingContext) {
    match env.types_of(&name).split_first() {
        // if A(x) = ∅ then (α, {x : α}), where α is a fresh type variable
        None => {
            let a = ConstrainedType {
                constraints: vec![],
                r#type: Type {
                    kind: TypeKind::TypeVariable(state.fresh_type_variable()),
                    arguments: vec![],
                },
            };
            let context = TypingContext(Set::new().insert(Typing {
                name,
                scheme: Scheme {
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
                    constraints: vec![Constraint {
                        name: state.fresh_term_variable(),
                        r#type: lcgti.clone(),
                    }],
                    r#type: lcgti,
                },
                tail.iter()
                    .fold(head.context.substitute(&name, &x_prime), |result, entry| {
                        result.union(&entry.context.substitute(&name, &x_prime))
                    }),
            )
        }
    }
}

struct NonEmpty<T>(T, Vec<T>);

fn lcg(types: NonEmpty<Type>, state: &mut State) -> Type {
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

fn lcgp(t1: &Type, t2: &Type, state: &mut State) -> Type {
    if t1.arguments.len() != t2.arguments.len() {
        return Type {
            kind: TypeKind::TypeVariable(state.fresh_type_variable()),
            arguments: vec![],
        };
    }
    let lcg0 = match (&t1.kind, &t2.kind) {
        (TypeKind::Named(a), TypeKind::Named(b)) if a == b => TypeKind::Named(a.clone()),
        _ => TypeKind::TypeVariable(state.fresh_type_variable()),
    };

    // This vector is needed to implement this:
    //   ...and type variables are renamed so that α ≡ α′ whenever there exist τa, τb such that
    //   lcgp(τa, τb) = α and lcgp(τa, τb) = α′
    let mut generated_type_variables: Vec<(Set<Type>, /*type variable name*/ String)> = vec![];
    let lcgi = t1
        .arguments
        .iter()
        .zip(t2.arguments.iter())
        .map(|(t1_arg, t2_arg)| {
            if let Some(a) =
                generated_type_variables
                    .iter()
                    .find_map(|(types, type_variable_name)| {
                        if types.eq(&Set::new().insert(t1_arg.clone()).insert(t2_arg.clone())) {
                            Some(type_variable_name)
                        } else {
                            None
                        }
                    })
            {
                return Type {
                    kind: TypeKind::TypeVariable(a.clone()),
                    arguments: vec![],
                };
            }
            match lcgp(t1_arg, t2_arg, state) {
                Type {
                    kind: TypeKind::TypeVariable(a),
                    arguments,
                } => {
                    generated_type_variables.push((
                        Set::new().insert(t1_arg.clone()).insert(t2_arg.clone()),
                        a.clone(),
                    ));
                    Type {
                        kind: TypeKind::TypeVariable(a),
                        arguments,
                    }
                }
                other => other,
            }
        })
        .collect();

    Type {
        kind: lcg0,
        arguments: lcgi,
    }
}

#[cfg(test)]
mod tests {
    // Note this useful idiom: importing names from outer (for mod tests) scope.
    use super::*;

    fn named_type(name: String, arguments: Vec<Type>) -> Type {
        Type {
            kind: TypeKind::Named(name),
            arguments,
        }
    }

    #[test]
    /// lcg({Int → Int,Bool → Bool}) = α → α
    fn test_lcg_1() {
        fn int() -> Type {
            named_type("Int".to_string(), vec![])
        }
        fn bool() -> Type {
            named_type("Bool".to_string(), vec![])
        }
        let int_to_int = named_type("->".to_string(), vec![int(), int()]);
        let bool_to_bool = named_type("->".to_string(), vec![bool(), bool()]);

        fn alpha() -> Type {
            type_variable("'0".to_string(), vec![])
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

        let expected_type = type_variable("'0".to_string(), vec![int]);
        assert_eq!(
            lcg(NonEmpty(tree_of_int, vec![list_of_int]), &mut State::new()),
            expected_type
        );
    }

    #[test]
    /// lcg({Tree β, List β}) = α α′
    fn test_lcg_3() {
        let beta = type_variable("β".to_string(), vec![]);
        let tree_of_beta = named_type("Tree".to_string(), vec![beta.clone()]);
        let list_of_beta = named_type("List".to_string(), vec![beta.clone()]);

        let expected_type = type_variable(
            "'0".to_string(),
            vec![type_variable("'1".to_string(), vec![])],
        );
        assert_eq!(
            lcg(
                NonEmpty(tree_of_beta, vec![list_of_beta]),
                &mut State::new()
            ),
            expected_type
        )
    }
}
