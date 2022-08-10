use std::collections::HashMap;

use crate::expr::{replace_ty_constants_with_vars, Expr, Id, Level, Type, TypeVar};

#[derive(Debug, PartialEq)]
pub enum Error {
    TypeVarIdNotFound(Id),
    RecursiveType,
    CannotUnify(Type, Type),
    ExpectedAFunction,
    UnexpectedNumberOfArguments,
    VariableNotFound(String),
}

type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Debug, Default)]
pub struct Env {
    pub vars: HashMap<String, Type>,
    pub tvars: Vec<TypeVar>,
}

impl Env {
    pub fn replace_ty_constants_with_vars(&mut self, vars: Vec<String>, mut ty: Type) -> Type {
        if !vars.is_empty() {
            let env: HashMap<String, Type> = vars
                .into_iter()
                .map(|name| (name, self.new_generic_tvar()))
                .collect();
            ty = replace_ty_constants_with_vars(&env, ty);
        }
        ty
    }

    fn get_var(&self, name: &str) -> Result<&Type> {
        self.vars
            .get(name)
            .ok_or_else(|| Error::VariableNotFound(name.to_owned()))
    }

    fn new_unbound_tvar(&mut self, level: Level) -> Type {
        let id = self.tvars.len();
        self.tvars.push(TypeVar::Unbound(level));
        Type::Var(id)
    }

    fn new_generic_tvar(&mut self) -> Type {
        let id = self.tvars.len();
        self.tvars.push(TypeVar::Generic);
        Type::Var(id)
    }

    fn get_tvar(&self, id: Id) -> Result<&TypeVar> {
        self.tvars.get(id).ok_or(Error::TypeVarIdNotFound(id))
    }

    fn get_mut_tvar(&mut self, id: Id) -> Result<&mut TypeVar> {
        self.tvars.get_mut(id).ok_or(Error::TypeVarIdNotFound(id))
    }

    fn link(&mut self, id: Id, ty: Type) -> Result<()> {
        let tvar = self.get_mut_tvar(id)?;
        *tvar = TypeVar::Link(ty);
        Ok(())
    }

    fn occurs_check_adjust_levels(
        &mut self,
        tvar_id: Id,
        tvar_level: Level,
        ty: &Type,
    ) -> Result<()> {
        match ty {
            Type::Var(other_id) => {
                let other_tvar = self.get_mut_tvar(*other_id)?;
                match other_tvar.clone() {
                    TypeVar::Link(ty) => self.occurs_check_adjust_levels(tvar_id, tvar_level, &ty),
                    TypeVar::Generic => panic!(),
                    TypeVar::Unbound(other_level) => {
                        if *other_id == tvar_id {
                            Err(Error::RecursiveType)
                        } else {
                            if other_level > tvar_level {
                                *other_tvar = TypeVar::Unbound(tvar_level);
                            }
                            Ok(())
                        }
                    }
                }
            }
            Type::App(ty, args) => {
                for arg in args {
                    self.occurs_check_adjust_levels(tvar_id, tvar_level, arg)?;
                }
                self.occurs_check_adjust_levels(tvar_id, tvar_level, ty)
            }
            Type::Arrow(params, ret) => {
                for param in params {
                    self.occurs_check_adjust_levels(tvar_id, tvar_level, param)?;
                }
                self.occurs_check_adjust_levels(tvar_id, tvar_level, ret)
            }
            Type::Const(_) => Ok(()),
        }
    }

    fn unify(&mut self, ty1: &Type, ty2: &Type) -> Result<()> {
        if ty1 == ty2 {
            return Ok(());
        }
        match (ty1, ty2) {
            (Type::Const(name1), Type::Const(name2)) if name1 == name2 => Ok(()),
            (Type::App(app_ty1, args1), Type::App(app_ty2, args2)) => {
                if args1.len() != args2.len() {
                    return Err(Error::CannotUnify(ty1.clone(), ty2.clone()));
                }
                for i in 0..args1.len() {
                    let arg1 = &args1[i];
                    let arg2 = &args2[i];
                    self.unify(arg1, arg2)?;
                }
                self.unify(app_ty1, app_ty2)
            }
            (Type::Arrow(params1, ret1), Type::Arrow(params2, ret2)) => {
                if params1.len() != params2.len() {
                    return Err(Error::CannotUnify(ty1.clone(), ty2.clone()));
                }
                for i in 0..params1.len() {
                    let param1 = &params1[i];
                    let param2 = &params2[i];
                    self.unify(param1, param2)?;
                }
                self.unify(ret1, ret2)
            }
            (Type::Var(id1), Type::Var(id2)) if id1 == id2 => {
                panic!("multiple instance of a type variable")
            }
            (Type::Var(id), _) => {
                let tvar = self.get_tvar(*id)?;
                match tvar.clone() {
                    TypeVar::Unbound(level) => {
                        self.occurs_check_adjust_levels(*id, level, ty2)?;
                        self.link(*id, ty2.clone())
                    }
                    TypeVar::Link(ty1) => self.unify(&ty1, ty2),
                    TypeVar::Generic => Err(Error::CannotUnify(ty1.clone(), ty2.clone())),
                }
            }
            (_, Type::Var(id)) => {
                let tvar = self.get_mut_tvar(*id)?;
                match tvar.clone() {
                    TypeVar::Unbound(level) => {
                        self.occurs_check_adjust_levels(*id, level, ty1)?;
                        self.link(*id, ty1.clone())
                    }
                    TypeVar::Link(ty2) => self.unify(ty1, &ty2),
                    TypeVar::Generic => Err(Error::CannotUnify(ty1.clone(), ty2.clone())),
                }
            }
            _ => Err(Error::CannotUnify(ty1.clone(), ty2.clone())),
        }
    }

    fn generalize(&mut self, level: Level, ty: &Type) -> Result<()> {
        match ty {
            Type::Var(id) => {
                let tvar = self.get_mut_tvar(*id)?;
                match tvar.clone() {
                    TypeVar::Unbound(other_level) if other_level > level => {
                        *tvar = TypeVar::Generic;
                        Ok(())
                    }
                    TypeVar::Unbound(_) => Ok(()),
                    TypeVar::Link(ty) => self.generalize(level, &ty),
                    TypeVar::Generic => Ok(()),
                }
            }
            Type::App(ty, args) => {
                for arg in args {
                    self.generalize(level, arg)?;
                }
                self.generalize(level, ty)
            }
            Type::Arrow(params, ret) => {
                for param in params {
                    self.generalize(level, param)?;
                }
                self.generalize(level, ret)
            }
            Type::Const(_) => Ok(()),
        }
    }

    fn instantiate(&mut self, level: Level, ty: Type) -> Result<Type> {
        let mut id_vars = HashMap::new();
        self.instantiate_impl(&mut id_vars, level, ty)
    }

    fn instantiate_impl(
        &mut self,
        id_vars: &mut HashMap<Id, Type>,
        level: Level,
        ty: Type,
    ) -> Result<Type> {
        match ty {
            Type::Const(_) => Ok(ty),
            Type::Var(id) => {
                let tvar = self.get_tvar(id)?;
                match tvar.clone() {
                    TypeVar::Unbound(_) => Ok(ty),
                    TypeVar::Link(ty) => self.instantiate_impl(id_vars, level, ty),
                    TypeVar::Generic => {
                        let ty = id_vars
                            .entry(id)
                            .or_insert_with(|| self.new_unbound_tvar(level));
                        Ok(ty.clone())
                    }
                }
            }
            Type::App(ty, args) => {
                let instantiated_ty = self.instantiate_impl(id_vars, level, *ty)?;
                let mut instantiated_args = Vec::with_capacity(args.len());
                for arg in args {
                    let instantiated_arg = self.instantiate_impl(id_vars, level, arg)?;
                    instantiated_args.push(instantiated_arg);
                }
                Ok(Type::App(Box::new(instantiated_ty), instantiated_args))
            }
            Type::Arrow(params, ret) => {
                let instantiated_ret = self.instantiate_impl(id_vars, level, *ret)?;
                let mut instantiated_params = Vec::with_capacity(params.len());
                for param in params {
                    let instantiated_param = self.instantiate_impl(id_vars, level, param)?;
                    instantiated_params.push(instantiated_param);
                }
                Ok(Type::Arrow(instantiated_params, Box::new(instantiated_ret)))
            }
        }
    }

    fn match_fun_ty(&mut self, num_params: usize, ty: Type) -> Result<(Vec<Type>, Box<Type>)> {
        match ty {
            Type::Arrow(params, ret) => {
                if params.len() != num_params {
                    Err(Error::UnexpectedNumberOfArguments)
                } else {
                    Ok((params, ret))
                }
            }
            Type::Var(id) => {
                let tvar = self.get_tvar(id)?;
                match tvar.clone() {
                    TypeVar::Unbound(level) => {
                        let mut params = Vec::with_capacity(num_params);
                        for _ in 0..num_params {
                            let param = self.new_unbound_tvar(level);
                            params.push(param);
                        }
                        let ret = Box::new(self.new_unbound_tvar(level));
                        let ty = Type::Arrow(params.clone(), ret.clone());
                        self.link(id, ty)?;
                        Ok((params, ret))
                    }
                    TypeVar::Link(ty) => self.match_fun_ty(num_params, ty),
                    TypeVar::Generic => Err(Error::ExpectedAFunction),
                }
            }
            _ => Err(Error::ExpectedAFunction),
        }
    }

    pub fn infer(&mut self, expr: &Expr) -> Result<Type> {
        let ty = self.infer_impl(0, expr)?;
        self.generalize(-1, &ty)?;
        Ok(ty)
    }

    fn infer_impl(&mut self, level: Level, expr: &Expr) -> Result<Type> {
        match expr {
            Expr::Var(name) => {
                let ty = self.get_var(name)?.clone();
                self.instantiate(level, ty)
            }
            Expr::Fun(params, body) => {
                let mut param_tys = Vec::with_capacity(params.len());
                let old_vars = self.vars.clone();
                for param in params {
                    let param_ty = self.new_unbound_tvar(level);
                    self.vars.insert(param.to_owned(), param_ty.clone());
                    param_tys.push(param_ty);
                }
                let ret_ty = self.infer_impl(level, body)?;
                self.vars = old_vars;
                Ok(Type::Arrow(param_tys, Box::new(ret_ty)))
            }
            Expr::Let(name, value, body) => {
                let var_ty = self.infer_impl(level + 1, value)?;
                self.generalize(level, &var_ty)?;
                self.vars.insert(name.clone(), var_ty);
                self.infer_impl(level, body)
            }
            Expr::Call(f, args) => {
                let f_ty = self.infer_impl(level, f)?;
                let (params, ret) = self.match_fun_ty(args.len(), f_ty)?;
                for i in 0..args.len() {
                    let arg = &args[i];
                    let arg_ty = self.infer_impl(level, arg)?;
                    let param = &params[i];
                    self.unify(&arg_ty, param)?;
                }
                Ok(*ret)
            }
        }
    }

    pub fn ty_to_string(&self, ty: &Type) -> Result<String> {
        let mut namer = Namer::new();
        self.ty_to_string_impl(&mut namer, ty, false)
    }

    fn ty_to_string_impl(&self, namer: &mut Namer, ty: &Type, is_simple: bool) -> Result<String> {
        match ty {
            Type::Const(name) => Ok(name.clone()),
            Type::App(ty, args) => {
                let mut ty_str = self.ty_to_string_impl(namer, ty, true)?;
                ty_str.push('[');
                for (i, arg) in args.iter().enumerate() {
                    if i != 0 {
                        ty_str.push_str(", ")
                    }
                    let arg = self.ty_to_string_impl(namer, arg, false)?;
                    ty_str.push_str(&arg);
                }
                ty_str.push(']');
                Ok(ty_str)
            }
            Type::Arrow(params, ret) => {
                let mut ty_str = if is_simple {
                    "(".to_owned()
                } else {
                    "".to_owned()
                };
                if params.len() == 1 {
                    let param = self.ty_to_string_impl(namer, &params[0], true)?;
                    let ret = self.ty_to_string_impl(namer, ret, false)?;
                    ty_str.push_str(&param);
                    ty_str.push_str(" -> ");
                    ty_str.push_str(&ret);
                } else {
                    ty_str.push('(');
                    for (i, param) in params.iter().enumerate() {
                        if i != 0 {
                            ty_str.push_str(", ");
                        }
                        let param = self.ty_to_string_impl(namer, param, false)?;
                        ty_str.push_str(&param);
                    }
                    let ret = self.ty_to_string_impl(namer, ret, false)?;
                    ty_str.push_str(") -> ");
                    ty_str.push_str(&ret);
                }
                if is_simple {
                    ty_str.push(')');
                }
                Ok(ty_str)
            }
            Type::Var(id) => {
                let tvar = self.get_tvar(*id)?;
                match tvar {
                    TypeVar::Generic => {
                        let name = namer.get_or_insert(*id);
                        Ok(name.to_string())
                    }
                    TypeVar::Unbound(_) => Ok(format!("_{}", id)),
                    TypeVar::Link(ty) => self.ty_to_string_impl(namer, ty, is_simple),
                }
            }
        }
    }
}

struct Namer {
    next_name: u8,
    names: HashMap<Id, u8>,
}

impl Namer {
    fn new() -> Self {
        let next_name = 97;
        let names = HashMap::new();
        Self { next_name, names }
    }

    fn get_or_insert(&mut self, id: Id) -> char {
        let name = match self.names.get(&id) {
            Some(name) => *name,
            None => {
                let name = self.next_name;
                self.next_name += 1;
                self.names.insert(id, name);
                name
            }
        };
        name as char
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        core::make_env,
        expr::Type,
        parser::{parse_expr, parse_ty},
    };

    use super::Error;

    enum Expected {
        Pass(String),
        Fail(Error),
    }

    fn pass(sig: &str) -> Expected {
        Expected::Pass(sig.to_owned())
    }

    fn fail(e: Error) -> Expected {
        Expected::Fail(e)
    }

    #[test]
    fn infer() {
        let test_cases: Vec<(&str, Expected)> = vec![
            ("id", pass("forall[a] a -> a")),
            ("one", pass("int")),
            ("x", fail(Error::VariableNotFound("x".to_owned()))),
            (
                "let x = x in x",
                fail(Error::VariableNotFound("x".to_owned())),
            ),
            ("let x = id in x", pass("forall[a] a -> a")),
            ("let x = fun y -> y in x", pass("forall[a] a -> a")),
            ("fun x -> x", pass("forall[a] a -> a")),
            ("fun x -> x", pass("forall[int] int -> int")),
            ("pair", pass("forall[a b] (a, b) -> pair[a, b]")),
            ("pair", pass("forall[z x] (x, z) -> pair[x, z]")),
            (
                "fun x -> let y = fun z -> z in y",
                pass("forall[a b] a -> b -> b"),
            ),
            (
                "let f = fun x -> x in let id = fun y -> y in eq(f, id)",
                pass("bool"),
            ),
            (
                "let f = fun x -> x in let id = fun y -> y in eq_curry(f)(id)",
                pass("bool"),
            ),
            ("let f = fun x -> x in eq(f, succ)", pass("bool")),
            ("let f = fun x -> x in eq_curry(f)(succ)", pass("bool")),
            (
                "let f = fun x -> x in pair(f(one), f(true))",
                pass("pair[int, bool]"),
            ),
            (
                "fun f -> pair(f(one), f(true))",
                fail(Error::CannotUnify(
                    Type::Const("bool".to_owned()),
                    Type::Const("int".to_owned()),
                )),
            ),
            (
                "let f = fun x y -> let a = eq(x, y) in eq(x, y) in f",
                pass("forall[a] (a, a) -> bool"),
            ),
            (
                "let f = fun x y -> let a = eq_curry(x)(y) in eq_curry(x)(y) in f",
                pass("forall[a] (a, a) -> bool"),
            ),
            ("id(id)", pass("forall[a] a -> a")),
            (
                "choose(fun x y -> x, fun x y -> y)",
                pass("forall[a] (a, a) -> a"),
            ),
            (
                "choose_curry(fun x y -> x)(fun x y -> y)",
                pass("forall[a] (a, a) -> a"),
            ),
            (
                "let x = id in let y = let z = x(id) in z in y",
                pass("forall[a] a -> a"),
            ),
            ("cons(id, nil)", pass("forall[a] list[a -> a]")),
            ("cons_curry(id)(nil)", pass("forall[a] list[a -> a]")),
            (
                "let lst1 = cons(id, nil) in let lst2 = cons(succ, lst1) in lst2",
                pass("list[int -> int]"),
            ),
            (
                "cons_curry(id)(cons_curry(succ)(cons_curry(id)(nil)))",
                pass("list[int -> int]"),
            ),
            (
                "plus(one, true)",
                fail(Error::CannotUnify(
                    Type::Const("bool".to_owned()),
                    Type::Const("int".to_owned()),
                )),
            ),
            ("plus(one)", fail(Error::UnexpectedNumberOfArguments)),
            ("fun x -> let y = x in y", pass("forall[a] a -> a")),
            (
                "fun x -> let y = let z = x(fun x -> x) in z in y",
                pass("forall[a b] ((a -> a) -> b) -> b"),
            ),
            (
                "fun x -> fun y -> let x = x(y) in x(y)",
                pass("forall[a b] (a -> a -> b) -> a -> b"),
            ),
            (
                "fun x -> let y = fun z -> x(z) in y",
                pass("forall[a b] (a -> b) -> a -> b"),
            ),
            (
                "fun x -> let y = fun z -> x in y",
                pass("forall[a b] a -> b -> a"),
            ),
            (
                "fun x -> fun y -> let x = x(y) in fun x -> y(x)",
                pass("forall[a b c] ((a -> b) -> c) -> (a -> b) -> a -> b"),
            ),
            ("fun x -> let y = x in y(y)", fail(Error::RecursiveType)),
            (
                "fun x -> let y = fun z -> z in y(y)",
                pass("forall[a b] a -> b -> b"),
            ),
            ("fun x -> x(x)", fail(Error::RecursiveType)),
            ("one(id)", fail(Error::ExpectedAFunction)),
            (
                "fun f -> let x = fun g y -> let _ = g(y) in eq(f, g) in x",
                pass("forall[a b] (a -> b) -> (a -> b, a) -> bool"),
            ),
            (
                "let const = fun x -> fun y -> x in const",
                pass("forall[a b] a -> b -> a"),
            ),
            (
                "let apply = fun f x -> f(x) in apply",
                pass("forall[a b] (a -> b, a) -> b"),
            ),
            (
                "let apply_curry = fun f -> fun x -> f(x) in apply_curry",
                pass("forall[a b] (a -> b) -> a -> b"),
            ),
        ];
        let env = make_env();
        for (expr, expected) in test_cases {
            match expected {
                Expected::Pass(expected) => {
                    let (vars, ty) = parse_ty(&expected).unwrap();
                    let mut env = env.clone();
                    let expected = env.replace_ty_constants_with_vars(vars, ty);
                    let expr = parse_expr(expr).unwrap();
                    let actual = env.infer_impl(0, &expr).unwrap();
                    env.generalize(-1, &actual).unwrap();
                    let expected = env.ty_to_string(&expected).unwrap();
                    let actual = env.ty_to_string(&actual).unwrap();
                    assert_eq!(expected, actual);
                }
                Expected::Fail(expected) => {
                    let mut env = env.clone();
                    let expr = parse_expr(expr).unwrap();
                    let actual = env.infer_impl(0, &expr).unwrap_err();
                    assert_eq!(expected, actual);
                }
            }
        }
    }
}
