use std::collections::HashMap;

#[derive(Debug, PartialEq)]
pub enum Expr {
    Var(String),
    Call(Box<Expr>, Vec<Expr>),
    Fun(Vec<String>, Box<Expr>),
    Let(String, Box<Expr>, Box<Expr>),
}

pub type Id = usize;
pub type Level = i64;

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    Const(String),
    App(Box<Type>, Vec<Type>),
    Arrow(Vec<Type>, Box<Type>),
    Var(Id),
}

pub fn replace_ty_constants_with_vars(env: &HashMap<String, Type>, ty: Type) -> Type {
    match ty {
        Type::Const(name) => match env.get(&name) {
            Some(ty) => ty.clone(),
            None => Type::Const(name),
        },
        Type::Var(_) => ty,
        Type::App(ty, args) => {
            let ty = Box::new(replace_ty_constants_with_vars(env, *ty));
            let args = args
                .into_iter()
                .map(|arg| replace_ty_constants_with_vars(env, arg))
                .collect();
            Type::App(ty, args)
        }
        Type::Arrow(params, ret) => {
            let params = params
                .into_iter()
                .map(|param| replace_ty_constants_with_vars(env, param))
                .collect();
            let ret = Box::new(replace_ty_constants_with_vars(env, *ret));
            Type::Arrow(params, ret)
        }
    }
}

#[derive(Clone, Debug)]
pub enum TypeVar {
    Unbound(Level),
    Link(Type),
    Generic,
}
