use std::rc::Rc;
use std::{borrow::Borrow, collections::HashMap};

type Name = String;

enum Expr {
    Var(Name),
    Call(Box<Expr>, Vec<Expr>),
    Fun(Vec<Name>, Box<Expr>),
    Let(Name, Box<Expr>, Box<Expr>),
}

impl ToString for Expr {
    fn to_string(&self) -> String {
        fn f(is_simple: bool, expr: &Expr) -> String {
            match expr {
                Expr::Var(name) => name.clone(),
                Expr::Call(fun, args) => {
                    let str_fun = f(true, fun);
                    let str_args = args
                        .into_iter()
                        .map(|arg| f(false, arg))
                        .collect::<Vec<String>>()
                        .join(", ");
                    format!("{}({})", str_fun, str_args)
                }
                Expr::Fun(params, body) => {
                    let str_params = params.join(" ");
                    let str_body = f(false, body);
                    let str_fun = format!("fun {} -> {}", str_params, str_body);
                    if is_simple {
                        format!("({})", str_fun)
                    } else {
                        str_fun
                    }
                }
                Expr::Let(name, value, body) => {
                    let value_str = f(false, value);
                    let body_str = f(false, body);
                    let let_str = format!("let {} = {} in {}", name, value_str, body_str);
                    if is_simple {
                        format!("({})", let_str)
                    } else {
                        let_str
                    }
                }
            }
        }
        f(false, self).clone()
    }
}

#[test]
fn test_expr_to_string() {
    assert_eq!(Expr::Var("a".to_owned()).to_string(), "a");
    assert_eq!(
        Expr::Call(
            Box::new(Expr::Var("f".to_owned())),
            vec![Expr::Var("a".to_owned()), Expr::Var("b".to_owned())]
        )
        .to_string(),
        "f(a, b)"
    );
    assert_eq!(
        Expr::Fun(vec!["x".to_owned()], Box::new(Expr::Var("x".to_owned()))).to_string(),
        "fun x -> x"
    );
    assert_eq!(
        Expr::Let(
            "b".to_owned(),
            Box::new(Expr::Var("a".to_owned())),
            Box::new(Expr::Var("b".to_owned()))
        )
        .to_string(),
        "let b = a in b"
    );
}

type Id = i64;
type Level = i64;

enum Type {
    Const(Name),
    App(Box<Type>, Vec<Type>),
    Arrow(Vec<Type>, Box<Type>),
    Var(TypeVar),
}

enum TypeVar {
    Unbound(Id, Level),
    Link(Rc<Type>),
    Generic(Id),
}

struct NameEnv {
    count: u8,
    names: HashMap<Id, Name>,
}

impl NameEnv {
    fn next(&mut self) -> Name {
        let i = self.count;
        self.count = self.count + 1;
        ((i + 97) as char).to_string()
    }

    fn get(&self, id: &Id) -> Option<Name> {
        self.names.get(id).map(|name| name.clone())
    }

    fn get_or_next(&mut self, id: &Id) -> Name {
        match self.get(id) {
            Option::Some(name) => name,
            Option::None => {
                let name = self.next();
                self.names.insert(id.clone(), name.clone());
                name
            }
        }
    }
}

impl ToString for Type {
    fn to_string(&self) -> String {
        let mut name_env = NameEnv {
            count: 0,
            names: HashMap::new(),
        };
        fn f(name_env: &mut NameEnv, is_simple: bool, ty: &Type) -> String {
            match ty {
                Type::Const(name) => name.clone(),
                Type::App(ty, ty_args) => {
                    let str_ty = f(name_env, true, ty);
                    let str_ty_args = ty_args
                        .into_iter()
                        .map(|ty_arg| f(name_env, false, ty_arg))
                        .collect::<Vec<String>>()
                        .join(", ");
                    format!("{}[{}]", str_ty, str_ty_args)
                }
                Type::Arrow(params, ret) => {
                    let str_arrow_ty = match params[..].borrow() {
                        [param] => {
                            let str_param = f(name_env, true, param.borrow());
                            let str_ret = f(name_env, false, ret);
                            format!("{} -> {}", str_param, str_ret)
                        }
                        _ => {
                            let str_params = params
                                .into_iter()
                                .map(|param| f(name_env, false, param))
                                .collect::<Vec<String>>()
                                .join(", ");
                            let str_ret = f(name_env, false, ret);
                            format!("({}) -> {}", str_params, str_ret)
                        }
                    };
                    if is_simple {
                        format!("({})", str_arrow_ty)
                    } else {
                        str_arrow_ty
                    }
                }
                Type::Var(TypeVar::Generic(id)) => name_env.get_or_next(id),
                Type::Var(TypeVar::Unbound(id, _)) => format!("_{}", id),
                Type::Var(TypeVar::Link(ty)) => f(name_env, is_simple, ty),
            }
        }
        let ty_str = f(&mut name_env, false, self);
        if name_env.count > 0 {
            let var_names = name_env
                .names
                .values()
                .into_iter()
                .map(|v| v.clone())
                .collect::<Vec<String>>()
                .join(" ");
            format!("forall[{}] {}", var_names, ty_str)
        } else {
            ty_str
        }
    }
}

#[test]
fn test_type_to_string() {
    assert_eq!(Type::Const("int".to_owned()).to_string(), "int");
    assert_eq!(
        Type::App(
            Box::new(Type::Const("list".to_owned())),
            vec![Type::Const("int".to_owned())]
        )
        .to_string(),
        "list[int]"
    );
    assert_eq!(
        Type::Arrow(
            vec![Type::Const("int".to_owned()), Type::Const("int".to_owned())],
            Box::new(Type::Const("int".to_owned()))
        )
        .to_string(),
        "(int, int) -> int"
    );
    assert_eq!(Type::Var(TypeVar::Generic(0)).to_string(), "forall[a] a");
    assert_eq!(Type::Var(TypeVar::Unbound(0, 0)).to_string(), "_0");
    assert_eq!(
        Type::Var(TypeVar::Link(Rc::new(Type::Const("int".to_owned())))).to_string(),
        "int"
    );
}
